/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.Convex.Simplex
public import Ito2026Adversarial.Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Ito2026Adversarial.Mathlib.MeasureTheory.Measure.Weighted
public import Ito2026Adversarial.LeanMachineLearning.Online.Convex.OnlineLearner
public import Mathlib.Algebra.BigOperators.Field

/-!
# Sampling, importance weighting, and bandit algorithms from full-information learners

Many adversarial bandit algorithms maintain a probability vector `p` over the arms, pull an arm
`a ∼ p`, and feed a full-information online learner with an *estimate* of the loss vector built
from the only loss `v` they observe, the loss of the arm `a`. This file provides the three
ingredients and assembles them.

## Main definitions

* `simplexKernel ι`: the kernel sampling `i ∼ p` from a point `p` of the simplex `simplex ι`,
  built on `weightedMeasure`;
* `Bandits.importanceWeighted p i v j = 𝟙{i = j} v / p i`: the importance-weighted estimate of a
  loss vector from the loss `v` of the arm `i` drawn with probability `p i`;
* `OnlineLearner.toBanditAlgorithm L hL est hest`: the bandit algorithm running the online
  learner `L` (which plays probability vectors over the arms and is fed loss vectors) on loss
  estimates: at each round, pull an arm drawn from the current play of `L`, observe its loss `v`
  and feed `L` the estimate `est p a v` computed from the play `p` and the arm `a`
  (`OnlineLearner.banditUpdate`, `OnlineLearner.banditPolicy`). EXP3 is Hedge run in this way on
  importance-weighted estimates (`Online/Bandit/EXP3.lean`).

## Main results

* `Bandits.sum_mul_importanceWeighted`: the importance-weighted estimate is unbiased;
* `OnlineLearner.policy_toBanditAlgorithm_apply`: the policy of `L.toBanditAlgorithm` draws the
  arm from the play of `L` in the state reached on the history;
* `IsAlgEnvSeq.hasCondDistrib_action_toBanditAlgorithm`: in a run of `L.toBanditAlgorithm`, the
  arm of round `n` has conditional law `weightedMeasure (L.play s o)` given the state `s` of the
  learner and the observation `o` of round `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

/-! ### Sampling from a point of the simplex -/

namespace Learning

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]

/-- The kernel sampling an index `i ∼ p` from a point `p` of the simplex. -/
noncomputable def simplexKernel (ι : Type*) [Fintype ι] [MeasurableSpace ι] :
    Kernel (simplex ι) ι where
  toFun p := weightedMeasure p
  measurable' := measurable_weightedMeasure.comp (by fun_prop)

@[simp]
lemma simplexKernel_apply (p : simplex ι) : simplexKernel ι p = weightedMeasure p := rfl

instance : IsMarkovKernel (simplexKernel ι) :=
  ⟨fun p ↦ isProbabilityMeasure_weightedMeasure p.2.1 p.2.2⟩

/-- The kernel `simplexKernel ι` draws `i` with probability `p i`. -/
lemma simplexKernel_real_singleton [MeasurableSingletonClass ι] (p : simplex ι) (i : ι) :
    (simplexKernel ι p).real {i} = p i := by
  rw [measureReal_def, simplexKernel_apply, weightedMeasure_singleton,
    ENNReal.toReal_ofReal (p.2.1 i)]

end Learning

/-! ### Importance weighting -/

namespace Bandits

variable {ι : Type*} [DecidableEq ι]

/-- The importance-weighted estimate of a loss vector, from the loss `v` of the arm `i` drawn
with probability `p i`: `v / p i` at `i` and `0` elsewhere. -/
noncomputable def importanceWeighted (p : ι → ℝ) (i : ι) (v : ℝ) (j : ι) : ℝ :=
  if i = j then v / p i else 0

@[simp]
lemma importanceWeighted_self (p : ι → ℝ) (i : ι) (v : ℝ) : importanceWeighted p i v i = v / p i :=
  by simp [importanceWeighted]

lemma importanceWeighted_of_ne (p : ι → ℝ) {i j : ι} (v : ℝ) (h : i ≠ j) :
    importanceWeighted p i v j = 0 := by simp [importanceWeighted, h]

/-- Unbiasedness of the importance-weighted estimate: if the arm `i` is drawn with probability
`p i` and its loss is `v i`, the expectation of the estimate at `j` is `v j` (for `p j ≠ 0`). -/
lemma sum_mul_importanceWeighted [Fintype ι] {p : ι → ℝ} (v : ι → ℝ) {j : ι} (hj : p j ≠ 0) :
    ∑ i, p i * importanceWeighted p i (v i) j = v j := by
  simp only [importanceWeighted, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' univ j (fun i ↦ p i * (v i / p i))]
  simp only [Finset.mem_univ, ite_true]
  field_simp

@[fun_prop]
lemma measurable_importanceWeighted [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {X : Type*} [MeasurableSpace X] {p : X → ι → ℝ} {i : X → ι} {v : X → ℝ} (hp : Measurable p)
    (hi : Measurable i) (hv : Measurable v) (j : ι) :
    Measurable fun x ↦ importanceWeighted (p x) (i x) (v x) j := by
  unfold importanceWeighted
  exact Measurable.ite (hi (measurableSet_singleton j)) (hv.div (Measurable.eval_prod hp hi))
    measurable_const

end Bandits

/-! ### Bandit algorithms from full-information learners -/

namespace Learning.OnlineLearner

variable {σ 𝓧 ι : Type*} [MeasurableSpace σ] [MeasurableSpace 𝓧] [MeasurableSpace ι]
  (L : OnlineLearner σ 𝓧 (ι → ℝ) (ι → ℝ))

/-- The state update of the bandit algorithm of the learner `L` with the loss estimator `est`:
after a round with side information `o`, arm `a` and loss `v`, feed `L` the estimate `est p a v`
computed from its play `p = L.play s o`. -/
def banditUpdate (est : (ι → ℝ) → ι → ℝ → ι → ℝ) (s : σ) (r : Round 𝓧 ι ℝ) : σ :=
  L.update s (est (L.play s r.obs) r.action r.feedback)

lemma measurable_banditUpdate {est : (ι → ℝ) → ι → ℝ → ι → ℝ}
    (hest : Measurable fun q : (ι → ℝ) × ι × ℝ ↦ est q.1 q.2.1 q.2.2) :
    Measurable fun p : σ × Round 𝓧 ι ℝ ↦ L.banditUpdate est p.1 p.2 := by
  have hplay : Measurable fun p : σ × Round 𝓧 ι ℝ ↦ L.play p.1 p.2.obs :=
    L.measurable_play.comp (measurable_fst.prodMk (Round.measurable_obs.comp measurable_snd))
  exact L.measurable_update.comp (measurable_fst.prodMk (hest.comp (hplay.prodMk
    ((Round.measurable_action.comp measurable_snd).prodMk
      (Round.measurable_feedback.comp measurable_snd)))))

variable [Fintype ι]

/-- The policy of the bandit algorithm of the learner `L`, whose plays are probability vectors:
draw the arm from the play `L.play s o` in the state `s` with side information `o`. -/
noncomputable def banditPolicy (hL : ∀ s o, WithLp.toLp 2 (L.play s o) ∈ simplex ι) :
    Kernel (σ × 𝓧) ι :=
  (simplexKernel ι).comap (fun q ↦ ⟨WithLp.toLp _ (L.play q.1 q.2), hL q.1 q.2⟩)
    ((WithLp.measurable_toLp _ _).comp L.measurable_play).subtype_mk

@[simp]
lemma banditPolicy_apply (hL : ∀ s o, WithLp.toLp 2 (L.play s o) ∈ simplex ι) (s : σ) (o : 𝓧) :
    L.banditPolicy hL (s, o) = weightedMeasure (L.play s o) := rfl

instance (hL : ∀ s o, WithLp.toLp 2 (L.play s o) ∈ simplex ι) :
    IsMarkovKernel (L.banditPolicy hL) := by
  unfold banditPolicy
  infer_instance

/-- **The bandit algorithm of a full-information learner.** The learner `L` plays probability
vectors over the arms; at each round, pull an arm drawn from the play of `L`, observe its loss
`v`, and feed `L` the estimate `est p a v` of the loss vector computed from the play `p` and the
arm `a`. -/
noncomputable def toBanditAlgorithm (hL : ∀ s o, WithLp.toLp 2 (L.play s o) ∈ simplex ι)
    (est : (ι → ℝ) → ι → ℝ → ι → ℝ)
    (hest : Measurable fun q : (ι → ℝ) × ι × ℝ ↦ est q.1 q.2.1 q.2.2) : Algorithm 𝓧 ι ℝ :=
  Algorithm.stateful L.init (fun _ ↦ L.banditUpdate est)
    ((L.measurable_banditUpdate hest).comp measurable_snd) fun _ ↦ L.banditPolicy hL

variable {hL : ∀ s o, WithLp.toLp 2 (L.play s o) ∈ simplex ι} {est : (ι → ℝ) → ι → ℝ → ι → ℝ}
  {hest : Measurable fun q : (ι → ℝ) × ι × ℝ ↦ est q.1 q.2.1 q.2.2}

/-- The policy of `L.toBanditAlgorithm` draws the arm from the play of `L` in the state reached
on the history. -/
lemma policy_toBanditAlgorithm_apply (n : ℕ) (p : Hist 𝓧 ι ℝ n × 𝓧) :
    (L.toBanditAlgorithm hL est hest).policy n p =
      weightedMeasure (L.play (foldHist (L.banditUpdate est) L.init n p.1) p.2) := rfl

/-- **Runs of the bandit algorithm of a learner.** In a run of `L.toBanditAlgorithm`, the arm of
round `n` has conditional law `weightedMeasure (L.play s o)` given the state `s` of the learner
(`stateProcess`) and the observation `o` of round `n`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondDistrib_action_toBanditAlgorithm {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {env : Environment 𝓧 ι ℝ}
    {O : ℕ → Ω → 𝓧} {A : ℕ → Ω → ι} {Y : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq O A Y (L.toBanditAlgorithm hL est hest) env P) (n : ℕ) :
    HasCondDistrib (A n)
      (fun ω ↦ (stateProcess (fun _ ↦ L.banditUpdate est) L.init O A Y n ω, O n ω))
      (L.banditPolicy hL) P :=
  h.hasCondDistrib_action_stateful n

end Learning.OnlineLearner
