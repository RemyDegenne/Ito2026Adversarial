/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.ImportanceWeighting
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.SimplexFTRL

/-!
# Tsallis-INF

The Tsallis-INF algorithm (Zimmert, Seldin 2021) for multi-armed bandits with arms `ι` and
rewards in `[-1, 1]`, with entropy parameter `α` and learning rates `η`: at round `t`, with the
cumulative reward estimate `G_t = ∑_{s < t} g_s`, play `x_t ∼ p_t` for
`p_t = argmax_{p ∈ simplex} ⟪p, G_t⟫ + φ_α(p) / η_t` (`TsallisINF.dist`, the FTRL distribution
`ftrlSimplex` of the Tsallis entropy `tsallisEntropy α`), observe the reward `r_t` and set the
importance-weighted estimate `g_t x = 1 - (1 - r_t) / p_t x` if `x = x_t` and `1` otherwise
(`TsallisINF.estimate`, built on `importanceWeighted`).

## Main definitions

* `tsallisINF α η : Algorithm Unit ι ℝ`: Tsallis-INF, an `Algorithm.stateful` with state `G_t`
  whose policy draws the arm with `simplexKernel`;
* `TsallisINF.dist`, `TsallisINF.estimate`, `TsallisINF.update`: the FTRL distribution, the
  reward estimate and the state update;
* `TsallisINF.cumEstimate α η n h`: the state `G_n` after the history `h` of `n` rounds.

## Main results

* `TsallisINF.cumEstimate_zero`, `TsallisINF.cumEstimate_succ`: the recursion of the estimates;
* `policy_tsallisINF_apply`: Tsallis-INF draws the arm from `dist α η n G_n`;
* `IsAlgEnvSeq.hasCondDistrib_action_tsallisINF`: in a run, the arm of round `n` has conditional
  law `dist α η n G_n` given the cumulative estimate `G_n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped RealInnerProductSpace

namespace Bandits

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

namespace TsallisINF

/-- The importance-weighted reward estimate of a round played with the distribution `p`:
`g x = 1 - (1 - r) / p x` for the arm `x` played, with reward `r`, and `g x = 1` otherwise (the
importance-weighted estimate `importanceWeighted p x (1 - r)` of the loss vector `1 - g`). -/
noncomputable def estimate (p : simplex ι) (r : Round Unit ι ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp _ (1 - importanceWeighted (fun x ↦ (p : EuclideanSpace ℝ ι) x) r.action
    (1 - r.feedback))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma estimate_apply (p : simplex ι) (r : Round Unit ι ℝ) (x : ι) :
    estimate p r x = 1 - importanceWeighted (fun x ↦ (p : EuclideanSpace ℝ ι) x) r.action
      (1 - r.feedback) x := rfl

@[fun_prop]
lemma measurable_estimate {X : Type*} [MeasurableSpace X] {p : X → simplex ι}
    {r : X → Round Unit ι ℝ} (hp : Measurable p) (hr : Measurable r) :
    Measurable fun x ↦ estimate (p x) (r x) := by
  unfold estimate
  fun_prop

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The importance-weighted estimate, coordinatewise:
`g i = 1 - 𝟙{x_t = i} (1 - r) / p x_t`. -/
lemma estimate_apply_eq (p : simplex ι) (r : Round Unit ι ℝ) (i : ι) :
    estimate p r i = 1 - if r.action = i then (1 - r.feedback) / p r.action else 0 := by
  rw [estimate_apply, importanceWeighted]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The gain of the distribution `p` under its importance-weighted estimate is the reward. -/
lemma inner_estimate (p : simplex ι) (r : Round Unit ι ℝ) (hp : p r.action ≠ 0) :
    ⟪(p : EuclideanSpace ℝ ι), estimate p r⟫ = r.feedback := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, estimate_apply_eq, sub_mul,
    one_mul, sum_sub_distrib, ite_mul, zero_mul]
  rw [sum_ite_eq univ r.action, ite_eq_left (mem_univ _)]
  have h1 : ∑ i, (p : EuclideanSpace ℝ ι) i = 1 := p.2.2
  change ∑ i, p i = 1 at h1
  change ∑ i, p i - (1 - r.feedback) / p r.action * p r.action = r.feedback
  rw [h1, div_mul_cancel₀ _ hp]
  ring

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The gain of a vertex `x` under the importance-weighted estimate. -/
lemma inner_single_estimate (p : simplex ι) (r : Round Unit ι ℝ) (x : ι) :
    ⟪EuclideanSpace.single x (1 : ℝ), estimate p r⟫ = estimate p r x := by
  rw [EuclideanSpace.inner_single_left]
  simp

variable [Nonempty ι]

/-- The distribution played at round `n` from the cumulative estimate `G`:
`argmax_{p ∈ simplex} ⟪p, G⟫ + φ_α(p) / η n = argmax_{p ∈ simplex} ⟪p, η n • G⟫ + φ_α(p)`. -/
noncomputable def dist (α : ℝ) (η : ℕ → ℝ) (n : ℕ) (G : EuclideanSpace ℝ ι) : simplex ι :=
  ftrlSimplex (tsallisEntropy α) (η n • G)

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
@[fun_prop]
lemma measurable_dist {X : Type*} [MeasurableSpace X] (α : ℝ) (η : ℕ → ℝ) {n : X → ℕ}
    {G : X → EuclideanSpace ℝ ι} (hn : Measurable n) (hG : Measurable G) :
    Measurable fun x ↦ dist α η (n x) (G x) := by
  unfold dist
  fun_prop

/-- The state update of Tsallis-INF at round `n`: `G ↦ G + g_n`. -/
noncomputable def update (α : ℝ) (η : ℕ → ℝ) (n : ℕ) (G : EuclideanSpace ℝ ι)
    (r : Round Unit ι ℝ) : EuclideanSpace ℝ ι :=
  G + estimate (dist α η n G) r

@[fun_prop]
lemma measurable_update {X : Type*} [MeasurableSpace X] (α : ℝ) (η : ℕ → ℝ) {n : X → ℕ}
    {G : X → EuclideanSpace ℝ ι} {r : X → Round Unit ι ℝ} (hn : Measurable n) (hG : Measurable G)
    (hr : Measurable r) : Measurable fun x ↦ update α η (n x) (G x) (r x) := by
  unfold update
  fun_prop

/-- The cumulative reward estimate `G_n = ∑_{s < n} g_s` after the history `h` of `n` rounds. -/
noncomputable def cumEstimate (α : ℝ) (η : ℕ → ℝ) (n : ℕ) (h : Hist Unit ι ℝ n) :
    EuclideanSpace ℝ ι :=
  foldHistIdx (update α η) 0 n h

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
@[simp]
lemma cumEstimate_zero (α : ℝ) (η : ℕ → ℝ) (h : Hist Unit ι ℝ 0) : cumEstimate α η 0 h = 0 :=
  rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma cumEstimate_succ (α : ℝ) (η : ℕ → ℝ) (n : ℕ) (h : Hist Unit ι ℝ (n + 1)) :
    cumEstimate α η (n + 1) h = cumEstimate α η n (fun i ↦ h i.castSucc) +
      estimate (dist α η n (cumEstimate α η n fun i ↦ h i.castSucc)) (h (Fin.last n)) := rfl

@[fun_prop]
lemma measurable_cumEstimate (α : ℝ) (η : ℕ → ℝ) (n : ℕ) :
    Measurable (cumEstimate (ι := ι) α η n) := by
  unfold cumEstimate
  fun_prop

/-- The policy of Tsallis-INF at round `n` from the state `G_n`: sample from `dist α η n G_n`. -/
noncomputable def policy (α : ℝ) (η : ℕ → ℝ) (n : ℕ) : Kernel (EuclideanSpace ℝ ι × Unit) ι :=
  (simplexKernel ι).comap (fun q ↦ dist α η n q.1) (by fun_prop)

omit [DecidableEq ι] [MeasurableSingletonClass ι] in
@[simp]
lemma policy_apply (α : ℝ) (η : ℕ → ℝ) (n : ℕ) (q : EuclideanSpace ℝ ι × Unit) :
    policy α η n q = weightedMeasure fun i ↦ (dist α η n q.1 : EuclideanSpace ℝ ι) i := rfl

instance (α : ℝ) (η : ℕ → ℝ) (n : ℕ) : IsMarkovKernel (policy (ι := ι) α η n) := by
  unfold policy; infer_instance

end TsallisINF

variable [Nonempty ι]

/-- **Tsallis-INF** with entropy parameter `α` and learning rates `η`: at round `n`, play an arm
drawn from `argmax_{p ∈ simplex} ⟪p, G_n⟫ + φ_α(p) / η n`, where `G_n` is the cumulative
importance-weighted reward estimate. -/
noncomputable def tsallisINF (α : ℝ) (η : ℕ → ℝ) : Algorithm Unit ι ℝ :=
  Algorithm.stateful 0 (TsallisINF.update α η) (by fun_prop) (TsallisINF.policy α η)

/-- Tsallis-INF draws the arm of round `n` from the FTRL distribution of the cumulative reward
estimate. -/
lemma policy_tsallisINF_apply (α : ℝ) (η : ℕ → ℝ) (n : ℕ) (p : Hist Unit ι ℝ n × Unit) :
    (tsallisINF α η).policy n p =
      weightedMeasure fun i ↦ (TsallisINF.dist α η n (TsallisINF.cumEstimate α η n p.1) :
        EuclideanSpace ℝ ι) i := rfl

/-- **Runs of Tsallis-INF.** In a run of Tsallis-INF, the arm of round `n` has conditional law
`dist α η n G_n` given the cumulative reward estimate `G_n`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondDistrib_action_tsallisINF {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {env : Environment Unit ι ℝ}
    {O : ℕ → Ω → Unit} {A : ℕ → Ω → ι} {Y : ℕ → Ω → ℝ} {α : ℝ} {η : ℕ → ℝ}
    (h : IsAlgEnvSeq O A Y (tsallisINF α η) env P) (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (TsallisINF.cumEstimate α η n (history O A Y n ω), O n ω))
      (TsallisINF.policy α η n) P :=
  h.hasCondDistrib_action_stateful n

end Bandits
