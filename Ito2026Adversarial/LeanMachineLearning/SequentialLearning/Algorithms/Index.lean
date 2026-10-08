/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.Algorithms.Stateful
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

/-!
# Index algorithms

An *index algorithm* on a finite action set computes an index for every action from the history
and the current observation, and plays an action with the highest index (`argmax`; ties are
broken by the choice made in `argmax`). UCB, Maximin-UCB (`index x = min_y U(x, y)`), Maximin-LinUCB
and greedy policies are of this form.

## Main definitions

* `Algorithm.index idx hidx`: the deterministic algorithm playing `argmax (idx n (h, o))` at
  round `n`;
* `Algorithm.statefulIndex s0 upd hupd idx hidx`: the same with an index computed from a state
  maintained by `upd` (`Algorithm.detStateful`), e.g. a ridge regression state.

## Main statements

* `IsAlgEnvSeq.idx_le_idx_action_index`,
  `IsAlgEnvSeq.idx_le_idx_action_statefulIndex`: in a run of an index algorithm, the
  action of every round maximizes the index, almost surely.

## Future work

Section 4.5 of `LIBRARY_STATUS_REVIEW.md` describes randomized index algorithms (an index
computed from an independent draw, announced), of which Thompson sampling and FTPL are instances;
only the deterministic case is written here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 σ : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
  [MeasurableSpace σ] [Fintype 𝓐] [Nonempty 𝓐]

/-- The index algorithm with indices `idx n (h, o) a`: at round `n`, play an action maximizing
the index computed from the history `h` and the observation `o`. -/
noncomputable def Algorithm.index (idx : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓐 → ℝ)
    (hidx : ∀ n, Measurable (idx n)) : Algorithm 𝓞 𝓐 𝓨 :=
  Algorithm.deterministic (fun n p ↦ argmax (idx n p)) fun n ↦ measurable_argmax.comp (hidx n)

instance (idx : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓐 → ℝ) (hidx : ∀ n, Measurable (idx n)) :
    Algorithm.IsDeterministic (Algorithm.index idx hidx) :=
  inferInstanceAs (Algorithm.IsDeterministic (Algorithm.deterministic _ _))

@[simp]
lemma Algorithm.policy_index (idx : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓐 → ℝ)
    (hidx : ∀ n, Measurable (idx n)) (n : ℕ) :
    (Algorithm.index idx hidx).policy n
      = Kernel.deterministic (fun p ↦ argmax (idx n p)) (measurable_argmax.comp (hidx n)) := rfl

/-- An index algorithm factors through its index. -/
lemma factorsThrough_index (idx : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓐 → ℝ)
    (hidx : ∀ n, Measurable (idx n)) :
    (Algorithm.index idx hidx).FactorsThrough (𝓑 := fun _ ↦ 𝓐 → ℝ) idx :=
  factorsThrough_deterministic (f := fun _ ↦ argmax) (fun _ ↦ measurable_argmax) _

/-- The stateful index algorithm: the state is maintained by `upd` from `s0`, and at round `n`
an action maximizing `idx n s o` is played from the state `s` and the observation `o`. -/
noncomputable def Algorithm.statefulIndex (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (idx : ℕ → σ → 𝓞 → 𝓐 → ℝ)
    (hidx : Measurable fun p : ℕ × σ × 𝓞 ↦ idx p.1 p.2.1 p.2.2) : Algorithm 𝓞 𝓐 𝓨 :=
  Algorithm.detStateful s0 upd hupd (fun n s o ↦ argmax (idx n s o)) (measurable_argmax.comp hidx)

instance (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (idx : ℕ → σ → 𝓞 → 𝓐 → ℝ)
    (hidx : Measurable fun p : ℕ × σ × 𝓞 ↦ idx p.1 p.2.1 p.2.2) :
    Algorithm.IsDeterministic (Algorithm.statefulIndex s0 upd hupd idx hidx) :=
  inferInstanceAs (Algorithm.IsDeterministic (Algorithm.deterministic _ _))

@[simp]
lemma Algorithm.policy_statefulIndex (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (idx : ℕ → σ → 𝓞 → 𝓐 → ℝ)
    (hidx : Measurable fun p : ℕ × σ × 𝓞 ↦ idx p.1 p.2.1 p.2.2) (n : ℕ) :
    (Algorithm.statefulIndex s0 upd hupd idx hidx).policy n
      = Kernel.deterministic (fun p ↦ argmax (idx n (foldHistIdx upd s0 n p.1) p.2))
        ((measurable_argmax.comp hidx).comp (measurable_const.prodMk
          (((measurable_foldHistIdx hupd s0 n).comp measurable_fst).prodMk measurable_snd))) :=
  rfl

/-! ### Runs of index algorithms -/

namespace IsAlgEnvSeq

variable {Ω : Type*} [MeasurableSpace Ω] {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} [MeasurableEq 𝓐]

/-- In a run of an index algorithm, the action of round `n` is almost surely the `argmax` of the
index computed from the history and the observation. -/
lemma action_index_ae_eq {idx : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓐 → ℝ}
    {hidx : ∀ n, Measurable (idx n)} (h : IsAlgEnvSeq O A Y (Algorithm.index idx hidx) env P)
    (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ argmax (idx n (history O A Y n ω, O n ω)) :=
  action_deterministic_ae_eq h n

/-- **Runs of an index algorithm.** In a run of an index algorithm, the action of round `n`
maximizes the index, almost surely. -/
lemma idx_le_idx_action_index {idx : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓐 → ℝ}
    {hidx : ∀ n, Measurable (idx n)} (h : IsAlgEnvSeq O A Y (Algorithm.index idx hidx) env P)
    (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ a,
      idx n (history O A Y n ω, O n ω) a ≤ idx n (history O A Y n ω, O n ω) (A n ω) := by
  filter_upwards [h.action_index_ae_eq n] with ω hω a
  rw [hω]
  exact isMaxOn_argmax _ a

variable {s0 : σ} {upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ}
  {hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2}
  {idx : ℕ → σ → 𝓞 → 𝓐 → ℝ} {hidx : Measurable fun p : ℕ × σ × 𝓞 ↦ idx p.1 p.2.1 p.2.2}

/-- In a run of a stateful index algorithm, the action of round `n` is almost surely the `argmax`
of the index computed from the state and the observation. -/
lemma action_statefulIndex_ae_eq
    (h : IsAlgEnvSeq O A Y (Algorithm.statefulIndex s0 upd hupd idx hidx) env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ argmax (idx n (stateProcess upd s0 O A Y n ω) (O n ω)) :=
  action_deterministic_ae_eq h n

/-- **Runs of a stateful index algorithm.** In a run of a stateful index algorithm, the action of
round `n` maximizes the index computed from the state and the observation, almost surely. -/
lemma idx_le_idx_action_statefulIndex
    (h : IsAlgEnvSeq O A Y (Algorithm.statefulIndex s0 upd hupd idx hidx) env P) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ a, idx n (stateProcess upd s0 O A Y n ω) (O n ω) a
      ≤ idx n (stateProcess upd s0 O A Y n ω) (O n ω) (A n ω) := by
  filter_upwards [h.action_statefulIndex_ae_eq n] with ω hω a
  rw [hω]
  exact isMaxOn_argmax _ a

end IsAlgEnvSeq

end Learning
