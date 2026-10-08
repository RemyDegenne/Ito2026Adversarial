/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.DesignMatrix
public import Ito2026Adversarial.Mathlib.Analysis.InnerProductSpace.Mahalanobis
public import Ito2026Adversarial.Mathlib.Analysis.Matrix.MeasurableSpace
public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.Algorithms.Stateful

/-!
# The ridge regression state of linear bandit algorithms

Linear bandit algorithms (LinUCB, linear Thompson sampling, ensemble sampling, Maximin-LinUCB)
maintain the *ridge regression state* `(V, b) = (λ I + ∑_s x_s x_sᵀ, ∑_s y_s x_s)` of the
features `x_s` played so far and of the observed rewards `y_s`, and estimate the reward vector by
the ridge regression estimate `θ̂ = V⁻¹ b`. The matrix `V` is the regularized Gram matrix
`regGram λ x t` of `DesignMatrix.lean`.

The state update only reads a feature vector and a reward, so the same update serves every action
type (finite arm types with feature maps, infinite action sets, pairs of actions of a game): an
algorithm with rounds `r` uses `fun s r ↦ ridgeUpdate s (feat r) (rew r)` for its own reading
`feat r`, `rew r` of the round.

## Main definitions

* `RidgeState ι`: the ridge regression state `(V, b)`;
* `ridgeUpdate s x y`: the update `(V, b) ↦ (V + x xᵀ, b + y x)`;
* `ridgeEstimate s = V⁻¹ b`: the ridge regression estimate;
* `ridgeState λ x y t`: the state after the first `t` terms of the sequences `x`, `y`.
* `ucbIndex β s v = ⟪v, θ̂⟫ + β ‖v‖_{V⁻¹}`: the optimistic index of the feature vector `v`.

## Main results

* `ridgeState_succ`: the state of sequences is obtained by the ridge updates;
* `stateProcess_ridgeUpdate`: along a run of a stateful algorithm with a ridge update, the state
  is the ridge state of the features and rewards of the run.
-/

@[expose] public section

open MeasureTheory Finset Matrix Learning

open scoped RealInnerProductSpace

namespace Bandits.Linear

variable {ι : Type*}

/-- The ridge regression state `(V, b)`: the (regularized) design matrix and the sum of the
features weighted by the rewards. -/
abbrev RidgeState (ι : Type*) := Matrix ι ι ℝ × EuclideanSpace ℝ ι

/-- The ridge regression update `(V, b) ↦ (V + x xᵀ, b + y x)` with the feature `x` and the
reward `y`. -/
noncomputable def ridgeUpdate (s : RidgeState ι) (x : EuclideanSpace ℝ ι) (y : ℝ) :
    RidgeState ι :=
  (s.1 + outerSelf x, s.2 + y • x)

@[simp]
lemma ridgeUpdate_fst (s : RidgeState ι) (x : EuclideanSpace ℝ ι) (y : ℝ) :
    (ridgeUpdate s x y).1 = s.1 + outerSelf x := rfl

@[simp]
lemma ridgeUpdate_snd (s : RidgeState ι) (x : EuclideanSpace ℝ ι) (y : ℝ) :
    (ridgeUpdate s x y).2 = s.2 + y • x := rfl

@[fun_prop]
lemma measurable_ridgeUpdate [Finite ι] {X : Type*} [MeasurableSpace X] {s : X → RidgeState ι}
    {x : X → EuclideanSpace ℝ ι} {y : X → ℝ} (hs : Measurable s) (hx : Measurable x)
    (hy : Measurable y) : Measurable fun q ↦ ridgeUpdate (s q) (x q) (y q) := by
  have := Fintype.ofFinite ι
  unfold ridgeUpdate
  fun_prop

section Estimate

variable [Fintype ι] [DecidableEq ι]

/-- The ridge regression estimate `θ̂ = V⁻¹ b`. -/
noncomputable def ridgeEstimate (s : RidgeState ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp _ (s.1⁻¹ *ᵥ WithLp.ofLp s.2)

@[fun_prop]
lemma measurable_ridgeEstimate : Measurable (ridgeEstimate (ι := ι)) := by
  unfold ridgeEstimate
  fun_prop

/-- The optimistic index `⟪v, θ̂⟫ + β ‖v‖_{V⁻¹}` of the feature vector `v`, from the ridge state
`(V, b)` and the confidence radius `β`. -/
noncomputable def ucbIndex (β : ℝ) (s : RidgeState ι) (v : EuclideanSpace ℝ ι) : ℝ :=
  ⟪v, ridgeEstimate s⟫ + β * √(mahalanobisSq s.1⁻¹ v)

@[fun_prop]
lemma measurable_ucbIndex {X : Type*} [MeasurableSpace X] {β : X → ℝ} {s : X → RidgeState ι}
    {v : X → EuclideanSpace ℝ ι} (hβ : Measurable β) (hs : Measurable s) (hv : Measurable v) :
    Measurable fun q ↦ ucbIndex (β q) (s q) (v q) := by
  unfold ucbIndex
  fun_prop

end Estimate

/-! ### The ridge state of sequences -/

section Sequence

variable [DecidableEq ι]

/-- The ridge regression state `(λ I + ∑_{s < t} x_s x_sᵀ, ∑_{s < t} y_s x_s)` of the first `t`
terms of the sequences of features `x` and rewards `y`. -/
noncomputable def ridgeState (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (y : ℕ → ℝ) (t : ℕ) :
    RidgeState ι :=
  (regGram lam x t, ∑ s ∈ range t, y s • x s)

variable (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (y : ℕ → ℝ)

@[simp]
lemma ridgeState_fst (t : ℕ) : (ridgeState lam x y t).1 = regGram lam x t := rfl

@[simp]
lemma ridgeState_snd (t : ℕ) : (ridgeState lam x y t).2 = ∑ s ∈ range t, y s • x s := rfl

@[simp]
lemma ridgeState_zero : ridgeState lam x y 0 = (lam • 1, 0) := by
  simp [ridgeState]

lemma ridgeState_succ (t : ℕ) :
    ridgeState lam x y (t + 1) = ridgeUpdate (ridgeState lam x y t) (x t) (y t) := by
  simp [ridgeState, ridgeUpdate, regGram_succ, sum_range_succ]

/-- **The ridge state along a run.** For a stateful algorithm whose state is updated by
`ridgeUpdate` with the feature `feat r` and the reward `rew r` of each round `r`, the state after
`t` rounds of a run is the ridge state of the features and rewards of the first `t` rounds. -/
lemma stateProcess_ridgeUpdate {𝓞 𝓐 𝓨 Ω : Type*} (feat : Round 𝓞 𝓐 𝓨 → EuclideanSpace ℝ ι)
    (rew : Round 𝓞 𝓐 𝓨 → ℝ) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (t : ℕ)
    (ω : Ω) :
    stateProcess (fun _ s r ↦ ridgeUpdate s (feat r) (rew r)) (lam • 1, 0) O A Y t ω =
      ridgeState lam (fun s ↦ feat (O s ω, A s ω, Y s ω)) (fun s ↦ rew (O s ω, A s ω, Y s ω))
        t := by
  induction t with
  | zero => simp
  | succ t ih => rw [stateProcess_succ, ih, ridgeState_succ]

end Sequence

end Bandits.Linear
