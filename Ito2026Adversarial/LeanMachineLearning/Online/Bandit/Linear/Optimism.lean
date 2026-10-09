/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.Linear.Ridge

/-!
# Optimism of the linear UCB index on the confidence ellipsoid

If the parameter `θ` lies in the confidence ellipsoid `‖θ - θ̂‖_V ≤ β` around the ridge regression
estimate `θ̂ = V⁻¹ b` of a ridge state `(V, b)` with `V` positive definite, then the optimistic
index `ucbIndex β' s v = ⟪v, θ̂⟫ + β' ‖v‖_{V⁻¹}` of any radius `β' ≥ β` is an upper confidence
bound of `⟪v, θ⟫`, which it exceeds by at most `2 β' ‖v‖_{V⁻¹}`.

## Main statements

* `Bandits.Linear.abs_inner_sub_inner_ridgeEstimate_le`: `|⟪v, θ⟫ - ⟪v, θ̂⟫| ≤ β ‖v‖_{V⁻¹}`
  (Cauchy–Schwarz for the inner product of `V`);
* `Bandits.Linear.inner_le_ucbIndex`: `⟪v, θ⟫ ≤ ucbIndex β' s v`;
* `Bandits.Linear.ucbIndex_le_inner_add`: `ucbIndex β' s v ≤ ⟪v, θ⟫ + 2 β' ‖v‖_{V⁻¹}`.
-/

@[expose] public section

open Matrix Real

open scoped RealInnerProductSpace

namespace Bandits.Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {s : RidgeState ι} {θ : EuclideanSpace ℝ ι}
  {β β' : ℝ}

/-- On the confidence ellipsoid `‖θ - θ̂‖_V ≤ β`, `|⟪v, θ⟫ - ⟪v, θ̂⟫| ≤ β ‖v‖_{V⁻¹}` for every `v`
(Cauchy–Schwarz for the inner product of `V`). -/
lemma abs_inner_sub_inner_ridgeEstimate_le (hV : s.1.PosDef)
    (hθ : √(mahalanobisSq s.1 (θ - ridgeEstimate s)) ≤ β) (v : EuclideanSpace ℝ ι) :
    |⟪v, θ⟫ - ⟪v, ridgeEstimate s⟫| ≤ β * √(mahalanobisSq s.1⁻¹ v) := by
  rw [← inner_sub_right]
  have h := hV.inner_sq_le_mahalanobisSq_inv_mul v (θ - ridgeEstimate s)
  refine (abs_le_sqrt h).trans ?_
  rw [sqrt_mul (hV.inv.posSemidef.mahalanobisSq_nonneg v), mul_comm]
  exact mul_le_mul_of_nonneg_right hθ (sqrt_nonneg _)

/-- **Optimism of the linear UCB index.** On the confidence ellipsoid `‖θ - θ̂‖_V ≤ β`, the
optimistic index of any radius `β' ≥ β` is an upper bound of `⟪v, θ⟫`. -/
lemma inner_le_ucbIndex (hV : s.1.PosDef) (hθ : √(mahalanobisSq s.1 (θ - ridgeEstimate s)) ≤ β)
    (hβ : β ≤ β') (v : EuclideanSpace ℝ ι) :
    ⟪v, θ⟫ ≤ ucbIndex β' s v := by
  have h := (abs_le.1 (abs_inner_sub_inner_ridgeEstimate_le hV hθ v)).2
  have h' : β * √(mahalanobisSq s.1⁻¹ v) ≤ β' * √(mahalanobisSq s.1⁻¹ v) :=
    mul_le_mul_of_nonneg_right hβ (sqrt_nonneg _)
  rw [ucbIndex]
  linarith

/-- On the confidence ellipsoid `‖θ - θ̂‖_V ≤ β`, the optimistic index of a radius `β' ≥ β`
exceeds `⟪v, θ⟫` by at most `2 β' ‖v‖_{V⁻¹}`. -/
lemma ucbIndex_le_inner_add (hV : s.1.PosDef)
    (hθ : √(mahalanobisSq s.1 (θ - ridgeEstimate s)) ≤ β) (hβ : β ≤ β')
    (v : EuclideanSpace ℝ ι) :
    ucbIndex β' s v ≤ ⟪v, θ⟫ + 2 * β' * √(mahalanobisSq s.1⁻¹ v) := by
  have h := (abs_le.1 (abs_inner_sub_inner_ridgeEstimate_le hV hθ v)).1
  have h' : β * √(mahalanobisSq s.1⁻¹ v) ≤ β' * √(mahalanobisSq s.1⁻¹ v) :=
    mul_le_mul_of_nonneg_right hβ (sqrt_nonneg _)
  rw [ucbIndex]
  linarith

end Bandits.Linear
