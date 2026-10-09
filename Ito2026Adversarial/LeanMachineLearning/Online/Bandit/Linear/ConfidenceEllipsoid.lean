/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.Linear.Ridge

/-!
# Confidence ellipsoids of ridge regression and optimism

For features `x_s`, a parameter `θ` and rewards `y_s = ⟪x_s, θ⟫ + η_s`, the ridge regression
estimate `θ̂_t = V_t⁻¹ b_t` (`ridgeEstimate (ridgeState λ x y t)`) satisfies
`θ - θ̂_t = V_t⁻¹ (λ θ - S_t)` with `S_t = ∑_{s < t} η_s x_s`, hence
`‖θ - θ̂_t‖_{V_t} ≤ ‖S_t‖_{V_t⁻¹} + √λ ‖θ‖` (Abbasi-Yadkori, Pál, Szepesvári 2011, proof of
Theorem 2). Combined with a self-normalized bound on `‖S_t‖_{V_t⁻¹}`, this gives the confidence
ellipsoids of linear bandit algorithms.

## Main statements

* `Bandits.Linear.sqrt_mahalanobisSq_sub_ridgeEstimate_le`: the deterministic bound
  `‖θ - θ̂_t‖_{V_t} ≤ ‖∑_{s < t} (y_s - ⟪x_s, θ⟫) x_s‖_{V_t⁻¹} + √λ ‖θ‖`;
* `Bandits.Linear.abs_inner_sub_inner_ridgeEstimate_le`: on the confidence ellipsoid
  `‖θ - θ̂‖_V ≤ β`, `|⟪v, θ⟫ - ⟪v, θ̂⟫| ≤ β ‖v‖_{V⁻¹}` (Cauchy–Schwarz for the inner product
  of `V`);
* `Bandits.Linear.inner_le_ucbIndex`, `Bandits.Linear.ucbIndex_le_inner_add`: the optimistic index
  `ucbIndex β' s v = ⟪v, θ̂⟫ + β' ‖v‖_{V⁻¹}` of any radius `β' ≥ β` satisfies
  `⟪v, θ⟫ ≤ ucbIndex β' s v ≤ ⟪v, θ⟫ + 2 β' ‖v‖_{V⁻¹}`.

## Tags

linear bandit, ridge regression, confidence ellipsoid, LinUCB, optimism
-/

@[expose] public section

open Finset Matrix Learning
open scoped RealInnerProductSpace MatrixOrder

namespace Bandits.Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The error of the ridge regression estimate** (Abbasi-Yadkori, Pál, Szepesvári 2011, proof of
Theorem 2). For `λ > 0`, features `x_s`, rewards `y_s` and any parameter `θ`, with
`V_t = λ I + ∑_{s < t} x_s x_sᵀ` and the ridge estimate `θ̂_t = V_t⁻¹ ∑_{s < t} y_s x_s`,
`‖θ - θ̂_t‖_{V_t} ≤ ‖∑_{s < t} (y_s - ⟪x_s, θ⟫) x_s‖_{V_t⁻¹} + √λ ‖θ‖`. -/
lemma sqrt_mahalanobisSq_sub_ridgeEstimate_le {lam : ℝ} (hlam : 0 < lam)
    (θ : EuclideanSpace ℝ ι) (x : ℕ → EuclideanSpace ℝ ι) (y : ℕ → ℝ) (t : ℕ) :
    √(mahalanobisSq (regGram lam x t) (θ - ridgeEstimate (ridgeState lam x y t))) ≤
      √(mahalanobisSq (regGram lam x t)⁻¹ (∑ s ∈ range t, (y s - ⟪x s, θ⟫) • x s)) +
        √lam * ‖θ‖ := by
  set V := regGram lam x t with hV
  set S := ∑ s ∈ range t, (y s - ⟪x s, θ⟫) • x s with hS
  have hpd : V.PosDef := posDef_regGram hlam x t
  have hunit : IsUnit V := hpd.isUnit
  set L := toEuclideanCLM (𝕜 := ℝ) V with hL
  set Linv := toEuclideanCLM (𝕜 := ℝ) V⁻¹ with hLinv
  -- `θ - θ̂ = V⁻¹ (λ θ - S)`
  have hb : (ridgeState lam x y t).2 = S + toEuclideanCLM (𝕜 := ℝ) (Learning.gram x t) θ := by
    rw [ridgeState_snd, hS, Learning.gram, map_sum]
    simp only [FunLike.coe_sum, Finset.sum_apply, toEuclideanCLM_outerSelf_apply,
      ← Finset.sum_add_distrib, sub_smul, real_inner_comm θ]
    exact Finset.sum_congr rfl fun s _ ↦ by abel
  have hVθ : L θ = lam • θ + toEuclideanCLM (𝕜 := ℝ) (Learning.gram x t) θ := by
    rw [hL, hV, regGram, map_add, _root_.add_apply, map_smul, map_one]
    rfl
  have herr : θ - ridgeEstimate (ridgeState lam x y t) = Linv (lam • θ - S) := by
    have h1 : ridgeEstimate (ridgeState lam x y t) = Linv (ridgeState lam x y t).2 := rfl
    have h2 : Linv (L θ) = θ := toEuclideanCLM_inv_apply_toEuclideanCLM hunit θ
    calc θ - ridgeEstimate (ridgeState lam x y t)
        = Linv (L θ) - Linv (ridgeState lam x y t).2 := by rw [h1, h2]
      _ = Linv (L θ - (ridgeState lam x y t).2) := (map_sub _ _ _).symm
      _ = Linv (lam • θ - S) := by
        rw [hVθ, hb]
        congr 1
        abel
  -- the Mahalanobis norm for `V⁻¹` is the Euclidean norm after `√(V⁻¹)`
  set N := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt V⁻¹) with hN
  have hnorm : ∀ w, √(mahalanobisSq V⁻¹ w) = ‖N w‖ := fun w ↦ by
    rw [← norm_toEuclideanCLM_sqrt_inv_sq hpd w, Real.sqrt_sq (norm_nonneg _)]
  rw [herr, mahalanobisSq_toEuclideanCLM_inv ((isUnit_iff_isUnit_det V).1 hunit), hnorm, hnorm,
    map_sub, map_smul]
  have hθ : lam * ‖N θ‖ ≤ √lam * ‖θ‖ := by
    have h1 : ‖N θ‖ ≤ √(lam⁻¹ * ‖θ‖ ^ 2) := by
      rw [← hnorm]
      exact Real.sqrt_le_sqrt (mahalanobisSq_inv_regGram_le hlam x t θ)
    have hsl : 0 < √lam := Real.sqrt_pos.2 hlam
    rw [Real.sqrt_mul (inv_nonneg.2 hlam.le), Real.sqrt_sq (norm_nonneg _), Real.sqrt_inv] at h1
    calc lam * ‖N θ‖ ≤ lam * ((√lam)⁻¹ * ‖θ‖) := by gcongr
      _ = √lam * ‖θ‖ := by
        rw [← mul_assoc]
        congr 1
        nth_rw 1 [← Real.mul_self_sqrt hlam.le]
        field_simp
  calc ‖lam • N θ - N S‖ ≤ ‖lam • N θ‖ + ‖N S‖ := norm_sub_le _ _
    _ = lam * ‖N θ‖ + ‖N S‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
    _ ≤ ‖N S‖ + √lam * ‖θ‖ := by linarith

/-! ### Optimism of the linear UCB index -/

section Optimism

open Real

variable {s : RidgeState ι} {θ : EuclideanSpace ℝ ι}
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

end Optimism

end Bandits.Linear
