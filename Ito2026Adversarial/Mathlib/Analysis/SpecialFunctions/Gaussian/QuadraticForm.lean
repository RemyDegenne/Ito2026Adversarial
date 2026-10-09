/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.InnerProductSpace.Mahalanobis
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Gaussian integrals of quadratic forms

The real Gaussian integral with a linear term on a finite-dimensional real inner product space,
`∫ exp(-b ‖v‖² + c ⟪w, v⟫) dv = (π / b)^{d/2} exp(c² ‖w‖² / (4 b))` (the real counterpart of
Mathlib's `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`), and its version for the quadratic
form of a positive definite matrix `A` on `EuclideanSpace ℝ ι`, obtained by the linear change of
variables `x = √A θ`:
`∫ exp(⟪θ, s⟫ - θᵀ A θ / 2) dθ = (2π)^{d/2} (det A)^{-1/2} exp(sᵀ A⁻¹ s / 2)`.

This is the Gaussian integral behind the method of mixtures for vector-valued martingales
(Abbasi-Yadkori, Pál, Szepesvári 2011).

## Main statements

* `integrable_exp_neg_mul_sq_norm_add`, `integral_exp_neg_mul_sq_norm_add`;
* `Matrix.PosDef.det_sqrt`: `det √A = √(det A)`;
* `Matrix.PosDef.lintegral_exp_inner_sub_mahalanobisSq`: the Gaussian integral of the quadratic
  form of `A`, as a lower Lebesgue integral.

## Tags

Gaussian integral, quadratic form, positive definite matrix
-/

@[expose] public section

open MeasureTheory Real Matrix
open scoped RealInnerProductSpace MatrixOrder

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The real Gaussian function with a linear term `v ↦ exp(-b ‖v‖² + c ⟪w, v⟫)` is integrable
for `b > 0`. -/
lemma integrable_exp_neg_mul_sq_norm_add {b : ℝ} (hb : 0 < b) (c : ℝ) (w : V) :
    Integrable (fun v : V ↦ rexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) (c : ℂ) w).norm
  refine h.congr (ae_of_all _ fun v ↦ ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- **Gaussian integral with a linear term** on a finite-dimensional real inner product space:
`∫ exp(-b ‖v‖² + c ⟪w, v⟫) dv = (π / b)^{d/2} exp(c² ‖w‖² / (4 b))` for `b > 0`. -/
lemma integral_exp_neg_mul_sq_norm_add {b : ℝ} (hb : 0 < b) (c : ℝ) (w : V) :
    ∫ v : V, rexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫) =
      (π / b) ^ (Module.finrank ℝ V / 2 : ℝ) * rexp (c ^ 2 * ‖w‖ ^ 2 / (4 * b)) := by
  rw [← Complex.ofReal_inj]
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) (c : ℂ) w (V := V)
  rw [← integral_complex_ofReal]
  push_cast
  convert h using 2
  · rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf

end InnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of the positive square root of a positive definite matrix is the square root
of its determinant. -/
lemma PosDef.det_sqrt {A : Matrix ι ι ℝ} (hA : A.PosDef) : (CFC.sqrt A).det = √A.det := by
  have h1 : (CFC.sqrt A).det ^ 2 = A.det := by
    rw [sq, ← det_mul, hA.posSemidef.sqrt_mul_sqrt]
  rw [← h1, Real.sqrt_sq hA.sqrt.det_pos.le]

/-- **Gaussian integral of a quadratic form.** For a positive definite matrix `A` of dimension `d`
and a vector `s`,
`∫⁻ exp(⟪θ, s⟫ - θᵀ A θ / 2) dθ = (2π)^{d/2} / √(det A) · exp(sᵀ A⁻¹ s / 2)`. Proof: the change
of variables `x = √A θ` (of Jacobian `√(det A)`) reduces it to the isotropic Gaussian integral
`integral_exp_neg_mul_sq_norm_add`. -/
lemma PosDef.lintegral_exp_inner_sub_mahalanobisSq {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (s : EuclideanSpace ℝ ι) :
    ∫⁻ θ : EuclideanSpace ℝ ι, ENNReal.ofReal (rexp (⟪θ, s⟫ - mahalanobisSq A θ / 2)) =
      ENNReal.ofReal ((2 * π) ^ (Fintype.card ι / 2 : ℝ) / √A.det *
        rexp (mahalanobisSq A⁻¹ s / 2)) := by
  set L := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) with hL
  set w := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) s with hw
  set g : EuclideanSpace ℝ ι → ENNReal :=
    fun x ↦ ENNReal.ofReal (rexp (-(1 / 2) * ‖x‖ ^ 2 + 1 * ⟪w, x⟫)) with hg
  have hcomp : (fun θ : EuclideanSpace ℝ ι ↦
      ENNReal.ofReal (rexp (⟪θ, s⟫ - mahalanobisSq A θ / 2))) = g ∘ L := by
    funext θ
    simp only [Function.comp_apply, hg, hL, hw]
    rw [norm_toEuclideanCLM_sqrt_sq hA.posSemidef,
      real_inner_comm (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) θ),
      inner_toEuclideanCLM_sqrt_sqrt_inv hA]
    ring_nf
  have hdetL : LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = √A.det := by
    rw [hL, coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.det_toLin, hA.det_sqrt]
  have hdet_pos : 0 < √A.det := Real.sqrt_pos.2 hA.det_pos
  have hgm : Measurable g := by fun_prop
  rw [hcomp]
  change ∫⁻ θ, g (L θ) = _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (f := (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) (by rw [hdetL]; exact hdet_pos.ne')
  rw [ContinuousLinearMap.coe_coe] at hmap
  rw [← lintegral_map hgm L.continuous.measurable, hmap,
    lintegral_smul_measure, hdetL, hg,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq_norm_add (by norm_num) _ _)
      (ae_of_all _ fun _ ↦ (exp_pos _).le),
    integral_exp_neg_mul_sq_norm_add (by norm_num), smul_eq_mul,
    ← ENNReal.ofReal_mul (abs_nonneg _), finrank_euclideanSpace, hw,
    norm_toEuclideanCLM_sqrt_inv_sq hA]
  congr 1
  rw [abs_of_pos (inv_pos.2 hdet_pos)]
  field_simp
  ring_nf

end Matrix
