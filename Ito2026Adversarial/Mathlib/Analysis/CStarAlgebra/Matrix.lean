/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix

/-!
# Matrices as (continuous) linear maps on Euclidean spaces

Small lemmas about `Matrix.toEuclideanLin` and `Matrix.toEuclideanCLM`.

## Main statements

* `Matrix.ofLp_toEuclideanLin`, `Matrix.toEuclideanLin_mul_apply`: coordinates of
  `toEuclideanLin M v` and the action of a product;
* `Matrix.adjoint_toEuclideanCLM`: the adjoint of the continuous linear map
  `Matrix.toEuclideanCLM M` on `EuclideanSpace 𝕜 n` is the map of the conjugate transpose `Mᴴ`
  (for real matrices, of the transpose `Mᵀ`, by `Matrix.conjTranspose_eq_transpose_of_trivial`);
* `Matrix.toEuclideanCLM_inv_apply_toEuclideanCLM`: `M⁻¹ (M θ) = θ` for an invertible matrix;
* `Matrix.span_image_toEuclideanCLM_eq_top`: the image of a spanning set by an invertible matrix
  is spanning.
-/

@[expose] public section

namespace Matrix

variable {𝕜 l m n : Type*} [RCLike 𝕜]

lemma ofLp_toEuclideanLin [Fintype n] [DecidableEq n] (M : Matrix m n 𝕜)
    (v : EuclideanSpace 𝕜 n) :
    WithLp.ofLp (toEuclideanLin M v) = M *ᵥ WithLp.ofLp v := rfl

lemma toEuclideanLin_mul_apply [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (A * B) v = toEuclideanLin A (toEuclideanLin B v) := by
  apply WithLp.ofLp_injective
  simp only [ofLp_toEuclideanLin, mulVec_mulVec]

variable [Fintype n] [DecidableEq n]

/-- The adjoint of the continuous linear map associated to a matrix `M` is the map associated to
its conjugate transpose `Mᴴ`. -/
lemma adjoint_toEuclideanCLM (M : Matrix n n 𝕜) :
    ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := 𝕜) M) = toEuclideanCLM (𝕜 := 𝕜) Mᴴ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_eq_conjTranspose]

/-- `M⁻¹ (M θ) = θ` for an invertible matrix `M`. -/
lemma toEuclideanCLM_inv_apply_toEuclideanCLM {M : Matrix n n 𝕜} (hM : IsUnit M)
    (θ : EuclideanSpace 𝕜 n) :
    toEuclideanCLM (𝕜 := 𝕜) M⁻¹ (toEuclideanCLM (𝕜 := 𝕜) M θ) = θ := by
  rw [← mul_apply_eq_comp, ← map_mul,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hM), map_one, one_apply_eq_self]

/-- `M (M⁻¹ θ) = θ` for an invertible matrix `M`. -/
lemma toEuclideanCLM_apply_toEuclideanCLM_inv {M : Matrix n n 𝕜} (hM : IsUnit M)
    (θ : EuclideanSpace 𝕜 n) :
    toEuclideanCLM (𝕜 := 𝕜) M (toEuclideanCLM (𝕜 := 𝕜) M⁻¹ θ) = θ := by
  rw [← mul_apply_eq_comp, ← map_mul,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM), map_one, one_apply_eq_self]

/-- The image of a spanning set by an invertible matrix is spanning. -/
lemma span_image_toEuclideanCLM_eq_top {M : Matrix n n 𝕜} (hM : IsUnit M)
    {𝒳 : Set (EuclideanSpace 𝕜 n)} (hspan : Submodule.span 𝕜 𝒳 = ⊤) :
    Submodule.span 𝕜 (toEuclideanCLM (𝕜 := 𝕜) M '' 𝒳) = ⊤ := by
  rw [← ContinuousLinearMap.coe_coe, Submodule.span_image, hspan, Submodule.map_top,
    LinearMap.range_eq_top]
  exact fun y ↦ ⟨_, toEuclideanCLM_apply_toEuclideanCLM_inv hM y⟩

end Matrix
