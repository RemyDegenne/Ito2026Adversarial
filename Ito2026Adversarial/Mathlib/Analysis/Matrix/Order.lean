/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Matrix.Order

/-!
# The Loewner order: quadratic forms, inversion and square roots

Facts about the Loewner order `A ≤ B` on matrices (`Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef`,
scoped in `MatrixOrder`) over `RCLike 𝕜`.

## Main statements

* `Matrix.convex_posSemidef`: the cone of positive semidefinite matrices is convex;
* `Matrix.dotProduct_mulVec_le_of_le`, `Matrix.le_iff_dotProduct_mulVec_le`: `A ≤ B` implies
  `x* A x ≤ x* B x` for every `x`, and conversely for Hermitian matrices;
* `Matrix.mul_mul_conjTranspose_le_of_le`, `Matrix.conjTranspose_mul_mul_le_of_le`: the order is
  preserved by congruence `A ↦ M A M*` (with `M` possibly rectangular);
* `Matrix.PosDef.of_le`: a matrix above a positive definite matrix is positive definite;
* `Matrix.PosDef.inv_le_inv`: for positive definite matrices `A ≤ B`, we have `B⁻¹ ≤ A⁻¹`;
  `Matrix.PosDef.inv_le_inv_iff` is the equivalence, and `Matrix.PosDef.inv_le_inv_smul`,
  `Matrix.PosDef.dotProduct_inv_mulVec_le_of_smul_le` the scalar forms (`c • A ≤ B` gives
  `B⁻¹ ≤ c⁻¹ • A⁻¹`);
* facts about the positive square root `CFC.sqrt A` of a positive definite matrix:
  `Matrix.PosDef.sqrt`, `Matrix.PosDef.sqrt_inv_mul_mul_sqrt_inv` (`√(A⁻¹) A √(A⁻¹) = 1`),
  `Matrix.conjTranspose_sqrt`, `Matrix.inner_toEuclideanCLM_sqrt_sqrt_inv`
  (`⟪√A u, √(A⁻¹) v⟫ = ⟪u, v⟫`).

## Implementation notes

Mathlib proves the antitonicity of the inverse for units of a unital C⋆-algebra
(`CStarAlgebra.inv_le_inv`), which applies to `Matrix n n ℂ` but not to `Matrix n n ℝ` (there is
no `CStarAlgebra` instance on real matrices). Here we give a direct proof over any `RCLike 𝕜`,
using only the real continuous functional calculus on matrices: writing `S := √(A⁻¹)` (so that
`S * A * S = 1`), the inequality `A ≤ B` becomes `1 ≤ S * B * S`; a positive definite matrix `C`
with `1 ≤ C` has `C⁻¹ ≤ 1` (a spectral statement), and conjugating back by `S` gives
`B⁻¹ ≤ A⁻¹`.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- The cone of positive semidefinite matrices is convex. -/
lemma convex_posSemidef : Convex ℝ {A : Matrix n n 𝕜 | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

/-! ### The Loewner order and quadratic forms -/

section Order

variable [Fintype n] {A B : Matrix n n 𝕜}

/-- The Loewner order implies the order of the quadratic forms. -/
lemma dotProduct_mulVec_le_of_le (h : A ≤ B) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x ≤ star x ⬝ᵥ B *ᵥ x := by
  have := (le_iff.mp h).dotProduct_mulVec_nonneg x
  rwa [sub_mulVec, dotProduct_sub, sub_nonneg] at this

/-- For Hermitian matrices, the Loewner order is the order of the quadratic forms. -/
lemma le_iff_dotProduct_mulVec_le (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ x, star x ⬝ᵥ A *ᵥ x ≤ star x ⬝ᵥ B *ᵥ x := by
  refine ⟨dotProduct_mulVec_le_of_le, fun h ↦ le_iff.mpr ?_⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) fun x ↦ ?_
  rw [sub_mulVec, dotProduct_sub, sub_nonneg]
  exact h x

/-- Congruence `A ↦ M A M*` preserves the Loewner order. -/
lemma mul_mul_conjTranspose_le_of_le [Finite m] (h : A ≤ B) (M : Matrix m n 𝕜) :
    M * A * Mᴴ ≤ M * B * Mᴴ := by
  have := Fintype.ofFinite m
  rw [le_iff] at h ⊢
  simpa [Matrix.mul_sub, Matrix.sub_mul] using h.mul_mul_conjTranspose_same M

/-- Congruence `A ↦ M* A M` preserves the Loewner order. -/
lemma conjTranspose_mul_mul_le_of_le [Finite m] (h : A ≤ B) (M : Matrix n m 𝕜) :
    Mᴴ * A * M ≤ Mᴴ * B * M := by
  have := Fintype.ofFinite m
  rw [le_iff] at h ⊢
  simpa [Matrix.mul_sub, Matrix.sub_mul] using h.conjTranspose_mul_mul_same M

omit [Fintype n] in
/-- A matrix above a positive definite matrix in the Loewner order is positive definite. -/
lemma PosDef.of_le (hA : A.PosDef) (hAB : A ≤ B) : B.PosDef := by
  simpa using hA.add_posSemidef (le_iff.mp hAB)

end Order

/-! ### Inversion -/

section Inverse

variable [Fintype n] [DecidableEq n]

/-- A positive definite matrix `C` with `1 ≤ C` satisfies `C⁻¹ ≤ 1`. -/
lemma PosDef.inv_le_one_of_one_le {C : Matrix n n 𝕜} (hC : C.PosDef) (h : 1 ≤ C) : C⁻¹ ≤ 1 := by
  have hC' : IsSelfAdjoint C := hC.isHermitian.isSelfAdjoint
  have h_spec : ∀ x ∈ spectrum ℝ C, 1 ≤ x := (CFC.one_le_iff (R := ℝ) C hC').mp h
  have h_cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (spectrum ℝ C) :=
    continuousOn_id.inv₀ fun x hx ↦ (zero_lt_one.trans_le (h_spec x hx)).ne'
  rw [nonsing_inv_eq_ringInverse, ← cfc_ringInverse_id (R := ℝ) C hC.isUnit hC',
    cfc_le_one_iff _ C h_cont hC']
  exact fun x hx ↦ inv_le_one_of_one_le₀ (h_spec x hx)

/-- Matrix inversion is antitone on positive definite matrices for the Loewner order. -/
lemma PosDef.inv_le_inv {A B : Matrix n n 𝕜} (hA : A.PosDef) (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  -- `S` is the positive square root of `A⁻¹`
  set S := CFC.sqrt A⁻¹ with hS_def
  have hS_nonneg : 0 ≤ S := CFC.sqrt_nonneg _
  have hSS : S * S = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hA_det : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA.isUnit
  have hS_det : IsUnit S.det := by
    have : IsUnit (S * S).det := by rw [hSS]; exact (isUnit_iff_isUnit_det _).mp hA.inv.isUnit
    rw [det_mul] at this
    exact (IsUnit.mul_iff.mp this).1
  have hS_unit : IsUnit S := (isUnit_iff_isUnit_det S).mpr hS_det
  -- `S * A * S = 1`
  have hSAS : S * A * S = 1 := by
    have hA' : A = S⁻¹ * S⁻¹ := by rw [← mul_inv_rev, hSS, nonsing_inv_nonsing_inv A hA_det]
    calc S * A * S = (S * S⁻¹) * (S⁻¹ * S) := by rw [hA']; simp only [mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv S hS_det, nonsing_inv_mul S hS_det, one_mul]
  -- `C := S * B * S` satisfies `1 ≤ C` and is positive definite
  have hC : 1 ≤ S * B * S := hSAS ▸ conjugate_le_conjugate_of_nonneg hAB hS_nonneg
  have hC_pd : (S * B * S).PosDef :=
    (nonneg_iff_posSemidef.mp (zero_le_one.trans hC)).posDef_iff_isUnit.mpr
      ((hS_unit.mul (hA.of_le hAB).isUnit).mul hS_unit)
  -- conjugate `C⁻¹ ≤ 1` back by `S`
  have hSCS : S * (S * B * S)⁻¹ * S = B⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev]
    calc S * (S⁻¹ * (B⁻¹ * S⁻¹)) * S = (S * S⁻¹) * B⁻¹ * (S⁻¹ * S) := by simp only [mul_assoc]
      _ = B⁻¹ := by rw [mul_nonsing_inv S hS_det, nonsing_inv_mul S hS_det, one_mul, mul_one]
  calc B⁻¹ = S * (S * B * S)⁻¹ * S := hSCS.symm
    _ ≤ S * 1 * S := conjugate_le_conjugate_of_nonneg (hC_pd.inv_le_one_of_one_le hC) hS_nonneg
    _ = A⁻¹ := by rw [mul_one, hSS]

/-- For positive definite matrices, `B⁻¹ ≤ A⁻¹ ↔ A ≤ B` in the Loewner order. -/
lemma PosDef.inv_le_inv_iff {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    B⁻¹ ≤ A⁻¹ ↔ A ≤ B := by
  refine ⟨fun h ↦ ?_, hA.inv_le_inv⟩
  have h' := hB.inv.inv_le_inv h
  rwa [nonsing_inv_nonsing_inv A ((isUnit_iff_isUnit_det A).mp hA.isUnit),
    nonsing_inv_nonsing_inv B ((isUnit_iff_isUnit_det B).mp hB.isUnit)] at h'

/-- If `c • A ≤ B` with `A` positive definite and `c > 0`, then `B⁻¹ ≤ c⁻¹ • A⁻¹`. -/
lemma PosDef.inv_le_inv_smul {A B : Matrix n n 𝕜} (hA : A.PosDef) {c : 𝕜} (hc : 0 < c)
    (h : c • A ≤ B) : B⁻¹ ≤ c⁻¹ • A⁻¹ := by
  have hA' : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA.isUnit
  have h_inv : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, nonsing_inv_mul A hA', inv_mul_cancel₀ hc.ne', one_smul]
  rw [← h_inv]
  exact (hA.smul hc).inv_le_inv h

/-- If `c • A ≤ B` with `A` positive definite and `c > 0`, then
`x* B⁻¹ x ≤ c⁻¹ * x* A⁻¹ x` for every `x`. -/
lemma PosDef.dotProduct_inv_mulVec_le_of_smul_le {A B : Matrix n n 𝕜} (hA : A.PosDef) {c : 𝕜}
    (hc : 0 < c) (h : c • A ≤ B) (x : n → 𝕜) :
    star x ⬝ᵥ B⁻¹ *ᵥ x ≤ c⁻¹ * (star x ⬝ᵥ A⁻¹ *ᵥ x) := by
  have := dotProduct_mulVec_le_of_le (hA.inv_le_inv_smul hc h) x
  rwa [smul_mulVec, dotProduct_smul, smul_eq_mul] at this

end Inverse

/-! ### Square roots -/

section Sqrt

variable [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

-- The `DecidableEq n` instance enters the type through the continuous functional calculus
-- instance on matrices; the linter does not see it.
set_option linter.unusedDecidableInType false in
/-- The square root of a positive definite matrix is positive definite. -/
lemma PosDef.sqrt (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  have hnn : (CFC.sqrt A).PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  refine hnn.posDef_iff_isUnit.mpr ?_
  rw [CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg]
  exact hA.isUnit

set_option linter.unusedDecidableInType false in
/-- `√A * √A = A` for a positive semidefinite matrix. -/
lemma PosSemidef.sqrt_mul_sqrt (hA : A.PosSemidef) : CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- `√A * √(A⁻¹) = 1` for a positive definite matrix. -/
lemma PosDef.sqrt_mul_sqrt_inv (hA : A.PosDef) : CFC.sqrt A * CFC.sqrt A⁻¹ = 1 := by
  rw [← hA.posSemidef.inv_sqrt, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA.sqrt.isUnit)]

/-- `√(A⁻¹) * √A = 1` for a positive definite matrix. -/
lemma PosDef.sqrt_inv_mul_sqrt (hA : A.PosDef) : CFC.sqrt A⁻¹ * CFC.sqrt A = 1 := by
  rw [← hA.posSemidef.inv_sqrt, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA.sqrt.isUnit)]

/-- `√(A⁻¹) * A * √(A⁻¹) = 1` for a positive definite matrix: `√(A⁻¹)` whitens `A`. -/
lemma PosDef.sqrt_inv_mul_mul_sqrt_inv (hA : A.PosDef) : CFC.sqrt A⁻¹ * A * CFC.sqrt A⁻¹ = 1 := by
  calc CFC.sqrt A⁻¹ * A * CFC.sqrt A⁻¹
      = CFC.sqrt A⁻¹ * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt A⁻¹ := by
        rw [hA.posSemidef.sqrt_mul_sqrt]
    _ = 1 := by
        rw [← mul_assoc, mul_assoc _ (CFC.sqrt A), hA.sqrt_mul_sqrt_inv, mul_one,
          hA.sqrt_inv_mul_sqrt]

/-- `√A * A⁻¹ * √A = 1` for a positive definite matrix. -/
lemma PosDef.sqrt_mul_inv_mul_sqrt (hA : A.PosDef) : CFC.sqrt A * A⁻¹ * CFC.sqrt A = 1 := by
  calc CFC.sqrt A * A⁻¹ * CFC.sqrt A
      = CFC.sqrt A * (CFC.sqrt A⁻¹ * CFC.sqrt A⁻¹) * CFC.sqrt A := by
        rw [hA.inv.posSemidef.sqrt_mul_sqrt]
    _ = 1 := by
        rw [← mul_assoc, mul_assoc _ (CFC.sqrt A⁻¹), hA.sqrt_inv_mul_sqrt, mul_one,
          hA.sqrt_mul_sqrt_inv]

set_option linter.unusedDecidableInType false in
/-- The square root of a matrix is Hermitian (`CFC.sqrt A` is positive semidefinite for every
`A`, being `0` when `A` is not positive semidefinite). -/
lemma conjTranspose_sqrt (A : Matrix n n 𝕜) : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian.eq

set_option linter.unusedDecidableInType false in
/-- The square root of a real matrix is symmetric. -/
lemma transpose_sqrt (A : Matrix n n ℝ) : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
  simpa using conjTranspose_sqrt A

/-- `⟪√A u, √(A⁻¹) v⟫ = ⟪u, v⟫` for a positive definite matrix `A`. -/
lemma inner_toEuclideanCLM_sqrt_sqrt_inv (hA : A.PosDef) (u v : EuclideanSpace 𝕜 n) :
    ⟪toEuclideanCLM (𝕜 := 𝕜) (CFC.sqrt A) u, toEuclideanCLM (𝕜 := 𝕜) (CFC.sqrt A⁻¹) v⟫_𝕜 =
      ⟪u, v⟫_𝕜 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_toEuclideanCLM, conjTranspose_sqrt,
    ← mul_apply_eq_comp, ← map_mul, hA.sqrt_mul_sqrt_inv, map_one, one_apply_eq_self]

end Sqrt

end Matrix
