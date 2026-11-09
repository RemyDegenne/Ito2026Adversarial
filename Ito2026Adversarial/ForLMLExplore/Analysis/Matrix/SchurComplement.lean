/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The matrix determinant lemma for a rank-one update

## Main statements

* `Matrix.det_add_vecMulVec`: `det (A + u vᵀ) = det A * (1 + vᵀ A⁻¹ u)` for an invertible `A`.
  This is Mathlib's `Matrix.det_add_replicateCol_mul_replicateRow` with the rank-one matrix written
  as `vecMulVec u v` and the `1 × 1` determinant computed.
-/

@[expose] public section

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The **matrix determinant lemma** for a rank-one update `A + u vᵀ`. -/
lemma det_add_vecMulVec {A : Matrix n n R} (hA : IsUnit A.det) (u v : n → R) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ A⁻¹ *ᵥ u) := by
  have h : A + vecMulVec u v = A * (1 + vecMulVec (A⁻¹ *ᵥ u) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, mulVec_mulVec, mul_nonsing_inv A hA,
      one_mulVec]
  rw [h, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

end Matrix
