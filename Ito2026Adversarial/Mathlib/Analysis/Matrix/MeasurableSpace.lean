/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Instances.Matrix

/-!
# Measurability of matrix operations

For the measurable space structure on `Matrix m n α` (that of `m → n → α`):

* `Matrix.measurable_inv`: matrix inversion `A ↦ A⁻¹` is measurable on `Matrix ι ι 𝕜` for
  `𝕜 = ℝ` or `ℂ` (the inverse is the adjugate divided by the determinant, and both are
  continuous);
* `Matrix.measurable_mulVec`: the matrix-vector product `(A, v) ↦ A *ᵥ v` is measurable.

The compositional versions `Measurable.matrix_inv`, `Measurable.mulVec`, `Measurable.dotProduct`,
`Measurable.matrix_add`, `Measurable.matrix_smul` are tagged `@[fun_prop]`.
-/

@[expose] public section

open Matrix

variable {X m n α : Type*} [MeasurableSpace X] [MeasurableSpace α]

section Arithmetic

@[fun_prop]
lemma Measurable.dotProduct [Fintype n] [Mul α] [AddCommMonoid α] [MeasurableMul₂ α]
    [MeasurableAdd₂ α] {v w : X → n → α} (hv : Measurable v) (hw : Measurable w) :
    Measurable fun x ↦ v x ⬝ᵥ w x := by
  change Measurable fun x ↦ ∑ i, v x i * w x i
  exact Finset.measurable_sum _ fun i _ ↦ (hv.eval (a := i)).mul (hw.eval (a := i))

@[fun_prop]
lemma Measurable.mulVec [Fintype n] [NonUnitalNonAssocSemiring α] [MeasurableMul₂ α]
    [MeasurableAdd₂ α] {A : X → Matrix m n α} {v : X → n → α} (hA : Measurable A)
    (hv : Measurable v) :
    Measurable fun x ↦ A x *ᵥ v x :=
  Measurable.of_eval fun i ↦ Measurable.dotProduct (hA.eval (a := i)) hv

/-- The matrix-vector product is measurable. -/
lemma Matrix.measurable_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] [MeasurableMul₂ α]
    [MeasurableAdd₂ α] :
    Measurable fun p : Matrix m n α × (n → α) ↦ p.1 *ᵥ p.2 :=
  measurable_fst.mulVec measurable_snd

@[fun_prop]
lemma Measurable.matrix_add [Add α] [MeasurableAdd₂ α] {A B : X → Matrix m n α}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x ↦ A x + B x :=
  Measurable.of_eval_matrix _ fun _ _ ↦ hA.eval_matrix.add hB.eval_matrix

@[fun_prop]
lemma Measurable.matrix_smul {R : Type*} [MeasurableSpace R] [SMul R α] [MeasurableSMul₂ R α]
    {c : X → R} {A : X → Matrix m n α} (hc : Measurable c) (hA : Measurable A) :
    Measurable fun x ↦ c x • A x :=
  Measurable.of_eval_matrix _ fun _ _ ↦ hc.smul hA.eval_matrix

end Arithmetic

section Inverse

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Matrix inversion is measurable. -/
lemma Matrix.measurable_inv : Measurable fun A : Matrix ι ι 𝕜 ↦ A⁻¹ := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact continuous_id.matrix_det.measurable.inv.mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

@[fun_prop]
lemma Measurable.matrix_inv {A : X → Matrix ι ι 𝕜} (hA : Measurable A) :
    Measurable fun x ↦ (A x)⁻¹ :=
  Matrix.measurable_inv.comp hA

end Inverse
