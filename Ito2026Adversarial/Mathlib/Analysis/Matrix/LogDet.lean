/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The log-determinant of a positive definite matrix

## Main statements

* `Matrix.PosDef.log_det_le_card_mul_log_trace_div`: for a positive definite real matrix `A` of
  dimension `d`, `log det A ≤ d log(tr A / d)` (AM–GM inequality for the eigenvalues, in
  logarithmic form).
-/

@[expose] public section

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- **AM–GM inequality for the eigenvalues of a positive definite matrix**, in logarithmic form:
`log det A ≤ d log(tr A / d)`, where `d` is the dimension. Proof: `log (λᵢ / m) ≤ λᵢ / m - 1` for
the eigenvalues `λᵢ` and their mean `m = tr A / d`, and the right-hand sides sum to `0`. -/
lemma PosDef.log_det_le_card_mul_log_trace_div (hA : A.PosDef) :
    Real.log A.det ≤ Fintype.card n * Real.log (A.trace / Fintype.card n) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  set e := hA.1.eigenvalues with he
  have he_pos : ∀ i, 0 < e i := hA.eigenvalues_pos
  have hdet : A.det = ∏ i, e i := by
    rw [hA.1.det_eq_prod_eigenvalues]
    simp [he]
  have htr : A.trace = ∑ i, e i := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp [he]
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have htr_pos : 0 < A.trace := htr ▸ sum_pos (fun i _ ↦ he_pos i) univ_nonempty
  set m := A.trace / Fintype.card n with hm
  have hm_pos : 0 < m := div_pos htr_pos hd
  rw [hdet, Real.log_prod (fun i _ ↦ (he_pos i).ne')]
  have h1 (i : n) : Real.log (e i) - Real.log m ≤ e i / m - 1 := by
    rw [← Real.log_div (he_pos i).ne' hm_pos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (he_pos i) hm_pos)
  have h2 : ∑ i, (Real.log (e i) - Real.log m) ≤ ∑ i, (e i / m - 1) :=
    sum_le_sum fun i _ ↦ h1 i
  have h3 : ∑ i, (e i / m - 1) = 0 := by
    rw [sum_sub_distrib, ← sum_div, ← htr, hm, sum_const, card_univ]
    field_simp [htr_pos.ne']
    ring
  rw [sum_sub_distrib, h3, sum_const, card_univ, nsmul_eq_mul] at h2
  linarith

end Matrix
