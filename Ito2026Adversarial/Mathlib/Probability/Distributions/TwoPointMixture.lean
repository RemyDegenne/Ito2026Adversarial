/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Probability.Distributions.TwoPoint
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Mean and mixtures of two-point distributions

Complements to `Ito2026Adversarial.Mathlib.Probability.Distributions.TwoPoint`: the two-point
distribution `twoPoint x` on `{-1, 1}` with mean `x ∈ [-1, 1]` has mean `x`, is supported in
`[-1, 1]`, and two-point distributions are linear in their mean: a mixture of two-point
distributions is the two-point distribution of the mixed mean.

## Main statements

* `integral_twoPoint`: `∫ r ∂twoPoint x = x` for `x ∈ [-1, 1]`.
* `ae_mem_Icc_twoPoint`: `twoPoint x` is supported in `[-1, 1]`.
* `sum_smul_twoPoint`: `∑ i ∈ s, w i • twoPoint (a i) = twoPoint (∑ i ∈ s, w i * a i)` for
  nonnegative weights `w` summing to `1` and means `a i ∈ [-1, 1]`.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

/-- The two-point distribution `twoPoint x` has mean `x`, for `x ∈ [-1, 1]`. -/
lemma integral_twoPoint {x : ℝ} (hx : x ∈ Icc (-1) 1) : ∫ r, r ∂twoPoint x = x := by
  have h : (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [twoPoint, integral_bernoulliMeasure, Nat.cast_ofNat, projIcc_of_mem _ h]
  simp only [smul_eq_mul]
  ring

/-- The two-point distribution is supported in `[-1, 1]`. -/
lemma ae_mem_Icc_twoPoint (x : ℝ) : ∀ᵐ r ∂twoPoint x, r ∈ Icc (-1) 1 := by
  rw [twoPoint, bernoulliMeasure_def, ae_add_measure_iff]
  refine ⟨?_, ?_⟩ <;>
  · refine Measure.ae_smul_measure ?_ _
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)

/-- A mixture of two-point distributions is the two-point distribution of the mixed mean. -/
lemma sum_smul_twoPoint {ι : Type*} {s : Finset ι} {w a : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, a i ∈ Icc (-1) 1) :
    ∑ i ∈ s, ENNReal.ofReal (w i) • twoPoint (a i) = twoPoint (∑ i ∈ s, w i * a i) := by
  have hmem : ∑ i ∈ s, w i * a i ∈ Icc (-1) 1 := by
    constructor
    · calc (-1 : ℝ) = ∑ i ∈ s, w i * (-1) := by rw [← Finset.sum_mul, hw1]; ring
        _ ≤ ∑ i ∈ s, w i * a i :=
          Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (ha i hi).1 (hw i hi)
    · calc ∑ i ∈ s, w i * a i ≤ ∑ i ∈ s, w i * 1 :=
          Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (ha i hi).2 (hw i hi)
        _ = 1 := by rw [← Finset.sum_mul, hw1, one_mul]
  have key (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
      ∑ i ∈ s, ENNReal.ofReal (w i) * ENNReal.ofReal (f i)
        = ENNReal.ofReal (∑ i ∈ s, w i * f i) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i hi ↦ mul_nonneg (hw i hi) (hf i hi)]
    exact Finset.sum_congr rfl fun i hi ↦ (ENNReal.ofReal_mul (hw i hi)).symm
  rw [twoPoint_eq hmem, Finset.sum_congr rfl fun i hi ↦ by rw [twoPoint_eq (ha i hi)]]
  simp only [smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
  rw [key _ fun i hi ↦ by linarith [(ha i hi).1], key _ fun i hi ↦ by linarith [(ha i hi).2]]
  congr 3
  · simp_rw [mul_div_assoc', mul_add, mul_one, ← Finset.sum_div, Finset.sum_add_distrib, hw1]
  · simp_rw [mul_div_assoc', mul_sub, mul_one, ← Finset.sum_div, Finset.sum_sub_distrib, hw1]

end ProbabilityTheory
