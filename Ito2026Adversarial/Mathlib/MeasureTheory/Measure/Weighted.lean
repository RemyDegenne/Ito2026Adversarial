/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def

/-!
# Weighted measures on a finite type

`weightedMeasure p = ∑ i, p i • δ_i` is the measure on a finite type `ι` with (real) weights `p`
(negative weights are replaced by `0`). The map `p ↦ weightedMeasure p` is measurable, which
allows building kernels sampling from a computed distribution.

## Main definitions

* `MeasureTheory.weightedMeasure p = ∑ i, ENNReal.ofReal (p i) • δ_i`.

## Main statements

* `weightedMeasure_apply`, `weightedMeasure_singleton`, `measureReal_weightedMeasure_singleton`:
  the masses of sets and of atoms;
* `isFiniteMeasure_weightedMeasure`: a weighted measure is finite (an instance);
* `isProbabilityMeasure_weightedMeasure`: it is a probability measure for a probability vector `p`;
* `weightedMeasure_absolutelyContinuous`: `weightedMeasure q ≪ weightedMeasure p` when the support
  of `q` is contained in that of `p`;
* `measurable_weightedMeasure`: `p ↦ weightedMeasure p` is measurable.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] {p q : ι → ℝ}

/-- The measure on `ι` with weights `p`: `∑ i, p i • δ_i` (negative weights count as `0`). -/
noncomputable def weightedMeasure (p : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

/-- The mass of a measurable set under `weightedMeasure p`. -/
lemma weightedMeasure_apply (p : ι → ℝ) {s : Set ι} (hs : MeasurableSet s) :
    weightedMeasure p s = ∑ i, ENNReal.ofReal (p i) * s.indicator 1 i := by
  simp [weightedMeasure, Finset.sum_apply, Measure.dirac_apply' _ hs]

/-- The total mass of `weightedMeasure p`. -/
lemma weightedMeasure_univ (p : ι → ℝ) :
    weightedMeasure p Set.univ = ∑ i, ENNReal.ofReal (p i) := by
  simp [weightedMeasure_apply _ MeasurableSet.univ]

/-- The mass of an atom under `weightedMeasure p`. -/
@[simp]
lemma weightedMeasure_singleton [MeasurableSingletonClass ι] (p : ι → ℝ) (i : ι) :
    weightedMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  rw [weightedMeasure_apply p (measurableSet_singleton i)]
  simp [Set.indicator_apply]

/-- The real mass of an atom under `weightedMeasure p`, for nonnegative weights. -/
lemma measureReal_weightedMeasure_singleton [MeasurableSingletonClass ι] (hp : ∀ i, 0 ≤ p i)
    (i : ι) :
    (weightedMeasure p).real {i} = p i := by
  rw [measureReal_def, weightedMeasure_singleton, ENNReal.toReal_ofReal (hp i)]

/-- A weighted measure is finite. -/
instance isFiniteMeasure_weightedMeasure (p : ι → ℝ) : IsFiniteMeasure (weightedMeasure p) :=
  ⟨by simp [weightedMeasure_univ, ENNReal.sum_lt_top]⟩

/-- The weighted measure of a probability vector is a probability measure. -/
lemma isProbabilityMeasure_weightedMeasure (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    IsProbabilityMeasure (weightedMeasure p) := by
  constructor
  rw [weightedMeasure_univ, ← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp0 i), hp1,
    ENNReal.ofReal_one]

/-- `weightedMeasure q ≪ weightedMeasure p` when the support of `q` is contained in that of
`p`. -/
lemma weightedMeasure_absolutelyContinuous [MeasurableSingletonClass ι]
    (hq : ∀ i, 0 < q i → 0 < p i) :
    weightedMeasure q ≪ weightedMeasure p := by
  intro s hs
  rw [weightedMeasure_apply q (s.toFinite.measurableSet)]
  rw [weightedMeasure_apply p (s.toFinite.measurableSet)] at hs
  rw [Finset.sum_eq_zero_iff] at hs ⊢
  intro i _
  have hi := hs i (Finset.mem_univ i)
  by_cases his : i ∈ s
  · simp only [Set.indicator_of_mem his, Pi.one_apply, mul_one, ENNReal.ofReal_eq_zero] at hi ⊢
    by_contra h
    exact absurd hi (not_le.2 (hq i (not_le.1 h)))
  · simp [Set.indicator_of_notMem his]

/-- The integral against `weightedMeasure p` is the weighted sum `∑ x, p x * f x`. -/
lemma lintegral_weightedMeasure_eq_sum [MeasurableSingletonClass ι] (p : ι → ℝ) (f : ι → ℝ≥0∞) :
    ∫⁻ x, f x ∂(weightedMeasure p) = ∑ x, ENNReal.ofReal (p x) * f x := by
  simp only [weightedMeasure, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]

/-- The map `p ↦ weightedMeasure p` is measurable. -/
lemma measurable_weightedMeasure : Measurable (weightedMeasure (ι := ι)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [weightedMeasure_apply _ hs]
  exact Finset.measurable_sum _ fun i _ ↦
    (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul measurable_const

end MeasureTheory
