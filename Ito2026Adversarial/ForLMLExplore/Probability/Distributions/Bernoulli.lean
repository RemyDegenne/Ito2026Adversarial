/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integrals and densities of Bernoulli measures

For the Bernoulli measure `Ber(x, y, p) = p δₓ + (1 - p) δ_y` of Mathlib
(`ProbabilityTheory.bernoulliMeasure`, `p : unitInterval`), with the weights written as
`ENNReal.ofReal p` and `ENNReal.ofReal (1 - p)` (`unitInterval.coe_toNNReal_eq_ofReal`).

## Main statements

* `lintegral_bernoulliMeasure`: `∫⁻ f ∂Ber(x, y, p) = p f x + (1 - p) f y`;
* `bernoulliMeasure_eq_withDensity`: for `x ≠ y` and `q ∉ {0, 1}`, `Ber(x, y, p)` has density
  `p / q` at `x` and `(1 - p) / (1 - q)` at `y` with respect to `Ber(x, y, q)`; hence
  `Ber(x, y, p) ≪ Ber(x, y, q)` (`bernoulliMeasure_absolutelyContinuous`) and the
  Radon–Nikodym derivative is that density (`rnDeriv_bernoulliMeasure`);
* `bernoulliMeasure_absolutelyContinuous_iff`: for `x ≠ y`, `Ber(x, y, p) ≪ Ber(x, y, q)` unless
  `q ∈ {0, 1}` and `p ≠ q`;
* `bernoulliMeasure_apply_singleton_left`, `bernoulliMeasure_apply_singleton_right`: the masses
  of the two atoms.
-/

@[expose] public section

open MeasureTheory unitInterval
open scoped ENNReal NNReal

/-- The coercion `unitInterval → ℝ≥0 → ℝ≥0∞` is `ENNReal.ofReal`. -/
lemma unitInterval.coe_toNNReal_eq_ofReal (p : I) :
    ((toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p := by
  rw [← unitInterval.coe_toNNReal, ENNReal.ofReal_coe_nnreal]

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {x y : X} {p q : I}

lemma bernoulliMeasure_apply_singleton_left (hxy : x ≠ y) (p : I) :
    Ber(x, y, p) {x} = ENNReal.ofReal p := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton x) (Set.mem_singleton x)
    (by simpa using hxy.symm), coe_toNNReal_eq_ofReal]

lemma bernoulliMeasure_apply_singleton_right (hxy : x ≠ y) (p : I) :
    Ber(x, y, p) {y} = ENNReal.ofReal (1 - p) := by
  rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton y) (by simpa using hxy)
    (Set.mem_singleton y), coe_toNNReal_eq_ofReal, coe_symm_eq]

/-- The Lebesgue integral of a function against a Bernoulli measure. -/
lemma lintegral_bernoulliMeasure (x y : X) (p : I) (f : X → ℝ≥0∞) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, ENNReal.smul_def, ENNReal.smul_def, coe_toNNReal_eq_ofReal,
    coe_toNNReal_eq_ofReal, coe_symm_eq, smul_eq_mul, smul_eq_mul]

/-- For `x ≠ y` and `q ∉ {0, 1}`, the Bernoulli measure `Ber(x, y, p)` has density `p / q` at `x`
and `(1 - p) / (1 - q)` at `y` with respect to `Ber(x, y, q)`. -/
lemma bernoulliMeasure_eq_withDensity [DecidableEq X] (hxy : x ≠ y) (p : I) (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    Ber(x, y, p) = Ber(x, y, q).withDensity
      (fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))) := by
  have hq0 : (q : ℝ) ≠ 0 := coe_ne_zero.2 hq
  have hq1' : (1 : ℝ) - q ≠ 0 := sub_ne_zero.2 (coe_ne_one.2 hq1).symm
  rw [bernoulliMeasure_def, bernoulliMeasure_def, withDensity_add_measure]
  simp_rw [ENNReal.smul_def]
  rw [withDensity_smul_measure, withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
    ite_eq_left rfl, ite_eq_right hxy.symm, smul_smul, smul_smul, coe_toNNReal_eq_ofReal,
    coe_toNNReal_eq_ofReal, coe_toNNReal_eq_ofReal, coe_toNNReal_eq_ofReal, coe_symm_eq,
    coe_symm_eq]
  congr 1 <;> congr 1
  · rw [← ENNReal.ofReal_mul q.2.1]
    congr 1
    field_simp
  · rw [← ENNReal.ofReal_mul (sub_nonneg.2 q.2.2)]
    congr 1
    field_simp

/-- For `x ≠ y` and `q ∉ {0, 1}`, `Ber(x, y, p) ≪ Ber(x, y, q)`. -/
lemma bernoulliMeasure_absolutelyContinuous (hxy : x ≠ y) (p : I) (hq : q ≠ 0) (hq1 : q ≠ 1) :
    Ber(x, y, p) ≪ Ber(x, y, q) := by
  classical
  rw [bernoulliMeasure_eq_withDensity hxy p hq hq1]
  exact withDensity_absolutelyContinuous _ _

/-- For `x ≠ y`, `Ber(x, y, p) ≪ Ber(x, y, q)` unless `q ∈ {0, 1}` and `p ≠ q`. -/
lemma bernoulliMeasure_absolutelyContinuous_iff (hxy : x ≠ y) :
    Ber(x, y, p) ≪ Ber(x, y, q) ↔ (q = 0 → p = 0) ∧ (q = 1 → p = 1) := by
  refine ⟨fun h ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩, fun ⟨h0, h1⟩ ↦ ?_⟩
  · subst hq
    have hx : Ber(x, y, p) {x} = 0 := h (by simp [hxy.symm])
    rw [bernoulliMeasure_apply_singleton_left hxy, ENNReal.ofReal_eq_zero] at hx
    exact Set.Icc.coe_eq_zero.1 (le_antisymm hx p.2.1)
  · subst hq
    have hy : Ber(x, y, p) {y} = 0 := h (by simp [hxy])
    rw [bernoulliMeasure_apply_singleton_right hxy, ENNReal.ofReal_eq_zero, sub_nonpos] at hy
    exact Set.Icc.coe_eq_one.1 (le_antisymm p.2.2 hy)
  · by_cases hq : q = 0
    · rw [h0 hq, hq]
    by_cases hq1 : q = 1
    · rw [h1 hq1, hq1]
    exact bernoulliMeasure_absolutelyContinuous hxy p hq hq1

/-- The Radon–Nikodym derivative of `Ber(x, y, p)` with respect to `Ber(x, y, q)`. -/
lemma rnDeriv_bernoulliMeasure [DecidableEq X] (hxy : x ≠ y) (p : I) (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    Ber(x, y, p).rnDeriv Ber(x, y, q) =ᵐ[Ber(x, y, q)]
      fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q)) := by
  rw [bernoulliMeasure_eq_withDensity hxy p hq hq1]
  exact Measure.rnDeriv_withDensity _
    (Measurable.ite (measurableSet_singleton x) measurable_const measurable_const)

end ProbabilityTheory
