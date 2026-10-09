/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability and integrals of real functions

## Main statements

* `MeasureTheory.Integrable.of_ae_abs_le`: a real function bounded almost everywhere in absolute
  value is integrable for a finite measure (`Integrable.of_bound` with `|·|` for the norm);
* `MeasureTheory.integral_eq_of_lintegral_ofReal_eq`: two nonnegative functions with the same
  Lebesgue integral of `ENNReal.ofReal` have the same integral.

## Tags

integral, integrable function, Lebesgue integral
-/

@[expose] public section

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- An almost everywhere strongly measurable real function which is almost everywhere bounded in
absolute value is integrable for a finite measure. -/
lemma Integrable.of_ae_abs_le [IsFiniteMeasure P] {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    {M : ℝ} (hM : ∀ᵐ ω ∂P, |f ω| ≤ M) : Integrable f P :=
  Integrable.of_bound hf M (by filter_upwards [hM] with ω hω; rwa [Real.norm_eq_abs])

/-- Two almost everywhere nonnegative functions with the same Lebesgue integral of `ofReal` have the
same integral. -/
lemma integral_eq_of_lintegral_ofReal_eq {f g : Ω → ℝ} (hfm : AEStronglyMeasurable f P)
    (hgm : AEStronglyMeasurable g P) (hf : 0 ≤ᵐ[P] f) (hg : 0 ≤ᵐ[P] g)
    (heq : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P) :
    ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
  rw [integral_eq_lintegral_of_nonneg_ae hf hfm, integral_eq_lintegral_of_nonneg_ae hg hgm, heq]

end MeasureTheory
