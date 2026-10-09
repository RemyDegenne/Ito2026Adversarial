/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Integrals against a conditional distribution

## Main statements

* `ProbabilityTheory.HasCondDistrib.lintegral_prodMk`: if `κ` is the conditional law of `Y` given
  `X`, the Lebesgue integral of a function of `(X, Y)` is the integral of its integral against
  `κ (X ω)`.

## Tags

conditional distribution, disintegration
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {P : Measure Ω} {X : Ω → α} {Y : Ω → β} {κ : Kernel α β}

/-- The Lebesgue integral of a function of `(X, Y)` is the integral of its integral against the
conditional law of `Y` given `X`. -/
lemma HasCondDistrib.lintegral_prodMk [SFinite P] [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ b, f (X ω, b) ∂κ (X ω) ∂P := by
  rw [HasLaw.lintegral_comp h hf.aemeasurable, Measure.lintegral_compProd hf,
    lintegral_map' (hf.lintegral_kernel_prod_right').aemeasurable h.aemeasurable_fst]

end ProbabilityTheory
