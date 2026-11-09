/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Measurability of the gradient

The gradient of a function on a complete inner product space is a measurable function of the
point (`measurable_gradient`), as the Fréchet derivative is (`measurable_fderiv`). This is what
makes maximizers defined as gradients of value functions measurable (Danskin's theorem read
backwards: the FTRL distribution on the simplex, the FTPL action as the gradient of a support
function).

## Main statements

* `measurable_gradient`: `x ↦ ∇f x` is measurable.
-/

@[expose] public section

/-- The gradient of a function on a complete inner product space is measurable. -/
@[fun_prop]
lemma measurable_gradient {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (f : E → 𝕜) :
    Measurable (gradient f) :=
  (InnerProductSpace.toDual 𝕜 E).symm.continuous.measurable.comp (measurable_fderiv 𝕜 f)
