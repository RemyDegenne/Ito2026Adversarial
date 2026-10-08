/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.Calculus.Gradient.Measurable
public import Ito2026Adversarial.Mathlib.MeasureTheory.MeasurableSpace.ToSet
public import Ito2026Adversarial.Mathlib.Analysis.Convex.FenchelConjugate
public import Ito2026Adversarial.Mathlib.Analysis.Convex.Simplex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Follow-the-regularized-leader on the probability simplex

The distribution played by follow-the-regularized-leader (FTRL) on the simplex of
`EuclideanSpace ℝ ι`, as a measurable function of the cumulative loss (or reward) vector, so that
FTRL-based bandit algorithms (Tsallis-INF, `Online/Bandit/TsallisINF.lean`) can be built with
`Algorithm.stateful`. The arm is then drawn with `simplexKernel`
(`Online/Bandit/ImportanceWeighting.lean`).

## Main definitions

* `ftrlValue φ θ = sup_{p ∈ simplex} ⟪p, θ⟫ + φ p`: the value function of FTRL with (concave)
  regularizer `φ`, the Fenchel conjugate of `-φ` on the simplex. Its gradient is the FTRL
  distribution `ftrlSimplex φ θ = argmax_{p ∈ simplex} ⟪p, θ⟫ + φ p` (as an element of the
  simplex; an arbitrary element where the value function is not differentiable, which does not
  happen for strictly concave `φ`). Defining the maximizer as a gradient makes it measurable
  (`measurable_ftrlSimplex`).
* `ftrlSimplexParam φ (β, θ)`: the same for a regularizer `φ β` depending on a parameter `β` in
  an inner product space, defined through the partial gradient in `θ` of the joint value function
  (`gradientSnd`), so as to be measurable in `(β, θ)`.
* `tsallisEntropy α p = (1 / α) ∑ i, (p i ^ α - p i)`: the Tsallis entropy, nonnegative and
  concave on the simplex for `α ∈ (0, 1)`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace Learning

variable {ι : Type*} [Fintype ι]

/-! ### The FTRL distribution as a gradient -/

/-- The value function `Φ(θ) = sup_{p ∈ simplex} ⟪p, θ⟫ + φ p` of FTRL with regularizer `φ`: the
Fenchel conjugate of `-φ` on the simplex. -/
noncomputable def ftrlValue (φ : EuclideanSpace ℝ ι → ℝ) (θ : EuclideanSpace ℝ ι) : ℝ :=
  (fenchelConjugateOn (simplex ι) (-φ) θ).toReal

/-- The FTRL distribution `argmax_{p ∈ simplex} ⟪p, θ⟫ + φ p`, defined as the gradient of the
value function `ftrlValue φ` at `θ` (an arbitrary element of the simplex where the value function
is not differentiable). -/
noncomputable def ftrlSimplex [Nonempty ι] (φ : EuclideanSpace ℝ ι → ℝ) (θ : EuclideanSpace ℝ ι) :
    simplex ι :=
  toSet (simplex ι) (gradient (ftrlValue φ) θ)

@[fun_prop]
lemma measurable_ftrlSimplex [Nonempty ι] (φ : EuclideanSpace ℝ ι → ℝ) :
    Measurable (ftrlSimplex φ) :=
  (measurable_toSet measurableSet_simplex).comp (measurable_gradient _)

section Param

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The gradient with respect to the second variable of a function `G : F × E → ℝ`, obtained by
restricting the joint Fréchet derivative to the second factor (zero where `G` is not
differentiable). -/
noncomputable def gradientSnd (G : F × E → ℝ) (q : F × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ G q).comp (ContinuousLinearMap.inr ℝ F E))

omit [CompleteSpace F] [SecondCountableTopology F] in
@[fun_prop]
lemma measurable_gradientSnd (G : F × E → ℝ) : Measurable (gradientSnd G) := by
  have h1 : Measurable fun q ↦ (fderiv ℝ G q).comp (ContinuousLinearMap.inr ℝ F E) :=
    ((ContinuousLinearMap.compL ℝ E (F × E) ℝ).flip
      (ContinuousLinearMap.inr ℝ F E)).continuous.measurable.comp (measurable_fderiv ℝ G)
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp h1

/-- The value function of FTRL with a regularizer `φ β` depending on a parameter `β : F`, as a
function of `(β, θ)`. -/
noncomputable def ftrlValueParam (φ : F → EuclideanSpace ℝ ι → ℝ) (q : F × EuclideanSpace ℝ ι) :
    ℝ :=
  ftrlValue (φ q.1) q.2

/-- The FTRL distribution `argmax_{p ∈ simplex} ⟪p, θ⟫ + φ β p` for the regularizer `φ β`, defined
as the partial gradient in `θ` of the joint value function `ftrlValueParam φ` at `(β, θ)`. The
parameter `β` lives in an inner product space `F` (a real, or a vector of means). -/
noncomputable def ftrlSimplexParam [Nonempty ι] (φ : F → EuclideanSpace ℝ ι → ℝ)
    (q : F × EuclideanSpace ℝ ι) : simplex ι :=
  toSet (simplex ι) (gradientSnd (ftrlValueParam φ) q)

omit [CompleteSpace F] [SecondCountableTopology F] in
@[fun_prop]
lemma measurable_ftrlSimplexParam [Nonempty ι] (φ : F → EuclideanSpace ℝ ι → ℝ) :
    Measurable (ftrlSimplexParam φ) :=
  (measurable_toSet measurableSet_simplex).comp (measurable_gradientSnd _)

end Param

/-! ### Tsallis entropy -/

/-- The Tsallis entropy `φ_α(p) = (1 / α) ∑ i, (p i ^ α - p i)`, nonnegative and concave on the
simplex for `α ∈ (0, 1)`. -/
noncomputable def tsallisEntropy (α : ℝ) (p : EuclideanSpace ℝ ι) : ℝ :=
  α⁻¹ * ∑ i, (p i ^ α - p i)

@[fun_prop]
lemma measurable_tsallisEntropy (α : ℝ) : Measurable (tsallisEntropy (ι := ι) α) := by
  unfold tsallisEntropy
  fun_prop

end Learning
