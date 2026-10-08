/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.EReal.Basic

/-!
# Fenchel conjugates

The Fenchel conjugate of a real function on a real inner product space, with values in `EReal`.
Mathlib has no Fenchel (Legendre) conjugate.

## Main definitions

* `fenchelConjugateOn s f θ = sup_{x ∈ s} ⟪x, θ⟫ - f x`: the Fenchel conjugate of the restriction
  of `f` to `s` (`⊥` if `s` is empty, `⊤` if the supremum is infinite);
* `fenchelConjugate f = fenchelConjugateOn univ f`: the conjugate over the whole space.

## Main statements

* `le_fenchelConjugateOn` (the Fenchel–Young inequality `⟪x, θ⟫ ≤ f x + f^*(θ)`),
  `fenchelConjugateOn_le`, `fenchelConjugateOn_mono`, `fenchelConjugateOn_empty`.

## TODO

The general conjugate is a function on the dual `StrongDual ℝ E` of a normed space (or on a space
in duality with `E` through a pairing), and of an `EReal`-valued function; the inner-product
formulation is the one used by the online learning developments.
-/

@[expose] public section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s t : Set E} {f : E → ℝ}
  {x θ : E}

/-- The Fenchel conjugate of `f` restricted to `s`: `θ ↦ sup_{x ∈ s} ⟪x, θ⟫ - f x`, with values in
`EReal` (`⊥` if `s` is empty, `⊤` if the supremum is infinite). -/
noncomputable def fenchelConjugateOn (s : Set E) (f : E → ℝ) (θ : E) : EReal :=
  ⨆ x : s, ((⟪(x : E), θ⟫ - f x : ℝ) : EReal)

/-- The Fenchel conjugate `θ ↦ sup_x ⟪x, θ⟫ - f x` of `f`, with values in `EReal`. -/
noncomputable def fenchelConjugate (f : E → ℝ) : E → EReal := fenchelConjugateOn Set.univ f

lemma fenchelConjugateOn_apply (s : Set E) (f : E → ℝ) (θ : E) :
    fenchelConjugateOn s f θ = ⨆ x : s, ((⟪(x : E), θ⟫ - f x : ℝ) : EReal) := rfl

lemma fenchelConjugate_apply (f : E → ℝ) (θ : E) :
    fenchelConjugate f θ = fenchelConjugateOn Set.univ f θ := rfl

@[simp]
lemma fenchelConjugateOn_empty (f : E → ℝ) (θ : E) : fenchelConjugateOn ∅ f θ = ⊥ := by
  simp [fenchelConjugateOn]

/-- The Fenchel–Young inequality: `⟪x, θ⟫ - f x ≤ f^*(θ)` for `x ∈ s`. -/
lemma le_fenchelConjugateOn (f : E → ℝ) (hx : x ∈ s) (θ : E) :
    ((⟪x, θ⟫ - f x : ℝ) : EReal) ≤ fenchelConjugateOn s f θ :=
  le_iSup (fun x : s ↦ ((⟪(x : E), θ⟫ - f x : ℝ) : EReal)) ⟨x, hx⟩

/-- The Fenchel–Young inequality for the conjugate over the whole space. -/
lemma le_fenchelConjugate (f : E → ℝ) (x θ : E) :
    ((⟪x, θ⟫ - f x : ℝ) : EReal) ≤ fenchelConjugate f θ :=
  le_fenchelConjugateOn f (Set.mem_univ x) θ

lemma fenchelConjugateOn_le {c : EReal} (h : ∀ x ∈ s, ((⟪x, θ⟫ - f x : ℝ) : EReal) ≤ c) :
    fenchelConjugateOn s f θ ≤ c :=
  iSup_le fun x ↦ h x x.2

lemma fenchelConjugateOn_mono (h : s ⊆ t) (f : E → ℝ) (θ : E) :
    fenchelConjugateOn s f θ ≤ fenchelConjugateOn t f θ :=
  fenchelConjugateOn_le fun _ hx ↦ le_fenchelConjugateOn f (h hx) θ
