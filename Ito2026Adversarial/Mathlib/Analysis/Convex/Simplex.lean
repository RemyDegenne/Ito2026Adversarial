/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# The probability simplex

## Main definitions

* `simplex ι`: the probability simplex `{p | ∀ i, 0 ≤ p i, ∑ i, p i = 1}` of `EuclideanSpace ℝ ι`;
* `openSimplex ι`: its subset of distributions with positive coordinates;
* `uniformVec ι`, `uniformSimplex ι`: the uniform distribution, as a vector and as an element of
  the simplex.

## Main statements

* `convex_simplex`, `isClosed_simplex`, `isCompact_simplex`, `measurableSet_simplex`: the simplex
  is a compact convex set;
* `single_mem_simplex`: its vertices;
* `simplex_eq_range_weights`: it is the set of weight vectors of `Convexity.StdSimplex ℝ ι`;
* `toLp_mem_simplex_iff`: a function `p : ι → ℝ` gives a point of the simplex iff its coordinates
  are nonnegative and sum to `1`.

A point `p : simplex ι` coerces to the function `ι → ℝ` of its coordinates (`p i`), so that it can
be passed to definitions taking general weight vectors.

## Implementation notes

Mathlib models the standard simplex by the *bundled type* `Convexity.StdSimplex ℝ ι`, whose terms
are the weight vectors themselves (the set-valued `stdSimplex` of `ι → ℝ` was deprecated on
2026-08-29). We keep a set inside a vector space because the algorithms and statements of this
library take convex combinations of weight vectors, speak of convexity, concavity and continuity
*on the simplex*, and differentiate on it (gradients, Fenchel conjugates, Bregman divergences),
none of which the bundled type expresses (it is not a module). The ambient space is
`EuclideanSpace ℝ ι` rather than `ι → ℝ` because the latter carries the sup norm and no inner
product. The two descriptions carry the same information: `simplex_eq_range_weights`. Weight
vectors computed as functions `ι → ℝ` (softmax weights, normalized counts, …) enter the simplex
through `WithLp.toLp 2` (`toLp_mem_simplex_iff`).
-/

@[expose] public section

open MeasureTheory

namespace Learning

variable {ι : Type*} [Fintype ι]

/-- The probability simplex `{p | ∀ i, 0 ≤ p i, ∑ i, p i = 1}` of `EuclideanSpace ℝ ι`. -/
def simplex (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

lemma mem_simplex_iff {p : EuclideanSpace ℝ ι} :
    p ∈ simplex ι ↔ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := Iff.rfl

/-- A function `p : ι → ℝ` gives a point of the simplex iff its coordinates are nonnegative and
sum to `1`. -/
lemma toLp_mem_simplex_iff {p : ι → ℝ} :
    WithLp.toLp 2 p ∈ simplex ι ↔ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := Iff.rfl

lemma nonneg_of_mem_simplex {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (i : ι) : 0 ≤ p i :=
  hp.1 i

lemma sum_eq_one_of_mem_simplex {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    ∑ i, p i = 1 :=
  hp.2

lemma le_one_of_mem_simplex {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (i : ι) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ ↦ hp.1 j) (Finset.mem_univ i)

/-- A point of the simplex is a function on `ι`: `p i` is its `i`-th coordinate. -/
instance : CoeFun (simplex ι) (fun _ ↦ ι → ℝ) := ⟨fun p ↦ (p : EuclideanSpace ℝ ι).ofLp⟩

namespace simplex

lemma nonneg (p : simplex ι) (i : ι) : 0 ≤ p i := p.2.1 i

lemma sum_eq_one (p : simplex ι) : ∑ i, p i = 1 := p.2.2

lemma le_one (p : simplex ι) (i : ι) : p i ≤ 1 := le_one_of_mem_simplex p.2 i

end simplex

@[fun_prop]
lemma continuous_coe_simplex : Continuous fun p : simplex ι ↦ (p : ι → ℝ) :=
  (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

@[fun_prop]
lemma measurable_coe_simplex : Measurable fun p : simplex ι ↦ (p : ι → ℝ) :=
  (WithLp.measurable_ofLp 2 _).comp measurable_subtype_coe

/-- The probability simplex is the set of weight vectors of Mathlib's bundled
`Convexity.StdSimplex ℝ ι`. -/
lemma simplex_eq_range_weights :
    simplex ι = Set.range fun w : Convexity.StdSimplex ℝ ι ↦ WithLp.toLp 2 ⇑w.weights := by
  ext p
  have h := Set.ext_iff.1 (Convexity.StdSimplex.range_toFun_comp_weights (R := ℝ) (X := ι))
    (WithLp.ofLp p)
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at h
  refine ⟨fun hp ↦ ?_, ?_⟩
  · obtain ⟨w, hw⟩ := h.2 hp
    exact ⟨w, by simp only [hw, WithLp.toLp_ofLp]⟩
  · rintro ⟨w, rfl⟩
    exact h.1 ⟨w, rfl⟩

lemma convex_simplex : Convex ℝ (simplex ι) := by
  refine fun f hf g hg a b ha hb hab ↦ ⟨fun i ↦ ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf.1 i)) (mul_nonneg hb (hg.1 i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2, hg.2, mul_one, mul_one,
      hab]

lemma isClosed_simplex : IsClosed (simplex ι) := by
  have : simplex ι = (⋂ i, {p : EuclideanSpace ℝ ι | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1} := by
    ext p
    simp [mem_simplex_iff]
  rw [this]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_eq (by fun_prop) continuous_const)

lemma isCompact_simplex : IsCompact (simplex ι) := by
  rw [simplex_eq_range_weights]
  exact isCompact_range ((PiLp.continuous_toLp 2 _).comp
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous)

lemma measurableSet_simplex : MeasurableSet (simplex ι) := isClosed_simplex.measurableSet

lemma single_mem_simplex [DecidableEq ι] (i : ι) : EuclideanSpace.single i (1 : ℝ) ∈ simplex ι := by
  refine ⟨fun j ↦ ?_, by simp⟩
  rw [PiLp.single_apply]
  split_ifs <;> norm_num

/-- The open simplex `{p ∈ simplex ι | ∀ i, 0 < p i}` of distributions with positive
coordinates. -/
def openSimplex (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {p ∈ simplex ι | ∀ i, 0 < p i}

lemma openSimplex_subset : openSimplex ι ⊆ simplex ι := fun _ h ↦ h.1

/-- The uniform distribution `(1/|ι|, …, 1/|ι|)` of `EuclideanSpace ℝ ι`. -/
noncomputable def uniformVec (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun _ ↦ (Fintype.card ι : ℝ)⁻¹

@[simp] lemma uniformVec_apply (i : ι) : uniformVec ι i = (Fintype.card ι : ℝ)⁻¹ := rfl

lemma uniformVec_mem_simplex [Nonempty ι] : uniformVec ι ∈ simplex ι := by
  refine ⟨fun _ ↦ by simp only [uniformVec_apply]; positivity, ?_⟩
  simp [Finset.sum_const, Finset.card_univ]

/-- The uniform distribution, as an element of the simplex. -/
noncomputable def uniformSimplex (ι : Type*) [Fintype ι] [Nonempty ι] : simplex ι :=
  ⟨uniformVec ι, uniformVec_mem_simplex⟩

instance [Nonempty ι] : Nonempty (simplex ι) := ⟨uniformSimplex ι⟩

end Learning
