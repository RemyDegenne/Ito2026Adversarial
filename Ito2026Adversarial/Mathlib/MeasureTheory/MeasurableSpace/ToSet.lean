/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable projection of a point onto a set

`toSet K v` is the point `v` as an element of the subtype `K`, or an arbitrary element of `K` when
`v ∉ K`. It is measurable when `K` is a measurable set (`measurable_toSet`). It turns a measurable
map into `X` whose values are known to lie in `K` (a gradient of a support function, a maximizer of
a concave function on the simplex) into a measurable map into `K`.

## Main definitions

* `toSet K v`: `v` as an element of `K` if `v ∈ K`, an arbitrary element of `K` otherwise.

## Main statements

* `coe_toSet_of_mem`: `toSet K v = v` for `v ∈ K`;
* `measurable_toSet`: `toSet K` is measurable if `K` is a measurable set.
-/

@[expose] public section

namespace Learning

variable {X : Type*} {K : Set X} [Nonempty K] {v : X}

open scoped Classical in
/-- The point `v` as an element of `K`, or an arbitrary element of `K` if `v ∉ K`. -/
noncomputable def toSet (K : Set X) [Nonempty K] (v : X) : K :=
  if h : v ∈ K then ⟨v, h⟩ else Classical.arbitrary K

open scoped Classical in
lemma coe_toSet (K : Set X) [Nonempty K] (v : X) :
    (toSet K v : X) = K.piecewise id (fun _ ↦ (Classical.arbitrary K : X)) v := by
  unfold toSet
  split_ifs with h <;> simp [h]

lemma toSet_of_mem (hv : v ∈ K) : toSet K v = ⟨v, hv⟩ := by simp [toSet, hv]

@[simp]
lemma coe_toSet_of_mem (hv : v ∈ K) : (toSet K v : X) = v := by rw [toSet_of_mem hv]

@[simp]
lemma toSet_coe (x : K) : toSet K x = x := toSet_of_mem x.2

lemma measurable_toSet [MeasurableSpace X] (hK : MeasurableSet K) : Measurable (toSet K) := by
  classical
  rw [← (MeasurableEmbedding.subtype_coe hK).measurable_comp_iff]
  have : Subtype.val ∘ toSet K = K.piecewise id fun _ ↦ (Classical.arbitrary K : X) :=
    funext (coe_toSet K)
  rw [this]
  exact Measurable.piecewise hK measurable_id measurable_const

end Learning
