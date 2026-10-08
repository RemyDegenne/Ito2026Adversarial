/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Compactness of the convex hull of a compact set

## Main statements

* `IsCompact.convexHull`: the convex hull of a compact subset of a finite-dimensional real
  topological vector space is compact (Carathéodory). Mathlib has the case of a finite set,
  `Set.Finite.isCompact_convexHull`.
-/

@[expose] public section

open Convexity

/-- The convex hull of a compact subset of a finite-dimensional real topological vector space is
compact. By Carathéodory's theorem, it is the image of the compact set `StdSimplex × sⁿ` (with
`n = finrank + 1`) by the continuous map `(w, z) ↦ ∑ᵢ wᵢ zᵢ`. -/
lemma IsCompact.convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E] {s : Set E}
    (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set n := Module.finrank ℝ E + 1 with hn
  let f : StdSimplex ℝ (Fin n) × (Fin n → E) → E := fun p ↦ ∑ i, p.1.weights i • p.2 i
  have hf : Continuous f :=
    continuous_finsetSum _ fun i _ ↦
      ((StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst).smul
        ((continuous_apply i).comp continuous_snd)
  have hK : IsCompact (Set.univ ×ˢ Set.pi Set.univ fun _ : Fin n ↦ s) :=
    (isCompact_univ (X := StdSimplex ℝ (Fin n))).prod (isCompact_univ_pi fun _ ↦ hs)
  suffices _root_.convexHull ℝ s = f '' (Set.univ ×ˢ Set.pi Set.univ fun _ : Fin n ↦ s) by
    rw [this]
    exact hK.image hf
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨κ, _, z, w, hz, hind, hw, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card κ ≤ Fintype.card (Fin n) :=
      (AffineIndependent.card_le_finrank_succ hind).trans
        (by rw [Fintype.card_fin, hn]; gcongr; exact Submodule.finrank_le _)
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let w' : Fin n → ℝ := Function.extend e w 0
    let z' : Fin n → E := Function.extend e z fun _ ↦ x₀
    have hw'e : ∀ i, w' (e i) = w i := fun i ↦ e.injective.extend_apply _ _ i
    have hz'e : ∀ i, z' (e i) = z i := fun i ↦ e.injective.extend_apply _ _ i
    have hw'0 : ∀ j ∉ Set.range e, w' j = 0 := fun j hj ↦ Function.extend_apply' _ _ _ hj
    have hz'0 : ∀ j ∉ Set.range e, z' j = x₀ := fun j hj ↦ Function.extend_apply' _ _ _ hj
    have hw'nonneg : ∀ j, 0 ≤ w' j := by
      intro j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [hw'e]
        exact (hw i).le
      · rw [hw'0 j hj]
    have hw'1 : ∑ j, w' j = 1 := by
      rw [← hw1]
      exact (Fintype.sum_of_injective e e.injective _ _ hw'0 fun i ↦ (hw'e i).symm).symm
    let ω : StdSimplex ℝ (Fin n) :=
      { weights := Finsupp.equivFunOnFinite.symm w'
        nonneg := fun j ↦ by simpa using hw'nonneg j
        total := by simpa [Finsupp.sum_fintype] using hw'1 }
    refine ⟨(ω, z'), ⟨Set.mem_univ _, fun j _ ↦ ?_⟩, ?_⟩
    · change z' j ∈ s
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [hz'e]
        exact hz (Set.mem_range_self i)
      · rw [hz'0 j hj]
        exact hx₀
    · change ∑ j, w' j • z' j = ∑ i, w i • z i
      exact (Fintype.sum_of_injective e e.injective _ _
        (fun j hj ↦ by rw [hw'0 j hj, zero_smul]) fun i ↦ by rw [hw'e, hz'e]).symm
  · rintro _ ⟨⟨w, z⟩, ⟨-, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ w.weights_nonneg i) w.total_of_fintype
      fun i _ ↦ subset_convexHull ℝ s (hz i (Set.mem_univ _))
