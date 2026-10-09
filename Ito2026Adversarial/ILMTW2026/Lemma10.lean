/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.LeanMachineLearning.Game.Maximin

/-!
# Lemma 10: the mixed gap of a `2 × 2` game

For a `2 × 2` zero-sum game with entries in `[-1, 1]` whose unique Nash equilibrium is mixed,
`Δ^mix ≥ Δ_M² / 4` where `Δ_M` is the minimum entry gap.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- If `Δ ≤ x`, `Δ ≤ y` and `0 < D ≤ 4`, then `Δ² / 4 ≤ x y / D`. -/
private lemma sq_div_four_le_mul_div {Δ x y D : ℝ} (hΔ : 0 ≤ Δ) (hx : Δ ≤ x) (hy : Δ ≤ y)
    (hD : 0 < D) (hD4 : D ≤ 4) : Δ ^ 2 / 4 ≤ x * y / D := by
  rw [le_div_iff₀ hD]
  nlinarith [mul_le_mul hx hy hΔ (hΔ.trans hx), sq_nonneg Δ]

/-- **Lemma 10** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). Let `u` be a `2 × 2` zero-sum game with
entries in `[-1, 1]` and without pure-strategy Nash equilibrium. Then `Δ^mix ≥ Δ_M² / 4`, where
`Δ_M = min {|a - b|, |a - c|, |b - d|, |c - d|}` is the minimum entry gap.

The paper assumes a unique mixed-strategy Nash equilibrium, and its proof uses that there is no
PSNE (the lemma is false for a unique pure equilibrium, where `Δ^mix = 0 < Δ_M² / 4` in general).
A `2 × 2` game without PSNE has a unique mixed equilibrium, so uniqueness is not assumed. -/
theorem sq_entryGap_div_four_le_mixGap (u : Fin 2 → Fin 2 → ℝ)
    (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hpure : ¬ HasPSNE u) :
    entryGap u ^ 2 / 4 ≤ mixGap u := by
  obtain ⟨h00, h00'⟩ := hu 0 0
  obtain ⟨h01, h01'⟩ := hu 0 1
  obtain ⟨h10, h10'⟩ := hu 1 0
  obtain ⟨h11, h11'⟩ := hu 1 1
  have hΔ0 : 0 ≤ entryGap u :=
    le_min (le_min (abs_nonneg _) (abs_nonneg _)) (le_min (abs_nonneg _) (abs_nonneg _))
  have hΔ1 : entryGap u ≤ |u 0 0 - u 0 1| := (min_le_left _ _).trans (min_le_left _ _)
  have hΔ2 : entryGap u ≤ |u 0 0 - u 1 0| := (min_le_left _ _).trans (min_le_right _ _)
  have hΔ3 : entryGap u ≤ |u 0 1 - u 1 1| := (min_le_right _ _).trans (min_le_left _ _)
  have hΔ4 : entryGap u ≤ |u 1 0 - u 1 1| := (min_le_right _ _).trans (min_le_right _ _)
  -- `v^Nash = (a d - b c) / (a - b - c + d)` and `v* = max (min a b) (min c d)`
  rw [mixGap, nashValue_eq_of_not_hasPSNE hpure, pureMaximin_fin_two, le_sub_comm, max_le_iff]
  rcases lt_and_lt_or_lt_and_lt_of_not_hasPSNE hpure with h | h
  · -- the diagonal entries are the largest: `v^Nash - b = (a - b) (d - b) / (a - b - c + d)` and
    -- `v^Nash - c = (a - c) (d - c) / (a - b - c + d)`
    obtain ⟨hba, hca, hbd, hcd⟩ := h
    rw [abs_of_pos (by linarith)] at hΔ1 hΔ2
    rw [abs_of_neg (by linarith)] at hΔ3 hΔ4
    have hD : 0 < u 0 0 - u 0 1 - u 1 0 + u 1 1 := by linarith
    refine ⟨(min_le_right _ _).trans ?_, (min_le_left _ _).trans ?_⟩
    · have := sq_div_four_le_mul_div hΔ0 hΔ1 (hΔ3.trans_eq (neg_sub _ _)) hD (by linarith)
      rw [le_sub_comm]
      convert this using 1
      field_simp
      ring
    · have := sq_div_four_le_mul_div hΔ0 hΔ2 (hΔ4.trans_eq (neg_sub _ _)) hD (by linarith)
      rw [le_sub_comm]
      convert this using 1
      field_simp
      ring
  · -- the off-diagonal entries are the largest: `v^Nash - a = (b - a) (c - a) / (b + c - a - d)`
    -- and `v^Nash - d = (b - d) (c - d) / (b + c - a - d)`
    obtain ⟨hab, hac, hdb, hdc⟩ := h
    rw [abs_of_neg (by linarith)] at hΔ1 hΔ2
    rw [abs_of_pos (by linarith)] at hΔ3 hΔ4
    have hD : 0 < u 0 1 + u 1 0 - u 0 0 - u 1 1 := by linarith
    have hD' : u 0 0 - u 0 1 - u 1 0 + u 1 1 ≠ 0 := by linarith
    refine ⟨(min_le_left _ _).trans ?_, (min_le_right _ _).trans ?_⟩
    · have := sq_div_four_le_mul_div hΔ0 (hΔ1.trans_eq (neg_sub _ _))
        (hΔ2.trans_eq (neg_sub _ _)) hD (by linarith)
      rw [le_sub_comm]
      convert this using 1
      field_simp
      ring
    · have := sq_div_four_le_mul_div hΔ0 hΔ3 hΔ4 hD (by linarith)
      rw [le_sub_comm]
      convert this using 1
      field_simp
      ring

end Ito2026Adversarial
