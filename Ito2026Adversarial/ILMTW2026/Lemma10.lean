/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

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

/-- **Lemma 10** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). Let `u` be a `2 × 2` zero-sum game with
entries in `[-1, 1]` and without pure-strategy Nash equilibrium. Then `Δ^mix ≥ Δ_M² / 4`, where
`Δ_M = min {|a - b|, |a - c|, |b - d|, |c - d|}` is the minimum entry gap.

The paper assumes a unique mixed-strategy Nash equilibrium, and its proof uses that there is no
PSNE (the lemma is false for a unique pure equilibrium, where `Δ^mix = 0 < Δ_M² / 4` in general).
A `2 × 2` game without PSNE has a unique mixed equilibrium, so uniqueness is not assumed. -/
theorem sq_entryGap_div_four_le_mixGap (u : Fin 2 → Fin 2 → ℝ)
    (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hpure : ¬ HasPSNE u) :
    entryGap u ^ 2 / 4 ≤ mixGap u := by
  sorry

end Ito2026Adversarial
