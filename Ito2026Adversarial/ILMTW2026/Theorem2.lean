/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Theorem 2: lower bound for uninformed learners

For small enough gaps `Δʳ_min, Δᶜ_min`, large enough `T` and any uninformed learner, there is a
`2 × 2` game with a strict PSNE and an adversary under which the learner's PSMR is
`Ω(min {1 / (Δʳ_min Δᶜ_min), √T})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- **Theorem 2** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). There are `c > 0`, `Δ₀ > 0` and `T₀`
such that for all gaps `Δʳ, Δᶜ ∈ (0, Δ₀)`, all `T ≥ T₀` and every uninformed learner, there is a
`2 × 2` game `u` with utilities in `[-1, 1]` and a strict PSNE `(x*, y*)` with
`Δʳ_min = Δʳ`, `Δᶜ_min = Δᶜ`, an adversary and a reward noise (with conditional mean `u` and
rewards in `[-1, 1]`) under which the learner's PSMR after `T` rounds is at least
`c min {1 / (Δʳ Δᶜ), √T}`. -/
theorem exists_forall_psmr_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∃ T₀ : ℕ,
      ∀ {Δr Δc : ℝ}, Δr ∈ Set.Ioo 0 Δ₀ → Δc ∈ Set.Ioo 0 Δ₀ → ∀ T : ℕ, T₀ ≤ T →
      ∀ alg : Algorithm Unit (Fin 2) ℝ,
      ∃ (u : Fin 2 → Fin 2 → ℝ) (x₀ y₀ : Fin 2), (∀ x y, u x y ∈ Set.Icc (-1) 1) ∧
        IsStrictPSNE u x₀ y₀ ∧ rowGapMin u x₀ y₀ = Δr ∧ colGapMin u x₀ y₀ = Δc ∧
        ∃ (opp : Player (Fin 2) (Fin 2)) (R : RewardKernel (Fin 2) (Fin 2))
          (_ : ∀ n, IsMarkovKernel (R n)),
          RewardKernel.HasMean R u ∧ RewardKernel.RewardsIn R (Set.Icc (-1) 1) ∧
          ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
            (X : ℕ → Ω → Fin 2) (Y : ℕ → Ω → Fin 2) (Rw : ℕ → Ω → ℝ),
            IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
              (Player.ofUninformed alg) (gameEnv opp R) P →
            c * min (1 / (Δr * Δc)) √T ≤ psmr u X Y P T := by
  sorry

end Ito2026Adversarial
