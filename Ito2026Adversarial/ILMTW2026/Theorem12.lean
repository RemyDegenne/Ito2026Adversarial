/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Theorem 12: PSMR of Maximin-LinUCB in bilinear games

With `λ = 1`, `δ = 1 / T` and
`β_t = √(λ d_x d_y) + √(2 log(1/δ) + d_x d_y log(1 + t / (d_x d_y λ)))`, Maximin-LinUCB has
worst-case PSMR `O(d_x d_y √T log T)` and instance-dependent PSMR `O(d_x² d_y² log² T / Δ^lin)`
simultaneously, against any adaptive adversary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix

universe u

namespace Ito2026Adversarial

/-- **Theorem 12** (Ito, Luo, Maiti, Tsuchiya, Wu 2026; formal version of Theorem 6). There is
a universal constant `C` such that for every bilinear game, every horizon `T ≥ 2`, every adaptive
adversary and every reward noise with conditional mean `u` and rewards in `[-1, 1]`, the run of
Maximin-LinUCB with `λ = 1` and radii `β_t = linRadius (d_x d_y) 1 (1 / T) t` satisfies
`PSMR_T ≤ C d_x d_y √T log T` and `PSMR_T ≤ C d_x² d_y² log² T / Δ^lin` for every gap threshold
`Δ^lin > 0` of the game. -/
theorem exists_psmr_maximinLinUCB_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {mx my dx dy : ℕ} [NeZero mx] [NeZero my] (φ : Fin mx → EuclideanSpace ℝ (Fin dx))
        (ψ : Fin my → EuclideanSpace ℝ (Fin dy)) (A : Matrix (Fin dx) (Fin dy) ℝ),
        IsBilinearGame φ ψ A → ∀ (T : ℕ), 2 ≤ T →
      ∀ (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
        [∀ n, IsMarkovKernel (R n)],
      RewardKernel.HasMean R (bilinearGame φ ψ A) → RewardKernel.RewardsIn R (Set.Icc (-1) 1) →
      ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ),
      IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
        (maximinLinUCB φ ψ 1 fun n ↦ linRadius (dx * dy) 1 (1 / T) (n + 1))
        (gameEnv opp R) P →
        psmr (bilinearGame φ ψ A) X Y P T ≤ C * (dx * dy * √T * log T) ∧
        ∀ Δ : ℝ, 0 < Δ → IsGapThreshold (bilinearGame φ ψ A) Δ →
          psmr (bilinearGame φ ψ A) X Y P T ≤ C * (dx ^ 2 * dy ^ 2 * log T ^ 2 / Δ) := by
  sorry

end Ito2026Adversarial
