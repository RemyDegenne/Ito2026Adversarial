/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Theorem 6: PSMR of Maximin-LinUCB in bilinear games (informal version)

In a bilinear game, the informed algorithm Maximin-LinUCB (with suitable parameters) has
worst-case PSMR `O(d_x d_y √T log T)` and instance-dependent PSMR `O(d_x² d_y² log² T / Δ^lin)`
simultaneously. The formal version, with explicit parameters, is Theorem 12.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix

universe u

namespace Ito2026Adversarial

/-- **Theorem 6** (Ito, Luo, Maiti, Tsuchiya, Wu 2026; informal version of Theorem 12). There
is a universal constant `C` such that for every bilinear game and every horizon `T ≥ 2` there are
parameters `(λ, β)` of Maximin-LinUCB such that, against every adaptive adversary and every reward
noise with conditional mean `u` and rewards in `[-1, 1]`, `PSMR_T ≤ C d_x d_y √T log T` and
`PSMR_T ≤ C d_x² d_y² log² T / Δ^lin` for every gap threshold `Δ^lin > 0` of the game. -/
theorem exists_forall_exists_psmr_maximinLinUCB_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {mx my dx dy : ℕ} [NeZero mx] [NeZero my] (φ : Fin mx → EuclideanSpace ℝ (Fin dx))
        (ψ : Fin my → EuclideanSpace ℝ (Fin dy)) (A : Matrix (Fin dx) (Fin dy) ℝ),
        IsBilinearGame φ ψ A → ∀ (T : ℕ), 2 ≤ T →
      ∃ (lam : ℝ) (β : ℕ → ℝ),
      ∀ (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
        [∀ n, IsMarkovKernel (R n)],
      RewardKernel.HasMean R (bilinearGame φ ψ A) → RewardKernel.RewardsIn R (Set.Icc (-1) 1) →
      ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ),
      IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) (maximinLinUCB φ ψ lam β)
        (gameEnv opp R) P →
        psmr (bilinearGame φ ψ A) X Y P T ≤ C * (dx * dy * √T * log T) ∧
        ∀ Δ : ℝ, 0 < Δ → IsGapThreshold (bilinearGame φ ψ A) Δ →
          psmr (bilinearGame φ ψ A) X Y P T ≤ C * (dx ^ 2 * dy ^ 2 * log T ^ 2 / Δ) := by
  sorry

end Ito2026Adversarial
