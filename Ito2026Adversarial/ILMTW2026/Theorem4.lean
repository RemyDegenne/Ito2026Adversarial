/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Theorem 4: PSMR of Maximin-UCB in normal-form games

The informed Maximin-UCB algorithm with `δ = 1 / T` has pure-strategy maximin regret
`O(∑_{x, y : Δ_{xy} > 0} (Δ_{xy} + log T / Δ_{xy}))` and `O(√(m_x m_y T log T))` against any
adaptive adversary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- **Theorem 4** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). There is a universal constant `C` such
that for every game `u` with utilities in `[-1, 1]`, every adaptive adversary, every reward noise
with conditional mean `u` and rewards in `[-1, 1]` and every `T ≥ 2`, the run of Maximin-UCB
with `δ = 1 / T` satisfies both
`PSMR_T ≤ C (∑_{x, y : Δ_{xy} > 0} (Δ_{xy} + log T / Δ_{xy}) + m_x m_y)` and
`PSMR_T ≤ C √(m_x m_y T log T)`.

The paper states the first bound without the term `m_x m_y`, which its proof gets from the event
(of probability at most `m_x m_y / T`) where a confidence bound fails, and claims that this term is
absorbed by the big-O; this is not the case when few action pairs have a positive gap. -/
theorem exists_psmr_maximinUCB_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {mx my : ℕ} [NeZero mx] [NeZero my] (u : Fin mx → Fin my → ℝ),
      (∀ x y, u x y ∈ Set.Icc (-1) 1) →
      ∀ (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
        [∀ n, IsMarkovKernel (R n)],
      RewardKernel.HasMean R u → RewardKernel.RewardsIn R (Set.Icc (-1) 1) →
      ∀ (T : ℕ), 2 ≤ T →
      ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ),
      IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) (maximinUCB (1 / T))
        (gameEnv opp R) P →
        psmr u X Y P T ≤ C * (∑ x, ∑ y,
          (if 0 < pairGap u x y then pairGap u x y + log T / pairGap u x y else 0) + mx * my) ∧
        psmr u X Y P T ≤ C * √(mx * my * T * log T) := by
  sorry

end Ito2026Adversarial
