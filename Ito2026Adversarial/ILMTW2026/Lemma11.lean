/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Lemma 11: confidence bounds of Maximin-UCB

For a fixed action pair `(x, y)`, with probability at least `1 - δ`, the empirical mean of the
rewards of the rounds in which `(x, y)` was played is within
`√((4 log(1/δ) + 2 log(1 + N_t(x, y))) / N_t(x, y))` of `u x y`, simultaneously for all `t` with
`N_t(x, y) > 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- **Lemma 11** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). In a run of any informed player against
any adaptive adversary, with reward noise of conditional mean `u` and rewards in `[-1, 1]`, for
every action pair `(x, y)` and `δ ∈ (0, 1)`, with probability at least `1 - δ`, for all `t` with
`N_t(x, y) > 0`,
`|u x y - R_t(x, y) / N_t(x, y)| ≤ √((4 log(1/δ) + 2 log(1 + N_t(x, y))) / N_t(x, y))`, where
`N_t(x, y)` and `R_t(x, y)` are the number of rounds among the first `t` in which `(x, y)` was
played and the sum of their rewards. -/
theorem probReal_forall_abs_sub_div_le_ge {mx my : ℕ} [NeZero mx] [NeZero my]
    (u : Fin mx → Fin my → ℝ) (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1)
    (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
    [∀ n, IsMarkovKernel (R n)] (hR : RewardKernel.HasMean R u)
    (hR' : RewardKernel.RewardsIn R (Set.Icc (-1) 1)) (alg : Player (Fin mx) (Fin my))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (x : Fin mx) (y : Fin my) {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ P.real {ω | ∀ t, 0 < pairCount X Y Rw x y t ω →
      |u x y - pairSum X Y Rw x y t ω / pairCount X Y Rw x y t ω| ≤
        √((4 * log (1 / δ) + 2 * log (1 + pairCount X Y Rw x y t ω))
          / pairCount X Y Rw x y t ω)} := by
  sorry

end Ito2026Adversarial
