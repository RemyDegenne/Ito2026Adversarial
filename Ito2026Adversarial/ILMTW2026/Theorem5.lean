/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Theorem 5: PSMR of Tsallis-FTRL-SPM in bilinear games

In a bilinear game with `m_x`, `m_y` actions with features in `ℝ^{d_x}`, `ℝ^{d_y}`, the uninformed
algorithm
Tsallis-FTRL-SPM with `α = 1 - 1 / (4 log m_x)`, `β₁ = 8 c d_x / (1 - α)`,
`β̄ = 32 d_x / ((1 - α)² β₁)` and an exploration distribution of variance ratio `c` has PSMR
`O(√(T d_x log m_x) + m_x log m_x)`; `O(d_x log m_x log T / (Δʳ_min Δᶜ_min) + m_x log m_x)` if the
game has a strict PSNE; `O(d_x log m_x / Δ^mix + m_x log m_x)` if it has no PSNE.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix

universe u

namespace Ito2026Adversarial

/-- **Theorem 5** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). For every variance ratio `c > 0` there is
a constant `C` such that for every bilinear game (`IsBilinearGame`) with `m_x ≥ 2` actions of the
learner, every exploration distribution `p₀` of variance ratio `c`, every adaptive adversary and
every reward noise with conditional mean `u` and rewards in `[-1, 1]`, the run of
Tsallis-FTRL-SPM with the parameters of the theorem satisfies
`PSMR_T ≤ C (√(T d_x log m_x) + m_x log m_x)`; moreover
`PSMR_T ≤ C (d_x log m_x (1 + log T) (1 + 1 / Δᶜ_min) / Δʳ_min + m_x log m_x)` if `(x*, y*)` is a
strict PSNE and `PSMR_T ≤ C (d_x log m_x / Δ^mix + m_x log m_x)` if `Δ^mix > 0`.

As for Theorem 1, the second bound is the form given by the proof (the paper's
`O(d_x log m_x log T / (Δʳ_min Δᶜ_min) + m_x log m_x)` follows for `m_y ≥ 2` and `T ≥ 2`, and is
false in Lean for `m_y = 1`), and the third is stated for `Δ^mix > 0`, which the paper deduces
from the absence of PSNE (not true in general) and which is all its proof uses. The variance ratio
`HasVarianceRatio` includes the invertibility of `S(p₀)`. -/
theorem forall_exists_psmr_tsallisSPMPaper_le :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ {mx my dx dy : ℕ} [NeZero mx] [NeZero my] (φ : Fin mx → EuclideanSpace ℝ (Fin dx))
        (ψ : Fin my → EuclideanSpace ℝ (Fin dy)) (A : Matrix (Fin dx) (Fin dy) ℝ),
        IsBilinearGame φ ψ A → 2 ≤ mx →
      ∀ (p₀ : simplex (Fin mx)), HasVarianceRatio φ p₀ c →
      ∀ (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
        [∀ n, IsMarkovKernel (R n)],
      RewardKernel.HasMean R (bilinearGame φ ψ A) → RewardKernel.RewardsIn R (Set.Icc (-1) 1) →
      ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ),
      IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
        (Player.ofUninformed (tsallisSPMPaper φ c p₀)) (gameEnv opp R) P →
      ∀ T : ℕ,
        psmr (bilinearGame φ ψ A) X Y P T ≤
          C * (√(T * dx * log mx) + mx * log mx) ∧
        (∀ x₀ y₀, IsStrictPSNE (bilinearGame φ ψ A) x₀ y₀ →
          psmr (bilinearGame φ ψ A) X Y P T ≤
            C * (dx * log mx * (1 + log T) * (1 + 1 / colGapMin (bilinearGame φ ψ A) x₀ y₀)
              / rowGapMin (bilinearGame φ ψ A) x₀ y₀ + mx * log mx)) ∧
        (0 < mixGap (bilinearGame φ ψ A) →
          psmr (bilinearGame φ ψ A) X Y P T ≤
            C * (dx * log mx / mixGap (bilinearGame φ ψ A) + mx * log mx)) := by
  sorry

end Ito2026Adversarial
