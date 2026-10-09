/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.ILMTW2026.TsallisINFRegret

/-!
# Theorem 1: PSMR of Tsallis-INF in normal-form games

Against any adaptive adversary, the uninformed Tsallis-INF algorithm with `α = 1/2` and
`η_t = 1 / (2 √t)` has pure-strategy maximin regret `O(√(m_x T))`;
`O(Δᶜ_min⁻¹ ∑_{x ≠ x*} log T / Δʳ_x)` if the game has a strict PSNE `(x*, y*)`; `O(m_x / Δ^mix)`
if it has no PSNE.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- **Theorem 1** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). There is a universal constant `C` such
that for every game `u` with utilities in `[-1, 1]`, every adaptive adversary and every reward
noise with conditional mean `u` and rewards in `[-1, 1]`, the run of Tsallis-INF (`α = 1/2`,
`η_t = 1 / (2 √t)`) satisfies `PSMR_T ≤ C √(m_x T)`; moreover
`PSMR_T ≤ C (1 + 1 / Δᶜ_min) ∑_{x ≠ x*} (1 + log T) / Δʳ_x` if `(x*, y*)` is a strict PSNE and
`PSMR_T ≤ C m_x / Δ^mix` if `Δ^mix > 0`.

The paper states the second bound as `O((1 / Δᶜ_min) ∑_{x ≠ x*} log T / Δʳ_x)`; the form above is
the one its proof gives, and implies the paper's for `m_y ≥ 2` and `T ≥ 2` (`Δᶜ_min ≤ 2`). For
`m_y = 1` the paper's form is false in Lean, where `Δᶜ_min` is an infimum over no action and
`C / 0 = 0`. The paper states the third bound for games without PSNE, claiming that they have
`Δ^mix > 0`; this fails in general (the rows `(0, 0)`, `(1, -1)`, `(-1, 1)` give a game without
PSNE with `v* = v^Nash = 0`), and the proof only uses `Δ^mix > 0`. -/
theorem exists_psmr_tsallisINFHalf_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {mx my : ℕ} [NeZero mx] [NeZero my] (u : Fin mx → Fin my → ℝ),
      (∀ x y, u x y ∈ Set.Icc (-1) 1) →
      ∀ (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
        [∀ n, IsMarkovKernel (R n)],
      RewardKernel.HasMean R u → RewardKernel.RewardsIn R (Set.Icc (-1) 1) →
      ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ),
      IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
        (Player.ofUninformed (tsallisINFHalf mx)) (gameEnv opp R) P →
      ∀ T : ℕ,
        psmr u X Y P T ≤ C * √(mx * T) ∧
        (∀ x₀ y₀, IsStrictPSNE u x₀ y₀ →
          psmr u X Y P T ≤
            C * (1 + 1 / colGapMin u x₀ y₀) *
              ∑ x ∈ univ.erase x₀, (1 + log T) / rowGap u x₀ y₀ x) ∧
        (0 < mixGap u → psmr u X Y P T ≤ C * mx / mixGap u) := by
  refine ⟨200, by norm_num, ?_⟩
  intro mx my _ _ u hu opp R _ hRu hR Ω _ P _ X Y Rw h T
  refine ⟨?_, fun x₀ y₀ hxy ↦ ?_, fun hΔ ↦ ?_⟩
  · exact (psmr_tsallisINFHalf_le_sqrt hu hRu hR h T).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))
  · refine (psmr_tsallisINFHalf_le_of_isStrictPSNE hu hRu hR h hxy T).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) ?_) ?_)
    · exact add_nonneg zero_le_one
        (one_div_nonneg.2 (Real.iInf_nonneg fun y ↦ (hxy.colGap_pos y.2).le))
    · exact sum_nonneg fun x hx ↦ div_nonneg
        (add_nonneg zero_le_one (Real.log_natCast_nonneg T))
        (hxy.rowGap_pos (ne_of_mem_erase hx)).le
  · refine (psmr_tsallisINFHalf_le_of_mixGap_pos hu hRu hR h hΔ T).trans ?_
    gcongr
    norm_num

end Ito2026Adversarial
