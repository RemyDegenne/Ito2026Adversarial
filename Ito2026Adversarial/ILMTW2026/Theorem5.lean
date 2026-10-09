/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.ILMTW2026.TsallisSPMPaper
public import Ito2026Adversarial.ILMTW2026.MaximinLinUCBAnalysis

/-!
# Theorem 5: PSMR of Tsallis-FTRL-SPM in bilinear games

In a bilinear game with `m_x`, `m_y` actions with features in `ℝ^{d_x}`, `ℝ^{d_y}`, the uninformed
algorithm
Tsallis-FTRL-SPM with `α = 1 - 1 / (4 log m_x)`, `β₁ = 8 c d_x / (1 - α)`,
`β̄ = 32 d_x / ((1 - α)² β₁)` and an exploration distribution of variance ratio `c` has PSMR
`O(√(T d_x log m_x) + m_x log² m_x)`; `O(d_x log m_x log T / (Δʳ_min Δᶜ_min) + m_x log² m_x)` if
the game has a strict PSNE; `O(d_x log m_x / Δ^mix + m_x log² m_x)` if it has no PSNE.

The paper states the additive term as `m_x log m_x`. With these parameters the penalty term
`β̄ h₀` of Ito, Tsuchiya and Honda (2024, Eq. (24)) is of order `m_x log² m_x / c`, and this
order is attained: for `d_x = 1`, `φ = ±1` (one good action), `A = 1` and a single column, the
PSMR at `T = m_x²` is of order `m_x log² m_x`, while `√(T log m_x) + m_x log m_x = O(m_x log m_x)`.
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
`PSMR_T ≤ C (√(T d_x log m_x) + m_x log² m_x)`; moreover
`PSMR_T ≤ C (d_x log m_x (1 + log T) (1 + 1 / Δᶜ_min) / Δʳ_min + m_x log² m_x)` if `(x*, y*)` is a
strict PSNE and `PSMR_T ≤ C (d_x log m_x / Δ^mix + m_x log² m_x)` if `Δ^mix > 0`.

As for Theorem 1, the second bound is the form given by the proof (the paper's
`O(d_x log m_x log T / (Δʳ_min Δᶜ_min) + m_x log² m_x)` follows for `m_y ≥ 2` and `T ≥ 2`, and is
false in Lean for `m_y = 1`), and the third is stated for `Δ^mix > 0`, which the paper deduces
from the absence of PSNE (not true in general) and which is all its proof uses. The variance ratio
`HasVarianceRatio` includes the invertibility of `S(p₀)`. The additive term is `m_x log² m_x`, not
the paper's `m_x log m_x` (see the module docstring). -/
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
          C * (√(T * dx * log mx) + mx * log mx ^ 2) ∧
        (∀ x₀ y₀, IsStrictPSNE (bilinearGame φ ψ A) x₀ y₀ →
          psmr (bilinearGame φ ψ A) X Y P T ≤
            C * (dx * log mx * (1 + log T) * (1 + 1 / colGapMin (bilinearGame φ ψ A) x₀ y₀)
              / rowGapMin (bilinearGame φ ψ A) x₀ y₀ + mx * log mx ^ 2)) ∧
        (0 < mixGap (bilinearGame φ ψ A) →
          psmr (bilinearGame φ ψ A) X Y P T ≤
            C * (dx * log mx / mixGap (bilinearGame φ ψ A) + mx * log mx ^ 2)) := by
  intro c hc
  refine ⟨8 * (16 + 8 * c) + (128 * c + 64 / c + (16 + 8 * c) / c) + (8 * (16 + 8 * c)) ^ 2 / 4
    + (32 * (16 + 8 * c)) ^ 2 + 2 * (128 * c + 64 / c + (16 + 8 * c) * (48 + 1 / c)),
    by positivity, ?_⟩
  intro mx my dx dy _ _ φ ψ A hA hm p₀ hV opp R _ hRu hR Ω _ P _ X Y Rw h T
  have hu1 := hA.bilinearGame_mem_Icc
  have hL := half_le_log hm
  have hlogT := Real.log_natCast_nonneg T
  have hm0 : (0 : ℝ) ≤ mx := Nat.cast_nonneg _
  have hc4 : 0 < 128 * c + 64 / c + (16 + 8 * c) / c := by positivity
  have hcK : 0 < 128 * c + 64 / c + (16 + 8 * c) * (48 + 1 / c) := by positivity
  rcases Nat.eq_zero_or_pos dx with rfl | hd
  · -- in dimension `0` the game is zero and the regret vanishes
    have hu0 (x : Fin mx) (y : Fin my) : bilinearGame φ ψ A x y = 0 := bilinearGame_eq_zero x y
    have hpm : pureMaximin (bilinearGame φ ψ A) = 0 := by
      simp [pureMaximin, hu0]
    have hpsmr : psmr (bilinearGame φ ψ A) X Y P T = 0 := by
      simp [psmr, hpm, hu0]
    refine ⟨?_, fun x₀ y₀ hxy ↦ ?_, fun hΔ ↦ ?_⟩
    · rw [hpsmr]
      positivity
    · exfalso
      obtain ⟨x', hx'⟩ : ∃ x' : Fin mx, x' ≠ x₀ :=
        ⟨⟨if x₀.val = 0 then 1 else 0, by split_ifs <;> omega⟩, by
          intro hx
          rw [Fin.ext_iff] at hx
          simp only at hx
          split_ifs at hx with h0 <;> omega⟩
      have := hxy.1 x' hx'
      rw [hu0, hu0] at this
      exact lt_irrefl _ this
    · exfalso
      have hnash : nashValue (bilinearGame φ ψ A) = 0 := by
        simp [nashValue, mixedUtility, hu0]
      rw [mixGap, hnash, hpm, sub_zero] at hΔ
      exact lt_irrefl _ hΔ
  have hdm : dx ≤ mx := by
    have h1 := finrank_range_le_card (R := ℝ) φ
    rw [Set.finrank, hA.span_x, finrank_top, finrank_euclideanSpace_fin, Fintype.card_fin] at h1
    exact h1
  have hu : ∀ x y, bilinearGame φ ψ A x y = WithLp.ofLp (φ x) ⬝ᵥ (A *ᵥ WithLp.ofLp (ψ y)) :=
    fun x y ↦ rfl
  have hsub := psmr_tsallisSPMPaper_le_sub hc hd hm hV hu hu1 hRu hR h hdm T
  have hΔ0 := mixGap_nonneg (bilinearGame φ ψ A)
  have hsq : 0 ≤ √(T * dx * log mx) := Real.sqrt_nonneg _
  have hmL : 0 ≤ mx * log mx ^ 2 := by positivity
  refine ⟨?_, fun x₀ y₀ hxy ↦ ?_, fun hΔ ↦ ?_⟩
  · have : 0 ≤ mixGap (bilinearGame φ ψ A) * T := mul_nonneg hΔ0 (Nat.cast_nonneg T)
    have h8 : 0 ≤ 8 * (16 + 8 * c) := by positivity
    nlinarith
  · have key := psmr_tsallisSPMPaper_le_of_isStrictPSNE hc hd hm hV hu hu1 hRu hR h hdm hxy T
    have hΔc0 : 0 ≤ colGapMin (bilinearGame φ ψ A) x₀ y₀ :=
      Real.iInf_nonneg fun y ↦ (hxy.colGap_pos y.2).le
    have hΔr0 : 0 ≤ rowGapMin (bilinearGame φ ψ A) x₀ y₀ :=
      Real.iInf_nonneg fun x ↦ (hxy.rowGap_pos x.2).le
    have hQ : 0 ≤ dx * log mx * (1 + log T) * (1 + 1 / colGapMin (bilinearGame φ ψ A) x₀ y₀)
        / rowGapMin (bilinearGame φ ψ A) x₀ y₀ := by positivity
    have h8 : 0 ≤ 8 * (16 + 8 * c) := by positivity
    nlinarith
  · -- Lemma 7: `A √(T d L) - Δ^mix T ≤ A² d L / (4 Δ^mix)`
    have hdL : 0 < (8 * (16 + 8 * c)) ^ 2 * (dx * log mx) := by
      have : (1 : ℝ) ≤ dx := by exact_mod_cast hd
      positivity
    have h7 := (sqrt_mul_sub_mul_le ((8 * (16 + 8 * c)) ^ 2 * (dx * log mx))
      (mixGap (bilinearGame φ ψ A)) hdL hΔ).1 T (Nat.cast_nonneg T)
    have hroot : √((8 * (16 + 8 * c)) ^ 2 * (dx * log mx) * T)
        = 8 * (16 + 8 * c) * √(T * dx * log mx) := by
      rw [show (8 * (16 + 8 * c)) ^ 2 * (dx * log mx) * T
          = (8 * (16 + 8 * c)) ^ 2 * (T * dx * log mx) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [hroot] at h7
    have e : (8 * (16 + 8 * c)) ^ 2 * (dx * log mx) / (4 * mixGap (bilinearGame φ ψ A))
        = (8 * (16 + 8 * c)) ^ 2 / 4 * (dx * log mx / mixGap (bilinearGame φ ψ A)) := by
      field_simp
    rw [e] at h7
    have hq : 0 ≤ dx * log mx / mixGap (bilinearGame φ ψ A) := by positivity
    nlinarith

end Ito2026Adversarial
