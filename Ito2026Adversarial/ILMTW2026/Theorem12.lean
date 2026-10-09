/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.MaximinLinUCBAnalysis

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
  refine ⟨256, by norm_num, ?_⟩
  intro mx my dx dy _ _ φ ψ A hA T hT opp R _ hR hR' Ω _mΩ P _ X Y Rw h
  have hX := h.measurable_action
  have hY (n : ℕ) : Measurable (Y n) := (h.measurable_feedback n).fst
  have hRw (n : ℕ) : Measurable (Rw n) := (h.measurable_feedback n).snd
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 1 / 2 ≤ log (T : ℝ) := by
    have h2 : 1 - (2 : ℝ)⁻¹ ≤ log 2 := one_sub_inv_le_log_of_pos (by norm_num)
    have := log_le_log (by norm_num) hT0
    linarith
  set u := bilinearGame φ ψ A with hu_def
  -- dimension `0`: the game is zero
  rcases Nat.eq_zero_or_pos (dx * dy) with hd0 | hd
  · have : IsEmpty (Fin dx × Fin dy) := by
      rcases Nat.mul_eq_zero.1 hd0 with h0 | h0 <;> subst h0 <;> infer_instance
    have hu : u = fun _ _ ↦ 0 := funext₂ fun x y ↦ bilinearGame_eq_zero x y
    have hpsmr : psmr u X Y P T = 0 := by simp [psmr, hu, pureMaximin]
    have hd0' : (dx : ℝ) * dy = 0 := by exact_mod_cast hd0
    refine ⟨by rw [hpsmr, hd0']; simp, fun Δ _ _ ↦ ?_⟩
    rw [hpsmr, ← mul_pow, hd0']
    simp
  -- dimension `d = d_x d_y ≥ 1`
  set L := log (T : ℝ) with hL
  have hL0 : 0 ≤ L := by linarith
  have hd1 : (1 : ℝ) ≤ (dx * dy : ℕ) := by exact_mod_cast hd
  set d : ℝ := ((dx * dy : ℕ) : ℝ) with hd_def
  have hd' : (dx : ℝ) * dy = d := by rw [hd_def]; push_cast; ring
  set B := linRadius (dx * dy) 1 (1 / T) T with hB_def
  have hB2 : B ^ 2 ≤ 12 * d * L := linRadius_sq_le hd hT
  have hB1 : 1 ≤ B := one_le_linRadius hd _ _
  have hδ : (1 / (T : ℝ)) ∈ Set.Ioo 0 1 :=
    ⟨by positivity, by rw [div_lt_one hTpos]; linarith⟩
  set G := linGoodEvent φ ψ A 1 (1 / T) X Y Rw with hG
  have hGm : MeasurableSet G := measurableSet_linGoodEvent 1 _ hX hY hRw
  have hGc : P.real Gᶜ ≤ 1 / T :=
    measureReal_compl_linGoodEvent_le hA opp R hR hR' _ P h one_pos hδ
  have hmax : ∀ᵐ ω ∂P, ∀ n < T, ∀ x, (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ x) (ψ y)).min
        ≤ (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ (X n ω)) (ψ y)).min := by
    have := ae_all_iff.2 fun n ↦ h.idx_le_idx_action_statefulIndex n
    filter_upwards [this] with ω hω n _ x using hω n x
  -- the contribution of the failure event
  have hfail {B' c : ℝ} (hB' : 0 ≤ B') (hc0 : 0 ≤ c) (hc : ∀ ω,
      ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ c * T)
      (hgood : ∀ ω ∈ G, (∀ n < T, ∀ x, (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ x) (ψ y)).min
        ≤ (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ (X n ω)) (ψ y)).min) →
        ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ B') :
      psmr u X Y P T ≤ B' + c := by
    have := psmr_le_add_mul_measureReal_compl u hX hY hGm (B := B') (c := c * T)
      (P := P) (T := T) ?_
    · calc psmr u X Y P T ≤ B' + c * T * P.real Gᶜ := this
        _ ≤ B' + c * T * (1 / T) := by gcongr
        _ = B' + c := by field_simp
    filter_upwards [hmax] with ω hω
    by_cases hωG : ω ∈ G
    · simpa [hωG] using hgood ω hωG hω
    · simp only [Set.indicator_of_mem (Set.mem_compl hωG)]
      linarith [hc ω]
  have hgap2 (x : Fin mx) (y : Fin my) : pairGap u x y ≤ 2 :=
    pairGap_le_two hA.bilinearGame_mem_Icc x y
  have hE : (0 : ℝ) ≤ 4 * d * L := by positivity
  constructor
  · -- worst-case bound
    have hpath (ω : Ω) : ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ 2 * T :=
      (sum_le_sum fun t _ ↦ hgap2 (X t ω) (Y t ω)).trans (by simp [mul_comm])
    have h := hfail (B' := 2 * B * (√T * √(4 * d * L))) (by positivity) zero_le_two hpath
      fun ω hωG hω ↦ sum_pureMaximin_sub_le_of_mem_linGoodEvent hA hT hd hωG hω
    have hsT : 1 ≤ √(T : ℝ) := by rw [one_le_sqrt]; linarith
    have hmain : 2 * B * (√T * √(4 * d * L)) ≤ 14 * (d * √T * L) := by
      rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
      have h1 : (2 * B * (√T * √(4 * d * L))) ^ 2 = 4 * B ^ 2 * T * (4 * d * L) := by
        rw [mul_pow, mul_pow, mul_pow, sq_sqrt hTpos.le, sq_sqrt hE]
        ring
      have h2 : (14 * (d * √T * L)) ^ 2 = 196 * d ^ 2 * T * L ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, sq_sqrt hTpos.le]
        ring
      rw [h1, h2]
      have : 4 * B ^ 2 * T * (4 * d * L) ≤ 4 * (12 * d * L) * T * (4 * d * L) := by gcongr
      nlinarith
    have h2le : (2 : ℝ) ≤ 4 * (d * √T * L) := by
      have : 1 ≤ d * √T := by nlinarith
      nlinarith
    rw [hd']
    linarith
  · -- instance-dependent bound
    intro Δ hΔ hgap
    have hpath (ω : Ω) : ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ 4 / Δ * T := by
      calc ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))
          ≤ ∑ t ∈ range T, (2 : ℝ) ^ 2 / Δ :=
            sum_le_sum fun t _ ↦ le_sq_div_of_le hΔ (hgap _ _) (hgap2 _ _)
        _ = 4 / Δ * T := by simp [mul_comm]; norm_num
    have h := hfail (B' := 4 * B ^ 2 * (4 * d * L) / Δ) (by positivity) (by positivity) hpath
      fun ω hωG hω ↦ sum_pureMaximin_sub_le_div_of_mem_linGoodEvent hA hT hd hωG hω hΔ hgap
    rw [← mul_pow, hd']
    have h1 : 4 * B ^ 2 * (4 * d * L) ≤ 192 * d ^ 2 * L ^ 2 := by
      have : 4 * B ^ 2 * (4 * d * L) ≤ 4 * (12 * d * L) * (4 * d * L) := by gcongr
      nlinarith
    have h2 : (4 : ℝ) ≤ 16 * d ^ 2 * L ^ 2 := by
      have hdL : 1 / 2 ≤ d * L := by nlinarith
      nlinarith [mul_le_mul hdL hdL (by norm_num) (by positivity)]
    calc psmr u X Y P T ≤ 4 * B ^ 2 * (4 * d * L) / Δ + 4 / Δ := h
      _ = (4 * B ^ 2 * (4 * d * L) + 4) / Δ := by ring
      _ ≤ (192 * d ^ 2 * L ^ 2 + 16 * d ^ 2 * L ^ 2) / Δ := by gcongr
      _ ≤ 256 * (d ^ 2 * L ^ 2 / Δ) := by
        rw [mul_div_assoc']
        gcongr
        nlinarith [sq_nonneg (d * L)]

end Ito2026Adversarial
