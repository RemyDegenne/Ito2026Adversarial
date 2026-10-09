/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.MaximinUCBAnalysis

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
  refine ⟨24, by norm_num, ?_⟩
  intro mx my _ _ u hu opp R _ hR hR' T hT Ω _mΩ P _ X Y Rw h
  have hX := h.measurable_action
  have hY (n : ℕ) : Measurable (Y n) := (h.measurable_feedback n).fst
  have hRw (n : ℕ) : Measurable (Rw n) := (h.measurable_feedback n).snd
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 1 / 2 ≤ log T := by
    have h2 : 1 - (2 : ℝ)⁻¹ ≤ log 2 := one_sub_inv_le_log_of_pos (by norm_num)
    have := log_le_log (by norm_num) hT0
    linarith
  have hδ : (1 / (T : ℝ)) ∈ Set.Ioo 0 1 :=
    ⟨by positivity, by rw [div_lt_one hTpos]; linarith⟩
  set G := ucbGoodEvent u (1 / T) X Y Rw with hG
  have hGm : MeasurableSet G := measurableSet_ucbGoodEvent u _ hX hY hRw
  have hGc : P.real Gᶜ ≤ mx * my * (1 / T) :=
    measureReal_compl_ucbGoodEvent_le hu opp R hR hR' _ P h hδ
  have hmax : ∀ᵐ ω ∂P, ∀ n < T, ∀ x,
      (fun y ↦ ucbIndex (1 / T) (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x y).min
        ≤ (fun y ↦ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) (X n ω) y).min := by
    have := ae_all_iff.2 fun n ↦ h.idx_le_idx_action_index n
    filter_upwards [this] with ω hω n _ x using hω n x
  have hpath (ω : Ω) : ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ 2 * T :=
    (sum_le_sum fun t _ ↦ pairGap_le_two hu (X t ω) (Y t ω)).trans (by simp [mul_comm])
  -- the contribution of the failure event
  have hfail {B : ℝ} (hB : 0 ≤ B) (hgood : ∀ ω ∈ G, (∀ n < T, ∀ x,
      (fun y ↦ ucbIndex (1 / T) (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x y).min
        ≤ (fun y ↦ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) (X n ω) y).min) →
      ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ B) :
      psmr u X Y P T ≤ B + 2 * mx * my := by
    have := psmr_le_add_mul_measureReal_compl u hX hY hGm (B := B) (c := 2 * T)
      (P := P) (T := T) ?_
    · calc psmr u X Y P T ≤ B + 2 * T * P.real Gᶜ := this
        _ ≤ B + 2 * T * (mx * my * (1 / T)) := by gcongr
        _ = B + 2 * mx * my := by field_simp
    filter_upwards [hmax] with ω hω
    by_cases hωG : ω ∈ G
    · simpa [hωG] using hgood ω hωG hω
    · simp only [Set.indicator_of_mem (Set.mem_compl hωG)]
      linarith [hpath ω]
  constructor
  · -- instance-dependent bound
    have hterm (x : Fin mx) (y : Fin my) :
        0 ≤ (if 0 < pairGap u x y then pairGap u x y + 24 * log T / pairGap u x y else 0) := by
      split_ifs with h0
      · have : 0 ≤ log (T : ℝ) := by linarith
        positivity
      · exact le_rfl
    refine (hfail (sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦ hterm x y)
      fun ω hωG hω ↦ sum_pureMaximin_sub_le_of_mem_ucbGoodEvent hu hT hωG hω).trans ?_
    have hle (x : Fin mx) (y : Fin my) :
        (if 0 < pairGap u x y then pairGap u x y + 24 * log T / pairGap u x y else 0)
          ≤ 24 * (if 0 < pairGap u x y then pairGap u x y + log T / pairGap u x y else 0) := by
      split_ifs with h0
      · have : 0 ≤ log (T : ℝ) := by linarith
        rw [mul_add, mul_div_assoc']
        linarith
      · simp
    have hsum := sum_le_sum fun x (_ : x ∈ univ) ↦ sum_le_sum fun y (_ : y ∈ univ) ↦ hle x y
    simp only [← mul_sum] at hsum
    have : (0 : ℝ) ≤ mx * my := by positivity
    linarith
  · -- worst-case bound
    set a : ℝ := mx * my with ha
    set L := log (T : ℝ) with hL
    have ha1 : 1 ≤ a := by
      have : (1 : ℝ) ≤ mx := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne mx)
      have : (1 : ℝ) ≤ my := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne my)
      rw [ha]
      nlinarith
    set s := √(a * T * L) with hs
    have hs2 : s ^ 2 = a * T * L := sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := sqrt_nonneg _
    have hL0 : 0 ≤ L := by linarith
    have haTL : a * T * (1 / 2) ≤ a * T * L := mul_le_mul_of_nonneg_left hlogT (by positivity)
    have hgood := hfail (B := 2 * mx * my + √(24 * L) * (√(mx * my) * √T)) (by positivity)
      fun ω hωG hω ↦ sum_pureMaximin_sub_le_sqrt_of_mem_ucbGoodEvent hu hT hωG hω
    have heq : √(24 * L) * (√(mx * my) * √T) = √24 * s := by
      rw [← sqrt_mul (by linarith : (0 : ℝ) ≤ a), ← sqrt_mul (by linarith : (0 : ℝ) ≤ 24 * L),
        hs, ← sqrt_mul (by norm_num : (0 : ℝ) ≤ 24)]
      congr 1
      ring
    have h24 : √24 ≤ 5 := by
      rw [sqrt_le_left (by norm_num)]
      norm_num
    rw [heq] at hgood
    have hglobal : psmr u X Y P T ≤ 2 * T :=
      psmr_le_mul_of_pairGap_le u hX hY (pairGap_le_two hu) T
    change psmr u X Y P T ≤ 24 * s
    rcases le_total a T with haT | haT
    · have h4a : 2 * a / 3 ≤ s := by
        rw [hs, le_sqrt (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left haT (by linarith : (0 : ℝ) ≤ a)]
      have : 2 * (mx : ℝ) * my = 2 * a := by rw [ha]; ring
      have : √24 * s ≤ 5 * s := mul_le_mul_of_nonneg_right h24 hs0
      linarith
    · have h2T : 2 * (T : ℝ) / 3 ≤ s := by
        rw [hs, le_sqrt (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right haT (by linarith : (0 : ℝ) ≤ T)]
      linarith

end Ito2026Adversarial
