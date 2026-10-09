/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.LowerBound

/-!
# Theorem 2: lower bound for uninformed learners

For small enough gaps `Δʳ_min, Δᶜ_min`, large enough `T` and any uninformed learner, there is a
`2 × 2` game with a strict PSNE and an adversary under which the learner's PSMR is
`Ω(min {1 / (Δʳ_min Δᶜ_min), √T})`.

The construction (the games, the oblivious adversary, the divergence decomposition and the
Bretagnolle–Huber step) is in `Ito2026Adversarial.ILMTW2026.LowerBound`
(`exists_psmr_ge_of_le_one`); the proof here chooses its parameters as in the two cases of the
paper, with `c = 1 / 4056`, `Δ₀ = 1 / 13`, `T₀ = 169`: if `1 / (Δʳ Δᶜ) < 13 √T`, `K = 1`,
`ε = Δʳ (1 - 12 Δᶜ)` and `T' = ⌊(13 Δʳ Δᶜ)⁻²⌋` (rounded down, which halves the constant
`1 / 2028` of the paper); otherwise `T' = T`, `ε = min {1, 1 / (13 Δᶜ √T)}` and
`K = (Δʳ - 12 / (13 √T)) / ε`.
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
  refine ⟨1 / 4056, by norm_num, 1 / 13, by norm_num, 169, ?_⟩
  intro Δr Δc hΔr hΔc T hT alg
  obtain ⟨hΔr0, hΔr13⟩ := hΔr
  obtain ⟨hΔc0, hΔc13⟩ := hΔc
  have hΔr' : Δr ∈ Set.Ioc 0 1 := ⟨hΔr0, by linarith⟩
  have hΔc' : Δc ∈ Set.Ioc 0 1 := ⟨hΔc0, by linarith⟩
  have ha0 : 0 < Δr * Δc := mul_pos hΔr0 hΔc0
  have ha13 : Δr * Δc < 1 / 169 := by nlinarith
  have hsT : √(T : ℝ) ^ 2 = T := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs13 : 13 ≤ √(T : ℝ) := by
    rw [show (13 : ℝ) = √169 by
      rw [show (169 : ℝ) = 13 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hT)
  by_cases hcase : 1 / (Δr * Δc) < 13 * √(T : ℝ)
  · -- first case: `T' = ⌊(13 Δr Δc)⁻²⌋`, `K = 1`, `ε = Δr (1 - 12 Δc)`
    set x : ℝ := ((13 * (Δr * Δc)) ^ 2)⁻¹ with hx
    have hxa : x * (13 * (Δr * Δc)) ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    have hx0 : 0 ≤ x := by positivity
    have hx2 : 2 ≤ x := by nlinarith
    have hxT : x < T := by
      have h1 : 1 < 13 * (Δr * Δc) * √(T : ℝ) := by
        rw [div_lt_iff₀ ha0] at hcase; linarith
      nlinarith [sq_nonneg (13 * (Δr * Δc) * √(T : ℝ) - 1)]
    have hT'x : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have hxT' : x / 2 ≤ ⌊x⌋₊ := by linarith [Nat.lt_floor_add_one x]
    let ε : unitInterval := ⟨Δr * (1 - 12 * Δc), by nlinarith, by nlinarith⟩
    have hε : (ε : ℝ) = Δr * (1 - 12 * Δc) := rfl
    obtain ⟨u, x₀, y₀, h1, h2, h3, h4, opp, R, hR, h5, h6, hpsmr⟩ :=
      exists_psmr_ge_of_le_one.{u} (K := 1) (ε := ε) (T' := ⌊x⌋₊) (T := T) hΔr' hΔc'
        ⟨by linarith, by linarith⟩ (by rw [hε]; nlinarith)
        (by rw [hε, abs_le]; constructor <;> nlinarith)
        (by rw [hε, abs_le]; constructor <;> nlinarith)
        (by
          rw [hε]
          have hδ0 : 0 ≤ Δr * (1 - 12 * Δc) * Δc - 1 * (Δr * (1 - 12 * Δc)) + Δr := by nlinarith
          have hδ1 : Δr * (1 - 12 * Δc) * Δc - 1 * (Δr * (1 - 12 * Δc)) + Δr
              ≤ 13 * (Δr * Δc) := by nlinarith
          calc (⌊x⌋₊ : ℝ) * (Δr * (1 - 12 * Δc) * Δc - 1 * (Δr * (1 - 12 * Δc)) + Δr) ^ 2
              ≤ x * (13 * (Δr * Δc)) ^ 2 := by gcongr
            _ = 1 := hxa)
        (Nat.floor_le_of_le hxT.le) alg
    refine ⟨u, x₀, y₀, h1, h2, h3, h4, opp, R, hR, h5, h6, ?_⟩
    intro Ω mΩ P _ X Y Rw h
    refine le_trans ?_ (hpsmr P X Y Rw h)
    rw [hε]
    calc 1 / 4056 * min (1 / (Δr * Δc)) √(T : ℝ) ≤ 1 / 4056 * (1 / (Δr * Δc)) := by
          gcongr; exact min_le_left _ _
      _ = x / 2 * ((Δr * Δc) / 12) := by
          rw [hx]; field_simp; ring
      _ ≤ ⌊x⌋₊ * ((Δr - 1 * (Δr * (1 - 12 * Δc))) / 12
          - 11 / 12 * (Δr * (1 - 12 * Δc) * Δc)) := by
          gcongr
          nlinarith
  · -- second case: `T' = T`, `ε = min 1 (1 / (13 Δc √T))`, `K = (Δr - 12 / (13 √T)) / ε`
    push Not at hcase
    set s := √(T : ℝ) with hs
    have hs0 : 0 < s := by linarith
    rw [le_div_iff₀ ha0] at hcase
    set e := min 1 (1 / (13 * Δc * s)) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have heΔr : Δr ≤ e := by
      refine le_min (by linarith) ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have he12 : 12 / (13 * s) ≤ e := by
      refine le_min ?_ ?_
      · rw [div_le_one (by positivity)]
        linarith
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    have heΔc : e * Δc ≤ 1 / (13 * s) := by
      calc e * Δc ≤ 1 / (13 * Δc * s) * Δc := by gcongr; exact min_le_right _ _
        _ = 1 / (13 * s) := by field_simp
    have h12 : 0 < 12 / (13 * s) := by positivity
    have h12' : 12 / (13 * s) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    let ε : unitInterval := ⟨e, he0.le, he1⟩
    have hε : (ε : ℝ) = e := rfl
    set K := (Δr - 12 / (13 * s)) / e with hK
    have hKe : K * e = Δr - 12 / (13 * s) := div_mul_cancel₀ _ he0.ne'
    obtain ⟨u, x₀, y₀, h1, h2, h3, h4, opp, R, hR, h5, h6, hpsmr⟩ :=
      exists_psmr_ge_of_le_one.{u} (K := K) (ε := ε) (T' := T) (T := T) hΔr' hΔc'
        (by
          constructor
          · rw [le_sub_iff_add_le, neg_add_eq_sub, hK, le_div_iff₀ he0]
            nlinarith
          · rw [sub_le_iff_le_add, hK, div_le_iff₀ he0]
            nlinarith)
        (by rw [hε, hKe]; linarith)
        (by rw [hε, abs_le]; constructor <;> nlinarith)
        (by rw [hε, hKe, abs_le]; constructor <;> linarith)
        (by
          rw [hε, hKe, ← hsT]
          have hδ0 : 0 ≤ e * Δc - (Δr - 12 / (13 * s)) + Δr := by nlinarith
          have hδ1 : e * Δc - (Δr - 12 / (13 * s)) + Δr ≤ 1 / s := by
            have : 1 / (13 * s) + 12 / (13 * s) = 1 / s := by field_simp; norm_num
            linarith
          calc s ^ 2 * (e * Δc - (Δr - 12 / (13 * s)) + Δr) ^ 2 ≤ s ^ 2 * (1 / s) ^ 2 := by
                gcongr
            _ = 1 := by field_simp)
        le_rfl alg
    refine ⟨u, x₀, y₀, h1, h2, h3, h4, opp, R, hR, h5, h6, ?_⟩
    intro Ω mΩ P _ X Y Rw h
    refine le_trans ?_ (hpsmr P X Y Rw h)
    rw [hε, hKe]
    have h13 : (Δr - (Δr - 12 / (13 * s))) / 12 = 1 / (13 * s) := by field_simp; ring
    calc 1 / 4056 * min (1 / (Δr * Δc)) s ≤ 1 / 4056 * s := by
          gcongr; exact min_le_right _ _
      _ ≤ s / 156 := by linarith
      _ = T * (1 / (13 * s) - 11 / 12 * (1 / (13 * s))) := by
          rw [← hsT]; field_simp; ring
      _ ≤ T * ((Δr - (Δr - 12 / (13 * s))) / 12 - 11 / 12 * (e * Δc)) := by
          rw [h13]
          gcongr

end Ito2026Adversarial
