/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.TsallisSPMRegret
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Tsallis-FTRL-SPM with the parameters of Theorem 5

The regret bounds of Tsallis-FTRL-SPM (`TsallisSPMRegret.lean`) for the parameters
`α = 1 - 1 / (4 log m_x)`, `β₁ = 8 c d_x / (1 - α)`, `βbar = 32 d_x / ((1 - α)² β₁)` of Theorem 5
(`tsallisSPMPaper`), with `L = log m_x`:

* `externalRegretAgainst_tsallisSPMPaper_le`:
  `ER_T(x) ≤ 64 c d_x L + 64 m_x L² / c + (16 + 8 c) (8 √(T d_x L) + 1 / (4 c))`;
* `externalRegretAgainst_tsallisSPMPaper_le_self`: for a PSNE `(x₀, y₀)` with `Δʳ_min > 0`,
  `ER_T(x₀) ≤ 64 c d_x L + 64 m_x L² / c
  + (16 + 8 c) (32 √(d_x L (1 + log T) / Δʳ_min E[∑_{t < T} Δʳ_{x_t}]) + 8 √(d_x L) + 1 / (4 c))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix
open scoped RealInnerProductSpace

namespace Ito2026Adversarial

/-! ### The parameters of Theorem 5 -/

section Params

variable {mx : ℕ}

/-- `log m_x ≥ 1/2` for `m_x ≥ 2`. -/
lemma half_le_log (hm : 2 ≤ mx) : 1 / 2 ≤ log mx := by
  have h2 : log 2 ≤ log mx := log_le_log (by norm_num) (by exact_mod_cast hm)
  have := log_two_gt_d9
  linarith

/-- `1 - α = 1 / (4 log m)` for the parameter `α` of Theorem 5. -/
lemma one_sub_spmAlpha (mx : ℕ) : 1 - spmAlpha mx = 1 / (4 * log mx) := by
  unfold spmAlpha
  ring

/-- `α < 1` for `m ≥ 2`. -/
lemma spmAlpha_lt_one (hm : 2 ≤ mx) : spmAlpha mx < 1 := by
  have := half_le_log hm
  have : 0 < 1 / (4 * log mx) := by positivity
  linarith [one_sub_spmAlpha mx]

/-- `α ≥ 1/2` for `m ≥ 2`. -/
lemma half_le_spmAlpha (hm : 2 ≤ mx) : 1 / 2 ≤ spmAlpha mx := by
  have hL := half_le_log hm
  have : 1 / (4 * log mx) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith [one_sub_spmAlpha mx]

/-- The parameters of Theorem 5 are admissible. -/
lemma isSPMParams_paper {c : ℝ} (hc : 0 < c) {dx : ℕ} (hd : 1 ≤ dx) (hm : 2 ≤ mx) :
    IsSPMParams (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))
      (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))) c dx where
  half_le := half_le_spmAlpha hm
  lt_one := spmAlpha_lt_one hm
  c_pos := hc
  one_le_d := hd
  le_beta₁ := le_rfl
  le_betaBar := le_rfl

/-- `m ^ (1 - α) = e ^ (1/4) ≤ 2` for `α = 1 - 1 / (4 log m)`. -/
lemma rpow_one_sub_spmAlpha_le (hm : 2 ≤ mx) : (mx : ℝ) ^ (1 - spmAlpha mx) ≤ 2 := by
  have hL := half_le_log hm
  have hm0 : (0 : ℝ) < mx := by
    have : (2 : ℝ) ≤ mx := by exact_mod_cast hm
    linarith
  rw [rpow_def_of_pos hm0, one_sub_spmAlpha, show log mx * (1 / (4 * log mx)) = 1 / 4 by
    field_simp]
  have h1 : exp (1 / 4) ^ 4 = exp 1 := by
    rw [← exp_nat_mul]
    norm_num
  have h2 := exp_one_lt_d9
  have h3 : 0 ≤ exp (1 / 4) := (exp_pos _).le
  nlinarith [sq_nonneg (exp (1 / 4) - 2), sq_nonneg (exp (1 / 4)), sq_nonneg (exp (1 / 4) + 2)]

/-- `m ^ (1 - α) ≥ 1`. -/
lemma one_le_rpow_one_sub_spmAlpha (hm : 2 ≤ mx) : 1 ≤ (mx : ℝ) ^ (1 - spmAlpha mx) :=
  one_le_rpow (by exact_mod_cast (by omega : 1 ≤ mx)) (by linarith [spmAlpha_lt_one hm])

/-- `log m ≤ 2 (log m)²` for `m ≥ 2`. -/
lemma log_le_two_mul_sq (hm : 2 ≤ mx) : log mx ≤ 2 * log mx ^ 2 := by
  have := half_le_log hm
  nlinarith

/-- `1 ≤ 4 m (log m)²` for `m ≥ 2`. -/
lemma one_le_four_mul_sq (hm : 2 ≤ mx) : 1 ≤ 4 * mx * log mx ^ 2 := by
  have := half_le_log hm
  have : (2 : ℝ) ≤ mx := by exact_mod_cast hm
  nlinarith

/-- `β₁ = 32 c d log m` for the parameters of Theorem 5. -/
lemma spmBeta₁_eq (c : ℝ) (dx : ℕ) (hm : 2 ≤ mx) :
    spmBeta₁ c dx (spmAlpha mx) = 32 * c * dx * log mx := by
  have := half_le_log hm
  rw [spmBeta₁, one_sub_spmAlpha]
  field_simp
  ring

/-- `βbar = 16 log m / c` for the parameters of Theorem 5. -/
lemma spmBetaBar_eq {c : ℝ} (hc : 0 < c) {dx : ℕ} (hd : 1 ≤ dx) (hm : 2 ≤ mx) :
    spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx)) = 16 * log mx / c := by
  have := half_le_log hm
  have hd' : (1 : ℝ) ≤ dx := by exact_mod_cast hd
  rw [spmBetaBar, spmBeta₁_eq c dx hm, one_sub_spmAlpha]
  field_simp
  ring

/-- The penalty coefficients of Theorem 5 are at most `2`. -/
lemma tsallisEntropy_le_two_of_spmAlpha (hm : 2 ≤ mx) {p : EuclideanSpace ℝ (Fin mx)}
    (hp : p ∈ simplex (Fin mx)) : tsallisEntropy (spmAlpha mx) p ≤ 2 := by
  have : NeZero mx := ⟨by omega⟩
  have hα := half_le_spmAlpha hm
  have hα1 := spmAlpha_lt_one hm
  have h1 := tsallisEntropy_le_of_mem_simplex (by linarith) hα1.le hp
  rw [Fintype.card_fin] at h1
  refine h1.trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith [rpow_one_sub_spmAlpha_le hm]

/-- `H = (m ^ (1 - α) - 1) / α ∈ [0, 2]` for the parameters of Theorem 5. -/
lemma spmH_le_two (hm : 2 ≤ mx) :
    0 ≤ ((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx
      ∧ ((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx ≤ 2 := by
  have hα := half_le_spmAlpha hm
  have h1 := one_le_rpow_one_sub_spmAlpha hm
  have h2 := rpow_one_sub_spmAlpha_le hm
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The complementary entropy of Theorem 5 is at most `4 m log m`. -/
lemma tsallisEntropy_one_sub_le_of_spmAlpha (hm : 2 ≤ mx) {p : EuclideanSpace ℝ (Fin mx)}
    (hp : p ∈ simplex (Fin mx)) :
    tsallisEntropy (1 - spmAlpha mx) p ≤ 4 * mx * log mx := by
  have : NeZero mx := ⟨by omega⟩
  have hα := half_le_spmAlpha hm
  have hα1 := spmAlpha_lt_one hm
  have hL := half_le_log hm
  have h1 := tsallisEntropy_le_of_mem_simplex (a := 1 - spmAlpha mx) (by linarith) (by linarith) hp
  rw [Fintype.card_fin] at h1
  refine h1.trans ?_
  rw [sub_sub_cancel, one_sub_spmAlpha]
  have hm1 : (1 : ℝ) ≤ mx := by exact_mod_cast (by omega : 1 ≤ mx)
  have : (mx : ℝ) ^ spmAlpha mx ≤ mx := by
    calc (mx : ℝ) ^ spmAlpha mx ≤ (mx : ℝ) ^ (1 : ℝ) :=
          rpow_le_rpow_of_exponent_le hm1 hα1.le
      _ = mx := rpow_one _
  rw [div_div_eq_mul_div, div_one]
  nlinarith

/-- The constant term of the self-bounding bound: for `1 ≤ d ≤ m`, `m ≥ 2` and `c > 0`,
`64 c d L + 64 m L² / c + (16 + 8 c) (8 √(d L) + 1 / (4 c)) ≤ K m L²` with
`K = 128 c + 64 / c + (16 + 8 c) (48 + 1 / c)` and `L = log m`. -/
lemma spm_const_le {c : ℝ} (hc : 0 < c) {dx : ℕ} (hd : 1 ≤ dx) (hdm : dx ≤ mx) (hm : 2 ≤ mx) :
    64 * c * dx * log mx + 64 * mx * log mx ^ 2 / c
        + (16 + 8 * c) * (8 * √(dx * log mx) + 1 / (4 * c))
      ≤ (128 * c + 64 / c + (16 + 8 * c) * (48 + 1 / c)) * (mx * log mx ^ 2) := by
  have hL := half_le_log hm
  have hL2 := log_le_two_mul_sq hm
  have h4 := one_le_four_mul_sq hm
  have hdx : (1 : ℝ) ≤ dx := by exact_mod_cast hd
  have hdm' : (dx : ℝ) ≤ mx := by exact_mod_cast hdm
  have hm0 : (0 : ℝ) ≤ mx := Nat.cast_nonneg _
  have hdl : (dx : ℝ) * log mx ≤ mx * (2 * log mx ^ 2) :=
    mul_le_mul hdm' hL2 (by linarith) hm0
  have e1 : 64 * c * dx * log mx ≤ 128 * c * (mx * log mx ^ 2) := by nlinarith
  have e2 : √(dx * log mx) ≤ 6 * (mx * log mx ^ 2) := by
    have hs : √(dx * log mx) ≤ dx * log mx + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg ((dx : ℝ) * log mx)]
    nlinarith
  have e3 : 1 / (4 * c) ≤ 1 / c * (mx * log mx ^ 2) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hc]
    nlinarith
  have e4 : 64 * mx * log mx ^ 2 / c = 64 / c * (mx * log mx ^ 2) := by ring
  have h8c : 0 ≤ 16 + 8 * c := by positivity
  have e5 : (16 + 8 * c) * (8 * √(dx * log mx) + 1 / (4 * c))
      ≤ (16 + 8 * c) * (48 * (mx * log mx ^ 2) + 1 / c * (mx * log mx ^ 2)) :=
    mul_le_mul_of_nonneg_left (add_le_add (by linarith) e3) h8c
  rw [e4]
  calc 64 * c * dx * log mx + 64 / c * (mx * log mx ^ 2)
        + (16 + 8 * c) * (8 * √(dx * log mx) + 1 / (4 * c))
      ≤ 128 * c * (mx * log mx ^ 2) + 64 / c * (mx * log mx ^ 2)
        + (16 + 8 * c) * (48 * (mx * log mx ^ 2) + 1 / c * (mx * log mx ^ 2)) := by
        linarith [e1, e5]
    _ = _ := by ring

end Params

/-- **The self-bounding argument** (Lemmas 7 and 8): if `A ≤ a √(Q E) + K`, `E ≤ A + 4 C`,
`Δ C ≤ A - R`, with `Q > 0`, `a, K, C, Δ ≥ 0` and `C = 0` when `Δ = 0`, then
`R ≤ a² Q (1 + 1 / Δ) + 2 K`. -/
lemma le_of_self_bound {A E C R Q a K Δ : ℝ} (hQ : 0 < Q) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hΔ : 0 ≤ Δ) (hΔC : Δ = 0 → C = 0) (hA : A ≤ a * √(Q * E) + K)
    (hE : E ≤ A + 4 * C) (hR : Δ * C ≤ A - R) :
    R ≤ a ^ 2 * Q * (1 + 1 / Δ) + 2 * K := by
  have hpos : 0 ≤ a ^ 2 * Q * (1 + 1 / Δ) := by positivity
  by_cases hA0 : A < 0
  · nlinarith [mul_nonneg hΔ hC]
  push Not at hA0
  have hroot : a * √(Q * E) ≤ √(a ^ 2 * Q * A + 4 * a ^ 2 * Q * C) := by
    rw [show a ^ 2 * Q * A + 4 * a ^ 2 * Q * C = a ^ 2 * (Q * (A + 4 * C)) by ring,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
    gcongr
  have h8 := le_add_sqrt_add_of_le_sqrt_add hA0 (by positivity : 0 ≤ a ^ 2 * Q)
    (by positivity : 0 ≤ 4 * a ^ 2 * Q * C) hK (by linarith)
  have hsq : √(4 * a ^ 2 * Q * C) - Δ * C ≤ a ^ 2 * Q * (1 / Δ) := by
    rcases hΔ.lt_or_eq with hpos | hzero
    · rcases ha.lt_or_eq with ha' | ha'
      · have h7 := (sqrt_mul_sub_mul_le (4 * a ^ 2 * Q) Δ (by positivity) hpos).1 C hC
        calc √(4 * a ^ 2 * Q * C) - Δ * C ≤ 4 * a ^ 2 * Q / (4 * Δ) := h7
          _ = a ^ 2 * Q * (1 / Δ) := by field_simp
      · rw [← ha']
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
          Real.sqrt_zero, zero_sub, neg_nonpos]
        positivity
    · rw [hΔC hzero.symm, ← hzero]
      simp
  have : a ^ 2 * Q * (1 + 1 / Δ) = a ^ 2 * Q + a ^ 2 * Q * (1 / Δ) := by ring
  linarith

/-! ### Regret bounds with the parameters of Theorem 5 -/

section Bounds

variable {mx my dx : ℕ} [NeZero mx] {φ : Fin mx → EuclideanSpace ℝ (Fin dx)} {c : ℝ}
  {p₀ : simplex (Fin mx)} {u : Fin mx → Fin my → ℝ} {w : Fin my → Fin dx → ℝ}
  {opp : Player (Fin my) (Fin mx)} {R : RewardKernel (Fin mx) (Fin my)}
  [∀ n, IsMarkovKernel (R n)] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℕ → Ω → Fin mx} {Y : ℕ → Ω → Fin my} {Rw : ℕ → Ω → ℝ}

omit [NeZero mx] in
/-- `tsallisSPMPaper` is `tsallisSPM` with the parameters of Theorem 5. -/
lemma tsallisSPMPaper_eq (φ : Fin mx → EuclideanSpace ℝ (Fin dx)) (c : ℝ)
    (p₀ : simplex (Fin mx)) [NeZero mx] :
    tsallisSPMPaper φ c p₀ = tsallisSPM φ (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))
      (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))) p₀ c := by
  simp only [tsallisSPMPaper, Fintype.card_fin]

/-- The penalty term `β₁ φ_α(p̂_0) + βbar φ_{1-α}(p̂_0) ≤ 64 c d L + 64 m L² / c`. -/
lemma penalty_zero_le (hc : 0 < c) (hd : 1 ≤ dx) (hm : 2 ≤ mx) :
    spmBeta₁ c dx (spmAlpha mx) * tsallisEntropy (spmAlpha mx)
        (spmHat (𝒳 := Fin mx) (spmAlpha mx)
          (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx)))
          (0, spmBeta₁ c dx (spmAlpha mx)) : EuclideanSpace ℝ (Fin mx))
      + spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))
        * tsallisEntropy (1 - spmAlpha mx) (spmHat (𝒳 := Fin mx) (spmAlpha mx)
          (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx)))
          (0, spmBeta₁ c dx (spmAlpha mx)) : EuclideanSpace ℝ (Fin mx))
      ≤ 64 * c * dx * log mx + 64 * mx * log mx ^ 2 / c := by
  have hL := half_le_log hm
  have hdx : (1 : ℝ) ≤ dx := by exact_mod_cast hd
  have h1 := tsallisEntropy_le_two_of_spmAlpha hm (spmHat (𝒳 := Fin mx) (spmAlpha mx)
    (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx)))
    (0, spmBeta₁ c dx (spmAlpha mx))).2
  have h2 := tsallisEntropy_one_sub_le_of_spmAlpha hm (spmHat (𝒳 := Fin mx) (spmAlpha mx)
    (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx)))
    (0, spmBeta₁ c dx (spmAlpha mx))).2
  have hβ₁ := spmBeta₁_eq c dx hm
  have hβbar := spmBetaBar_eq hc hd hm
  have hb1 : 0 ≤ spmBeta₁ c dx (spmAlpha mx) := by rw [hβ₁]; positivity
  have hb2 : 0 ≤ spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx)) := by
    rw [hβbar]; positivity
  refine (add_le_add (mul_le_mul_of_nonneg_left h1 hb1) (mul_le_mul_of_nonneg_left h2 hb2)).trans
    (le_of_eq ?_)
  rw [hβbar, hβ₁]
  ring

variable (hc : 0 < c) (hd : 1 ≤ dx) (hm : 2 ≤ mx) (hV : HasVarianceRatio φ p₀ c)
  (hu : ∀ x y, u x y = WithLp.ofLp (φ x) ⬝ᵥ w y) (hu1 : ∀ x y, u x y ∈ Set.Icc (-1) 1)
  (hRu : R.HasMean u) (hR : R.RewardsIn (Set.Icc (-1) 1))
  (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
    (Player.ofUninformed (tsallisSPMPaper φ c p₀)) (gameEnv opp R) P)
include hc hd hm hV hu hu1 hRu hR h

/-- **Worst-case regret with the parameters of Theorem 5**:
`ER_T(x) ≤ 64 c d L + 64 m L² / c + (16 + 8 c) (8 √(T d L) + 1 / (4 c))` with `L = log m`. -/
lemma externalRegretAgainst_tsallisSPMPaper_le (T : ℕ) (x : Fin mx) :
    externalRegretAgainst u X Y P T x
      ≤ 64 * c * dx * log mx + 64 * mx * log mx ^ 2 / c
        + (16 + 8 * c) * (8 * √(T * dx * log mx) + 1 / (4 * c)) := by
  have hP : IsSPMParams (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))
      (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))) c (Fintype.card (Fin dx)) := by
    rw [Fintype.card_fin]
    exact isSPMParams_paper hc hd hm
  rw [tsallisSPMPaper_eq] at h
  have key := externalRegretAgainst_tsallisSPM_le_sqrt hP hV hm hu hu1 hRu hR h T x
  rw [Fintype.card_fin] at key
  refine key.trans (add_le_add (penalty_zero_le hc hd hm) ?_)
  have hL := half_le_log hm
  have hdx : (1 : ℝ) ≤ dx := by exact_mod_cast hd
  obtain ⟨hH0, hH2⟩ := spmH_le_two hm
  have h1α := one_sub_spmAlpha mx
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ (le_of_eq ?_)) (by positivity)
  · have e : (dx : ℝ) / (1 - spmAlpha mx) = 4 * dx * log mx := by
      rw [h1α]
      field_simp
    rw [e]
    have : 2 * (((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx) * (T * (4 * dx * log mx))
        ≤ 4 ^ 2 * (T * dx * log mx) := by
      have : 0 ≤ (T : ℝ) * (4 * dx * log mx) := by positivity
      nlinarith
    calc 2 * √(2 * (((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx)
          * (T * (4 * dx * log mx)))
        ≤ 2 * √(4 ^ 2 * (T * dx * log mx)) := by gcongr
      _ = 8 * √(T * dx * log mx) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
          ring
  · rw [h1α, spmBeta₁_eq c dx hm]
    field_simp
    norm_num

/-- **Self-bounding regret with the parameters of Theorem 5**: if `Δ ≥ 0` and `Δ x ≥ Δmin > 0`
for `x ≠ x₀`, then with `L = log m` and `Q = d L (1 + log T) / Δmin`,
`ER_T(x₀) ≤ 64 c d L + 64 m L² / c
+ (16 + 8 c) (32 √(Q E[∑_{t < T} Δ x_t]) + 8 √(d L) + 1 / (4 c))`. -/
lemma externalRegretAgainst_tsallisSPMPaper_le_self (T : ℕ) {x₀ : Fin mx} {Δ : Fin mx → ℝ}
    {Δmin : ℝ} (hΔmin : 0 < Δmin) (hΔ0 : ∀ x, 0 ≤ Δ x) (hΔ : ∀ x, x ≠ x₀ → Δmin ≤ Δ x) :
    externalRegretAgainst u X Y P T x₀
      ≤ 64 * c * dx * log mx + 64 * mx * log mx ^ 2 / c
        + (16 + 8 * c) * (32 * √(dx * log mx * (1 + log T) / Δmin
              * ∫ ω, ∑ t ∈ range T, Δ (X t ω) ∂P)
            + 8 * √(dx * log mx) + 1 / (4 * c)) := by
  have hP : IsSPMParams (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))
      (spmBetaBar dx (spmAlpha mx) (spmBeta₁ c dx (spmAlpha mx))) c (Fintype.card (Fin dx)) := by
    rw [Fintype.card_fin]
    exact isSPMParams_paper hc hd hm
  rw [tsallisSPMPaper_eq] at h
  have key := externalRegretAgainst_tsallisSPM_le_self hP hV hm hu hu1 hRu hR h T
    (Nat.log 2 T + 1) hΔmin hΔ0 hΔ
  rw [Fintype.card_fin] at key
  refine key.trans (add_le_add (penalty_zero_le hc hd hm) ?_)
  have hL := half_le_log hm
  have hdx : (1 : ℝ) ≤ dx := by exact_mod_cast hd
  obtain ⟨hH0, hH2⟩ := spmH_le_two hm
  have h1α := one_sub_spmAlpha mx
  have hα := half_le_spmAlpha hm
  have hmα := rpow_one_sub_spmAlpha_le hm
  have hmα0 : 0 ≤ (mx : ℝ) ^ (1 - spmAlpha mx) := rpow_nonneg (Nat.cast_nonneg _) _
  set E := ∫ ω, ∑ t ∈ range T, Δ (X t ω) ∂P with hE
  have hE0 : 0 ≤ E := integral_nonneg fun ω ↦ sum_nonneg fun t _ ↦ hΔ0 _
  refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) (le_of_eq ?_))
    (by positivity)
  · -- the main term: `J W ≤ 64 d L (1 + log T) / Δmin`
    have hJ : ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤ 2 * (1 + log T) := by
      rcases Nat.eq_zero_or_pos T with rfl | hT
      · simp
      · have h1 := Real.natLog_le_logb T 2
        simp only [Nat.cast_ofNat] at h1
        have h2 : Real.logb 2 T = log T / log 2 := rfl
        have hl2 := log_two_gt_d9
        have hlT : 0 ≤ log T := Real.log_natCast_nonneg T
        have h3 : log T / log 2 ≤ 2 * log T := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        push_cast
        linarith
    have hW : 2 * dx * (mx : ℝ) ^ (1 - spmAlpha mx) / (spmAlpha mx * (1 - spmAlpha mx) * Δmin)
        ≤ 32 * dx * log mx / Δmin := by
      have e1 : spmAlpha mx * (1 - spmAlpha mx) * Δmin = spmAlpha mx * Δmin / (4 * log mx) := by
        rw [h1α]
        ring
      rw [e1, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hΔmin]
      have : 2 * dx * (mx : ℝ) ^ (1 - spmAlpha mx) * Δmin ≤ 2 * dx * 2 * Δmin := by
        gcongr
      nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < dx) (by linarith : (0 : ℝ) < log mx))
        (mul_pos (by linarith : (0 : ℝ) < spmAlpha mx) hΔmin)]
    have hJW : ((Nat.log 2 T + 1 : ℕ) : ℝ) * (2 * dx * (mx : ℝ) ^ (1 - spmAlpha mx)
        / (spmAlpha mx * (1 - spmAlpha mx) * Δmin)) * E
        ≤ 8 ^ 2 * (dx * log mx * (1 + log T) / Δmin * E) := by
      have hW0 : 0 ≤ 2 * dx * (mx : ℝ) ^ (1 - spmAlpha mx)
          / (spmAlpha mx * (1 - spmAlpha mx) * Δmin) := by
        rw [h1α]
        positivity
      calc ((Nat.log 2 T + 1 : ℕ) : ℝ) * (2 * dx * (mx : ℝ) ^ (1 - spmAlpha mx)
            / (spmAlpha mx * (1 - spmAlpha mx) * Δmin)) * E
          ≤ (2 * (1 + log T)) * (32 * dx * log mx / Δmin) * E := by
            gcongr
          _ = 8 ^ 2 * (dx * log mx * (1 + log T) / Δmin * E) := by ring
    calc 4 * √(((Nat.log 2 T + 1 : ℕ) : ℝ) * (2 * dx * (mx : ℝ) ^ (1 - spmAlpha mx)
          / (spmAlpha mx * (1 - spmAlpha mx) * Δmin)) * E)
        ≤ 4 * √(8 ^ 2 * (dx * log mx * (1 + log T) / Δmin * E)) := by gcongr
      _ = 32 * √(dx * log mx * (1 + log T) / Δmin * E) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
          ring
  · -- the remainder: `2 H / 2 ^ J T d / (1 - α) ≤ 16 d L`
    have hT : (T : ℝ) < 2 ^ (Nat.log 2 T + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) T
    have e : (dx : ℝ) / (1 - spmAlpha mx) = 4 * dx * log mx := by
      rw [h1α]
      field_simp
    rw [e]
    have h2J : (0 : ℝ) < 2 ^ (Nat.log 2 T + 1) := by positivity
    have hTJ : (T : ℝ) / 2 ^ (Nat.log 2 T + 1) ≤ 1 := (div_le_one h2J).2 hT.le
    have hTJ0 : 0 ≤ (T : ℝ) / 2 ^ (Nat.log 2 T + 1) := by positivity
    have : 2 * ((((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx) / 2 ^ (Nat.log 2 T + 1))
        * (T * (4 * dx * log mx)) ≤ 4 ^ 2 * (dx * log mx) := by
      have e2 : 2 * ((((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx) / 2 ^ (Nat.log 2 T + 1))
          * (T * (4 * dx * log mx))
          = (2 * (((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx) * (4 * dx * log mx))
            * ((T : ℝ) / 2 ^ (Nat.log 2 T + 1)) := by ring
      rw [e2]
      have hdl : 0 ≤ 4 * (dx : ℝ) * log mx := by positivity
      calc (2 * (((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx) * (4 * dx * log mx))
            * ((T : ℝ) / 2 ^ (Nat.log 2 T + 1))
          ≤ (2 * 2 * (4 * dx * log mx)) * 1 :=
            mul_le_mul (by gcongr) hTJ hTJ0 (by positivity)
        _ = 4 ^ 2 * (dx * log mx) := by ring
    calc 2 * √(2 * ((((mx : ℝ) ^ (1 - spmAlpha mx) - 1) / spmAlpha mx)
          / 2 ^ (Nat.log 2 T + 1)) * (T * (4 * dx * log mx)))
        ≤ 2 * √(4 ^ 2 * (dx * log mx)) := by gcongr
      _ = 8 * √(dx * log mx) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
          ring
  · rw [h1α, spmBeta₁_eq c dx hm]
    field_simp
    norm_num

include hc hd hm hV hu hu1 hRu hR h in
/-- **Worst-case regret of Theorem 5**: for `d ≤ m`,
`ER_T(x) ≤ 8 (16 + 8 c) √(T d L) + (128 c + 64 / c + (16 + 8 c) / c) m L²`. -/
lemma externalRegretAgainst_tsallisSPMPaper_le' (hdm : dx ≤ mx) (T : ℕ) (x : Fin mx) :
    externalRegretAgainst u X Y P T x
      ≤ 8 * (16 + 8 * c) * √(T * dx * log mx)
        + (128 * c + 64 / c + (16 + 8 * c) / c) * (mx * log mx ^ 2) := by
  refine (externalRegretAgainst_tsallisSPMPaper_le hc hd hm hV hu hu1 hRu hR h T x).trans ?_
  have hL := half_le_log hm
  have hL2 := log_le_two_mul_sq hm
  have h4 := one_le_four_mul_sq hm
  have hdm' : (dx : ℝ) ≤ mx := by exact_mod_cast hdm
  have hm0 : (0 : ℝ) ≤ mx := Nat.cast_nonneg _
  have e1 : 64 * c * dx * log mx ≤ 128 * c * (mx * log mx ^ 2) := by
    have : (dx : ℝ) * log mx ≤ mx * (2 * log mx ^ 2) :=
      mul_le_mul hdm' hL2 (by linarith) hm0
    nlinarith
  have e2 : (16 + 8 * c) * (1 / (4 * c)) ≤ (16 + 8 * c) / c * (mx * log mx ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have : (16 + 8 * c) * (1 / (4 * c)) * c = (16 + 8 * c) / 4 := by field_simp
    rw [this]
    nlinarith
  have e3 : 64 * mx * log mx ^ 2 / c = 64 / c * (mx * log mx ^ 2) := by ring
  nlinarith

include hc hd hm hV hu hu1 hRu hR h in
/-- **Worst-case PSMR bound of Theorem 5**, before Lemma 7:
`PSMR_T ≤ 8 (16 + 8 c) √(T d L) + (128 c + 64 / c + (16 + 8 c) / c) m L² - Δ^mix T`. -/
lemma psmr_tsallisSPMPaper_le_sub [NeZero my] (hdm : dx ≤ mx) (T : ℕ) :
    psmr u X Y P T
      ≤ 8 * (16 + 8 * c) * √(T * dx * log mx)
        + (128 * c + 64 / c + (16 + 8 * c) / c) * (mx * log mx ^ 2) - mixGap u * T := by
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hNR := nashRegret_eq_psmr_add (P := P) (u := u) hX hY T
  have hNE := nashRegret_le_externalRegret (P := P) (u := u) hX hY T
  have hER : externalRegret u X Y P T
      ≤ 8 * (16 + 8 * c) * √(T * dx * log mx)
        + (128 * c + 64 / c + (16 + 8 * c) / c) * (mx * log mx ^ 2) :=
    ciSup_le fun x ↦ externalRegretAgainst_tsallisSPMPaper_le' hc hd hm hV hu hu1 hRu hR h hdm T x
  linarith

include hc hd hm hV hu hu1 hRu hR h in
/-- **Strict-PSNE PSMR bound of Theorem 5**: for a strict PSNE `(x₀, y₀)` and `d ≤ m`, with
`L = log m`, `a = 32 (16 + 8 c)` and `K = 128 c + 64 / c + (16 + 8 c) (48 + 1 / c)`,
`PSMR_T ≤ a² d L (1 + log T) (1 + 1 / Δᶜ_min) / Δʳ_min + 2 K m L²` (Lemmas 7 and 8). -/
lemma psmr_tsallisSPMPaper_le_of_isStrictPSNE (hdm : dx ≤ mx) {x₀ : Fin mx}
    {y₀ : Fin my} (hxy : IsStrictPSNE u x₀ y₀) (T : ℕ) :
    psmr u X Y P T
      ≤ (32 * (16 + 8 * c)) ^ 2 * (dx * log mx * (1 + log T) * (1 + 1 / colGapMin u x₀ y₀)
          / rowGapMin u x₀ y₀)
        + 2 * ((128 * c + 64 / c + (16 + 8 * c) * (48 + 1 / c)) * (mx * log mx ^ 2)) := by
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hL := half_le_log hm
  have hdx : (1 : ℝ) ≤ dx := by exact_mod_cast hd
  -- the gaps
  have hne : Nonempty {x' // x' ≠ x₀} := by
    obtain ⟨x', hx'⟩ : ∃ x' : Fin mx, x' ≠ x₀ := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card (Fin mx) ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ by
        rw [hcon a, hcon b]
      simp at this
      omega
    exact ⟨⟨x', hx'⟩⟩
  have hΔmin : 0 < rowGapMin u x₀ y₀ := by
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun x' : {x' // x' ≠ x₀} ↦
      rowGap u x₀ y₀ x')
    rw [rowGapMin, ← hi]
    exact hxy.rowGap_pos i.2
  have hΔ0 (x : Fin mx) : 0 ≤ rowGap u x₀ y₀ x := by
    by_cases hx : x = x₀
    · simp [rowGap, hx]
    · exact (hxy.rowGap_pos hx).le
  have hΔ (x : Fin mx) (hx : x ≠ x₀) : rowGapMin u x₀ y₀ ≤ rowGap u x₀ y₀ x :=
    ciInf_le (Set.finite_range _).bddBelow (⟨x, hx⟩ : {x' // x' ≠ x₀})
  have hself := externalRegretAgainst_tsallisSPMPaper_le_self hc hd hm hV hu hu1 hRu hR h T
    hΔmin hΔ0 hΔ
  have h6 := integral_sum_rowGap_sub_le (P := P) x₀ y₀ hu1 hX hY T
  have hcol := IsPSNE.colGapMin_mul_le (P := P) hxy.isPSNE hX hY T
  have hK := spm_const_le hc hd hdm hm
  have hCy0 : 0 ≤ P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] :=
    integral_nonneg fun ω ↦ sum_nonneg fun t _ ↦ by split_ifs <;> norm_num
  have hΔc0 : 0 ≤ colGapMin u x₀ y₀ := Real.iInf_nonneg fun y ↦ (hxy.colGap_pos y.2).le
  have hlogT := Real.log_natCast_nonneg T
  have hQ0 : 0 < dx * log mx * (1 + log T) / rowGapMin u x₀ y₀ := by positivity
  have hΔC : colGapMin u x₀ y₀ = 0 →
      P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] = 0 := by
    intro hzero
    have hy (y : Fin my) : y = y₀ := by
      by_contra hne
      have : Nonempty {y' // y' ≠ y₀} := ⟨⟨y, hne⟩⟩
      obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun y' : {y' // y' ≠ y₀} ↦
        colGap u x₀ y₀ y')
      have := hxy.colGap_pos i.2
      rw [hi] at this
      exact absurd hzero (ne_of_lt this).symm
    have : ∀ t ω, Y t ω = y₀ := fun t ω ↦ hy _
    simp [this]
  have hK0 : 0 ≤ 64 * c * dx * log mx + 64 * mx * log mx ^ 2 / c
      + (16 + 8 * c) * (8 * √(dx * log mx) + 1 / (4 * c)) := by positivity
  have key := le_of_self_bound hQ0 (by positivity : (0 : ℝ) ≤ 32 * (16 + 8 * c)) hK0 hCy0 hΔc0
    hΔC (A := externalRegretAgainst u X Y P T x₀) (hself.trans (le_of_eq (by ring)))
    (by linarith) hcol
  have e : dx * log mx * (1 + log T) * (1 + 1 / colGapMin u x₀ y₀) / rowGapMin u x₀ y₀
      = dx * log mx * (1 + log T) / rowGapMin u x₀ y₀ * (1 + 1 / colGapMin u x₀ y₀) := by
    ring
  rw [e, ← mul_assoc]
  exact key.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hK zero_le_two))

end Bounds

end Ito2026Adversarial
