/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.TsallisHalf
public import Ito2026Adversarial.LeanMachineLearning.Game.UninformedRun
public import Ito2026Adversarial.LeanMachineLearning.Game.RegretRelations
public import Ito2026Adversarial.ILMTW2026.Lemma7
public import Ito2026Adversarial.ILMTW2026.Lemma8
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Regret of Tsallis-INF in a repeated game

The regret bounds of Tsallis-INF with `α = 1/2` and `η_t = 1 / (2 √t)` (`tsallisINFHalf`), cited by
the paper (Zimmert, Seldin 2021, Theorem 1; Ito et al. 2025, Theorem 1), for rewards in
`[-1, 1]` against an adaptive adversary, as used in the proof of Theorem 1.

## Main definitions

* `halfRate t = 1 / (2 √(t + 1))`: the learning rate of round `t` (rounds counted from `0`);
* `halfDist r t`, `halfEstimate r t`: the distribution and the reward estimate of round `t` of
  Tsallis-INF along a sequence of rounds `r`;
* `halfDistHist n h`: the distribution of round `n` after the history `h` of the game;
* `stabWeight p j`: the weight of the stability bound of a round in which `j` is played.

## Main statements

* `sum_inner_halfEstimate_le`: the pathwise regret bound of FTRL (penalty and stability terms) for
  any sequence of rounds with rewards in `[-1, 1]`;
* `integral_inner_halfEstimate`, `integral_stabWeight` (`lem:uninformed_run`): in a run against
  an adaptive adversary, the estimates are conditionally unbiased and the stability weight has
  conditional expectation `∑ i, √(p i) (1 - p i)`;
* `externalRegretAgainst_tsallisINFHalf_le` (`lem:tsallis_inf_self_bound`): the self-bounding
  form `ER_T(x₀) ≤ 12 E[∑_t (t + 1)^{-1/2} ∑_{x ≠ x₀} √(p_t x)] + 6`;
* `externalRegret_tsallisINFHalf_le` (`lem:tsallis_inf_worst`): `ER_T ≤ 24 √(m_x T) + 6`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Bandits.TsallisINF
open scoped RealInnerProductSpace ENNReal

namespace Ito2026Adversarial

/-! ### Learning rates and distributions -/

/-- The learning rate `η_t = 1 / (2 √(t + 1))` of `tsallisINFHalf` at round `t` (from `0`). -/
noncomputable def halfRate (t : ℕ) : ℝ := 1 / ((2 : ℕ) * √(t + 1))

/-- The learning rates are positive. -/
lemma halfRate_pos (t : ℕ) : 0 < halfRate t := by
  unfold halfRate
  positivity

/-- `η_t⁻¹ = 2 √(t + 1)`. -/
lemma inv_halfRate (t : ℕ) : (halfRate t)⁻¹ = 2 * √((t : ℝ) + 1) := by
  simp [halfRate]

/-- `η_t ≤ 1/4` from round `3` on. -/
lemma halfRate_le_quarter {t : ℕ} (ht : 3 ≤ t) : halfRate t ≤ 1 / 4 := by
  have h3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have h2 : (2 : ℝ) ≤ √((t : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  rw [halfRate, div_le_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  linarith

/-- `tsallisINFHalf` is Tsallis-INF with `α = 1/2` and the learning rates `halfRate`. -/
lemma tsallisINFHalf_eq (mx : ℕ) [NeZero mx] :
    tsallisINFHalf mx = Bandits.tsallisINF (1 / 2) halfRate := by
  unfold tsallisINFHalf
  rw [Nat.cast_ofNat]
  rfl

variable {m : ℕ} [NeZero m]

/-- The distribution of round `t` of Tsallis-INF (`α = 1/2`, `η_t = halfRate t`) along the
sequence of rounds `r`. -/
noncomputable def halfDist (r : ℕ → Round Unit (Fin m) ℝ) (t : ℕ) : simplex (Fin m) :=
  dist (1 / 2) halfRate t (cumEstimate (1 / 2) halfRate t fun i ↦ r i)

/-- The importance-weighted reward estimate of round `t` of Tsallis-INF along the sequence of
rounds `r`. -/
noncomputable def halfEstimate (r : ℕ → Round Unit (Fin m) ℝ) (t : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  estimate (halfDist r t) (r t)

/-- The cumulative estimate of Tsallis-INF is the sum of the estimates of the past rounds. -/
lemma cumEstimate_eq_sum_halfEstimate (r : ℕ → Round Unit (Fin m) ℝ) (t : ℕ) :
    cumEstimate (1 / 2) halfRate t (fun i : Fin t ↦ r i) = ∑ s ∈ range t, halfEstimate r s := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [cumEstimate_succ, sum_range_succ, ← ih]
    rfl

/-- The distribution of round `t` is the FTRL distribution of the Tsallis-`1/2` entropy for
the scaled cumulative estimate `η_t G_t`. -/
lemma halfDist_eq_ftrlSimplex (r : ℕ → Round Unit (Fin m) ℝ) (t : ℕ) :
    halfDist r t =
      ftrlSimplex (tsallisEntropy (1 / 2)) (halfRate t • ∑ s ∈ range t, halfEstimate r s) := by
  rw [halfDist, Bandits.TsallisINF.dist, cumEstimate_eq_sum_halfEstimate]

/-- The distributions of Tsallis-INF have positive coordinates. -/
lemma halfDist_pos (r : ℕ → Round Unit (Fin m) ℝ) (t : ℕ) (i : Fin m) : 0 < halfDist r t i := by
  rw [halfDist_eq_ftrlSimplex]
  exact (ftrlSimplex_tsallisEntropy_half _).1 i

/-- The weight `w(p, j) = ∑ i, √(p i)³ (if i = j then (1 / p j - 1)² else 1)` of the stability
bound of a round in which `j` is played with the distribution `p`. -/
noncomputable def stabWeight (p : simplex (Fin m)) (j : Fin m) : ℝ :=
  ∑ i, √(p i) ^ 3 * (if i = j then (1 / p j - 1) ^ 2 else 1)

/-! ### Pathwise regret bound -/

/-- The stability term of round `t` of Tsallis-INF along a sequence of rounds is at most `2`, and
at most `4 / √(t + 1) w(p_t, x_t)` from round `3` on (when `η_t ≤ 1/4`). -/
lemma stability_halfEstimate_le (r : ℕ → Round Unit (Fin m) ℝ) (t : ℕ)
    (hr : (r t).feedback ∈ Set.Icc (-1) 1) :
    ftrlValue ((halfRate t)⁻¹ • tsallisEntropy (1 / 2)) (∑ s ∈ range (t + 1), halfEstimate r s)
        - ftrlValue ((halfRate t)⁻¹ • tsallisEntropy (1 / 2)) (∑ s ∈ range t, halfEstimate r s)
        - ⟪(halfDist r t : EuclideanSpace ℝ (Fin m)), halfEstimate r t⟫
      ≤ if t < 3 then 2 else 4 / √((t : ℝ) + 1) * stabWeight (halfDist r t) (r t).action := by
  set G := ∑ s ∈ range t, halfEstimate r s with hG
  have hp := halfDist_eq_ftrlSimplex r t
  rw [← hG] at hp
  have hg : halfEstimate r t = estimate (halfDist r t) (r t) := rfl
  rw [sum_range_succ, ← hG, hg, hp, ftrlValue_add_sub_tsallisHalf (halfRate_pos t) G]
  have hpos := (ftrlSimplex_tsallisEntropy_half (halfRate t • G)).1
  split_ifs with ht
  · exact inner_sub_estimate_sub_le' (halfRate_pos t) _ hpos (ftrlSimplex _ _).2 (r t) hr
  · refine (inner_sub_estimate_sub_le (halfRate_pos t) (halfRate_le_quarter (by omega)) _ hpos
      (ftrlSimplex _ _).2 (r t) hr).trans (le_of_eq ?_)
    rw [stabWeight, halfRate]
    have : 0 < √((t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    field_simp
    push_cast
    ring

omit [NeZero m] in
/-- The penalty term of round `t + 1`:
`(η_{t+1}⁻¹ - η_t⁻¹) φ(p) ≤ 4 / √(t + 2) ∑_{i ≠ x} √(p i)`. -/
lemma inv_halfRate_sub_mul_le (t : ℕ) {p : EuclideanSpace ℝ (Fin m)} (hp : p ∈ simplex (Fin m))
    (x : Fin m) :
    ((halfRate (t + 1))⁻¹ - (halfRate t)⁻¹) * tsallisEntropy (1 / 2) p
      ≤ 4 / √(((t + 1 : ℕ) : ℝ) + 1) * ∑ i ∈ univ.erase x, √(p i) := by
  rw [inv_halfRate, inv_halfRate]
  push_cast
  set a := √((t : ℝ) + 1) with ha
  set b := √((t : ℝ) + 1 + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hb2 : b ^ 2 = a ^ 2 + 1 := by
    rw [ha, hb, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hb0 : 0 < b := ha0.trans_le hab
  have hφ0 := tsallisEntropy_half_nonneg hp
  have hφ := tsallisEntropy_half_le_sum_erase hp x
  have hc0 : 0 ≤ 2 * b - 2 * a := by linarith
  have hc : 2 * b - 2 * a ≤ 2 / b := by
    rw [le_div_iff₀ hb0]
    nlinarith
  calc (2 * b - 2 * a) * tsallisEntropy (1 / 2) p
      ≤ 2 / b * (2 * ∑ i ∈ univ.erase x, √(p i)) :=
        mul_le_mul hc hφ hφ0 (by positivity)
    _ = 4 / b * ∑ i ∈ univ.erase x, √(p i) := by ring

/-- **Pathwise regret of Tsallis-INF.** Along any sequence of rounds with rewards in `[-1, 1]`,
the regret of the distributions of Tsallis-INF (`α = 1/2`, `η_t = 1 / (2 √(t + 1))`) for the
importance-weighted estimates against the arm `x` is at most
`∑_t (4 / √(t + 1) ∑_{i ≠ x} √(p_t i) + B_t)`, with `B_t = 2` for `t < 3` and
`B_t = 4 / √(t + 1) w(p_t, x_t)` otherwise (FTRL decomposition, penalty and stability). -/
lemma sum_inner_halfEstimate_le (r : ℕ → Round Unit (Fin m) ℝ)
    (hr : ∀ t, (r t).feedback ∈ Set.Icc (-1) 1) (x : Fin m) (T : ℕ) :
    ∑ t ∈ range T,
        ⟪EuclideanSpace.single x (1 : ℝ) - halfDist r t, halfEstimate r t⟫ ≤
      ∑ t ∈ range T, (4 / √((t : ℝ) + 1) * ∑ i ∈ univ.erase x, √(halfDist r t i)
        + if t < 3 then 2 else 4 / √((t : ℝ) + 1) * stabWeight (halfDist r t) (r t).action) := by
  rcases T with _ | n
  · simp
  have hmax (t : ℕ) (q : EuclideanSpace ℝ (Fin m)) (hq : q ∈ simplex (Fin m)) :
      ⟪q, ∑ s ∈ range t, halfEstimate r s⟫ + (halfRate t)⁻¹ * tsallisEntropy (1 / 2) q
        ≤ ⟪(halfDist r t : EuclideanSpace ℝ (Fin m)), ∑ s ∈ range t, halfEstimate r s⟫
          + (halfRate t)⁻¹ * tsallisEntropy (1 / 2) (halfDist r t : EuclideanSpace ℝ (Fin m)) := by
    rw [halfDist_eq_ftrlSimplex]
    exact isMaxOn_ftrlSimplex_tsallisEntropy_half (halfRate_pos t) _ q hq
  have h := sum_inner_sub_le_ftrl_smul (halfEstimate r)
    (fun t ↦ (halfDist r t : EuclideanSpace ℝ (Fin m))) (tsallisEntropy (1 / 2)) halfRate
    (fun t ↦ (halfDist r t).2) hmax (single_mem_simplex x) n
  rw [tsallisEntropy_half_single] at h
  simp only [sub_zero] at h
  rw [sum_add_distrib]
  refine h.trans (add_le_add ?_ (sum_le_sum fun t _ ↦ stability_halfEstimate_le r t (hr t)))
  rw [sum_range_succ']
  have hs := sum_le_sum fun t (_ : t ∈ range n) ↦
    inv_halfRate_sub_mul_le t (halfDist r (t + 1)).2 x
  have h1 := tsallisEntropy_half_le_sum_erase (halfDist r 0).2 x
  have h0 : (halfRate 0)⁻¹ = 2 := by rw [inv_halfRate]; simp
  simp only [CharP.cast_eq_zero, zero_add, Real.sqrt_one, h0] at hs ⊢
  linarith

omit [NeZero m] in
/-- The regret of a round against the arm `x`, for the importance-weighted estimate:
`⟪e_x - p, g⟫ = (1 - r) - (1 - r) 𝟙{x_t = x} / p x`. -/
lemma inner_single_sub_estimate (p : simplex (Fin m)) (hp : ∀ i, 0 < p i)
    (r : Round Unit (Fin m) ℝ) (x : Fin m) :
    ⟪EuclideanSpace.single x (1 : ℝ) - p, estimate p r⟫
      = (1 - r.feedback) - (1 - r.feedback) * (if r.action = x then (p x)⁻¹ else 0) := by
  rw [inner_sub_left, inner_single_estimate, inner_estimate p r (hp _).ne', estimate_apply_eq]
  split_ifs with hx
  · subst hx
    ring
  · ring

omit [NeZero m] in
/-- `∑_{t < T} 1 / √(t + 1) ≤ 2 √T`. -/
lemma sum_inv_sqrt_le (T : ℕ) : ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ ≤ 2 * √(T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ]
    have ha := Real.sqrt_nonneg (T : ℝ)
    have hb : 0 < √((T : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hab : √(T : ℝ) ≤ √((T : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hsq : √((T : ℝ) + 1) ^ 2 = √(T : ℝ) ^ 2 + 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have key : (√((T : ℝ) + 1))⁻¹ ≤ 2 * √((T : ℝ) + 1) - 2 * √(T : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ hb]
      nlinarith
    push_cast
    linarith

omit [NeZero m] in
/-- `∑_{t < T} 𝟙{t < 3} 2 ≤ 6`. -/
lemma sum_ite_lt_three_le (T : ℕ) : ∑ t ∈ range T, (if t < 3 then (2 : ℝ) else 0) ≤ 6 := by
  rw [← sum_filter]
  calc ∑ t ∈ (range T).filter (· < 3), (2 : ℝ) ≤ ∑ t ∈ range 3, (2 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (fun t ht ↦ by simp at ht ⊢; omega)
          (fun _ _ _ ↦ by norm_num)
    _ = 6 := by norm_num

omit [NeZero m] in
/-- Measurability of the stability weight along a measurable family of distributions. -/
lemma measurable_stabWeight {α : Type*} [MeasurableSpace α] {g : α → simplex (Fin m)}
    (hg : Measurable fun a ↦ (g a : Fin m → ℝ)) (j : Fin m) :
    Measurable fun a ↦ stabWeight (g a) j := by
  unfold stabWeight
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  refine (((measurable_pi_apply i).comp hg).sqrt.pow_const 3).mul ?_
  split_ifs
  · exact ((measurable_const.div ((measurable_pi_apply j).comp hg)).sub
      measurable_const).pow_const 2
  · exact measurable_const

omit [NeZero m] in
/-- The stability weight is nonnegative. -/
lemma stabWeight_nonneg (p : simplex (Fin m)) (j : Fin m) : 0 ≤ stabWeight p j :=
  sum_nonneg fun i _ ↦ mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (by split_ifs <;> positivity)

/-! ### Auxiliary bounds for Theorem 1 -/

section Aux

/-- The harmonic sum `∑_{t < T} 1 / (t + 1) ≤ 1 + log T`. -/
lemma sum_inv_add_one_le_one_add_log (T : ℕ) :
    ∑ t ∈ range T, ((t : ℝ) + 1)⁻¹ ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  push_cast at h
  exact h

/-- **Cauchy–Schwarz**:
`∑_t (t + 1)^{-1/2} ∑_{x ∈ E} √(p_t x) ≤ √(H_T ∑_{x ∈ E} 1 / Δ_x) √(∑_t ∑_{x ∈ E} Δ_x p_t x)` with
`H_T = ∑_{t < T} 1 / (t + 1)`. -/
lemma sum_inv_sqrt_mul_sum_sqrt_le {ι : Type*} (T : ℕ) (E : Finset ι) {Δ : ι → ℝ}
    (hΔ : ∀ x ∈ E, 0 < Δ x) (p : ℕ → ι → ℝ) (hp : ∀ t x, 0 ≤ p t x) :
    ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ * ∑ x ∈ E, √(p t x)
      ≤ √((∑ t ∈ range T, ((t : ℝ) + 1)⁻¹) * ∑ x ∈ E, 1 / Δ x)
        * √(∑ t ∈ range T, ∑ x ∈ E, Δ x * p t x) := by
  have h1 : ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ * ∑ x ∈ E, √(p t x)
      = ∑ q ∈ range T ×ˢ E, ((√((q.1 : ℝ) + 1))⁻¹ * (√(Δ q.2))⁻¹) * (√(Δ q.2) * √(p q.1 q.2)) := by
    rw [sum_product]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun x hx ↦ ?_
    have : √(Δ x) ≠ 0 := (Real.sqrt_pos.2 (hΔ x hx)).ne'
    field_simp
  have h2 : ∑ q ∈ range T ×ˢ E, ((√((q.1 : ℝ) + 1))⁻¹ * (√(Δ q.2))⁻¹) ^ 2
      = (∑ t ∈ range T, ((t : ℝ) + 1)⁻¹) * ∑ x ∈ E, 1 / Δ x := by
    rw [sum_product, sum_mul_sum]
    refine sum_congr rfl fun t _ ↦ sum_congr rfl fun x hx ↦ ?_
    rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (hΔ x hx).le,
      one_div]
  have h3 : ∑ q ∈ range T ×ˢ E, (√(Δ q.2) * √(p q.1 q.2)) ^ 2
      = ∑ t ∈ range T, ∑ x ∈ E, Δ x * p t x := by
    rw [sum_product]
    refine sum_congr rfl fun t _ ↦ sum_congr rfl fun x hx ↦ ?_
    rw [mul_pow, Real.sq_sqrt (hΔ x hx).le, Real.sq_sqrt (hp t x)]
  rw [h1, ← h2, ← h3]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- **Jensen's inequality** for the square root: `E[√Z] ≤ √(E[Z])`. -/
lemma integral_sqrt_le_sqrt_integral {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω) (hZi : Integrable Z P)
    (hsi : Integrable (fun ω ↦ √(Z ω)) P) :
    ∫ ω, √(Z ω) ∂P ≤ √(∫ ω, Z ω ∂P) :=
  Real.strictConcaveOn_sqrt.concaveOn.le_map_integral Real.continuous_sqrt.continuousOn
    isClosed_Ici (ae_of_all _ hZ0) hZi hsi

variable {mx my : ℕ} [NeZero mx] [NeZero my] {u : Fin mx → Fin my → ℝ}

/-- For utilities in `[-1, 1]`, the mixed-strategy maximin value is at most `1`. -/
lemma nashValue_le_one (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) : nashValue u ≤ 1 := by
  obtain ⟨q₀⟩ := (inferInstance : Nonempty (simplex (Fin my)))
  have hle (p : simplex (Fin mx)) (q : simplex (Fin my)) : mixedUtility u p q ≤ 1 := by
    calc mixedUtility u p q ≤ ∑ x, ∑ y, (p : EuclideanSpace ℝ (Fin mx)) x
        * (q : EuclideanSpace ℝ (Fin my)) y * 1 :=
          sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦
            mul_le_mul_of_nonneg_left (hu x y).2 (mul_nonneg (p.2.1 x) (q.2.1 y))
      _ = 1 := by
        simp only [mul_one, ← mul_sum, q.2.2, p.2.2]
  have hbdd (p : simplex (Fin mx)) :
      BddBelow (Set.range fun q : simplex (Fin my) ↦ mixedUtility u p q) :=
    ⟨-∑ x, ∑ y, |u x y|, by
      rintro _ ⟨q, rfl⟩
      exact neg_le_of_abs_le (abs_mixedUtility_le p.2 q.2)⟩
  exact ciSup_le fun p ↦ (ciInf_le (hbdd p) q₀).trans (hle p q₀)

/-- For utilities in `[-1, 1]`, the pure-strategy maximin value is at least `-1`. -/
lemma neg_one_le_pureMaximin (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) : -1 ≤ pureMaximin u :=
  (le_ciInf fun y ↦ (hu 0 y).1).trans
    (le_ciSup (f := fun x ↦ ⨅ y, u x y) (Set.finite_range _).bddAbove 0)

/-- For utilities in `[-1, 1]`, `Δ^mix ≤ 2`. -/
lemma mixGap_le_two (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) : mixGap u ≤ 2 := by
  have := nashValue_le_one hu
  have := neg_one_le_pureMaximin hu
  rw [mixGap]
  linarith

end Aux

/-! ### Runs of Tsallis-INF in a repeated game -/

section Run

variable {mx my : ℕ} [NeZero mx] [NeZero my]

/-- The distribution of round `n` of Tsallis-INF after the history `h` of `n` rounds of the game
(the learner sees only its rewards). -/
noncomputable def halfDistHist (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) :
    simplex (Fin mx) :=
  dist (1 / 2) halfRate n (cumEstimate (1 / 2) halfRate n (Hist.mapFeedback Prod.snd h))

omit [NeZero my] in
/-- The distribution of Tsallis-INF is a measurable function of the history. -/
lemma measurable_halfDistHist (n : ℕ) :
    Measurable fun h : Hist Unit (Fin mx) (Fin my × ℝ) n ↦ (halfDistHist n h : Fin mx → ℝ) := by
  unfold halfDistHist
  exact measurable_coe_simplex.comp ((Bandits.TsallisINF.measurable_dist _ _ measurable_const
    ((measurable_cumEstimate _ _ n).comp (Hist.measurable_map measurable_id measurable_id
      measurable_snd n))))

omit [NeZero my] in
/-- The distributions of Tsallis-INF have positive coordinates. -/
lemma halfDistHist_pos (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) (x : Fin mx) :
    0 < halfDistHist n h x :=
  (ftrlSimplex_tsallisEntropy_half _).1 x

omit [NeZero my] in
/-- Tsallis-INF, as an uninformed player of the game, draws its action from `halfDistHist`. -/
lemma policy_ofUninformed_tsallisINFHalf (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) :
    (Player.ofUninformed (tsallisINFHalf mx) : Player (Fin mx) (Fin my)).policy n (h, ()) =
      weightedMeasure (halfDistHist n h : Fin mx → ℝ) := by
  rw [tsallisINFHalf_eq]
  rfl

variable {u : Fin mx → Fin my → ℝ} {opp : Player (Fin my) (Fin mx)}
  {R : RewardKernel (Fin mx) (Fin my)} [∀ n, IsMarkovKernel (R n)] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → Fin mx}
  {Y : ℕ → Ω → Fin my} {Rw : ℕ → Ω → ℝ}

omit [NeZero my] [IsProbabilityMeasure P] in
/-- Along a run, the distribution of round `n` is the distribution `halfDist` of the sequence
of the learner's rounds `((), x_s, r_s)`. -/
lemma halfDistHist_history (n : ℕ) (ω : Ω) :
    halfDistHist n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) =
      halfDist (fun s ↦ ((), X s ω, Rw s ω)) n := rfl

omit [IsProbabilityMeasure P] in
/-- Two a.e. nonnegative functions with the same Lebesgue integral of `ofReal` have the same
integral, and the first is integrable if the second is. -/
private lemma integrable_and_integral_eq_of_lintegral_eq {f g : Ω → ℝ}
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P) (hf : 0 ≤ᵐ[P] f)
    (hg : 0 ≤ᵐ[P] g) (hgi : Integrable g P)
    (heq : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P) :
    Integrable f P ∧ ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hfm hf).1 ?_, ?_⟩
  · rw [heq]
    exact (lintegral_ofReal_ne_top_iff_integrable hgm hg).2 hgi
  · rw [integral_eq_lintegral_of_nonneg_ae hf hfm, integral_eq_lintegral_of_nonneg_ae hg hgm, heq]

variable (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hRu : R.HasMean u)
  (hR : R.RewardsIn (Set.Icc (-1) 1))
  (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
    (Player.ofUninformed (tsallisINFHalf mx)) (gameEnv opp R) P)
include h

omit [NeZero my] in
/-- The distribution of round `t` of a run is measurable. -/
lemma measurable_halfDist_run (t : ℕ) :
    Measurable fun ω ↦ (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t : Fin mx → ℝ) := by
  have := (measurable_halfDistHist (my := my) t).comp (h.measurable_history t)
  exact this

omit [NeZero my] in
/-- The utility `f x_t y_t` of the actions of round `t` of a run is measurable. -/
lemma measurable_utility_run (t : ℕ) (f : Fin mx → Fin my → ℝ) :
    Measurable fun ω ↦ f (X t ω) (Y t ω) := by
  have hY : Measurable (Y t) := (h.measurable_feedback t).fst
  have := (measurable_of_countable (Function.uncurry f)).comp ((h.measurable_action t).prodMk hY)
  exact this

include hu hR hRu in
omit [NeZero my] in
/-- In a run, `E[1 - r_t] = E[1 - u(x_t, y_t)]` (the reward has conditional mean `u`). -/
lemma integral_one_sub_reward_run (t : ℕ) :
    Integrable (fun ω ↦ 1 - Rw t ω) P ∧
      ∫ ω, (1 - Rw t ω) ∂P = ∫ ω, (1 - u (X t ω) (Y t ω)) ∂P := by
  have hRwm : Measurable (Rw t) := (h.measurable_feedback t).snd
  have hum := measurable_utility_run h t u
  have key := h.lintegral_one_sub_gameReward_mul (measurable_of_countable _) hRu hR t
    (k := fun _ ↦ 1) measurable_const
  simp only [mul_one] at key
  refine integrable_and_integral_eq_of_lintegral_eq
    (measurable_const.sub hRwm).aestronglyMeasurable
    (measurable_const.sub hum).aestronglyMeasurable ?_
    (ae_of_all _ fun ω ↦ sub_nonneg.2 (hu _ _).2) ?_ key
  · filter_upwards [h.ae_gameReward_mem measurableSet_Icc hR t] with ω hω
    exact sub_nonneg.2 hω.2
  · refine Integrable.of_bound (measurable_const.sub hum).aestronglyMeasurable 2
      (ae_of_all _ fun ω ↦ ?_)
    have := hu (X t ω) (Y t ω)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]

include hu hR hRu in
omit [NeZero my] in
/-- **Unbiasedness of the importance-weighted estimate** (`lem:uninformed_run`): in a run,
`E[(1 - r_t) 𝟙{x_t = x} / p_t x] = E[1 - u(x, y_t)]`. -/
lemma integral_importanceWeight_run (t : ℕ) (x : Fin mx) :
    Integrable (fun ω ↦ (1 - Rw t ω) * (if X t ω = x then
        (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)⁻¹ else 0)) P ∧
      ∫ ω, (1 - Rw t ω) * (if X t ω = x then
          (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)⁻¹ else 0) ∂P
        = ∫ ω, (1 - u x (Y t ω)) ∂P := by
  have hRwm : Measurable (Rw t) := (h.measurable_feedback t).snd
  have hXm : Measurable (X t) := h.measurable_action t
  have hYm : Measurable (Y t) := (h.measurable_feedback t).fst
  have hpm := measurable_halfDist_run h t
  -- the weight `k(h, x', y) = 𝟙{x' = x} / p(h) x`
  set k : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my → ℝ≥0∞ :=
    fun q ↦ ENNReal.ofReal (if q.2.1 = x then ((halfDistHist t q.1 : Fin mx → ℝ) x)⁻¹ else 0)
    with hk
  have hkm : Measurable k := by
    refine measurable_from_prod_countable_left fun xy ↦ ?_
    simp only [hk]
    split_ifs
    · exact ENNReal.measurable_ofReal.comp
        (((measurable_pi_apply x).comp (measurable_halfDistHist t)).inv)
    · exact measurable_const
  have h1 := h.lintegral_one_sub_gameReward_mul (measurable_of_countable _) hRu hR t hkm
  have hf : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my ↦
      ENNReal.ofReal (1 - u q.2.1 q.2.2) * k q :=
    (ENNReal.measurable_ofReal.comp (measurable_const.sub
      ((measurable_of_countable (Function.uncurry u)).comp measurable_snd))).mul hkm
  have h2 := h.lintegral_gameAction_eq_sum (wt := fun n h ↦ (halfDistHist n h : Fin mx → ℝ))
    policy_ofUninformed_tsallisINFHalf (fun n h x ↦ (halfDistHist n h).2.1 x)
    (fun n h ↦ (halfDistHist n h).2.2) measurable_halfDistHist t hf
  have h3 := h.lintegral_gameAction_eq_sum (wt := fun n h ↦ (halfDistHist n h : Fin mx → ℝ))
    policy_ofUninformed_tsallisINFHalf (fun n h x ↦ (halfDistHist n h).2.1 x)
    (fun n h ↦ (halfDistHist n h).2.2) measurable_halfDistHist t
    (f := fun q ↦ ENNReal.ofReal (1 - u x q.2.2))
    (ENNReal.measurable_ofReal.comp (measurable_const.sub
      ((measurable_of_countable (u x)).comp (measurable_snd.comp measurable_snd))))
  simp only at h1 h2 h3
  refine integrable_and_integral_eq_of_lintegral_eq ?_ ?_ ?_
    (ae_of_all _ fun ω ↦ sub_nonneg.2 (hu _ _).2) ?_ ?_
  · refine Measurable.aestronglyMeasurable (hRwm.const_sub 1 |>.mul ?_)
    refine Measurable.ite (hXm (measurableSet_singleton x)) ?_ measurable_const
    exact ((measurable_pi_apply x).comp hpm).inv
  · exact (measurable_const.sub ((measurable_of_countable (u x)).comp hYm)).aestronglyMeasurable
  · filter_upwards [h.ae_gameReward_mem measurableSet_Icc hR t] with ω hω
    refine mul_nonneg (sub_nonneg.2 hω.2) ?_
    split_ifs
    · exact inv_nonneg.2 (halfDist_pos (fun s ↦ ((), X s ω, Rw s ω)) t x).le
    · exact le_rfl
  · refine Integrable.of_bound
      (measurable_const.sub ((measurable_of_countable (u x)).comp hYm)).aestronglyMeasurable 2
      (ae_of_all _ fun ω ↦ ?_)
    have := hu x (Y t ω)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  · have e1 : ∀ ω, ENNReal.ofReal ((1 - Rw t ω) * (if X t ω = x then
        (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)⁻¹ else 0)) =
        ENNReal.ofReal (1 - Rw t ω) *
          k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω, X t ω, Y t ω) := by
      intro ω
      have hnn : 0 ≤ (if X t ω = x then
          (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)⁻¹ else 0) := by
        split_ifs
        exacts [inv_nonneg.2 (halfDist_pos (fun s ↦ ((), X s ω, Rw s ω)) t x).le, le_rfl]
      rw [ENNReal.ofReal_mul' hnn]
      rfl
    simp_rw [e1]
    rw [h1, h2, h3]
    refine lintegral_congr fun ω ↦ ?_
    set p := halfDistHist t (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω)
    have hpx : 0 < p x := halfDistHist_pos _ _ _
    have hsum : ∑ x', ENNReal.ofReal (p x') = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x' _ ↦ p.2.1 x'), p.2.2, ENNReal.ofReal_one]
    rw [← sum_mul, hsum, one_mul, sum_eq_single x (fun b _ hb ↦ by simp [hk, hb]) (by simp)]
    simp only [hk, ite_true]
    rw [mul_comm (ENNReal.ofReal (1 - u x _)), ← mul_assoc, ← ENNReal.ofReal_mul hpx.le,
      mul_inv_cancel₀ hpx.ne', ENNReal.ofReal_one, one_mul]

include hu hR hRu in
omit [NeZero my] in
/-- **Unbiasedness of the estimates** (`lem:uninformed_run`): in a run against an adaptive
adversary, the expected regret of a round against `x` for the estimates is the expected regret
`E[u(x, y_t) - u(x_t, y_t)]`. -/
lemma integral_inner_halfEstimate_run (t : ℕ) (x : Fin mx) :
    Integrable (fun ω ↦ ⟪EuclideanSpace.single x (1 : ℝ)
        - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t,
        halfEstimate (fun s ↦ ((), X s ω, Rw s ω)) t⟫) P ∧
      ∫ ω, ⟪EuclideanSpace.single x (1 : ℝ) - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t,
          halfEstimate (fun s ↦ ((), X s ω, Rw s ω)) t⟫ ∂P
        = ∫ ω, (u x (Y t ω) - u (X t ω) (Y t ω)) ∂P := by
  obtain ⟨hi1, he1⟩ := integral_one_sub_reward_run hu hRu hR h t
  obtain ⟨hi2, he2⟩ := integral_importanceWeight_run hu hRu hR h t x
  have hYm : Measurable (Y t) := (h.measurable_feedback t).fst
  have hum := measurable_utility_run h t u
  have hbdd {g : Ω → ℝ} (hg : Measurable g) (hgb : ∀ ω, g ω ∈ Set.Icc (-1) 1) :
      Integrable (fun ω ↦ 1 - g ω) P := by
    refine Integrable.of_bound (measurable_const.sub hg).aestronglyMeasurable 2
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hgb ω).1, (hgb ω).2]
  have hi3 := hbdd hum fun ω ↦ hu _ _
  have hi4 : Integrable (fun ω ↦ 1 - u x (Y t ω)) P :=
    hbdd (g := fun ω ↦ u x (Y t ω)) ((measurable_of_countable (u x)).comp hYm) fun ω ↦ hu _ _
  have heq : (fun ω ↦ ⟪EuclideanSpace.single x (1 : ℝ)
      - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t,
      halfEstimate (fun s ↦ ((), X s ω, Rw s ω)) t⟫) = fun ω ↦ (1 - Rw t ω)
        - (1 - Rw t ω) * (if X t ω = x then
          (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)⁻¹ else 0) :=
    funext fun ω ↦ inner_single_sub_estimate _ (halfDist_pos _ t) _ x
  rw [heq]
  refine ⟨hi1.sub hi2, ?_⟩
  rw [integral_sub hi1 hi2, he1, he2, ← integral_sub hi3 hi4]
  congr 1
  ext ω
  ring

omit [NeZero my] in
/-- **Conditional law of the action** (`lem:uninformed_run`): in a run, `E[f(x_t)]` is
`E[∑ x, p_t x f(x)]` for every `f ≥ 0`. -/
lemma integral_comp_action_run (t : ℕ) {f : Fin mx → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∫ ω, f (X t ω) ∂P =
      ∫ ω, ∑ x, halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x * f x ∂P := by
  have hXm : Measurable (X t) := h.measurable_action t
  have hpm := measurable_halfDist_run h t
  have key := h.lintegral_gameAction_eq_sum (wt := fun n h ↦ (halfDistHist n h : Fin mx → ℝ))
    policy_ofUninformed_tsallisINFHalf (fun n h x ↦ (halfDistHist n h).2.1 x)
    (fun n h ↦ (halfDistHist n h).2.2) measurable_halfDistHist t
    (f := fun q ↦ ENNReal.ofReal (f q.2.1)) (measurable_of_countable _ |>.comp
      (measurable_fst.comp measurable_snd) |> ENNReal.measurable_ofReal.comp)
  simp only at key
  have hf2 : Measurable fun ω ↦ ∑ x, halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x * f x :=
    Finset.measurable_sum _ fun x _ ↦ ((measurable_pi_apply x).comp hpm).mul measurable_const
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ hf _)
      ((measurable_of_countable f).comp hXm).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ sum_nonneg fun x _ ↦
      mul_nonneg (simplex.nonneg _ x) (hf x)) hf2.aestronglyMeasurable, key]
  congr 1
  refine lintegral_congr fun ω ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun x _ ↦ mul_nonneg (simplex.nonneg _ x) (hf x)]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [ENNReal.ofReal_mul (simplex.nonneg _ x)]
  rfl

omit [NeZero my] in
/-- **Conditional expectation of the stability weight**: in a run, `E[w(p_t, x_t)]` is
`E[∑ i, √(p_t i) (1 - p_t i)]`. -/
lemma integral_stabWeight_run (t : ℕ) :
    Integrable (fun ω ↦ stabWeight (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) (X t ω)) P ∧
      ∫ ω, stabWeight (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) (X t ω) ∂P
        = ∫ ω, ∑ i, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i)
            * (1 - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i) ∂P := by
  have hXm : Measurable (X t) := h.measurable_action t
  have hpm := measurable_halfDist_run h t
  have hfm : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my ↦
      ENNReal.ofReal (stabWeight (halfDistHist t q.1) q.2.1) := by
    refine measurable_from_prod_countable_left fun xy ↦ ?_
    exact ENNReal.measurable_ofReal.comp (measurable_stabWeight (measurable_halfDistHist t) xy.1)
  have key := h.lintegral_gameAction_eq_sum (wt := fun n h ↦ (halfDistHist n h : Fin mx → ℝ))
    policy_ofUninformed_tsallisINFHalf (fun n h x ↦ (halfDistHist n h).2.1 x)
    (fun n h ↦ (halfDistHist n h).2.2) measurable_halfDistHist t hfm
  simp only at key
  have hgm : Measurable fun ω ↦ ∑ i, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i)
      * (1 - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i) :=
    Finset.measurable_sum _ fun i _ ↦ ((measurable_pi_apply i).comp hpm).sqrt.mul
      (measurable_const.sub ((measurable_pi_apply i).comp hpm))
  have hg0 (ω : Ω) : 0 ≤ ∑ i, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i)
      * (1 - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i) :=
    sum_nonneg fun i _ ↦ mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 (simplex.le_one _ i))
  refine integrable_and_integral_eq_of_lintegral_eq ?_ hgm.aestronglyMeasurable
    (ae_of_all _ fun ω ↦ stabWeight_nonneg _ _) (ae_of_all _ hg0) ?_ ?_
  · have hw : Measurable fun q : Ω × Fin mx ↦
        stabWeight (halfDist (fun s ↦ ((), X s q.1, Rw s q.1)) t) q.2 :=
      measurable_from_prod_countable_left fun j ↦ measurable_stabWeight hpm j
    exact (hw.comp (measurable_id.prodMk hXm)).aestronglyMeasurable
  · refine Integrable.of_bound hgm.aestronglyMeasurable mx (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
    calc _ ≤ ∑ _i : Fin mx, (1 : ℝ) := sum_le_sum fun i _ ↦ by
          have h1 := simplex.le_one (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) i
          have h0 := simplex.nonneg (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) i
          have : √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i) ≤ 1 := Real.sqrt_le_one.2 h1
          nlinarith [Real.sqrt_nonneg (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t i)]
      _ = mx := by simp
  · change ∫⁻ ω, ENNReal.ofReal (stabWeight (halfDistHist t
        (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω)) (X t ω)) ∂P = _
    rw [key]
    refine lintegral_congr fun ω ↦ ?_
    set p := halfDistHist t (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω)
    simp_rw [← ENNReal.ofReal_mul (p.2.1 _)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ mul_nonneg (p.2.1 x) (stabWeight_nonneg _ _)]
    congr 1
    exact sum_mul_stabilityWeight p (halfDistHist_pos t _)

include hu hR hRu in
omit [NeZero my] in
/-- **Tsallis-INF, self-bounding form** (`lem:tsallis_inf_self_bound`; Ito et al. 2025,
Theorem 1, with the constants of this proof): against an adaptive adversary, for every arm `x₀`,
`ER_T(x₀) ≤ 12 E[∑_{t < T} (t + 1)^{-1/2} ∑_{x ≠ x₀} √(p_t x)] + 6`. -/
lemma externalRegretAgainst_tsallisINFHalf_le (T : ℕ) (x₀ : Fin mx) :
    externalRegretAgainst u X Y P T x₀ ≤
      12 * ∫ ω, ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ *
        ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) ∂P + 6 := by
  set S : ℕ → Ω → ℝ := fun t ω ↦
    ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) with hS
  set W : ℕ → Ω → ℝ := fun t ω ↦
    stabWeight (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) (X t ω) with hW
  set B : ℕ → Ω → ℝ := fun t ω ↦ if t < 3 then 2 else 4 / √((t : ℝ) + 1) * W t ω with hB
  set L : ℕ → Ω → ℝ := fun t ω ↦ ⟪EuclideanSpace.single x₀ (1 : ℝ)
    - halfDist (fun s ↦ ((), X s ω, Rw s ω)) t, halfEstimate (fun s ↦ ((), X s ω, Rw s ω)) t⟫
    with hL
  have hSm (t : ℕ) : Measurable (S t) := Finset.measurable_sum _ fun x _ ↦
    ((measurable_pi_apply x).comp (measurable_halfDist_run h t)).sqrt
  have hS0 (t : ℕ) (ω : Ω) : 0 ≤ S t ω := sum_nonneg fun x _ ↦ Real.sqrt_nonneg _
  have hSle (t : ℕ) (ω : Ω) : S t ω ≤ mx := by
    calc S t ω ≤ ∑ _x ∈ univ.erase x₀, (1 : ℝ) := sum_le_sum fun x _ ↦
          Real.sqrt_le_one.2 (simplex.le_one _ x)
      _ ≤ ∑ _x : Fin mx, (1 : ℝ) := sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          fun _ _ _ ↦ zero_le_one
      _ = mx := by simp
  have hSi (t : ℕ) : Integrable (S t) P :=
    Integrable.of_bound (hSm t).aestronglyMeasurable mx (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hS0 t ω)]
      exact hSle t ω)
  have hWi (t : ℕ) : Integrable (W t) P := (integral_stabWeight_run h t).1
  have hWS (t : ℕ) : ∫ ω, W t ω ∂P ≤ 2 * ∫ ω, S t ω ∂P := by
    rw [(integral_stabWeight_run h t).2, ← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_) ((hSi t).const_mul 2)
      (ae_of_all _ fun ω ↦ sum_sqrt_mul_one_sub_le _ x₀)
    exact sum_nonneg fun i _ ↦ mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 (simplex.le_one _ i))
  have hBi (t : ℕ) : Integrable (B t) P := by
    by_cases ht : t < 3
    · simp only [hB, ht, ite_true]
      exact integrable_const _
    · simp only [hB, ht, ite_false]
      exact (hWi t).const_mul _
  have hBle (t : ℕ) : ∫ ω, B t ω ∂P
      ≤ (if t < 3 then 2 else 0) + 8 / √((t : ℝ) + 1) * ∫ ω, S t ω ∂P := by
    have hI : 0 ≤ ∫ ω, S t ω ∂P := integral_nonneg fun ω ↦ hS0 t ω
    have hc : 0 ≤ 8 / √((t : ℝ) + 1) := by positivity
    by_cases ht : t < 3
    · simp only [hB, ht, ite_true, integral_const, probReal_univ, smul_eq_mul, one_mul]
      nlinarith
    · simp only [hB, ht, ite_false, zero_add]
      rw [integral_const_mul]
      have h4 : 0 ≤ 4 / √((t : ℝ) + 1) := by positivity
      calc 4 / √((t : ℝ) + 1) * ∫ ω, W t ω ∂P ≤ 4 / √((t : ℝ) + 1) * (2 * ∫ ω, S t ω ∂P) :=
            mul_le_mul_of_nonneg_left (hWS t) h4
        _ = 8 / √((t : ℝ) + 1) * ∫ ω, S t ω ∂P := by ring
  have hLi (t : ℕ) : Integrable (L t) P := (integral_inner_halfEstimate_run hu hRu hR h t x₀).1
  have hpath : ∀ᵐ ω ∂P, ∑ t ∈ range T, L t ω
      ≤ ∑ t ∈ range T, (4 / √((t : ℝ) + 1) * S t ω + B t ω) := by
    filter_upwards [ae_all_iff.2 fun t ↦ h.ae_gameReward_mem measurableSet_Icc hR t] with ω hω
    exact sum_inner_halfEstimate_le (fun s ↦ ((), X s ω, Rw s ω)) hω x₀ T
  have hER : externalRegretAgainst u X Y P T x₀ = ∑ t ∈ range T, ∫ ω, L t ω ∂P := by
    rw [externalRegretAgainst, integral_finsetSum _ fun t _ ↦ ?_]
    · exact sum_congr rfl fun t _ ↦ ((integral_inner_halfEstimate_run hu hRu hR h t x₀).2).symm
    · have hum := measurable_utility_run h t u
      have hYm : Measurable (Y t) := (h.measurable_feedback t).fst
      refine Integrable.of_bound
        (((measurable_of_countable (u x₀)).comp hYm).sub hum).aestronglyMeasurable 2
        (ae_of_all _ fun ω ↦ ?_)
      have h1 := hu x₀ (Y t ω)
      have h2 := hu (X t ω) (Y t ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hTi (t : ℕ) : Integrable (fun ω ↦ 4 / √((t : ℝ) + 1) * S t ω + B t ω) P :=
    ((hSi t).const_mul _).add (hBi t)
  have hUi (t : ℕ) : Integrable (fun ω ↦ (√((t : ℝ) + 1))⁻¹ * S t ω) P := (hSi t).const_mul _
  have hVi (t : ℕ) : Integrable (fun ω ↦ 4 / √((t : ℝ) + 1) * S t ω) P := (hSi t).const_mul _
  rw [hER, ← integral_finsetSum _ fun t _ ↦ hLi t]
  calc ∫ ω, ∑ t ∈ range T, L t ω ∂P
      ≤ ∫ ω, ∑ t ∈ range T, (4 / √((t : ℝ) + 1) * S t ω + B t ω) ∂P :=
        integral_mono_ae (integrable_finsetSum _ fun t _ ↦ hLi t)
          (integrable_finsetSum _ fun t _ ↦ hTi t) hpath
    _ = ∑ t ∈ range T, (4 / √((t : ℝ) + 1) * ∫ ω, S t ω ∂P + ∫ ω, B t ω ∂P) := by
        rw [integral_finsetSum _ fun t _ ↦ hTi t]
        refine sum_congr rfl fun t _ ↦ ?_
        rw [integral_add (hVi t) (hBi t), integral_const_mul]
    _ ≤ ∑ t ∈ range T, (4 / √((t : ℝ) + 1) * ∫ ω, S t ω ∂P
          + ((if t < 3 then 2 else 0) + 8 / √((t : ℝ) + 1) * ∫ ω, S t ω ∂P)) :=
        sum_le_sum fun t _ ↦ by linarith [hBle t]
    _ = 12 * ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ * ∫ ω, S t ω ∂P
          + ∑ t ∈ range T, (if t < 3 then (2 : ℝ) else 0) := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun t _ ↦ ?_
        ring
    _ ≤ 12 * ∫ ω, ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ * S t ω ∂P + 6 := by
        rw [integral_finsetSum _ fun t _ ↦ hUi t]
        simp_rw [integral_const_mul]
        linarith [sum_ite_lt_three_le T]

include hu hR hRu in
omit [NeZero my] in
/-- **Tsallis-INF, worst case** (`lem:tsallis_inf_worst`; Zimmert, Seldin 2021, Theorem 1, with
the constants of this proof): against an adaptive adversary, `ER_T ≤ 24 √(m_x T) + 6`. -/
lemma externalRegret_tsallisINFHalf_le (T : ℕ) :
    externalRegret u X Y P T ≤ 24 * √((mx : ℝ) * T) + 6 := by
  refine ciSup_le fun x₀ ↦ (externalRegretAgainst_tsallisINFHalf_le hu hRu hR h T x₀).trans ?_
  have hpm := measurable_halfDist_run h
  have hle (ω : Ω) : ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ *
      ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)
        ≤ 2 * √((mx : ℝ) * T) := by
    calc _ ≤ ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ * √(mx : ℝ) := sum_le_sum fun t _ ↦ by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc _ ≤ ∑ x, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) :=
                sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
                  fun _ _ _ ↦ Real.sqrt_nonneg _
            _ ≤ √(Fintype.card (Fin mx) : ℝ) := sum_sqrt_le_sqrt_card (halfDist _ t).2
            _ = √(mx : ℝ) := by simp
      _ = (∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹) * √(mx : ℝ) := by rw [sum_mul]
      _ ≤ 2 * √(T : ℝ) * √(mx : ℝ) :=
          mul_le_mul_of_nonneg_right (sum_inv_sqrt_le T) (Real.sqrt_nonneg _)
      _ = 2 * √((mx : ℝ) * T) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _)]
          ring
  have hint : ∫ ω, ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ *
      ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) ∂P
        ≤ 2 * √((mx : ℝ) * T) := by
    have := integral_mono_of_nonneg (μ := P)
      (f := fun ω ↦ ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ *
        ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x))
      (ae_of_all _ fun ω ↦ sum_nonneg fun t _ ↦ mul_nonneg (by positivity)
        (sum_nonneg fun x _ ↦ Real.sqrt_nonneg _))
      (integrable_const (2 * √((mx : ℝ) * T))) (ae_of_all _ hle)
    simpa using this
  linarith

include hu hR hRu in
omit [NeZero my] in
/-- **Toward the strict-PSNE bound of Theorem 1.** For a strict PSNE `(x₀, y₀)`, the
self-bounding bound, Cauchy–Schwarz, Jensen's inequality and
`E[∑_t Δʳ_{x_t}] ≤ ER_T(x₀) + 4 E[#{t < T : y_t ≠ y₀}]` give
`ER_T(x₀) ≤ 12 √(H_T ∑_{x ≠ x₀} 1 / Δʳ_x) √(ER_T(x₀) + 4 E[#{t < T : y_t ≠ y₀}]) + 6`, with
`H_T = ∑_{t < T} 1 / (t + 1)`. -/
lemma externalRegretAgainst_le_of_isStrictPSNE {x₀ : Fin mx} {y₀ : Fin my}
    (hxy : IsStrictPSNE u x₀ y₀) (T : ℕ) :
    externalRegretAgainst u X Y P T x₀ ≤
      12 * √((∑ t ∈ range T, ((t : ℝ) + 1)⁻¹) * ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x)
        * √(externalRegretAgainst u X Y P T x₀
          + 4 * P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1]) + 6 := by
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hΔ (x : Fin mx) (hx : x ∈ univ.erase x₀) : 0 < rowGap u x₀ y₀ x :=
    hxy.rowGap_pos (ne_of_mem_erase hx)
  have hΔ0 (x : Fin mx) : 0 ≤ rowGap u x₀ y₀ x := by
    by_cases hx : x = x₀
    · simp [rowGap, hx]
    · exact (hxy.rowGap_pos hx).le
  have hΔ2 (x : Fin mx) : rowGap u x₀ y₀ x ≤ 2 := by
    simp only [rowGap]
    linarith [(hu x₀ y₀).2, (hu x y₀).1]
  have hpm := measurable_halfDist_run h (mx := mx)
  set Z : Ω → ℝ := fun ω ↦ ∑ t ∈ range T, ∑ x ∈ univ.erase x₀,
    rowGap u x₀ y₀ x * halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x with hZ
  have hZ0 (ω : Ω) : 0 ≤ Z ω := sum_nonneg fun t _ ↦ sum_nonneg fun x _ ↦
    mul_nonneg (hΔ0 x) (simplex.nonneg _ x)
  have hZm : Measurable Z := Finset.measurable_sum _ fun t _ ↦ Finset.measurable_sum _
    fun x _ ↦ measurable_const.mul ((measurable_pi_apply x).comp (hpm t))
  have hZb (ω : Ω) : Z ω ≤ 2 * T * mx := by
    calc Z ω ≤ ∑ _t ∈ range T, ∑ _x ∈ univ.erase x₀, (2 : ℝ) :=
          sum_le_sum fun t _ ↦ sum_le_sum fun x _ ↦ by
            have := simplex.le_one (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) x
            have := simplex.nonneg (halfDist (fun s ↦ ((), X s ω, Rw s ω)) t) x
            nlinarith [hΔ0 x, hΔ2 x]
      _ ≤ ∑ _t ∈ range T, ∑ _x : Fin mx, (2 : ℝ) := sum_le_sum fun t _ ↦
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ ↦ by norm_num
      _ = 2 * T * mx := by simp; ring
  have hZi : Integrable Z P := Integrable.of_bound hZm.aestronglyMeasurable (2 * T * mx)
    (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]; exact hZb ω)
  have hsZi : Integrable (fun ω ↦ √(Z ω)) P :=
    Integrable.of_bound hZm.sqrt.aestronglyMeasurable √(2 * T * mx)
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hZb ω))
  set HS := (∑ t ∈ range T, ((t : ℝ) + 1)⁻¹) * ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x
  have h1 := externalRegretAgainst_tsallisINFHalf_le hu hRu hR h T x₀
  have h2 (ω : Ω) : ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ *
      ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) ≤ √HS * √(Z ω) :=
    sum_inv_sqrt_mul_sum_sqrt_le T _ hΔ (fun t x ↦ halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x)
      fun t x ↦ simplex.nonneg _ x
  have h3 : ∫ ω, ∑ t ∈ range T, (√((t : ℝ) + 1))⁻¹ *
      ∑ x ∈ univ.erase x₀, √(halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) ∂P
        ≤ √HS * ∫ ω, √(Z ω) ∂P := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sum_nonneg fun t _ ↦
      mul_nonneg (by positivity) (sum_nonneg fun x _ ↦ Real.sqrt_nonneg _))
      (hsZi.const_mul _) (ae_of_all _ h2)
  have h4 := integral_sqrt_le_sqrt_integral hZ0 hZi hsZi
  have h5 : ∫ ω, Z ω ∂P = P[fun ω ↦ ∑ t ∈ range T, rowGap u x₀ y₀ (X t ω)] := by
    have hi1 (t : ℕ) : Integrable (fun ω ↦ ∑ x ∈ univ.erase x₀,
        rowGap u x₀ y₀ x * halfDist (fun s ↦ ((), X s ω, Rw s ω)) t x) P := by
      refine integrable_finsetSum _ fun x _ ↦ (Integrable.of_bound
        ((measurable_pi_apply x).comp (hpm t)).aestronglyMeasurable 1
        (ae_of_all _ fun ω ↦ ?_)).const_mul _
      simp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (simplex.nonneg _ x)]
      exact simplex.le_one _ x
    have hi2 (t : ℕ) : Integrable (fun ω ↦ rowGap u x₀ y₀ (X t ω)) P :=
      Integrable.of_bound
        ((measurable_of_countable (rowGap u x₀ y₀)).comp (hX t)).aestronglyMeasurable 2
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hΔ0 _)]; exact hΔ2 _)
    rw [integral_finsetSum _ fun t _ ↦ hi1 t, integral_finsetSum _ fun t _ ↦ hi2 t]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [integral_comp_action_run h t hΔ0]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only
    rw [← add_sum_erase _ _ (mem_univ x₀)]
    simp only [rowGap, sub_self, mul_zero, zero_add]
    exact sum_congr rfl fun x _ ↦ mul_comm _ _
  have h6 := IsPSNE.integral_sum_rowGap_sub_le (P := P) hxy.isPSNE hu hX hY T
  have hHS : 0 ≤ HS := mul_nonneg (sum_nonneg fun t _ ↦ by positivity)
    (sum_nonneg fun x hx ↦ (one_div_pos.2 (hΔ x hx)).le)
  calc externalRegretAgainst u X Y P T x₀
      ≤ 12 * (√HS * ∫ ω, √(Z ω) ∂P) + 6 := by linarith
    _ ≤ 12 * (√HS * √(externalRegretAgainst u X Y P T x₀
          + 4 * P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1])) + 6 := by
        gcongr
        exact h4.trans (Real.sqrt_le_sqrt (by linarith))
    _ = _ := by ring

/-! ### The three bounds of Theorem 1 -/

include hu hR hRu in
/-- `PSMR_T ≤ ER_T - Δ^mix T ≤ 24 √(m_x T) + 6 - Δ^mix T`. -/
lemma psmr_tsallisINFHalf_le_sub (T : ℕ) :
    psmr u X Y P T ≤ 24 * √((mx : ℝ) * T) + 6 - mixGap u * T := by
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hNR := nashRegret_eq_psmr_add (P := P) (u := u) hX hY T
  have hNE := nashRegret_le_externalRegret (P := P) (u := u) hX hY T
  have hER := externalRegret_tsallisINFHalf_le hu hRu hR h T
  linarith

include hu hR hRu in
/-- **Theorem 1, worst case**: `PSMR_T ≤ 30 √(m_x T)`. -/
lemma psmr_tsallisINFHalf_le_sqrt (T : ℕ) : psmr u X Y P T ≤ 30 * √((mx : ℝ) * T) := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [psmr]
  have hmx : (1 : ℝ) ≤ mx := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne mx))
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.2 hT
  have h1 : (1 : ℝ) ≤ √((mx : ℝ) * T) :=
    Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le hmx hT1)
  have h2 := psmr_tsallisINFHalf_le_sub hu hRu hR h T
  have h3 : 0 ≤ mixGap u * T := mul_nonneg (mixGap_nonneg u) (Nat.cast_nonneg T)
  linarith

include hu hR hRu in
/-- **Theorem 1, positive `Δ^mix`**: `PSMR_T ≤ 156 m_x / Δ^mix` (Lemma 7 and `Δ^mix ≤ 2`). -/
lemma psmr_tsallisINFHalf_le_of_mixGap_pos (hΔ : 0 < mixGap u) (T : ℕ) :
    psmr u X Y P T ≤ 156 * mx / mixGap u := by
  have hmx : (1 : ℝ) ≤ mx := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne mx))
  have h1 := psmr_tsallisINFHalf_le_sub hu hRu hR h T
  have h7 := (sqrt_mul_sub_mul_le (576 * mx) (mixGap u) (by linarith) hΔ).1 T (Nat.cast_nonneg T)
  have hsq : √(576 * mx * (T : ℝ)) = 24 * √((mx : ℝ) * T) := by
    rw [show (576 : ℝ) * mx * T = 24 ^ 2 * (mx * T) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h2 := mixGap_le_two hu
  have h3 : 6 ≤ 12 * mx / mixGap u := by
    rw [le_div_iff₀ hΔ]
    nlinarith
  have h4 : 576 * mx / (4 * mixGap u) = 144 * mx / mixGap u := by
    field_simp
    ring
  have h5 : 144 * mx / mixGap u + 12 * mx / mixGap u = 156 * mx / mixGap u := by
    rw [← add_div]
    ring
  rw [hsq, h4] at h7
  linarith

include hu hR hRu in
omit [NeZero my] in
/-- **Theorem 1, strict PSNE**: for a strict PSNE `(x₀, y₀)`,
`PSMR_T ≤ 144 H_T S (1 + 1 / Δᶜ_min) + 12` with `H_T = ∑_{t < T} 1 / (t + 1)` and
`S = ∑_{x ≠ x₀} 1 / Δʳ_x` (Lemmas 7 and 8). -/
lemma psmr_tsallisINFHalf_le_of_isStrictPSNE' {x₀ : Fin mx} {y₀ : Fin my}
    (hxy : IsStrictPSNE u x₀ y₀) (T : ℕ) :
    psmr u X Y P T ≤ 144 * (∑ t ∈ range T, ((t : ℝ) + 1)⁻¹)
        * (∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x) * (1 + 1 / colGapMin u x₀ y₀) + 12 := by
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hcol := IsStrictPSNE.colGapMin_mul_le (P := P) hxy hX hY T
  have hself := externalRegretAgainst_le_of_isStrictPSNE hu hRu hR h hxy T
  have h6 := IsPSNE.integral_sum_rowGap_sub_le (P := P) hxy.isPSNE hu hX hY T
  generalize hA : externalRegretAgainst u X Y P T x₀ = A at hcol hself h6
  generalize hCy : P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] = Cy
    at hcol hself h6
  generalize hH : ∑ t ∈ range T, ((t : ℝ) + 1)⁻¹ = H at hself
  generalize hS : ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x = S at hself
  have hCy0 : 0 ≤ Cy := by
    rw [← hCy]
    exact integral_nonneg fun ω ↦ sum_nonneg fun t _ ↦ by split_ifs <;> norm_num
  have hΔc0 : 0 ≤ colGapMin u x₀ y₀ := Real.iInf_nonneg fun y ↦ (hxy.colGap_pos y.2).le
  have hH0 : 0 ≤ H := by
    rw [← hH]
    exact sum_nonneg fun t _ ↦ by positivity
  have hS0 : 0 ≤ S := by
    rw [← hS]
    exact sum_nonneg fun x hx ↦ (one_div_pos.2 (hxy.rowGap_pos (ne_of_mem_erase hx))).le
  have hZ0 : 0 ≤ P[fun ω ↦ ∑ t ∈ range T, rowGap u x₀ y₀ (X t ω)] :=
    integral_nonneg fun ω ↦ sum_nonneg fun t _ ↦ by
      by_cases hx : X t ω = x₀
      · simp [rowGap, hx]
      · exact (hxy.rowGap_pos hx).le
  -- `√(576 H S C) - Δᶜ_min C ≤ 144 H S / Δᶜ_min`
  have hsq : √(576 * H * S * Cy) - colGapMin u x₀ y₀ * Cy
      ≤ 144 * H * S * (1 / colGapMin u x₀ y₀) := by
    rcases hΔc0.lt_or_eq with hpos | hzero
    · rcases (mul_nonneg hH0 hS0).lt_or_eq with hHS | hHS
      · have h7 := (sqrt_mul_sub_mul_le (576 * H * S) (colGapMin u x₀ y₀)
          (by rw [mul_assoc]; exact mul_pos (by norm_num) hHS) hpos).1 Cy hCy0
        calc √(576 * H * S * Cy) - colGapMin u x₀ y₀ * Cy
            ≤ 576 * H * S / (4 * colGapMin u x₀ y₀) := h7
          _ = 144 * H * S * (1 / colGapMin u x₀ y₀) := by field_simp; ring
      · rw [show 576 * H * S * Cy = 576 * (H * S) * Cy by ring, ← hHS]
        simp only [mul_zero, zero_mul, Real.sqrt_zero, zero_sub]
        have : 0 ≤ colGapMin u x₀ y₀ * Cy := mul_nonneg hΔc0 hCy0
        have : 0 ≤ 144 * H * S * (1 / colGapMin u x₀ y₀) := by positivity
        linarith
    · -- `Δᶜ_min = 0`: the adversary has a single action and `C = 0`
      have hy (y : Fin my) : y = y₀ := by
        by_contra hne
        have : Nonempty {y' // y' ≠ y₀} := ⟨⟨y, hne⟩⟩
        obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun y' : {y' // y' ≠ y₀} ↦
          colGap u x₀ y₀ y')
        have := hxy.colGap_pos i.2
        rw [hi] at this
        exact absurd hzero (ne_of_lt this)
      have hC0 : Cy = 0 := by
        rw [← hCy]
        have : ∀ t ω, Y t ω = y₀ := fun t ω ↦ hy _
        simp [this]
      rw [hC0, ← hzero]
      simp
  by_cases hA0 : A < 0
  · have : 0 ≤ 144 * H * S * (1 + 1 / colGapMin u x₀ y₀) := by positivity
    nlinarith [mul_nonneg hΔc0 hCy0]
  push Not at hA0
  have hAC : 0 ≤ A + 4 * Cy := by linarith
  have hroot : 12 * √(H * S) * √(A + 4 * Cy) = √(144 * H * S * A + 576 * H * S * Cy) := by
    rw [show 144 * H * S * A + 576 * H * S * Cy = 12 ^ 2 * (H * S) * (A + 4 * Cy) by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 12 ^ 2 * (H * S)) (A + 4 * Cy),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12 ^ 2) (H * S),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12)]
  have h8 := le_add_sqrt_add_of_le_sqrt_add hA0 (by positivity : 0 ≤ 144 * H * S)
    (by positivity : 0 ≤ 576 * H * S * Cy) (by norm_num : (0 : ℝ) ≤ 6)
    (by rw [← hroot]; linarith)
  have : 144 * H * S * (1 + 1 / colGapMin u x₀ y₀)
      = 144 * H * S + 144 * H * S * (1 / colGapMin u x₀ y₀) := by ring
  linarith

include hu hR hRu in
omit [NeZero my] in
/-- **Theorem 1, strict PSNE**: for a strict PSNE `(x₀, y₀)`,
`PSMR_T ≤ 168 (1 + 1 / Δᶜ_min) ∑_{x ≠ x₀} (1 + log T) / Δʳ_x`. -/
lemma psmr_tsallisINFHalf_le_of_isStrictPSNE {x₀ : Fin mx} {y₀ : Fin my}
    (hxy : IsStrictPSNE u x₀ y₀) (T : ℕ) :
    psmr u X Y P T ≤ 168 * (1 + 1 / colGapMin u x₀ y₀) *
      ∑ x ∈ univ.erase x₀, (1 + Real.log T) / rowGap u x₀ y₀ x := by
  have hkey := psmr_tsallisINFHalf_le_of_isStrictPSNE' hu hRu hR h hxy T
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hΔ (x : Fin mx) (hx : x ∈ univ.erase x₀) : 0 < rowGap u x₀ y₀ x :=
    hxy.rowGap_pos (ne_of_mem_erase hx)
  have hsumeq : ∑ x ∈ univ.erase x₀, (1 + Real.log T) / rowGap u x₀ y₀ x
      = (1 + Real.log T) * ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ ↦ by ring
  rw [hsumeq]
  have hΔc0 : 0 ≤ colGapMin u x₀ y₀ := Real.iInf_nonneg fun y ↦ (hxy.colGap_pos y.2).le
  have hK : 1 ≤ 1 + 1 / colGapMin u x₀ y₀ := le_add_of_nonneg_right (one_div_nonneg.2 hΔc0)
  have hlog : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have hHlog := sum_inv_add_one_le_one_add_log T
  have hH0 : 0 ≤ ∑ t ∈ range T, ((t : ℝ) + 1)⁻¹ := sum_nonneg fun t _ ↦ by positivity
  by_cases hE : univ.erase x₀ = ∅
  · -- a single action: `ER_T(x₀) = 0` and `PSMR_T ≤ 0`
    have hx (x : Fin mx) : x = x₀ := by
      by_contra hne
      have : x ∈ univ.erase x₀ := mem_erase.2 ⟨hne, mem_univ x⟩
      rw [hE] at this
      exact absurd this (notMem_empty x)
    have hcol := IsStrictPSNE.colGapMin_mul_le (P := P) hxy hX hY T
    have hA0 : externalRegretAgainst u X Y P T x₀ = 0 := by
      have : ∀ t ω, X t ω = x₀ := fun t ω ↦ hx _
      simp [externalRegretAgainst, this]
    have hCy0 : 0 ≤ P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] :=
      integral_nonneg fun ω ↦ sum_nonneg fun t _ ↦ by split_ifs <;> norm_num
    rw [hE, sum_empty, mul_zero, mul_zero]
    nlinarith [mul_nonneg hΔc0 hCy0]
  -- several actions: `∑_{x ≠ x₀} 1 / Δʳ_x ≥ 1/2`
  obtain ⟨x₁, hx₁⟩ := nonempty_iff_ne_empty.2 hE
  have hS1 : 1 / 2 ≤ ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x := by
    have h2 : rowGap u x₀ y₀ x₁ ≤ 2 := by
      simp only [rowGap]
      linarith [(hu x₀ y₀).2, (hu x₁ y₀).1]
    calc (1 : ℝ) / 2 ≤ 1 / rowGap u x₀ y₀ x₁ := one_div_le_one_div_of_le (hΔ x₁ hx₁) h2
      _ ≤ ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x :=
          single_le_sum (f := fun x ↦ 1 / rowGap u x₀ y₀ x)
            (fun x hx ↦ (one_div_pos.2 (hΔ x hx)).le) hx₁
  generalize ∑ x ∈ univ.erase x₀, 1 / rowGap u x₀ y₀ x = S at hkey hS1 ⊢
  generalize 1 + 1 / colGapMin u x₀ y₀ = K at hkey hK ⊢
  generalize ∑ t ∈ range T, ((t : ℝ) + 1)⁻¹ = H at hkey hHlog hH0
  have hL1 : 1 ≤ 1 + Real.log T := le_add_of_nonneg_right hlog
  have hLS : 1 / 2 ≤ (1 + Real.log T) * S := by nlinarith
  have hLSK : 1 / 2 ≤ (1 + Real.log T) * S * K := by nlinarith
  have hHSK : H * S * K ≤ (1 + Real.log T) * S * K :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHlog (by linarith)) (by linarith)
  nlinarith

end Run

end Ito2026Adversarial
