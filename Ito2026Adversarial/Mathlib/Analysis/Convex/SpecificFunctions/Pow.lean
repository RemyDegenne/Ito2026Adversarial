/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Inequalities for real powers with exponent in `[0, 1]`

For an exponent `a ∈ [0, 1]`, the function `x ↦ x ^ a` is concave on `[0, ∞)`. This file gives
quantitative forms of this concavity, used in the analysis of Tsallis-entropy regularizers.

## Main statements

* `Real.rpow_le_rpow_add_mul_sub`: the tangent-line inequality
  `y ^ a ≤ x ^ a + a x ^ (a - 1) (y - x)` for `x > 0`, `y ≥ 0` (Bernoulli's inequality);
* `Real.mul_sub_le_rpow_sub_rpow`: for `0 < s ≤ t ≤ M` and `a ≤ 1`,
  `(1 - a) M ^ (a - 2) (t - s) ≤ s ^ (a - 1) - t ^ (a - 1)`;
* `Real.sq_le_rpow_bregman`: the Bregman divergence of `-x ^ a` is at least quadratic on bounded
  intervals: `a (1 - a) M ^ (a - 2) (y - x)² / 2 ≤ x ^ a + a x ^ (a - 1) (y - x) - y ^ a` for
  `0 < x ≤ M`, `0 ≤ y ≤ M`;
* `Real.rpow_neg_le_one_sub_mul`: `K ^ (-a) ≤ 1 - a (1 - 1 / K)` for `K ≥ 1`;
* `Real.mul_rpow_le_rpow_sub`: `(1 - a) x ^ a / 2 ≤ x ^ a - x` for `0 ≤ x ≤ 1/2`;
* `Real.rpow_sum_le_sum_rpow`: subadditivity, `(∑ i ∈ s, x i) ^ a ≤ ∑ i ∈ s, x i ^ a`;
* `Real.sum_rpow_le_card_rpow_mul`: the power mean inequality
  `∑ i ∈ s, x i ^ a ≤ #s ^ (1 - a) (∑ i ∈ s, x i) ^ a`.

## Tags

concavity, power function, Bernoulli's inequality, power mean
-/

@[expose] public section

open Finset Set

namespace Real

/-- **Tangent-line inequality** for the concave function `x ↦ x ^ a`, `0 ≤ a ≤ 1`:
`y ^ a ≤ x ^ a + a x ^ (a - 1) (y - x)` for `x > 0` and `y ≥ 0`. -/
lemma rpow_le_rpow_add_mul_sub {a x y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x)
    (hy : 0 ≤ y) :
    y ^ a ≤ x ^ a + a * x ^ (a - 1) * (y - x) := by
  have hyx : 0 ≤ y / x := div_nonneg hy hx.le
  have h := rpow_one_add_le_one_add_mul_self (s := y / x - 1) (by linarith) ha0 ha1
  rw [add_sub_cancel, div_rpow hy hx.le] at h
  have hxa : 0 < x ^ a := rpow_pos_of_pos hx a
  rw [div_le_iff₀ hxa] at h
  rw [rpow_sub_one hx.ne']
  calc y ^ a ≤ (1 + a * (y / x - 1)) * x ^ a := h
    _ = x ^ a + a * (x ^ a / x) * (y - x) := by field_simp

/-- For `0 < s ≤ t ≤ M` and `a ≤ 1`: `(1 - a) M ^ (a - 2) (t - s) ≤ s ^ (a - 1) - t ^ (a - 1)`
(mean value theorem for `x ↦ x ^ (a - 1)`, whose derivative is at most `-(1 - a) M ^ (a - 2)` on
`(0, M]`). -/
lemma mul_sub_le_rpow_sub_rpow {a s t M : ℝ} (ha : a ≤ 1) (hs : 0 < s) (hst : s ≤ t)
    (htM : t ≤ M) :
    (1 - a) * M ^ (a - 2) * (t - s) ≤ s ^ (a - 1) - t ^ (a - 1) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hcont : ContinuousOn (fun y : ℝ ↦ y ^ (a - 1)) (Icc s t) :=
    fun y hy ↦ (continuousAt_rpow_const _ _ (Or.inl (hs.trans_le hy.1).ne')).continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ ↦ y ^ (a - 1))
    (fun y ↦ (a - 1) * y ^ (a - 1 - 1)) hst hcont
    fun y hy ↦ hasDerivAt_rpow_const (Or.inl (hs.trans hy.1).ne')
  have hξ0 : 0 < ξ := hs.trans hξ.1
  have hts : 0 < t - s := sub_pos.2 hst
  rw [eq_div_iff hts.ne'] at hξeq
  have hM : M ^ (a - 2) ≤ ξ ^ (a - 2) :=
    rpow_le_rpow_of_nonpos hξ0 (hξ.2.le.trans htM) (by linarith)
  have hξeq' : (a - 1) * ξ ^ (a - 2) * (t - s) = t ^ (a - 1) - s ^ (a - 1) := by
    rw [← hξeq]
    ring_nf
  nlinarith [mul_le_mul_of_nonneg_right hM hts.le, mul_nonneg (sub_nonneg.2 ha) hts.le]

/-- **Quadratic lower bound on the Bregman divergence of `-x ^ a`**: for `0 < a < 1`,
`0 < x ≤ M` and `0 ≤ y ≤ M`, `a (1 - a) M ^ (a - 2) (y - x)² / 2 ≤ x ^ a + a x ^ (a - 1) (y - x)
- y ^ a`. -/
lemma sq_le_rpow_bregman {a x y M : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hxM : x ≤ M)
    (hy : 0 ≤ y) (hyM : y ≤ M) :
    a * (1 - a) * M ^ (a - 2) * (y - x) ^ 2 / 2 ≤ x ^ a + a * x ^ (a - 1) * (y - x) - y ^ a := by
  set c := a * (1 - a) * M ^ (a - 2) with hc
  set F : ℝ → ℝ := fun w ↦ x ^ a + a * x ^ (a - 1) * (w - x) - w ^ a - c * (w - x) ^ 2 / 2
    with hF
  set F' : ℝ → ℝ := fun w ↦ a * x ^ (a - 1) - a * w ^ (a - 1) - c * (w - x) with hF'
  have hderiv (w : ℝ) (hw : 0 < w) : HasDerivAt F (F' w) w := by
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ a) (a * w ^ (a - 1)) w :=
      hasDerivAt_rpow_const (Or.inl hw.ne')
    have h2 : HasDerivAt (fun w : ℝ ↦ (w - x) ^ 2) (2 * (w - x)) w := by
      convert (hasDerivAt_pow 2 (w - x)).comp w ((hasDerivAt_id w).sub_const x) using 1
      · rfl
      · norm_num
    have h3 : HasDerivAt (fun w : ℝ ↦ a * x ^ (a - 1) * (w - x)) (a * x ^ (a - 1)) w := by
      simpa using ((hasDerivAt_id w).sub_const x).const_mul (a * x ^ (a - 1))
    have := ((h3.const_add (x ^ a)).sub h1).sub ((h2.const_mul c).div_const 2)
    convert this using 1
    simp only [hF']
    ring
  have hcont : ContinuousOn F (Icc 0 M) := by
    refine ContinuousOn.sub (ContinuousOn.sub (continuousOn_const.add ?_) ?_) ?_
    · exact (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · exact fun w _ ↦ (continuousAt_rpow_const _ _ (Or.inr ha0.le)).continuousWithinAt
    · exact ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)).div_const 2)
  have hFx : F x = 0 := by simp [hF]
  have hgoal : 0 ≤ F y := by
    rcases lt_trichotomy y x with hyx | rfl | hyx
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' hyx
        (hcont.mono (Icc_subset_Icc hy hxM)) fun w hw ↦ hderiv w (hy.trans_lt hw.1)
      have hξ0 : 0 < ξ := hy.trans_lt hξ.1
      have hA := mul_sub_le_rpow_sub_rpow ha1.le hξ0 hξ.2.le hxM
      have hxy : 0 < x - y := sub_pos.2 hyx
      rw [hFx, eq_div_iff hxy.ne'] at hξeq
      have hF'ξ : F' ξ ≤ 0 := by
        simp only [hF', hc]
        nlinarith [mul_le_mul_of_nonneg_left hA ha0.le]
      nlinarith
    · rw [hFx]
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' hyx
        (hcont.mono (Icc_subset_Icc hx.le hyM)) fun w hw ↦ hderiv w (hx.trans hw.1)
      have hξ0 : 0 < ξ := hx.trans hξ.1
      have hA := mul_sub_le_rpow_sub_rpow ha1.le hx hξ.1.le (hξ.2.le.trans hyM)
      have hxy : 0 < y - x := sub_pos.2 hyx
      rw [hFx, eq_div_iff hxy.ne'] at hξeq
      have hF'ξ : 0 ≤ F' ξ := by
        simp only [hF', hc]
        nlinarith [mul_le_mul_of_nonneg_left hA ha0.le]
      nlinarith
  simp only [hF] at hgoal
  linarith

/-- For `K ≥ 1` and `0 ≤ a ≤ 1`, `K ^ (-a) ≤ 1 - a (1 - 1 / K)` (Bernoulli's inequality). -/
lemma rpow_neg_le_one_sub_mul {K a : ℝ} (hK : 1 ≤ K) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    K ^ (-a) ≤ 1 - a * (1 - 1 / K) := by
  have hK0 : 0 < K := by linarith
  have h := rpow_one_add_le_one_add_mul_self (s := 1 / K - 1)
    (by have : 0 ≤ 1 / K := by positivity
        linarith) ha0 ha1
  rw [add_sub_cancel, div_rpow zero_le_one hK0.le, one_rpow] at h
  calc K ^ (-a) = 1 / K ^ a := by rw [rpow_neg hK0.le, one_div]
    _ ≤ 1 + a * (1 / K - 1) := h
    _ = 1 - a * (1 - 1 / K) := by ring

/-- `2 ^ (a - 1) ≤ 1 - (1 - a) / 2` for `0 ≤ a ≤ 1`. -/
lemma two_rpow_sub_one_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (2 : ℝ) ^ (a - 1) ≤ 1 - (1 - a) / 2 := by
  have := rpow_neg_le_one_sub_mul (K := 2) (a := 1 - a) (by norm_num) (by linarith) (by linarith)
  rw [neg_sub] at this
  linarith

/-- For `0 ≤ x ≤ 1/2` and `0 ≤ a ≤ 1`: `(1 - a) x ^ a / 2 ≤ x ^ a - x`. -/
lemma mul_rpow_le_rpow_sub {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - a) * x ^ a / 2 ≤ x ^ a - x := by
  rcases hx0.eq_or_lt with rfl | hx0
  · rcases ha0.eq_or_lt with rfl | ha0
    · norm_num
    · simp [zero_rpow ha0.ne']
  have e : x = x ^ a * x ^ (1 - a) := by
    rw [← rpow_add hx0, show a + (1 - a) = 1 by ring, rpow_one]
  have h1 : x ^ (1 - a) ≤ (1 / 2) ^ (1 - a) :=
    rpow_le_rpow hx0.le hx (by linarith)
  have h2 : (1 / 2 : ℝ) ^ (1 - a) ≤ 1 - (1 - a) / 2 := by
    have := two_rpow_sub_one_le ha0 ha1
    rwa [one_div, inv_rpow (by norm_num), ← rpow_neg (by norm_num), neg_sub]
  have hxa : 0 < x ^ a := rpow_pos_of_pos hx0 _
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hxa.le]

/-- Subadditivity of `x ↦ x ^ a` for `0 ≤ a ≤ 1`, over a finite sum. -/
lemma rpow_sum_le_sum_rpow {κ : Type*} (s : Finset κ) {x : κ → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) : (∑ i ∈ s, x i) ^ a ≤ ∑ i ∈ s, x i ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_rpow ha0.ne']
  | insert k s hk ih =>
    rw [sum_insert hk, sum_insert hk]
    have h0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi ↦ hx i (mem_insert_of_mem hi)
    calc (x k + ∑ i ∈ s, x i) ^ a ≤ x k ^ a + (∑ i ∈ s, x i) ^ a :=
          rpow_add_le_add_rpow (hx k (mem_insert_self k s)) h0 ha0.le ha1
      _ ≤ x k ^ a + ∑ i ∈ s, x i ^ a := by
          gcongr
          exact ih fun i hi ↦ hx i (mem_insert_of_mem hi)

/-- **Power mean inequality** for `x ↦ x ^ a`, `0 < a ≤ 1`:
`∑_{i ∈ s} x i ^ a ≤ #s ^ (1 - a) (∑_{i ∈ s} x i) ^ a`. -/
lemma sum_rpow_le_card_rpow_mul {κ : Type*} (s : Finset κ) {x : κ → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∑ i ∈ s, x i ^ a ≤ (#s : ℝ) ^ (1 - a) * (∑ i ∈ s, x i) ^ a := by
  rcases (sum_nonneg hx).eq_or_lt with h0 | hpos
  · have hx0 : ∀ i ∈ s, x i = 0 := (sum_eq_zero_iff_of_nonneg hx).1 h0.symm
    rw [sum_eq_zero fun i hi ↦ by rw [hx0 i hi, zero_rpow ha0.ne']]
    exact mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _)
      (rpow_nonneg (sum_nonneg hx) _)
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hpos
  have hn : (0 : ℝ) < #s := Nat.cast_pos.2 (card_pos.2 hs)
  have ht0 : 0 < (∑ i ∈ s, x i) / #s := div_pos hpos hn
  calc ∑ i ∈ s, x i ^ a ≤ ∑ i ∈ s, (((∑ i ∈ s, x i) / #s) ^ a
        + a * ((∑ i ∈ s, x i) / #s) ^ (a - 1) * (x i - (∑ i ∈ s, x i) / #s)) :=
        sum_le_sum fun i hi ↦ rpow_le_rpow_add_mul_sub ha0.le ha1 ht0 (hx i hi)
    _ = #s * ((∑ i ∈ s, x i) / #s) ^ a + a * ((∑ i ∈ s, x i) / #s) ^ (a - 1)
          * (∑ i ∈ s, x i - #s * ((∑ i ∈ s, x i) / #s)) := by
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
        simp
    _ = #s * ((∑ i ∈ s, x i) / #s) ^ a := by
        rw [mul_div_cancel₀ _ hn.ne', sub_self, mul_zero, add_zero]
    _ = (#s : ℝ) ^ (1 - a) * (∑ i ∈ s, x i) ^ a := by
        rw [div_rpow hpos.le hn.le, rpow_sub hn, rpow_one]
        field_simp

end Real
