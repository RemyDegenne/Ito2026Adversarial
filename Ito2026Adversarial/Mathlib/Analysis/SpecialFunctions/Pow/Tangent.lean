/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Tangent-line and Bregman bounds for real powers

For an exponent `a ∈ [0, 1]`, the function `x ↦ x ^ a` is concave on `[0, ∞)`; this file gives
the quantitative forms of this concavity used in the analysis of Tsallis-entropy regularizers.

## Main statements

* `Real.rpow_le_rpow_add_mul_sub`: the tangent-line inequality
  `y ^ a ≤ x ^ a + a x ^ (a - 1) (y - x)` for `x > 0`, `y ≥ 0` (Bernoulli's inequality);
* `Real.mul_sub_le_rpow_sub_rpow`: for `0 < s ≤ t ≤ M` and `a < 1`,
  `(1 - a) M ^ (a - 2) (t - s) ≤ s ^ (a - 1) - t ^ (a - 1)`;
* `Real.sq_le_rpow_bregman`: the Bregman divergence of `-x ^ a` is at least quadratic on bounded
  intervals: `a (1 - a) M ^ (a - 2) (y - x)² / 2 ≤ x ^ a + a x ^ (a - 1) (y - x) - y ^ a` for
  `0 < x ≤ M`, `0 ≤ y ≤ M`.
-/

@[expose] public section

open Set

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

end Real
