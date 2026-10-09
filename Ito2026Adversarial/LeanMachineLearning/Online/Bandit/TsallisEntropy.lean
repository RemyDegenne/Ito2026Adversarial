/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.SimplexFTRL
public import Ito2026Adversarial.Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Tsallis entropies on the simplex

Properties of the Tsallis entropy `φ_a(p) = (1 / a) ∑ i, (p i ^ a - p i)` (`tsallisEntropy`) on the
probability simplex of `EuclideanSpace ℝ ι`, for `0 < a ≤ 1`, used in the analysis of
follow-the-regularized-leader with Tsallis regularizers (Zimmert, Seldin 2021; Ito, Tsuchiya,
Honda 2024).

## Main definitions

* `qStar p = min (‖p‖_∞, 1 - ‖p‖_∞)`: the distance of the distribution `p` to the vertices of the
  simplex.

## Main statements

* `tsallisEntropy_nonneg`, `tsallisEntropy_single`: `φ_a` is nonnegative on the simplex and
  vanishes at its vertices;
* `tsallisEntropy_le_of_mem_simplex`: `φ_a(p) ≤ (card ι ^ (1 - a) - 1) / a`, the value at the
  uniform distribution;
* `tsallisEntropy_le_card_rpow_mul`: `φ_a(p) ≤ card ι ^ (1 - a) (1 - p x) ^ a / a` for every `x`
  (self-bounding form);
* `mul_qStar_rpow_le_tsallisEntropy`: `(1 - a) q* ^ a / (2 a) ≤ φ_a(p)`;
* `tsallisEntropy_le_mul_of_le_mul`: if `r ≤ c p` coordinatewise with `c ≥ 1`, then
  `φ_a(r) ≤ c φ_a(p)` (Ito, Tsuchiya, Honda 2024, Lemma 23);
* `tsallisEntropy_half`, `sum_sqrt_le_sqrt_card`: the case `a = 1/2`,
  `φ_{1/2}(p) = 2 ∑ i, (√(p i) - p i)`.

## Tags

Tsallis entropy, simplex, follow the regularized leader
-/

@[expose] public section

open Finset Real

namespace Learning

variable {ι : Type*} [Fintype ι]

/-! ### General parameter -/

/-- The Tsallis entropy is continuous for a nonnegative parameter. -/
lemma continuous_tsallisEntropy {a : ℝ} (ha : 0 ≤ a) : Continuous (tsallisEntropy (ι := ι) a) := by
  unfold tsallisEntropy
  refine continuous_const.mul (continuous_finsetSum _ fun i _ ↦ ?_)
  exact ((Real.continuous_rpow_const ha).comp (PiLp.continuous_apply 2 _ i)).sub
    (PiLp.continuous_apply 2 _ i)

/-- The Tsallis entropy of a point of the simplex is nonnegative, for `0 < a ≤ 1`. -/
lemma tsallisEntropy_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {p : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) : 0 ≤ tsallisEntropy a p := by
  unfold tsallisEntropy
  refine mul_nonneg (inv_nonneg.2 ha0.le) (sum_nonneg fun i _ ↦ sub_nonneg.2 ?_)
  calc p i = p i ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ p i ^ a := Real.rpow_le_rpow_of_exponent_ge' (hp.1 i) (le_one_of_mem_simplex hp i)
        ha0.le ha1

/-- The Tsallis entropy vanishes at the vertices of the simplex. -/
lemma tsallisEntropy_single [DecidableEq ι] {a : ℝ} (ha : a ≠ 0) (x : ι) :
    tsallisEntropy a (EuclideanSpace.single x (1 : ℝ)) = 0 := by
  unfold tsallisEntropy
  rw [sum_eq_zero fun i _ ↦ ?_, mul_zero]
  by_cases hi : i = x
  · subst hi
    simp
  · simp [hi, Real.zero_rpow ha]

/-- The Tsallis entropy of a point of the simplex is at most `card ι / a`. -/
lemma tsallisEntropy_le_card_div {a : ℝ} (ha0 : 0 < a) {q : EuclideanSpace ℝ ι}
    (hq : q ∈ simplex ι) : tsallisEntropy a q ≤ Fintype.card ι / a := by
  unfold tsallisEntropy
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  calc ∑ i, (q i ^ a - q i) ≤ ∑ _i : ι, (1 : ℝ) := sum_le_sum fun i _ ↦ by
        have := Real.rpow_le_one (hq.1 i) (le_one_of_mem_simplex hq i) ha0.le
        linarith [hq.1 i]
    _ = Fintype.card ι := by simp

/-- The Tsallis entropy on the simplex is at most `(card ι ^ (1 - a) - 1) / a` (its value at the
uniform distribution), for `0 < a ≤ 1`. -/
lemma tsallisEntropy_le_of_mem_simplex [Nonempty ι] {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    tsallisEntropy a p ≤ ((Fintype.card ι : ℝ) ^ (1 - a) - 1) / a := by
  have hK : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  set u := (Fintype.card ι : ℝ)⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 hK
  have hsum : ∑ i, p i ^ a ≤ (Fintype.card ι : ℝ) ^ (1 - a) := by
    calc ∑ i, p i ^ a ≤ ∑ i, (u ^ a + a * u ^ (a - 1) * (p i - u)) :=
          sum_le_sum fun i _ ↦ Real.rpow_le_rpow_add_mul_sub ha0.le ha1 hu0 (hp.1 i)
      _ = Fintype.card ι * u ^ a + a * u ^ (a - 1) * (∑ i, p i - Fintype.card ι * u) := by
          rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
          simp
      _ = (Fintype.card ι : ℝ) ^ (1 - a) := by
          rw [hp.2, hu, mul_inv_cancel₀ hK.ne', sub_self, mul_zero, add_zero,
            Real.rpow_sub hK, Real.rpow_one, Real.inv_rpow hK.le, div_eq_mul_inv]
  unfold tsallisEntropy
  rw [sum_sub_distrib, hp.2, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 ha0.le)

/-- **Self-bounding bound on the Tsallis entropy** (Ito, Tsuchiya, Honda 2024, Eq. (132)): for
every `x`, `φ_a(p) ≤ card ι ^ (1 - a) (1 - p x) ^ a / a` on the simplex, for `0 < a ≤ 1`. -/
lemma tsallisEntropy_le_card_rpow_mul {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (x : ι) :
    tsallisEntropy a p ≤ (Fintype.card ι : ℝ) ^ (1 - a) * (1 - p x) ^ a / a := by
  classical
  have hsum : ∑ i ∈ univ.erase x, p i = 1 - p x := by
    rw [← hp.2, ← add_sum_erase univ (fun i ↦ p i) (Finset.mem_univ x)]
    ring
  have hx1 : p x ^ a ≤ 1 := Real.rpow_le_one (hp.1 x) (le_one_of_mem_simplex hp x) ha0.le
  have h1 : ∑ i, (p i ^ a - p i) ≤ ∑ i ∈ univ.erase x, p i ^ a := by
    rw [sum_sub_distrib, hp.2, ← add_sum_erase univ (fun i ↦ p i ^ a) (Finset.mem_univ x)]
    linarith
  have h2 := Real.sum_rpow_le_card_rpow_mul (univ.erase x) (fun i _ ↦ hp.1 i) ha0 ha1
  rw [hsum] at h2
  have h3 : ((#(univ.erase x) : ℕ) : ℝ) ^ (1 - a) ≤ (Fintype.card ι : ℝ) ^ (1 - a) := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by linarith)
    exact_mod_cast (card_erase_le).trans (le_of_eq card_univ)
  have h4 : 0 ≤ (1 - p x) ^ a := Real.rpow_nonneg (by linarith [le_one_of_mem_simplex hp x]) _
  unfold tsallisEntropy
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  calc ∑ i, (p i ^ a - p i) ≤ ((#(univ.erase x) : ℕ) : ℝ) ^ (1 - a) * (1 - p x) ^ a := h1.trans h2
    _ ≤ (Fintype.card ι : ℝ) ^ (1 - a) * (1 - p x) ^ a := mul_le_mul_of_nonneg_right h3 h4

/-- **Lemma 23 of Ito, Tsuchiya, Honda (2024)**: if `r i ≤ c p i` for all `i` with `c ≥ 1`
(distributions of the simplex, `p` with positive coordinates), then `φ_a(r) ≤ c φ_a(p)` for
`0 < a ≤ 1`. -/
lemma tsallisEntropy_le_mul_of_le_mul {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hc : 1 ≤ c)
    {p r : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i) (hr : r ∈ simplex ι)
    (hrp : ∀ i, r i ≤ c * p i) :
    tsallisEntropy a r ≤ c * tsallisEntropy a p := by
  unfold tsallisEntropy
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  have hterm (i : ι) : r i ^ a - r i
      ≤ (p i ^ a - p i) + a * (c - 1) * (p i ^ a - p i) - (1 - a) * (r i - p i)
        + a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i) := by
    have h1 := Real.rpow_le_rpow_add_mul_sub ha0.le ha1 (hpos i) (hr.1 i)
    have e : p i ^ (a - 1) * p i = p i ^ a := by
      rw [← Real.rpow_add_one (hpos i).ne', sub_add_cancel]
    have e2 : a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i)
        = a * p i ^ (a - 1) * (r i - p i) - a * (c - 1) * p i ^ a - a * (r i - p i)
          + a * (c - 1) * p i := by
      rw [← e]
      ring
    linarith
  have hsum : ∑ i, (r i - p i) = 0 := by rw [sum_sub_distrib, hr.2, hp.2, sub_self]
  have hneg (i : ι) : a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i) ≤ 0 := by
    have h1 : 1 ≤ p i ^ (a - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hpos i) (le_one_of_mem_simplex hp i)
        (by linarith)
    have h2 : (r i - p i) - (c - 1) * p i ≤ 0 := by linarith [hrp i]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha0.le (by linarith)) h2
  have hpos' : 0 ≤ ∑ i, (p i ^ a - p i) := sum_nonneg fun i _ ↦ by
    have := Real.rpow_le_rpow_of_exponent_ge' (hp.1 i) (le_one_of_mem_simplex hp i) ha0.le ha1
    rw [Real.rpow_one] at this
    linarith
  calc ∑ i, (r i ^ a - r i)
      ≤ ∑ i, ((p i ^ a - p i) + a * (c - 1) * (p i ^ a - p i) - (1 - a) * (r i - p i)
        + a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i)) := sum_le_sum fun i _ ↦ hterm i
    _ ≤ ∑ i, ((p i ^ a - p i) + a * (c - 1) * (p i ^ a - p i) - (1 - a) * (r i - p i)) :=
        sum_le_sum fun i _ ↦ by linarith [hneg i]
    _ = (1 + a * (c - 1)) * ∑ i, (p i ^ a - p i) := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hsum]
        ring
    _ ≤ c * ∑ i, (p i ^ a - p i) := by
        gcongr
        nlinarith

section QStar

variable [Nonempty ι]

/-- `q* = min (‖p‖_∞, 1 - ‖p‖_∞)`: the distance of the distribution `p` to the vertices. -/
noncomputable def qStar (p : EuclideanSpace ℝ ι) : ℝ :=
  min (fun i ↦ p i).max (1 - (fun i ↦ p i).max)

/-- `q*` is measurable. -/
@[fun_prop]
lemma measurable_qStar : Measurable (qStar (ι := ι)) := by
  have hm : Measurable fun p : EuclideanSpace ℝ ι ↦ (fun i ↦ p i).max :=
    measurable_max.comp (by fun_prop)
  exact hm.min (measurable_const.sub hm)

/-- `q* ≤ ‖p‖_∞`. -/
lemma qStar_le_max (p : EuclideanSpace ℝ ι) : qStar p ≤ (fun i ↦ p i).max := min_le_left _ _

/-- `q* ≤ 1 - ‖p‖_∞`. -/
lemma qStar_le_one_sub_max (p : EuclideanSpace ℝ ι) : qStar p ≤ 1 - (fun i ↦ p i).max :=
  min_le_right _ _

/-- `q*` is nonnegative on the simplex. -/
lemma qStar_nonneg {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) : 0 ≤ qStar p := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  refine le_min ?_ ?_
  · rw [← hj]
    exact hp.1 j
  · rw [← hj]
    linarith [le_one_of_mem_simplex hp j]

/-- `q* ≤ 1/2`. -/
lemma qStar_le_half (p : EuclideanSpace ℝ ι) : qStar p ≤ 1 / 2 := by
  unfold qStar
  rcases le_total (fun i ↦ p i).max (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- A coordinate of `p` which is not a maximal coordinate is at most `q*`. -/
lemma le_qStar_of_ne {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {i j : ι}
    (hj : p j = (fun i ↦ p i).max) (hij : i ≠ j) : p i ≤ qStar p := by
  refine le_min (Function.le_max (fun i ↦ p i) i) ?_
  have := add_le_one_of_mem_simplex hp hij
  rw [← hj]
  linarith

/-- If a coordinate of `p` exceeds `q*`, it is larger than `1/2`. -/
lemma half_lt_of_qStar_lt {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {i : ι}
    (hi : qStar p < p i) : 1 / 2 < p i := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  by_cases hij : i = j
  · subst hij
    by_contra hle
    push Not at hle
    have : qStar p = p i := by
      unfold qStar
      rw [← hj]
      exact min_eq_left (by linarith)
    linarith
  · exact absurd (le_qStar_of_ne hp hj hij) (not_le.2 hi)

/-- If all the coordinates of `p` are at least `ℓ` and there are at least two coordinates, then
`ℓ ≤ q*`. -/
lemma le_qStar_of_forall_le {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {ℓ : ℝ}
    (hℓ : ∀ i, ℓ ≤ p i) (hcard : 2 ≤ Fintype.card ι) : ℓ ≤ qStar p := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  obtain ⟨k, hk⟩ : ∃ k, k ≠ j := by
    by_contra h
    push Not at h
    have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ by rw [h a, h b]
    omega
  refine le_min ?_ ?_
  · rw [← hj]
    exact hℓ j
  · have := add_le_one_of_mem_simplex hp hk
    rw [← hj]
    linarith [hℓ k]

/-- For every coordinate `x`, `q* ≤ 1 - p x`. -/
lemma qStar_le_one_sub {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (x : ι) :
    qStar p ≤ 1 - p x := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  by_cases hxj : x = j
  · subst hxj
    rw [hj]
    exact qStar_le_one_sub_max p
  · have := add_le_one_of_mem_simplex hp hxj
    have := qStar_le_max p
    rw [← hj] at this
    linarith

/-- `q* > 0` for a point of the simplex with positive coordinates and at least two coordinates. -/
lemma qStar_pos {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i)
    (hcard : 2 ≤ Fintype.card ι) : 0 < qStar p := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  obtain ⟨k, hk⟩ : ∃ k, k ≠ j := by
    by_contra h
    push Not at h
    have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ by rw [h a, h b]
    omega
  refine lt_min ?_ ?_
  · rw [← hj]
    exact hpos j
  · have := add_le_one_of_mem_simplex hp hk
    rw [← hj]
    linarith [hpos k]

end QStar

/-- **Lower bound on the Tsallis entropy** (Ito, Tsuchiya, Honda 2024, Eq. (125)):
`(1 - a) q* ^ a / (2 a) ≤ φ_a(p)` on the simplex, for `0 < a ≤ 1`. -/
lemma mul_qStar_rpow_le_tsallisEntropy [Nonempty ι] {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    (1 - a) * qStar p ^ a / (2 * a) ≤ tsallisEntropy a p := by
  classical
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  have hterm (i : ι) : 0 ≤ p i ^ a - p i := by
    have := Real.rpow_le_rpow_of_exponent_ge' (hp.1 i) (le_one_of_mem_simplex hp i) ha0.le ha1
    rw [Real.rpow_one] at this
    linarith
  unfold tsallisEntropy
  rw [show (1 - a) * qStar p ^ a / (2 * a) = a⁻¹ * ((1 - a) * qStar p ^ a * 2⁻¹) by
    rw [div_eq_mul_inv, mul_inv]
    ring]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  rcases le_or_gt (p j) (1 / 2) with hj2 | hj2
  · have hqj : qStar p = p j := by
      unfold qStar
      rw [← hj]
      exact min_eq_left (by linarith)
    rw [hqj]
    calc (1 - a) * p j ^ a * 2⁻¹ ≤ p j ^ a - p j := by
          have := Real.mul_rpow_le_rpow_sub ha0.le ha1 (hp.1 j) hj2
          linarith
      _ ≤ ∑ i, (p i ^ a - p i) :=
          single_le_sum (f := fun i ↦ p i ^ a - p i) (fun i _ ↦ hterm i) (Finset.mem_univ j)
  · have hqj : qStar p = 1 - p j := by
      unfold qStar
      rw [← hj]
      exact min_eq_right (by linarith)
    have hsum : ∑ i ∈ univ.erase j, p i = 1 - p j := by
      rw [← hp.2, ← add_sum_erase univ (fun i ↦ p i) (Finset.mem_univ j)]
      ring
    have hq2 : qStar p ≤ 1 / 2 := qStar_le_half p
    have hq0 : 0 ≤ qStar p := by rw [hqj]; linarith [le_one_of_mem_simplex hp j]
    calc (1 - a) * qStar p ^ a * 2⁻¹ ≤ qStar p ^ a - qStar p := by
          have := Real.mul_rpow_le_rpow_sub ha0.le ha1 hq0 hq2
          linarith
      _ ≤ ∑ i ∈ univ.erase j, p i ^ a - ∑ i ∈ univ.erase j, p i := by
          rw [hqj, ← hsum]
          gcongr
          exact Real.rpow_sum_le_sum_rpow _ (fun i _ ↦ hp.1 i) ha0 ha1
      _ = ∑ i ∈ univ.erase j, (p i ^ a - p i) := by rw [sum_sub_distrib]
      _ ≤ ∑ i, (p i ^ a - p i) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ hterm i

/-! ### The Tsallis entropy with parameter `1/2` -/

/-- The Tsallis entropy with parameter `1/2` is `2 ∑ i, (√(p i) - p i)`. -/
lemma tsallisEntropy_half (p : EuclideanSpace ℝ ι) :
    tsallisEntropy (1 / 2) p = 2 * ∑ i, (√(p i) - p i) := by
  simp only [tsallisEntropy, Real.sqrt_eq_rpow]
  norm_num

/-- On the simplex, the Tsallis entropy with parameter `1/2` is `2 (∑ i, √(p i) - 1)`. -/
lemma tsallisEntropy_half_of_mem_simplex {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    tsallisEntropy (1 / 2) p = 2 * (∑ i, √(p i) - 1) := by
  rw [tsallisEntropy_half, sum_sub_distrib, hp.2]

/-- The Tsallis entropy of `p` is at most `2 ∑_{i ≠ x} √(p i)`, for every `x`. -/
lemma tsallisEntropy_half_le_sum_erase [DecidableEq ι] {p : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) (x : ι) :
    tsallisEntropy (1 / 2) p ≤ 2 * ∑ i ∈ univ.erase x, √(p i) := by
  rw [tsallisEntropy_half_of_mem_simplex hp, ← add_sum_erase _ _ (mem_univ x)]
  have : √(p x) ≤ 1 := Real.sqrt_le_one.2 (le_one_of_mem_simplex hp x)
  linarith

/-- `∑ i, √(p i) ≤ √|ι|` on the simplex (Cauchy–Schwarz). -/
lemma sum_sqrt_le_sqrt_card {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    ∑ i, √(p i) ≤ √(Fintype.card ι) := by
  have h := sum_mul_sq_le_sq_mul_sq univ (fun _ ↦ (1 : ℝ)) fun i ↦ √(p i)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  have h1 : ∑ i, √(p i) ^ 2 = 1 := by
    rw [← hp.2]
    exact sum_congr rfl fun i _ ↦ Real.sq_sqrt (hp.1 i)
  rw [h1, mul_one] at h
  exact Real.le_sqrt_of_sq_le h

end Learning
