/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities

/-!
# Stability-penalty matching learning rates

The stability-penalty matching (SPM) learning rates of Ito, Tsuchiya and Honda (2024) for
follow-the-regularized-leader: given nonnegative stability coefficients `z t` and positive penalty
coefficients `h t`, the (inverse) learning rates are `b (t + 1) = b t + z t / (b t * h t)` from
`b 0 > 0`, so that the stability term `z t / b t` of round `t` matches the penalty increment
`(b (t + 1) - b t) h t`. This file bounds the sum `∑_{t < T} z t / b t` (Lemmas 9 and 10 of Ito,
Tsuchiya, Honda 2024, in the form used for best-of-both-worlds bounds).

## Main statements

* `sum_div_sqrt_sum_le`: `∑_{t < T} z t / √(∑_{s ≤ t} z s) ≤ 2 √(∑_{t < T} z t)`;
* `sum_div_le_two_mul_sum_div_succ`: `∑_{t < T} z t / b t ≤ 2 ∑_{t < T} z t / b (t + 1)
  + 2 zmax / b 0` for any nondecreasing positive sequence `b`;
* `spm_sum_le_sqrt`: the worst-case bound `∑_{t < T} z t / b t ≤ 2 √(2 H ∑_{t < T} z t)
  + 2 zmax / b 0` when `h t ≤ H`;
* `spm_sum_le_levels`: the bound
  `∑_{t < T} z t / b t ≤ 4 √(J ∑_{t < T} h t z t) + 2 √(2 H 2⁻ᴶ ∑_{t < T} z t) + 2 zmax / b 0`
  for every number of levels `J`, which gives the logarithmic (in `T`) bound of the
  self-bounding analysis.

## Tags

learning rate, stability-penalty matching, follow the regularized leader
-/

@[expose] public section

open Finset Real

namespace Learning

/-- `∑_{t < T} z t / √(∑_{s ≤ t} z s) ≤ 2 √(∑_{t < T} z t)` for nonnegative `z`. -/
lemma sum_div_sqrt_sum_le (z : ℕ → ℝ) (hz : ∀ t, 0 ≤ z t) (T : ℕ) :
    ∑ t ∈ range T, z t / √(∑ s ∈ range (t + 1), z s) ≤ 2 * √(∑ t ∈ range T, z t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ]
    set A := ∑ t ∈ range T, z t with hA
    have hA0 : 0 ≤ A := sum_nonneg fun t _ ↦ hz t
    have hz0 := hz T
    have key : z T / √(A + z T) ≤ 2 * √(A + z T) - 2 * √A := by
      rcases (add_nonneg hA0 hz0).eq_or_lt with h0 | hpos
      · have : z T = 0 := by linarith
        rw [this, zero_div, add_zero]
        linarith
      · have hs : 0 < √(A + z T) := Real.sqrt_pos.2 hpos
        rw [div_le_iff₀ hs]
        have h1 : √(A + z T) ^ 2 = A + z T := Real.sq_sqrt hpos.le
        have h2 : √A ^ 2 = A := Real.sq_sqrt hA0
        have h3 : √A ≤ √(A + z T) := Real.sqrt_le_sqrt (by linarith)
        nlinarith [Real.sqrt_nonneg A]
    linarith

/-! ### Dyadic levels -/

open scoped Classical in
/-- The dyadic level of `x ∈ (0, H]` among the levels `0, …, J`: the least `k` such that `k = J`
or `H / 2 ^ (k + 1) < x`, so that `H / 2 ^ (k + 1) < x ≤ H / 2 ^ k` for `k < J` and
`x ≤ H / 2 ^ J` for `k = J`. -/
noncomputable def dyadicLevel (H : ℝ) (J : ℕ) (x : ℝ) : ℕ :=
  Nat.find (⟨J, Or.inl rfl⟩ : ∃ k, k = J ∨ H / 2 ^ (k + 1) < x)

/-- The dyadic level is at most `J`. -/
lemma dyadicLevel_le (H : ℝ) (J : ℕ) (x : ℝ) : dyadicLevel H J x ≤ J := by
  classical
  unfold dyadicLevel
  exact Nat.find_min' _ (Or.inl rfl)

/-- A point of `(0, H]` is at most `H / 2 ^ k` at its level `k`. -/
lemma le_div_pow_dyadicLevel {H x : ℝ} (hx : x ≤ H) (J : ℕ) :
    x ≤ H / 2 ^ dyadicLevel H J x := by
  classical
  rcases Nat.eq_zero_or_pos (dyadicLevel H J x) with h0 | hpos
  · rw [h0, pow_zero, div_one]
    exact hx
  · have hlt : dyadicLevel H J x - 1 < dyadicLevel H J x := Nat.sub_lt hpos one_pos
    have := Nat.find_min (⟨J, Or.inl rfl⟩ : ∃ k, k = J ∨ H / 2 ^ (k + 1) < x) hlt
    push Not at this
    rw [Nat.sub_add_cancel hpos] at this
    exact this.2

/-- A point at a level `k < J` is larger than `H / 2 ^ (k + 1)`. -/
lemma div_pow_lt_of_dyadicLevel_lt {H x : ℝ} {J : ℕ} (h : dyadicLevel H J x < J) :
    H / 2 ^ (dyadicLevel H J x + 1) < x := by
  classical
  have := Nat.find_spec (⟨J, Or.inl rfl⟩ : ∃ k, k = J ∨ H / 2 ^ (k + 1) < x)
  rcases this with h' | h'
  · exact absurd h' h.ne
  · exact h'

/-- **The level bound** (Ito, Tsuchiya, Honda 2024, Lemma 10): for `0 < h t ≤ H`,
`∑_{t < T} z t / √(∑_{s ≤ t} z s / h s) ≤ 2 √(2 J ∑_{t < T} h t z t) + 2 √(H / 2 ^ J ∑_{t < T} z t)`
for every number of levels `J`. -/
lemma sum_div_sqrt_sum_div_le_levels {z h : ℕ → ℝ} (hz : ∀ t, 0 ≤ z t) (hh : ∀ t, 0 < h t)
    {H : ℝ}
    (hH : ∀ t, h t ≤ H) (J T : ℕ) :
    ∑ t ∈ range T, z t / √(∑ s ∈ range (t + 1), z s / h s)
      ≤ 2 * √(2 * J * ∑ t ∈ range T, h t * z t) + 2 * √(H / 2 ^ J * ∑ t ∈ range T, z t) := by
  classical
  have hH0 : 0 < H := (hh 0).trans_le (hH 0)
  set lev : ℕ → ℕ := fun t ↦ dyadicLevel H J (h t) with hlev
  set θ : ℕ → ℝ := fun k ↦ H / 2 ^ k with hθ
  have hθ0 (k : ℕ) : 0 < θ k := by simp only [hθ]; positivity
  set zk : ℕ → ℕ → ℝ := fun k s ↦ if lev s = k then z s else 0 with hzk
  have hzk0 (k s : ℕ) : 0 ≤ zk k s := by simp only [hzk]; split_ifs <;> simp [hz s]
  have hzkle (k s : ℕ) : zk k s ≤ z s := by simp only [hzk]; split_ifs <;> simp [hz s]
  -- step 1: the bound of a round by its level
  have hstep (t : ℕ) : z t / √(∑ s ∈ range (t + 1), z s / h s)
      ≤ ∑ k ∈ range (J + 1), √(θ k) * (zk k t / √(∑ s ∈ range (t + 1), zk k s)) := by
    have e : ∑ k ∈ range (J + 1), √(θ k) * (zk k t / √(∑ s ∈ range (t + 1), zk k s))
        = √(θ (lev t)) * (zk (lev t) t / √(∑ s ∈ range (t + 1), zk (lev t) s)) := by
      refine sum_eq_single (lev t) (fun k _ hk ↦ ?_) (fun h' ↦ ?_)
      · simp [hzk, Ne.symm hk]
      · exact absurd (mem_range.2 (Nat.lt_succ_of_le (dyadicLevel_le H J (h t)))) h'
    rw [e]
    · have hzt : zk (lev t) t = z t := by simp [hzk]
      rw [hzt]
      set k := lev t
      have hsum : (∑ s ∈ range (t + 1), zk k s) / θ k ≤ ∑ s ∈ range (t + 1), z s / h s := by
        rw [sum_div]
        refine sum_le_sum fun s _ ↦ ?_
        simp only [hzk]
        split_ifs with hs
        · refine div_le_div_of_nonneg_left (hz s) (hh s) ?_
          rw [← hs]
          exact le_div_pow_dyadicLevel (hH s) J
        · rw [zero_div]
          exact div_nonneg (hz s) (hh s).le
      rcases (sum_nonneg fun s (_ : s ∈ range (t + 1)) ↦ hzk0 k s).eq_or_lt with h0 | hpos
      · have : zk k t = 0 := (sum_eq_zero_iff_of_nonneg fun s _ ↦ hzk0 k s).1 h0.symm t
          (self_mem_range_succ t)
        rw [hzt] at this
        simp [this]
      · have hs : √((∑ s ∈ range (t + 1), zk k s) / θ k) ≤ √(∑ s ∈ range (t + 1), z s / h s) :=
          Real.sqrt_le_sqrt hsum
        have hpos' : 0 < √((∑ s ∈ range (t + 1), zk k s) / θ k) :=
          Real.sqrt_pos.2 (div_pos hpos (hθ0 k))
        calc z t / √(∑ s ∈ range (t + 1), z s / h s)
            ≤ z t / √((∑ s ∈ range (t + 1), zk k s) / θ k) :=
              div_le_div_of_nonneg_left (hz t) hpos' hs
          _ = √(θ k) * (z t / √(∑ s ∈ range (t + 1), zk k s)) := by
              rw [Real.sqrt_div' _ (hθ0 k).le]
              have : 0 < √(θ k) := Real.sqrt_pos.2 (hθ0 k)
              have : 0 < √(∑ s ∈ range (t + 1), zk k s) := Real.sqrt_pos.2 hpos
              field_simp
  -- step 2: sum over the rounds and swap the sums
  have h2 : ∑ t ∈ range T, z t / √(∑ s ∈ range (t + 1), z s / h s)
      ≤ ∑ k ∈ range (J + 1), √(θ k) * (2 * √(∑ t ∈ range T, zk k t)) := by
    refine (sum_le_sum fun t _ ↦ hstep t).trans ?_
    rw [sum_comm]
    refine sum_le_sum fun k _ ↦ ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_div_sqrt_sum_le (zk k) (hzk0 k) T) (Real.sqrt_nonneg _)
  refine h2.trans ?_
  rw [sum_range_succ]
  -- the last level
  have hlast : √(θ J) * (2 * √(∑ t ∈ range T, zk J t)) ≤ 2 * √(H / 2 ^ J * ∑ t ∈ range T, z t) := by
    rw [mul_left_comm, ← Real.sqrt_mul (hθ0 J).le]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) zero_le_two
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun t _ ↦ hzkle J t) (hθ0 J).le
  -- the other levels
  set Y : ℕ → ℝ := fun k ↦ ∑ t ∈ range T, h t * zk k t with hY
  have hY0 (k : ℕ) : 0 ≤ Y k := sum_nonneg fun t _ ↦ mul_nonneg (hh t).le (hzk0 k t)
  have hlevel (k : ℕ) (hk : k < J) : √(θ k) * (2 * √(∑ t ∈ range T, zk k t)) ≤ 2 * √(2 * Y k) := by
    rw [mul_left_comm, ← Real.sqrt_mul (hθ0 k).le]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) zero_le_two
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun t _ ↦ ?_
    simp only [hzk]
    split_ifs with ht
    · have := div_pow_lt_of_dyadicLevel_lt (H := H) (x := h t) (J := J) (by
        simp only [hlev] at ht
        rw [ht]
        exact hk)
      simp only [hlev] at ht
      rw [ht, pow_succ] at this
      have e : θ k = 2 * (H / (2 ^ k * 2)) := by
        simp only [hθ]
        field_simp
      rw [e]
      nlinarith [hz t]
    · simp
  have hYsum : ∑ k ∈ range J, Y k ≤ ∑ t ∈ range T, h t * z t := by
    simp only [hY]
    rw [sum_comm]
    refine sum_le_sum fun t _ ↦ ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (hh t).le
    calc ∑ k ∈ range J, zk k t ≤ ∑ k ∈ range (J + 1), zk k t :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.le_succ J))
            fun k _ _ ↦ hzk0 k t
      _ = z t := by
          rw [sum_eq_single (lev t)]
          · simp [hzk]
          · intro k _ hk
            simp [hzk, Ne.symm hk]
          · intro h'
            exact absurd (mem_range.2 (Nat.lt_succ_of_le (dyadicLevel_le H J (h t)))) h'
  have hcs : ∑ k ∈ range J, 2 * √(2 * Y k) ≤ 2 * √(2 * J * ∑ t ∈ range T, h t * z t) := by
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    have hcs' := Real.sum_mul_le_sqrt_mul_sqrt (range J) (fun _ ↦ (1 : ℝ)) (fun k ↦ √(2 * Y k))
    simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hcs'
    refine hcs'.trans ?_
    rw [← Real.sqrt_mul (Nat.cast_nonneg J)]
    refine Real.sqrt_le_sqrt ?_
    have e : ∑ k ∈ range J, √(2 * Y k) ^ 2 = 2 * ∑ k ∈ range J, Y k := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ ↦ Real.sq_sqrt (by linarith [hY0 k])
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hYsum (by positivity : (0 : ℝ) ≤ 2 * J)]
  have := sum_le_sum fun k (hk : k ∈ range J) ↦ hlevel k (mem_range.1 hk)
  linarith

section SPM

variable {b z h : ℕ → ℝ}

/-- For a nondecreasing positive sequence `b` and `0 ≤ z t ≤ zmax`,
`∑_{t < T} z t / b t ≤ 2 ∑_{t < T} z t / b (t + 1) + 2 zmax / b 0`: the rounds where `b` more
than doubles contribute at most `2 zmax / b 0` (a geometric sum, through telescoping). -/
lemma sum_div_le_two_mul_sum_div_succ (hb0 : 0 < b 0) (hmono : ∀ t, b t ≤ b (t + 1))
    (hz : ∀ t, 0 ≤ z t) {zmax : ℝ} (hzmax : ∀ t, z t ≤ zmax) (T : ℕ) :
    ∑ t ∈ range T, z t / b t ≤ 2 * ∑ t ∈ range T, z t / b (t + 1) + 2 * zmax / b 0 := by
  have hbpos (t : ℕ) : 0 < b t := by
    induction t with
    | zero => exact hb0
    | succ t ih => exact ih.trans_le (hmono t)
  have hstep (t : ℕ) :
      z t / b t ≤ 2 * (z t / b (t + 1)) + 2 * zmax * (1 / b t - 1 / b (t + 1)) := by
    have hb := hbpos t
    have hb' := hbpos (t + 1)
    have hinv : 0 ≤ 1 / b t - 1 / b (t + 1) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hb (hmono t)
    have hzmax0 : 0 ≤ zmax := (hz t).trans (hzmax t)
    rcases le_or_gt (b (t + 1)) (2 * b t) with h2 | h2
    · have : z t / b t ≤ 2 * (z t / b (t + 1)) := by
        rw [div_le_iff₀ hb, mul_comm, ← mul_assoc, mul_div_assoc', le_div_iff₀ hb']
        nlinarith [hz t]
      nlinarith [mul_nonneg hzmax0 hinv]
    · have : z t / b t ≤ 2 * zmax * (1 / b t - 1 / b (t + 1)) := by
        have e : 1 / b t - 1 / b (t + 1) = (b (t + 1) - b t) / (b t * b (t + 1)) := by
          field_simp
        rw [e, div_le_iff₀ hb]
        rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right (hzmax t) (mul_pos hb hb').le,
          mul_le_mul_of_nonneg_left (by linarith : b (t + 1) ≤ 2 * (b (t + 1) - b t))
            (mul_nonneg hzmax0 hb.le)]
      have : 0 ≤ 2 * (z t / b (t + 1)) := by have := hz t; positivity
      linarith
  have htel : ∑ t ∈ range T, (1 / b t - 1 / b (t + 1)) = 1 / b 0 - 1 / b T := by
    rw [sum_range_sub' (fun t ↦ 1 / b t)]
  calc ∑ t ∈ range T, z t / b t
      ≤ ∑ t ∈ range T, (2 * (z t / b (t + 1)) + 2 * zmax * (1 / b t - 1 / b (t + 1))) :=
        sum_le_sum fun t _ ↦ hstep t
    _ = 2 * ∑ t ∈ range T, z t / b (t + 1) + 2 * zmax * (1 / b 0 - 1 / b T) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, htel]
    _ ≤ 2 * ∑ t ∈ range T, z t / b (t + 1) + 2 * zmax / b 0 := by
        have hzmax0 : 0 ≤ zmax := (hz 0).trans (hzmax 0)
        have : 0 ≤ 2 * zmax * (1 / b T) := by have := hbpos T; positivity
        have e : 2 * zmax * (1 / b 0) = 2 * zmax / b 0 := by ring
        nlinarith

variable (hb0 : 0 < b 0) (hz : ∀ t, 0 ≤ z t) (hh : ∀ t, 0 < h t)
  (hrec : ∀ t, b (t + 1) = b t + z t / (b t * h t))
include hb0 hz hh hrec

/-- The SPM learning rates are positive. -/
lemma spm_pos (t : ℕ) : 0 < b t := by
  induction t with
  | zero => exact hb0
  | succ t ih =>
    rw [hrec t]
    have := hz t
    have := hh t
    positivity

/-- The SPM learning rates are nondecreasing. -/
lemma spm_le_succ (t : ℕ) : b t ≤ b (t + 1) := by
  rw [hrec t]
  have := spm_pos hb0 hz hh hrec t
  have := hz t
  have := hh t
  have : 0 ≤ z t / (b t * h t) := by positivity
  linarith

/-- `b t² ≥ b 0² + 2 ∑_{s < t} z s / h s`. -/
lemma spm_sq_ge (t : ℕ) : b 0 ^ 2 + 2 * ∑ s ∈ range t, z s / h s ≤ b t ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, hrec t]
    have hb := spm_pos hb0 hz hh hrec t
    have hht := hh t
    have e : 2 * b t * (z t / (b t * h t)) = 2 * (z t / h t) := by
      field_simp
    nlinarith [sq_nonneg (z t / (b t * h t))]

/-- `z t / b (t + 1) ≤ z t / √(2 ∑_{s ≤ t} z s / h s)`. -/
lemma spm_div_succ_le (t : ℕ) :
    z t / b (t + 1) ≤ z t / √(2 * ∑ s ∈ range (t + 1), z s / h s) := by
  have hb := spm_pos hb0 hz hh hrec (t + 1)
  have hsq := spm_sq_ge hb0 hz hh hrec (t + 1)
  have hW : 0 ≤ ∑ s ∈ range (t + 1), z s / h s :=
    sum_nonneg fun s _ ↦ div_nonneg (hz s) (hh s).le
  rcases (mul_nonneg zero_le_two hW).eq_or_lt with h0 | hpos
  · have hzt : z t / h t = 0 := by
      have : ∑ s ∈ range (t + 1), z s / h s = 0 := by linarith
      exact (sum_eq_zero_iff_of_nonneg fun s _ ↦ div_nonneg (hz s) (hh s).le).1 this t
        (self_mem_range_succ t)
    have : z t = 0 := by
      rcases div_eq_zero_iff.1 hzt with h | h
      · exact h
      · exact absurd h (hh t).ne'
    simp [this]
  · have hs : √(2 * ∑ s ∈ range (t + 1), z s / h s) ≤ b (t + 1) := by
      rw [Real.sqrt_le_left hb.le]
      nlinarith [sq_nonneg (b 0)]
    exact div_le_div_of_nonneg_left (hz t) (Real.sqrt_pos.2 hpos) hs

/-- **Worst-case bound for SPM learning rates**: if `h t ≤ H` and `z t ≤ zmax`, then
`∑_{t < T} z t / b t ≤ 2 √(2 H ∑_{t < T} z t) + 2 zmax / b 0`. -/
lemma spm_sum_le_sqrt {H : ℝ} (hH : ∀ t, h t ≤ H) {zmax : ℝ} (hzmax : ∀ t, z t ≤ zmax)
    (T : ℕ) :
    ∑ t ∈ range T, z t / b t ≤ 2 * √(2 * H * ∑ t ∈ range T, z t) + 2 * zmax / b 0 := by
  have hH0 : 0 < H := (hh 0).trans_le (hH 0)
  have h1 := sum_div_le_two_mul_sum_div_succ hb0 (spm_le_succ hb0 hz hh hrec) hz hzmax T
  have h2 (t : ℕ) : z t / b (t + 1) ≤ √(H / 2) * (z t / √(∑ s ∈ range (t + 1), z s)) := by
    refine (spm_div_succ_le hb0 hz hh hrec t).trans ?_
    have hW : ∑ s ∈ range (t + 1), z s / H ≤ ∑ s ∈ range (t + 1), z s / h s :=
      sum_le_sum fun s _ ↦ div_le_div_of_nonneg_left (hz s) (hh s) (hH s)
    rcases (sum_nonneg fun s (_ : s ∈ range (t + 1)) ↦ hz s).eq_or_lt with h0 | hpos
    · have : z t = 0 := (sum_eq_zero_iff_of_nonneg fun s _ ↦ hz s).1 h0.symm t
        (self_mem_range_succ t)
      simp [this]
    · have hs : √(2 * ∑ s ∈ range (t + 1), z s / H) ≤ √(2 * ∑ s ∈ range (t + 1), z s / h s) :=
        Real.sqrt_le_sqrt (by linarith)
      have hpos' : 0 < √(2 * ∑ s ∈ range (t + 1), z s / H) := by
        rw [← sum_div]
        positivity
      calc z t / √(2 * ∑ s ∈ range (t + 1), z s / h s)
          ≤ z t / √(2 * ∑ s ∈ range (t + 1), z s / H) :=
            div_le_div_of_nonneg_left (hz t) hpos' hs
        _ = √(H / 2) * (z t / √(∑ s ∈ range (t + 1), z s)) := by
            rw [← sum_div, show 2 * ((∑ s ∈ range (t + 1), z s) / H)
                = (∑ s ∈ range (t + 1), z s) / (H / 2) by field_simp,
              Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ H / 2)]
            field_simp
  have h3 := sum_div_sqrt_sum_le z hz T
  have h4 : ∑ t ∈ range T, z t / b (t + 1) ≤ √(H / 2) * (2 * √(∑ t ∈ range T, z t)) :=
    (sum_le_sum fun t _ ↦ h2 t).trans (by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _))
  have h5 : √(2 * H * ∑ t ∈ range T, z t) = 2 * (√(H / 2) * √(∑ t ∈ range T, z t)) := by
    rw [show 2 * H * ∑ t ∈ range T, z t = 2 ^ 2 * (H / 2 * ∑ t ∈ range T, z t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_mul (by positivity)]
  nlinarith

/-- **Level bound for SPM learning rates** (Ito, Tsuchiya, Honda 2024, Eq. (13)): if
`0 < h t ≤ H` and `z t ≤ zmax`, then for every number of levels `J`,
`∑_{t < T} z t / b t ≤ 4 √(J ∑_{t < T} h t z t) + 2 √(2 H / 2 ^ J ∑_{t < T} z t)
+ 2 zmax / b 0`. -/
lemma spm_sum_le_levels {H : ℝ} (hH : ∀ t, h t ≤ H) {zmax : ℝ} (hzmax : ∀ t, z t ≤ zmax)
    (J T : ℕ) :
    ∑ t ∈ range T, z t / b t ≤ 4 * √(J * ∑ t ∈ range T, h t * z t)
      + 2 * √(2 * (H / 2 ^ J) * ∑ t ∈ range T, z t) + 2 * zmax / b 0 := by
  have h1 := sum_div_le_two_mul_sum_div_succ hb0 (spm_le_succ hb0 hz hh hrec) hz hzmax T
  have h22 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hs2 : 0 < √(2 : ℝ) := by positivity
  have h2 (t : ℕ) : z t / b (t + 1)
      ≤ √2 / 2 * (z t / √(∑ s ∈ range (t + 1), z s / h s)) := by
    refine (spm_div_succ_le hb0 hz hh hrec t).trans (le_of_eq ?_)
    rw [Real.sqrt_mul zero_le_two]
    rcases (Real.sqrt_nonneg (∑ s ∈ range (t + 1), z s / h s)).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · field_simp
      linear_combination (-(z t)) * h22
  have h3 := sum_div_sqrt_sum_div_le_levels hz hh hH J T
  have h4 : ∑ t ∈ range T, z t / b (t + 1) ≤ √2 / 2 * (2 * √(2 * J * ∑ t ∈ range T, h t * z t)
      + 2 * √(H / 2 ^ J * ∑ t ∈ range T, z t)) := by
    refine (sum_le_sum fun t _ ↦ h2 t).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have e1 : 2 * (√2 / 2 * (2 * √(2 * J * ∑ t ∈ range T, h t * z t)))
      = 4 * √(J * ∑ t ∈ range T, h t * z t) := by
    rw [mul_assoc 2 (J : ℝ), Real.sqrt_mul zero_le_two]
    linear_combination (2 * √(↑J * ∑ t ∈ range T, h t * z t)) * h22
  have e2 : 2 * (√2 / 2 * (2 * √(H / 2 ^ J * ∑ t ∈ range T, z t)))
      = 2 * √(2 * (H / 2 ^ J) * ∑ t ∈ range T, z t) := by
    rw [mul_assoc 2 (H / 2 ^ J), Real.sqrt_mul zero_le_two (H / 2 ^ J * ∑ t ∈ range T, z t)]
    ring
  nlinarith

end SPM

end Learning
