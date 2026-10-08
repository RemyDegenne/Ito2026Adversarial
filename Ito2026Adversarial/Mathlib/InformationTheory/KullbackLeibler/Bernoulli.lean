/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Ito2026Adversarial.Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Ito2026Adversarial.Mathlib.Probability.Distributions.Bernoulli

/-!
# The Kullback-Leibler divergence between Bernoulli distributions

The Kullback-Leibler divergence between two Bernoulli distributions with parameters `p` and `q`
is `p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))` for `q ∈ (0, 1)`, and it is infinite
when `q ∈ {0, 1}` and `p ≠ q`. We define it, first as the real-valued function `klBerReal` given
by that formula, then as the `ℝ≥0∞`-valued function `klBer` which also has the right values at
the boundary, and identify it with the divergence between two Bernoulli measures
`Ber(x, y, p)`, `Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`).

## Main definitions

* `InformationTheory.klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`: the
  binary Kullback-Leibler divergence, as a real number.
* `InformationTheory.klBer`: the binary Kullback-Leibler divergence, in `ℝ≥0∞`.

## Main statements

* `monotoneOn_klBerReal`, `antitoneOn_klBerReal`: `klBerReal p` is nondecreasing on the right of
  `p` and nonincreasing on its left, in `(0, 1)`; `klBer_le_max`: on an interval, `klBer p` is
  bounded by the larger of its values at the endpoints;
* `sub_log_two_le_klBerReal`, `mul_log_sub_log_two_le_klBerReal`: lower bounds
  `(1 - p) log (1 / (1 - q)) - log 2 ≤ klBerReal p q` and `p log (1 / q) - log 2 ≤ klBerReal p q`;
* `klBerReal_le_div`: `klBerReal p q ≤ (p - q) ^ 2 / (q (1 - q))`;
* `klBer_le_of_tendsto`: lower semicontinuity of `klBer` on `[0, 1] × [0, 1]`;
* `klDiv_bernoulliMeasure`: `klDiv Ber(x, y, p) Ber(x, y, q) = klBer p q` for `x ≠ y`;
* `klDiv_bernoulliMeasure_eq_klBerReal`: its `ENNReal.ofReal (klBerReal p q)` form for
  `q ∉ {0, 1}`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Real Set unitInterval
open scoped ENNReal Topology

namespace InformationTheory

variable {p q : ℝ}

/-! ### The binary divergence as a real number -/

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
`p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. The formula is only meaningful for
`q ∈ (0, 1)`: see `klBer` for the `ℝ≥0∞`-valued version, which is infinite when `q ∈ {0, 1}`
and `p ≠ q`. -/
noncomputable def klBerReal (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- Unfolding lemma for `klBerReal`. -/
lemma klBerReal_apply (p q : ℝ) :
    klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := rfl

/-- The binary divergence from the parameter `0`. -/
@[simp] lemma klBerReal_zero_left : klBerReal 0 q = -log (1 - q) := by simp [klBerReal]

/-- The binary divergence from the parameter `1`. -/
@[simp] lemma klBerReal_one_left : klBerReal 1 q = -log q := by simp [klBerReal]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBerReal_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
  simp only [klBerReal, sub_sub_cancel]
  ring

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBerReal_self (p : ℝ) : klBerReal p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  simp [klBerReal, div_self hp, sub_ne_zero.2 hp1.symm]

/-- The binary divergence written without divisions inside the logarithms. -/
lemma klBerReal_eq_of_ne (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) := by
  rw [klBerReal, mul_log_div hq, mul_log_div (sub_ne_zero.2 hq1.symm)]

/-- The binary divergence in terms of the binary entropy: for `q ∉ {0, 1}`,
`klBerReal p q = -binEntropy p - p log q - (1 - p) log (1 - q)`. -/
lemma klBerReal_eq_neg_binEntropy_sub (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = -binEntropy p - p * log q - (1 - p) * log (1 - q) := by
  rw [klBerReal_eq_of_ne hq hq1]
  simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
  ring

/-! ### The binary divergence in `ℝ≥0∞` -/

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
in `ℝ≥0∞`: it is `ENNReal.ofReal (klBerReal p q)`, except that it is infinite when `q ∈ {0, 1}`
and `p ≠ q`, where the Bernoulli measures are not absolutely continuous. -/
noncomputable def klBer (p q : ℝ) : ℝ≥0∞ :=
  if q = 0 then (if p = 0 then 0 else ∞)
  else if q = 1 then (if p = 1 then 0 else ∞)
  else ENNReal.ofReal (klBerReal p q)

/-- The binary divergence to the parameter `0` is `0` or `∞`. -/
lemma klBer_zero_right : klBer p 0 = if p = 0 then 0 else ∞ := by simp [klBer]

/-- The binary divergence to the parameter `1` is `0` or `∞`. -/
lemma klBer_one_right : klBer p 1 = if p = 1 then 0 else ∞ := by simp [klBer]

/-- Away from the boundary, `klBer` is the real binary divergence. -/
lemma klBer_eq_ofReal (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBer p q = ENNReal.ofReal (klBerReal p q) := by
  simp [klBer, hq, hq1]

/-- The binary divergence is infinite exactly at the boundary, off the diagonal. -/
lemma klBer_eq_top_iff : klBer p q = ∞ ↔ (q = 0 ∧ p ≠ 0) ∨ (q = 1 ∧ p ≠ 1) := by
  unfold klBer
  split_ifs <;> simp_all

/-- The binary divergence from the parameter `0`, away from the boundary. -/
lemma klBer_zero_left (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBer 0 q = ENNReal.ofReal (-log (1 - q)) := by
  rw [klBer_eq_ofReal hq hq1, klBerReal_zero_left]

/-- The binary divergence from the parameter `1`, away from the boundary. -/
lemma klBer_one_left (hq : q ≠ 0) (hq1 : q ≠ 1) : klBer 1 q = ENNReal.ofReal (-log q) := by
  rw [klBer_eq_ofReal hq hq1, klBerReal_one_left]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBer_one_sub (p q : ℝ) : klBer (1 - p) (1 - q) = klBer p q := by
  simp only [klBer, klBerReal_one_sub]
  by_cases hq : q = 0
  · grind
  by_cases hq1 : q = 1 <;> grind

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBer_self (p : ℝ) : klBer p p = 0 := by
  simp only [klBer, klBerReal_self, ENNReal.ofReal_zero]
  split_ifs <;> simp_all

/-! ### Monotonicity, bounds and semicontinuity -/

section Inequalities

variable {q₁ q₂ a b : ℝ} {x y : ℕ → ℝ} {D : ℝ≥0∞}

/-- `klBerReal p` is continuous on `(0, 1)`. -/
lemma continuousOn_klBerReal (p : ℝ) : ContinuousOn (klBerReal p) (Ioo 0 1) := by
  refine ContinuousOn.congr
    (f := fun x ↦ p * (log p - log x) + (1 - p) * (log (1 - p) - log (1 - x)))
    ?_ fun x hx ↦ klBerReal_eq_of_ne hx.1.ne' hx.2.ne
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_log.mono fun x hx ↦ hx.1.ne'))
  · exact continuousOn_const.mul (continuousOn_const.sub
      ((continuousOn_const.sub continuousOn_id).log fun x hx ↦ (sub_pos.2 hx.2).ne'))

/-- The derivative of `klBerReal p` in the second variable on `(0, 1)`. -/
lemma hasDerivAt_klBerReal (p : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (klBerReal p) (-(p / q) + (1 - p) / (1 - q)) q := by
  have h1 : HasDerivAt (fun x ↦ p * (log p - log x)) (p * (-q⁻¹)) q :=
    ((hasDerivAt_log hq0.ne').const_sub (log p)).const_mul p
  have h2 : HasDerivAt (fun x ↦ (1 - p) * (log (1 - p) - log (1 - x)))
      ((1 - p) * (-(-1 / (1 - q)))) q :=
    ((((hasDerivAt_id' (x := q)).const_sub 1).log (sub_pos.2 hq1).ne').const_sub
      (log (1 - p))).const_mul (1 - p)
  have heq : p * (-q⁻¹) + (1 - p) * (-(-1 / (1 - q))) = -(p / q) + (1 - p) / (1 - q) := by
    rw [neg_div, neg_neg, mul_one_div, mul_neg, ← div_eq_mul_inv]
  refine ((h1.add h2).congr_deriv heq).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_Ioo (a := (0 : ℝ)) (b := 1)).mem_nhds ⟨hq0, hq1⟩] with x hx
  exact klBerReal_eq_of_ne hx.1.ne' hx.2.ne

/-- A point of the interior of `S ∩ (0, 1)` is in the interior of `S` and in `(0, 1)`. -/
private lemma interior_inter_Ioo {S : Set ℝ} {x : ℝ} (hx : x ∈ interior (S ∩ Ioo 0 1)) :
    x ∈ interior S ∧ x ∈ Ioo 0 1 := by
  rw [interior_inter, isOpen_Ioo.interior_eq] at hx
  exact hx

/-- On the right of `p`, `klBerReal p` is nondecreasing on `(0, 1)`. -/
lemma monotoneOn_klBerReal (p : ℝ) : MonotoneOn (klBerReal p) (Ici p ∩ Ioo 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg ((convex_Ici p).inter (convex_Ioo 0 1))
    ((continuousOn_klBerReal p).mono inter_subset_right)
    (f' := fun x ↦ -(p / x) + (1 - p) / (1 - x)) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨-, hx⟩ := interior_inter_Ioo hx
    exact (hasDerivAt_klBerReal p hx.1 hx.2).hasDerivWithinAt
  · obtain ⟨hpx, hx0, hx1⟩ := interior_inter_Ioo hx
    rw [interior_Ici] at hpx
    rw [neg_add_eq_sub, sub_nonneg, div_le_div_iff₀ hx0 (by linarith)]
    nlinarith [hpx.out]

/-- On the left of `p`, `klBerReal p` is nonincreasing on `(0, 1)`. -/
lemma antitoneOn_klBerReal (p : ℝ) : AntitoneOn (klBerReal p) (Iic p ∩ Ioo 0 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos ((convex_Iic p).inter (convex_Ioo 0 1))
    ((continuousOn_klBerReal p).mono inter_subset_right)
    (f' := fun x ↦ -(p / x) + (1 - p) / (1 - x)) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨-, hx⟩ := interior_inter_Ioo hx
    exact (hasDerivAt_klBerReal p hx.1 hx.2).hasDerivWithinAt
  · obtain ⟨hxp, hx0, hx1⟩ := interior_inter_Ioo hx
    rw [interior_Iic] at hxp
    rw [neg_add_eq_sub, sub_nonpos, div_le_div_iff₀ (by linarith) hx0]
    nlinarith [hxp.out]

/-- **Quasi-convexity of the binary divergence in its second argument**: on an interval,
`klBer p` is bounded by the larger of its values at the endpoints. -/
lemma klBer_le_max (hq₁ : 0 ≤ q₁) (h1 : q₁ ≤ q) (h2 : q ≤ q₂) (hq₂ : q₂ ≤ 1) :
    klBer p q ≤ max (klBer p q₁) (klBer p q₂) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [le_antisymm h1 hq₁]
    exact le_max_left _ _
  rcases eq_or_ne q 1 with rfl | hq1
  · rw [le_antisymm hq₂ h2]
    exact le_max_right _ _
  have hq0' : 0 < q := lt_of_le_of_ne (hq₁.trans h1) (Ne.symm hq0)
  have hq1' : q < 1 := lt_of_le_of_ne (h2.trans hq₂) hq1
  rcases le_total q p with hqp | hpq
  · refine le_trans ?_ (le_max_left _ _)
    rcases eq_or_ne q₁ 0 with rfl | hz
    · rcases eq_or_ne p 0 with rfl | hp
      · exact absurd hq0' (not_lt.2 hqp)
      · simp [klBer_zero_right, hp]
    · have hq₁0 : 0 < q₁ := lt_of_le_of_ne hq₁ (Ne.symm hz)
      rw [klBer_eq_ofReal hq0 hq1, klBer_eq_ofReal hz (by linarith : q₁ ≠ 1)]
      exact ENNReal.ofReal_le_ofReal (antitoneOn_klBerReal p
        ⟨h1.trans hqp, hq₁0, h1.trans_lt hq1'⟩ ⟨hqp, hq0', hq1'⟩ h1)
  · refine le_trans ?_ (le_max_right _ _)
    rcases eq_or_ne q₂ 1 with rfl | hz
    · rcases eq_or_ne p 1 with rfl | hp
      · exact absurd hq1' (not_lt.2 hpq)
      · simp [klBer_one_right, hp]
    · have hq₂1 : q₂ < 1 := lt_of_le_of_ne hq₂ hz
      rw [klBer_eq_ofReal hq0 hq1, klBer_eq_ofReal (hq0'.trans_le h2).ne' hz]
      exact ENNReal.ofReal_le_ofReal (monotoneOn_klBerReal p
        ⟨hpq, hq0', hq1'⟩ ⟨hpq.trans h2, hq0'.trans_le h2, hq₂1⟩ h2)

/-- **Lower bound on the binary divergence**:
`(1 - p) log (1 / (1 - q)) - log 2 ≤ klBerReal p q`. -/
lemma sub_log_two_le_klBerReal (hp0 : 0 ≤ p) (hq0 : 0 < q) (hq1 : q < 1) :
    (1 - p) * log (1 / (1 - q)) - log 2 ≤ klBerReal p q := by
  rw [klBerReal_eq_neg_binEntropy_sub hq0.ne' hq1.ne, one_div, log_inv]
  have h1 : binEntropy p ≤ log 2 := binEntropy_le_log_two
  have h2 : p * log q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (log_nonpos hq0.le hq1.le)
  nlinarith

/-- **Lower bound on the binary divergence**, the form used for a second argument close to `0`:
`p log (1 / q) - log 2 ≤ klBerReal p q`. -/
lemma mul_log_sub_log_two_le_klBerReal (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    p * log (1 / q) - log 2 ≤ klBerReal p q := by
  have h := sub_log_two_le_klBerReal (p := 1 - p) (q := 1 - q) (by linarith) (by linarith)
    (by linarith)
  rwa [klBerReal_one_sub, sub_sub_cancel, sub_sub_cancel] at h

/-- **Upper bound on the binary divergence** (by the `χ²` divergence):
`klBerReal p q ≤ (p - q) ^ 2 / (q (1 - q))`. -/
lemma klBerReal_le_div (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klBerReal p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  have hq1' : 0 < 1 - q := by linarith
  have hA : p * log (p / q) ≤ p * (p - q) / q := by
    rcases hp0.eq_or_lt with rfl | hp
    · simp
    · have h := log_le_sub_one_of_pos (div_pos hp hq0)
      calc p * log (p / q) ≤ p * (p / q - 1) := by nlinarith
        _ = p * (p - q) / q := by field_simp
  have hB : (1 - p) * log ((1 - p) / (1 - q)) ≤ (1 - p) * (q - p) / (1 - q) := by
    rcases (sub_nonneg.2 hp1).eq_or_lt with h | hp
    · rw [← h]; simp
    · have h := log_le_sub_one_of_pos (div_pos hp hq1')
      calc (1 - p) * log ((1 - p) / (1 - q)) ≤ (1 - p) * ((1 - p) / (1 - q) - 1) := by
            nlinarith
        _ = (1 - p) * (q - p) / (1 - q) := by field_simp; ring
  have hsum : p * (p - q) / q + (1 - p) * (q - p) / (1 - q) = (p - q) ^ 2 / (q * (1 - q)) := by
    field_simp
    ring
  rw [klBerReal_apply, ← hsum]
  exact add_le_add hA hB

/-- A finite bound `D` on `klBer p q` with `p > 0` bounds `q` away from `0`:
`exp (-(D + log 2) / p) ≤ q`. -/
lemma exp_neg_le_of_klBer_le (hD : D ≠ ∞) (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (h : klBer p q ≤ D) :
    exp (-((D.toReal + log 2) / p)) ≤ q := by
  have hK : 0 ≤ D.toReal + log 2 := by
    have : (0 : ℝ) < log 2 := log_pos (by norm_num)
    positivity
  rcases eq_or_lt_of_le hq0 with rfl | hq0'
  · rw [klBer_zero_right, ite_eq_right hp0.ne'] at h
    exact absurd (top_le_iff.1 h) hD
  rcases eq_or_lt_of_le hq1 with rfl | hq1'
  · refine exp_le_one_iff.2 ?_
    simp only [neg_nonpos]
    positivity
  rw [klBer_eq_ofReal hq0'.ne' hq1'.ne, ENNReal.ofReal_le_iff_le_toReal hD] at h
  have hlow := mul_log_sub_log_two_le_klBerReal hp1 hq0' hq1'
  have hlog : log (1 / q) ≤ (D.toReal + log 2) / p := by
    rw [le_div_iff₀ hp0]
    linarith
  rw [one_div, log_inv, neg_le] at hlog
  exact (le_log_iff_exp_le hq0').1 (by linarith)

/-- If the parameters `x n, y n ∈ [0, 1]` converge to `a` and `0` and `klBer (x n) (y n) ≤ D`
for every `n`, then `klBer a 0 ≤ D`. See `klBer_le_of_tendsto` for any limit. -/
lemma klBer_le_of_tendsto_zero (hx01 : ∀ n, x n ∈ Icc (0 : ℝ) 1)
    (hy01 : ∀ n, y n ∈ Icc (0 : ℝ) 1) (hx : Tendsto x atTop (𝓝 a))
    (hy : Tendsto y atTop (𝓝 0)) (h : ∀ n, klBer (x n) (y n) ≤ D) :
    klBer a 0 ≤ D := by
  rcases eq_or_ne D ∞ with rfl | hD
  · exact le_top
  have ha0 : 0 ≤ a := ge_of_tendsto' hx fun n ↦ (hx01 n).1
  rcases eq_or_lt_of_le ha0 with rfl | ha
  · simp
  exfalso
  set K := D.toReal + log 2 with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) < log 2 := log_pos (by norm_num)
    positivity
  have hev : ∀ᶠ n in atTop, exp (-(K / (a / 2))) ≤ y n := by
    filter_upwards [hx.eventually_const_lt (show a / 2 < a by linarith)] with n hn
    refine le_trans (exp_le_exp.2 ?_) (exp_neg_le_of_klBer_le hD (by linarith) (hx01 n).2
      (hy01 n).1 (hy01 n).2 (h n))
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hK0 (by linarith) hn.le
  exact absurd (ge_of_tendsto hy hev) (not_le.2 (exp_pos _))

/-- **Lower semicontinuity of the binary divergence**: if the parameters `x n, y n ∈ [0, 1]`
converge to `a, b` and `klBer (x n) (y n) ≤ D` for every `n`, then `klBer a b ≤ D`. -/
lemma klBer_le_of_tendsto (hx01 : ∀ n, x n ∈ Icc (0 : ℝ) 1) (hy01 : ∀ n, y n ∈ Icc (0 : ℝ) 1)
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b))
    (h : ∀ n, klBer (x n) (y n) ≤ D) :
    klBer a b ≤ D := by
  rcases eq_or_ne D ∞ with rfl | hD
  · exact le_top
  have hb0 : 0 ≤ b := ge_of_tendsto' hy fun n ↦ (hy01 n).1
  have hb1 : b ≤ 1 := le_of_tendsto' hy fun n ↦ (hy01 n).2
  rcases eq_or_lt_of_le hb0 with rfl | hb0'
  · exact klBer_le_of_tendsto_zero hx01 hy01 hx hy h
  rcases eq_or_lt_of_le hb1 with rfl | hb1'
  · have h' : ∀ n, klBer (1 - x n) (1 - y n) ≤ D := fun n ↦ by rw [klBer_one_sub]; exact h n
    have hy' : Tendsto (fun n ↦ 1 - y n) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hy
    have hz := klBer_le_of_tendsto_zero (x := fun n ↦ 1 - x n) (y := fun n ↦ 1 - y n)
      (fun n ↦ ⟨by linarith [(hx01 n).2], by linarith [(hx01 n).1]⟩)
      (fun n ↦ ⟨by linarith [(hy01 n).2], by linarith [(hy01 n).1]⟩)
      (tendsto_const_nhds.sub hx) hy' h'
    rwa [show (0 : ℝ) = 1 - 1 by ring, klBer_one_sub] at hz
  have hpos : ∀ᶠ n in atTop, 0 < y n := hy.eventually_const_lt hb0'
  have hlt : ∀ᶠ n in atTop, y n < 1 := hy.eventually_lt_const hb1'
  have hmain : Tendsto
      (fun n ↦ -binEntropy (x n) - x n * log (y n) - (1 - x n) * log (1 - y n)) atTop
      (𝓝 (-binEntropy a - a * log b - (1 - a) * log (1 - b))) := by
    have hlog : Tendsto (fun n ↦ log (y n)) atTop (𝓝 (log b)) :=
      (continuousAt_log hb0'.ne').tendsto.comp hy
    have hlog' : Tendsto (fun n ↦ log (1 - y n)) atTop (𝓝 (log (1 - b))) :=
      (continuousAt_log (by linarith : (1 : ℝ) - b ≠ 0)).tendsto.comp
        (tendsto_const_nhds.sub hy)
    exact ((((binEntropy_continuous.tendsto a).comp hx).neg).sub (hx.mul hlog)).sub
      ((tendsto_const_nhds.sub hx).mul hlog')
  have heq : (fun n ↦ -binEntropy (x n) - x n * log (y n) - (1 - x n) * log (1 - y n)) =ᶠ[atTop]
      fun n ↦ klBerReal (x n) (y n) := by
    filter_upwards [hpos, hlt] with n h1 h2
    exact (klBerReal_eq_neg_binEntropy_sub h1.ne' h2.ne).symm
  have hcont : Tendsto (fun n ↦ klBerReal (x n) (y n)) atTop (𝓝 (klBerReal a b)) := by
    rw [klBerReal_eq_neg_binEntropy_sub hb0'.ne' hb1'.ne]
    exact hmain.congr' heq
  rw [klBer_eq_ofReal hb0'.ne' hb1'.ne, ENNReal.ofReal_le_iff_le_toReal hD]
  refine le_of_tendsto hcont ?_
  filter_upwards [hpos, hlt] with n h1 h2
  have hn := h n
  rwa [klBer_eq_ofReal h1.ne' h2.ne, ENNReal.ofReal_le_iff_le_toReal hD] at hn

end Inequalities

/-! ### Divergence between Bernoulli measures -/

section bernoulliMeasure

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {x y : X}

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`), for `x ≠ y` and `q ∉ {0, 1}`, is
the binary divergence `klBerReal p q`. -/
lemma klDiv_bernoulliMeasure_eq_klBerReal (hxy : x ≠ y) (p : I) {q : I} (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (klBerReal p q) := by
  classical
  have hq0 : (0 : ℝ) < q := coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hq)
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.2 (coe_lt_one.2 (unitInterval.lt_one_iff_ne_one.2 hq1))
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.2.2
  rw [klDiv_eq_lintegral_klFun_of_ac (bernoulliMeasure_absolutelyContinuous hxy p hq hq1),
    lintegral_congr_ae ((rnDeriv_bernoulliMeasure hxy p hq hq1).mono fun z hz ↦ by rw [hz]),
    lintegral_bernoulliMeasure]
  simp only [ite_true, ite_eq_right hxy.symm, ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
    ENNReal.toReal_ofReal (div_nonneg hp1 hq1'.le)]
  rw [← ENNReal.ofReal_mul hq0.le, ← ENNReal.ofReal_mul hq1'.le, ← ENNReal.ofReal_add
      (mul_nonneg hq0.le (klFun_nonneg (div_nonneg hp0 hq0.le)))
      (mul_nonneg hq1'.le (klFun_nonneg (div_nonneg hp1 hq1'.le)))]
  congr 1
  simp only [klFun, klBerReal]
  field_simp
  ring

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`), for `x ≠ y`, is the binary
divergence `klBer p q`. -/
lemma klDiv_bernoulliMeasure (hxy : x ≠ y) (p q : I) :
    klDiv Ber(x, y, p) Ber(x, y, q) = klBer p q := by
  by_cases hq0 : q = 0
  · subst hq0
    by_cases hp0 : p = 0
    · simp [hp0]
    rw [klDiv_of_not_ac fun h ↦ hp0 (((bernoulliMeasure_absolutelyContinuous_iff hxy).1 h).1 rfl),
      Icc.coe_zero, klBer_zero_right, ite_eq_right (coe_ne_zero.2 hp0)]
  by_cases hq1 : q = 1
  · subst hq1
    by_cases hp1 : p = 1
    · simp [hp1]
    rw [klDiv_of_not_ac fun h ↦ hp1 (((bernoulliMeasure_absolutelyContinuous_iff hxy).1 h).2 rfl),
      Icc.coe_one, klBer_one_right, ite_eq_right (coe_ne_one.2 hp1)]
  rw [klDiv_bernoulliMeasure_eq_klBerReal hxy p hq0 hq1,
    klBer_eq_ofReal (coe_ne_zero.2 hq0) (coe_ne_one.2 hq1)]

end bernoulliMeasure

end InformationTheory
