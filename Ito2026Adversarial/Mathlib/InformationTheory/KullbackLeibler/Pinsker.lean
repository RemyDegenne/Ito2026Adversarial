/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Ito2026Adversarial.Mathlib.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Pinsker's inequality for a single event

We prove **Pinsker's inequality** in the form `2 (μ A - ν A)² ≤ KL(μ ‖ ν)` for probability
measures `μ ν` and a measurable set `A`.

The proof goes through the Bernoulli case: for the Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`, `p q : unitInterval`), the
Kullback-Leibler divergence is the binary divergence `klBer p q`
(`InformationTheory.klDiv_bernoulliMeasure`), which dominates `2 (p - q)²` by a calculus argument.
The general case follows from the data processing inequality `klDiv_map_le` applied to the
indicator function of `A`, whose image measure is the Bernoulli measure `Ber(1, 0, μ.real A)`
(Mathlib's `hasLaw_indicator_one_bernoulliMeasure`).

## Main statements

* `sq_sub_le_klBerReal`: `2 * (p - q) ^ 2 ≤ klBerReal p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`;
  `sq_sub_le_klBer`: `ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klBer p q` for `p, q ∈ [0, 1]`.
* `ofReal_le_klDiv_bernoulliMeasure`: `ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv Ber(x, y, p)
  Ber(x, y, q)` for all `p q : unitInterval`.
* `klBer_measureReal_le_klDiv`: `klBer (μ.real A) (ν.real A) ≤ klDiv μ ν`, the data-processing
  inequality applied to the indicator of `A`;
* `sq_sub_le_klDiv`: `ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν`.
* `abs_sub_le_sqrt_klDiv`: `|μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set unitInterval
open scoped ENNReal

namespace InformationTheory

/-! ### The binary Pinsker inequality -/

/-- Auxiliary function for the proof of the binary Pinsker inequality: the difference
`klBerReal p q - 2 * (p - q) ^ 2`, written as a function of `q` without divisions inside
the logarithms. -/
private noncomputable def klBerRealGap (p q : ℝ) : ℝ :=
  p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) - ((2 : ℕ) : ℝ) * (p - q) ^ 2

/-- Derivative of `klBerRealGap p` in the second variable, in factored form: its sign is the sign
of `q - p` on `(0, 1)`. -/
private lemma hasDerivAt_klBerRealGap {p q : ℝ} (hq : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt (klBerRealGap p) ((q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) q := by
  have hq1' : 1 - q ≠ 0 := sub_ne_zero.2 hq1.symm
  have h1 : HasDerivAt (fun x ↦ p * (log p - log x)) (p * (-q⁻¹)) q :=
    ((hasDerivAt_log hq).const_sub (log p)).const_mul p
  have h2 : HasDerivAt (fun x ↦ (1 - p) * (log (1 - p) - log (1 - x)))
      ((1 - p) * (-(-1 / (1 - q)))) q :=
    ((((hasDerivAt_id' (x := q)).const_sub 1).log hq1').const_sub (log (1 - p))).const_mul (1 - p)
  have h3 := (((hasDerivAt_id' (x := q)).const_sub p).pow 2).const_mul 2
  refine ((h1.add h2).sub h3).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

/-- `klBerRealGap p` is continuous on `[p, 1)` for `0 ≤ p` (including at `p = 0`, where the
logarithmic term has a zero coefficient). -/
private lemma continuousOn_klBerRealGap {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (klBerRealGap p) (Ico p 1) := by
  have h1 : ContinuousOn (fun x ↦ p * (log p - log x)) (Ico p 1) := by
    rcases hp.eq_or_lt with rfl | hp
    · simp [continuousOn_const]
    · exact continuousOn_const.mul (continuousOn_const.sub
        (continuousOn_log.mono fun x hx ↦ (hp.trans_le hx.1).ne'))
  have h2 : ContinuousOn (fun x ↦ (1 - p) * (log (1 - p) - log (1 - x))) (Ico p 1) :=
    continuousOn_const.mul (continuousOn_const.sub
      ((continuousOn_const.sub continuousOn_id).log fun x hx ↦ (sub_pos.2 hx.2).ne'))
  exact (h1.add h2).sub (by fun_prop)

/-- `klBerRealGap p` vanishes at `q = p`. -/
private lemma klBerRealGap_self (p : ℝ) : klBerRealGap p p = 0 := by simp [klBerRealGap]

/-- Binary Pinsker inequality when `p ≤ q`. -/
lemma sq_sub_le_klBerReal_of_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ klBerReal p q := by
  rcases (hp.trans hpq).eq_or_lt with rfl | hq0
  · obtain rfl : p = 0 := le_antisymm hpq hp
    simp
  have hmono : MonotoneOn (klBerRealGap p) (Ico p 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico p 1) (continuousOn_klBerRealGap hp)
      (f' := fun q ↦ (q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ico] at hx ⊢
      exact (hasDerivAt_klBerRealGap (hp.trans_lt hx.1).ne' hx.2.ne).hasDerivWithinAt
    · rw [interior_Ico] at hx
      exact div_nonneg (mul_nonneg (sub_nonneg.2 hx.1.le) (sq_nonneg _))
        (mul_pos (hp.trans_lt hx.1) (sub_pos.2 hx.2)).le
  have h := hmono ⟨le_rfl, hpq.trans_lt hq1⟩ ⟨hpq, hq1⟩ hpq
  rw [klBerRealGap_self] at h
  unfold klBerRealGap at h
  rw [Nat.cast_ofNat] at h
  rw [klBerReal_eq_of_ne hq0.ne' hq1.ne]
  linarith

/-- **Binary Pinsker inequality**: `2 * (p - q) ^ 2 ≤ klBerReal p q` for `p ∈ [0, 1]` and
`q ∈ (0, 1)`. -/
lemma sq_sub_le_klBerReal {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ klBerReal p q := by
  rcases le_or_gt p q with hpq | hpq
  · exact sq_sub_le_klBerReal_of_le hp hpq hq1
  · have := sq_sub_le_klBerReal_of_le (sub_nonneg.2 hp1) (sub_le_sub_left hpq.le 1) (by linarith)
    rw [klBerReal_one_sub, sub_sub_sub_cancel_left] at this
    linarith [this, show (p - q) ^ 2 = (q - p) ^ 2 by ring]

/-- **Binary Pinsker inequality**: `2 * (p - q) ^ 2 ≤ klBer p q` for `p, q ∈ [0, 1]`. -/
lemma sq_sub_le_klBer {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klBer p q := by
  rcases hq.eq_or_lt with rfl | hq0
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · simp [klBer_zero_right, hp0]
  rcases hq1.eq_or_lt with rfl | hq1
  · rcases eq_or_ne p 1 with rfl | hp1
    · simp
    · simp [klBer_one_right, hp1]
  rw [klBer_eq_ofReal hq0.ne' hq1.ne]
  exact ENNReal.ofReal_le_ofReal (sq_sub_le_klBerReal hp hp1 hq0 hq1)

/-- Bernoulli Pinsker inequality in `ℝ≥0∞`, for all parameters in `[0, 1]`:
`2 (p - q) ^ 2 ≤ KL(Ber(x, y, p) ‖ Ber(x, y, q))` (the divergence is infinite when `q ∈ {0, 1}`
and `p ≠ q`). -/
lemma ofReal_le_klDiv_bernoulliMeasure {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {x y : X} (hxy : x ≠ y) (p q : I) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv Ber(x, y, p) Ber(x, y, q) :=
  (sq_sub_le_klBer p.2.1 p.2.2 q.2.1 q.2.2).trans_eq (klDiv_bernoulliMeasure hxy p q).symm

/-! ### Pinsker's inequality -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {A : Set Ω}

/-- **Data processing to an event**: the binary divergence between the probabilities of a
measurable set under two probability measures is at most the divergence between the measures. -/
lemma klBer_measureReal_le_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) :
    klBer (μ.real A) (ν.real A) ≤ klDiv μ ν := by
  calc klBer (μ.real A) (ν.real A)
      = klDiv (μ.map (A.indicator (1 : Ω → ℝ))) (ν.map (A.indicator (1 : Ω → ℝ))) := by
        rw [(hasLaw_indicator_one_bernoulliMeasure (P := μ) (M := ℝ) hA.nullMeasurableSet).map_eq,
          (hasLaw_indicator_one_bernoulliMeasure (P := ν) (M := ℝ) hA.nullMeasurableSet).map_eq,
          klDiv_bernoulliMeasure (x := (1 : ℝ)) (y := 0) one_ne_zero
            ⟨μ.real A, measureReal_nonneg, measureReal_le_one⟩
            ⟨ν.real A, measureReal_nonneg, measureReal_le_one⟩]
    _ ≤ klDiv μ ν := klDiv_map_le μ ν (measurable_one.indicator hA)

/-- **Pinsker's inequality** for a single event: `2 (μ A - ν A)² ≤ KL(μ ‖ ν)`. -/
theorem sq_sub_le_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν :=
  (sq_sub_le_klBer measureReal_nonneg measureReal_le_one measureReal_nonneg
    measureReal_le_one).trans (klBer_measureReal_le_klDiv hA)

/-- **Pinsker's inequality** for a single event, real form:
`|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`. -/
lemma abs_sub_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (h : klDiv μ ν ≠ ∞) :
    |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  have := sq_sub_le_klDiv (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at this
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

end InformationTheory
