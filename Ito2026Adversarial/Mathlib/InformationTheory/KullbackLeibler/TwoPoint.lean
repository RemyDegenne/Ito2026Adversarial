/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.InformationTheory.KullbackLeibler.Bernoulli
public import Ito2026Adversarial.Mathlib.Probability.Distributions.TwoPoint

/-!
# The Kullback-Leibler divergence between two-point distributions

The two-point distribution `twoPoint x` on `{-1, 1}` with mean `x` is the Bernoulli measure
`Ber(1, -1, (1 + x) / 2)`, so the divergence between two of them is a binary divergence. Away from
the boundary, the binary divergence is at most a constant times the square of the difference of
the parameters.

## Main statements

* `InformationTheory.klBerReal_le_four_mul_sq`: `klBerReal p q ≤ 4 (p - q) ^ 2` for
  `p, q ∈ [1/4, 3/4]`;
* `ProbabilityTheory.klDiv_twoPoint`: `klDiv (twoPoint a) (twoPoint b) = klBer ((1 + a) / 2)
  ((1 + b) / 2)` for `a, b ∈ [-1, 1]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set unitInterval

namespace InformationTheory

/-- The derivative of `r ↦ klBerReal p r - 4 (p - r) ^ 2` on `(0, 1)`, in factored form: its
sign is the sign of `(r - p) (1 - 8 r (1 - r))`. -/
lemma hasDerivAt_klBerReal_sub_four_mul_sq (p : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun r ↦ klBerReal p r - 4 * (p - r) ^ 2)
      ((r - p) * (1 - 8 * (r * (1 - r))) / (r * (1 - r))) r := by
  have h := (hasDerivAt_klBerReal p hr0 hr1).sub
    ((((hasDerivAt_id' (x := r)).const_sub p).pow 2).const_mul 4)
  refine h.congr_deriv ?_
  have : 1 - r ≠ 0 := by linarith
  field_simp
  ring

/-- For `1/4 ≤ p ≤ q ≤ 3/4`, `klBerReal p q ≤ 4 (p - q) ^ 2`. -/
lemma klBerReal_le_four_mul_sq_of_le {p q : ℝ} (hp : 1 / 4 ≤ p) (hpq : p ≤ q) (hq : q ≤ 3 / 4) :
    klBerReal p q ≤ 4 * (p - q) ^ 2 := by
  -- `r ↦ klBerReal p r - 4 (p - r) ^ 2` is nonincreasing on `[p, q]`, where `r (1 - r) ≥ 3/16`
  have hanti : AntitoneOn (fun r ↦ klBerReal p r - 4 * (p - r) ^ 2) (Icc p q) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc p q)
      (((continuousOn_klBerReal p).mono fun r hr ↦
        ⟨by linarith [hr.1], by linarith [hr.2]⟩).sub (by fun_prop))
      (f' := fun r ↦ (r - p) * (1 - 8 * (r * (1 - r))) / (r * (1 - r))) (fun r hr ↦ ?_)
      fun r hr ↦ ?_
    · rw [interior_Icc] at hr
      exact (hasDerivAt_klBerReal_sub_four_mul_sq p (by linarith [hr.1])
        (by linarith [hr.2])).hasDerivWithinAt
    · rw [interior_Icc] at hr
      have hr0 : 0 < r := by linarith [hr.1]
      have hr1 : 0 < 1 - r := by linarith [hr.2]
      refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith [hr.1])
        ?_) (mul_pos hr0 hr1).le
      nlinarith [hr.1, hr.2]
  have h := hanti ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
  simp only [klBerReal_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at h
  linarith

/-- For `p, q ∈ [1/4, 3/4]`, `klBerReal p q ≤ 4 (p - q) ^ 2`: away from the boundary, the binary
divergence is at most four times the square of the difference of the parameters. -/
lemma klBerReal_le_four_mul_sq {p q : ℝ} (hp : p ∈ Icc (1 / 4) (3 / 4))
    (hq : q ∈ Icc (1 / 4) (3 / 4)) :
    klBerReal p q ≤ 4 * (p - q) ^ 2 := by
  rcases le_total p q with hpq | hqp
  · exact klBerReal_le_four_mul_sq_of_le hp.1 hpq hq.2
  · have h := klBerReal_le_four_mul_sq_of_le (p := 1 - p) (q := 1 - q) (by linarith [hp.2])
      (by linarith) (by linarith [hq.1])
    rw [klBerReal_one_sub] at h
    linarith [show (1 - p - (1 - q)) ^ 2 = (p - q) ^ 2 by ring]

end InformationTheory

namespace ProbabilityTheory

open InformationTheory

/-- The Kullback-Leibler divergence between two-point distributions on `{-1, 1}` is the binary
divergence between the probabilities `(1 + a) / 2`, `(1 + b) / 2` of `1`. -/
lemma klDiv_twoPoint {a b : ℝ} (ha : a ∈ Icc (-1) 1) (hb : b ∈ Icc (-1) 1) :
    klDiv (twoPoint a) (twoPoint b) = klBer ((1 + a) / 2) ((1 + b) / 2) := by
  have ha' : (1 + a) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hb' : (1 + b) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  rw [twoPoint, twoPoint, klDiv_bernoulliMeasure (by norm_num), Nat.cast_ofNat,
    projIcc_of_mem _ ha', projIcc_of_mem _ hb']

end ProbabilityTheory
