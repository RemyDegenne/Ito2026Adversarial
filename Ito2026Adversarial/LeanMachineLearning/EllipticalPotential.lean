/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.DesignMatrix
public import Ito2026Adversarial.Mathlib.Analysis.Matrix.LogDet
public import Ito2026Adversarial.Mathlib.Analysis.SpecialFunctions.Log.OneAdd

/-!
# The elliptical potential lemma

For a sequence of vectors `x_t` of a Euclidean space of dimension `d` and `λ > 0`, let
`V_t = λ I + ∑_{s < t} x_s x_sᵀ` be the regularized Gram matrix (`regGram λ x t`). The
*elliptical potential lemma* bounds the sum of the squared norms `‖x_t‖²_{V_t⁻¹}` of the vectors
in the geometry of the past ones, which is the key step of the analysis of LinUCB and of the
other optimistic linear bandit algorithms.

## Main statements

* `Learning.log_det_regGram_le`: if `‖x_s‖ ≤ L`, then `log det V_t ≤ d log(λ + L² t / d)`
  (AM–GM inequality for the eigenvalues);
* `Learning.sum_min_one_mahalanobisSq_inv_regGram_le`: **the elliptical potential lemma**
  `∑_{t < T} min(1, ‖x_t‖²_{V_t⁻¹}) ≤ 2 log(det V_T / det V_0)`;
* `Learning.sum_min_one_mahalanobisSq_inv_regGram_le_card_mul_log`: with `‖x_t‖ ≤ L`, the sum is
  at most `2 d log(1 + L² T / (d λ))`.

The proof rests on the matrix determinant lemma `Learning.det_regGram_succ`,
`det V_{t+1} = det V_t (1 + ‖x_t‖²_{V_t⁻¹})`.

## Tags

elliptical potential, linear bandit, LinUCB, regularized Gram matrix
-/

@[expose] public section

open Matrix Finset Real

namespace Learning

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ℝ}

/-- **Determinant bound.** If `‖x_s‖ ≤ L` for `s < t`, then `log det V_t ≤ d log(λ + L² t / d)`,
where `d` is the dimension. -/
lemma log_det_regGram_le (hlam : 0 < lam) {L : ℝ} {x : ℕ → EuclideanSpace ℝ ι} {t : ℕ}
    (hx : ∀ s < t, ‖x s‖ ≤ L) :
    log (regGram lam x t).det ≤ Fintype.card ι * log (lam + L ^ 2 * t / Fintype.card ι) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine (posDef_regGram hlam x t).log_det_le_card_mul_log_trace_div.trans ?_
  have hsum : ∑ s ∈ range t, ‖x s‖ ^ 2 ≤ L ^ 2 * t := by
    calc ∑ s ∈ range t, ‖x s‖ ^ 2 ≤ ∑ s ∈ range t, L ^ 2 :=
          sum_le_sum fun s hs ↦ pow_le_pow_left₀ (norm_nonneg _) (hx s (mem_range.1 hs)) 2
      _ = L ^ 2 * t := by simp [mul_comm]
  have htr : 0 < (regGram lam x t).trace / Fintype.card ι := by
    rw [trace_regGram]
    exact div_pos (add_pos_of_pos_of_nonneg (mul_pos hlam hd)
      (sum_nonneg fun _ _ ↦ sq_nonneg _)) hd
  gcongr
  rw [trace_regGram, add_div, mul_div_assoc, div_self hd.ne', mul_one]
  gcongr

/-- **Elliptical potential lemma.** For `λ > 0`,
`∑_{t < T} min(1, ‖x_t‖²_{V_t⁻¹}) ≤ 2 (log det V_T - log det V_0)`: by the matrix determinant
lemma, `log det V_{t+1} - log det V_t = log(1 + ‖x_t‖²_{V_t⁻¹})`, and
`min(1, w) ≤ 2 log(1 + w)`. -/
lemma sum_min_one_mahalanobisSq_inv_regGram_le (hlam : 0 < lam) (x : ℕ → EuclideanSpace ℝ ι)
    (T : ℕ) :
    ∑ t ∈ range T, min 1 (mahalanobisSq (regGram lam x t)⁻¹ (x t))
      ≤ 2 * (log (regGram lam x T).det - log (regGram lam x 0).det) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hw := mahalanobisSq_inv_regGram_nonneg hlam x T (x T)
    rw [sum_range_succ, det_regGram_succ hlam,
      log_mul (det_regGram_pos hlam x T).ne' (by linarith)]
    linarith [Real.min_one_le_two_mul_log_one_add hw]

/-- **Elliptical potential lemma**, explicit form: if `λ > 0` and `‖x_t‖ ≤ L` for `t < T`, then
`∑_{t < T} min(1, ‖x_t‖²_{V_t⁻¹}) ≤ 2 d log(1 + L² T / (d λ))`. -/
lemma sum_min_one_mahalanobisSq_inv_regGram_le_card_mul_log (hlam : 0 < lam) {L : ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {T : ℕ} (hx : ∀ t < T, ‖x t‖ ≤ L) :
    ∑ t ∈ range T, min 1 (mahalanobisSq (regGram lam x t)⁻¹ (x t))
      ≤ 2 * Fintype.card ι * log (1 + L ^ 2 * T / (Fintype.card ι * lam)) := by
  refine (sum_min_one_mahalanobisSq_inv_regGram_le hlam x T).trans ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h0 : log (regGram lam x 0).det = Fintype.card ι * log lam := by
    rw [det_regGram_zero, log_pow]
  have hlog : log (lam + L ^ 2 * T / Fintype.card ι) - log lam
      = log (1 + L ^ 2 * T / (Fintype.card ι * lam)) := by
    rw [← log_div (by positivity) hlam.ne']
    congr 1
    field_simp
  have := log_det_regGram_le hlam hx
  rw [h0, mul_assoc, ← hlog]
  nlinarith

end Learning
