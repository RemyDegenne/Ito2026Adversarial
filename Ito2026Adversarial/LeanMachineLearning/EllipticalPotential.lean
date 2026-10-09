/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.DesignMatrix
public import Ito2026Adversarial.Mathlib.Analysis.Matrix.LogDet

/-!
# The elliptical potential lemma

For a sequence of vectors `x_t` of a Euclidean space of dimension `d` and `λ > 0`, let
`V_t = λ I + ∑_{s < t} x_s x_sᵀ` be the regularized Gram matrix (`regGram λ x t`). The
*elliptical potential lemma* bounds the sum of the squared norms `‖x_t‖²_{V_t⁻¹}` of the vectors
in the geometry of the past ones, which is the key step of the analysis of LinUCB and of the
other optimistic linear bandit algorithms.

## Main statements

* `Learning.det_regGram_succ`: the matrix determinant lemma
  `det V_{t+1} = det V_t (1 + ‖x_t‖²_{V_t⁻¹})`;
* `Learning.log_det_regGram_le`: if `‖x_s‖ ≤ L`, then `log det V_t ≤ d log(λ + L² t / d)`
  (AM–GM inequality for the eigenvalues);
* `Learning.sum_min_one_mahalanobisSq_inv_regGram_le`: **the elliptical potential lemma**
  `∑_{t < T} min(1, ‖x_t‖²_{V_t⁻¹}) ≤ 2 log(det V_T / det V_0)`;
* `Learning.sum_min_one_mahalanobisSq_inv_regGram_le_card_mul_log`: with `‖x_t‖ ≤ L`, the sum is
  at most `2 d log(1 + L² T / (d λ))`.
-/

@[expose] public section

open Matrix Finset Real

namespace Learning

/-- `min(1, w) ≤ 2 log(1 + w)` for `w ≥ 0`: both `min(1, w) ≤ 2 w / (1 + w)` and
`w / (1 + w) = 1 - 1 / (1 + w) ≤ log(1 + w)`. -/
lemma min_one_le_two_mul_log_one_add {w : ℝ} (hw : 0 ≤ w) : min 1 w ≤ 2 * log (1 + w) := by
  have h1 : 0 < 1 + w := by linarith
  have h2 : 1 - (1 + w)⁻¹ ≤ log (1 + w) := one_sub_inv_le_log_of_pos h1
  have h3 : min 1 w ≤ 2 * (1 - (1 + w)⁻¹) := by
    rw [show 1 - (1 + w)⁻¹ = w / (1 + w) by field_simp; ring]
    rcases le_total w 1 with h | h
    · rw [min_eq_right h, mul_div_assoc', le_div_iff₀ h1]
      nlinarith
    · rw [min_eq_left h, mul_div_assoc', le_div_iff₀ h1]
      linarith
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ℝ}

/-- For `λ > 0`, the regularized Gram matrix has a positive determinant. -/
lemma det_regGram_pos (hlam : 0 < lam) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) :
    0 < (regGram lam x t).det :=
  (posDef_regGram hlam x t).det_pos

/-- `det V_0 = det (λ I) = λ ^ d`. -/
lemma det_regGram_zero (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) :
    (regGram lam x 0).det = lam ^ Fintype.card ι := by
  simp

/-- For `λ > 0`, `‖v‖²_{V_t⁻¹} ≥ 0`. -/
lemma mahalanobisSq_inv_regGram_nonneg (hlam : 0 < lam) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ)
    (v : EuclideanSpace ℝ ι) : 0 ≤ mahalanobisSq (regGram lam x t)⁻¹ v :=
  (posDef_regGram hlam x t).inv.posSemidef.mahalanobisSq_nonneg v

/-- **Matrix determinant lemma** for the regularized Gram matrix:
`det V_{t+1} = det V_t (1 + ‖x_t‖²_{V_t⁻¹})`. -/
lemma det_regGram_succ (hlam : 0 < lam) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) :
    (regGram lam x (t + 1)).det
      = (regGram lam x t).det * (1 + mahalanobisSq (regGram lam x t)⁻¹ (x t)) := by
  rw [regGram_succ, outerSelf, det_add_vecMulVec (det_regGram_pos hlam x t).ne'.isUnit,
    mahalanobisSq_apply]

/-- The trace of the regularized Gram matrix: `tr V_t = λ d + ∑_{s < t} ‖x_s‖²`. -/
lemma trace_regGram (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) :
    (regGram lam x t).trace = lam * Fintype.card ι + ∑ s ∈ range t, ‖x s‖ ^ 2 := by
  simp [regGram, gram, trace_sum, trace_outerSelf]

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
    linarith [min_one_le_two_mul_log_one_add hw]

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
