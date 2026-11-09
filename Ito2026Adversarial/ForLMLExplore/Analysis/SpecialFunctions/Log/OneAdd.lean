/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lower bounds on `log (1 + x)`

## Main statements

* `Real.min_one_le_two_mul_log_one_add`: `min(1, w) ≤ 2 log(1 + w)` for `w ≥ 0`.

## Tags

logarithm, inequality
-/

@[expose] public section

namespace Real

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

end Real
