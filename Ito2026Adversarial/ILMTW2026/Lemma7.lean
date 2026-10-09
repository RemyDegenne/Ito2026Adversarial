/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Lemma 7: maximum of `√(a x) - b x`

For `a, b > 0`, the function `x ↦ √(a x) - b x` on `[0, ∞)` has maximum value `a / (4 b)`,
attained at `x = a / (4 b²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- **Lemma 7** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). For `a, b > 0`, `√(a x) - b x ≤ a / (4 b)`
for all `x ≥ 0`, with equality at `x = a / (4 b²)`. -/
theorem sqrt_mul_sub_mul_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ x : ℝ, 0 ≤ x → √(a * x) - b * x ≤ a / (4 * b)) ∧
      √(a * (a / (4 * b ^ 2))) - b * (a / (4 * b ^ 2)) = a / (4 * b) := by
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · -- `a / (4 b) - √a √x + b x = (√a - 2 b √x) ^ 2 / (4 b)`
    rw [sqrt_mul ha.le, le_div_iff₀ (by positivity)]
    have hsa := sq_sqrt ha.le
    have hsx := sq_sqrt hx
    nth_rewrite 2 [← hsx]
    conv_rhs => rw [← hsa]
    nlinarith [sq_nonneg (√a - 2 * b * √x)]
  · have h : a * (a / (4 * b ^ 2)) = (a / (2 * b)) ^ 2 := by field_simp; ring
    rw [h, sqrt_sq (by positivity)]
    field_simp
    ring

end Ito2026Adversarial
