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
  sorry

end Ito2026Adversarial
