/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Lemma 8: a self-bounding inequality

If `x, a, b, c ≥ 0` and `x ≤ √(a x + b) + c`, then `x ≤ a + √b + 2 c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- **Lemma 8** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). If `x, a, b, c ≥ 0` and
`x ≤ √(a x + b) + c`, then `x ≤ a + √b + 2 c`. -/
theorem le_add_sqrt_add_of_le_sqrt_add {x a b c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : x ≤ √(a * x + b) + c) :
    x ≤ a + √b + 2 * c := by
  sorry

end Ito2026Adversarial
