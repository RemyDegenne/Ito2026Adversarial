/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.Mathlib.InformationTheory.KullbackLeibler.Pinsker
public import Ito2026Adversarial.Mathlib.InformationTheory.KullbackLeibler.TwoPoint

/-!
# Lemma 9: KL divergence between two-point distributions

For `|a|, |b| ≤ 1/2`, `KL(B_{±1}(a) ‖ B_{±1}(b)) ≤ (a - b)²`, where `B_{±1}(x)` is the two-point
distribution on `{-1, 1}` with mean `x`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame InformationTheory

universe u

namespace Ito2026Adversarial

/-- **Lemma 9** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). For `|a|, |b| ≤ 1/2`, the KL divergence
between the two-point distributions on `{-1, 1}` with means `a` and `b` is at most `(a - b)²`. -/
theorem klDiv_twoPoint_le {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    klDiv (twoPoint a) (twoPoint b) ≤ ENNReal.ofReal ((a - b) ^ 2) := by
  rw [abs_le] at ha hb
  -- the divergence is the binary divergence between `(1 + a) / 2, (1 + b) / 2 ∈ [1/4, 3/4]`
  rw [klDiv_twoPoint ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩,
    klBer_eq_ofReal (by linarith) (by linarith)]
  refine ENNReal.ofReal_le_ofReal ((klBerReal_le_four_mul_sq ⟨?_, ?_⟩ ⟨?_, ?_⟩).trans_eq ?_)
  · linarith
  · linarith
  · linarith
  · linarith
  · ring

end Ito2026Adversarial
