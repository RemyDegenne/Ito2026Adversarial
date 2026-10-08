/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Two-point distributions on `{-1, 1}`

`twoPoint x` is the distribution on `ℝ` supported by `{-1, 1}` with mean `x ∈ [-1, 1]`: it puts
mass `(1 + x) / 2` on `1` and `(1 - x) / 2` on `-1`. It is the Bernoulli measure
`Ber(1, -1, (1 + x) / 2)` of Mathlib; the parameter is clamped to `[-1, 1]`.

## Main definitions

* `twoPoint x`: the two-point distribution on `{-1, 1}` with mean `x`.

## Main statements

* `twoPoint_eq`: `twoPoint x = ((1 + x) / 2) δ₁ + ((1 - x) / 2) δ₋₁` for `x ∈ [-1, 1]`.
-/

@[expose] public section

open MeasureTheory Set unitInterval

namespace ProbabilityTheory

/-- The two-point distribution on `{-1, 1}` with mean `x ∈ [-1, 1]`: mass `(1 + x) / 2` on `1`
and `(1 - x) / 2` on `-1`. -/
noncomputable def twoPoint (x : ℝ) : Measure ℝ :=
  bernoulliMeasure 1 (-1) (projIcc 0 1 zero_le_one ((1 + x) / (2 : ℕ)))

instance (x : ℝ) : IsProbabilityMeasure (twoPoint x) := by
  unfold twoPoint; infer_instance

lemma twoPoint_eq {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    twoPoint x = ENNReal.ofReal ((1 + x) / 2) • Measure.dirac 1
      + ENNReal.ofReal ((1 - x) / 2) • Measure.dirac (-1) := by
  have h : (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [twoPoint, Nat.cast_ofNat, bernoulliMeasure_def, projIcc_of_mem _ h]
  congr 2
  · ext
    exact (Real.coe_toNNReal _ h.1).symm
  · ext
    rw [Real.coe_toNNReal _ (by linarith [hx.2] : (0 : ℝ) ≤ (1 - x) / 2)]
    change 1 - (1 + x) / 2 = (1 - x) / 2
    ring

end ProbabilityTheory
