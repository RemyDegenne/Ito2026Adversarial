/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.Maximin
public import Ito2026Adversarial.LeanMachineLearning.Game.RepeatedGame

/-!
# Relations between the regrets of a repeated game

For actions `x_t`, `y_t` of the two players of a repeated zero-sum game `u` (any processes, under
any probability measure), relations between the pure-strategy maximin regret `PSMR_T`, the Nash
regret `NR_T` and the external regret `ER_T`.

## Main statements

* `nashRegret_eq_psmr_add`: `NR_T = PSMR_T + Δ^mix T`;
* `nashRegret_le_externalRegret`: `NR_T ≤ ER_T`;
* `IsStrictPSNE.colGapMin_mul_le`: for a strict PSNE `(x*, y*)`, `ER_T(x*) - PSMR_T` is at least
  `Δᶜ_min` times the expected number of rounds in which the adversary does not play `y*`;
* `IsPSNE.integral_sum_rowGap_sub_le`: for a PSNE and utilities in `[-1, 1]`,
  `E[∑_t Δʳ_{x_t}] - ER_T(x*)` is at most `4` times that number.

The actions take values in spaces with measurable singletons (for an arbitrary σ-algebra on the
action sets, `ω ↦ u (x_t ω) (y_t ω)` need not be measurable and the statements fail).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ProbabilityTheory

namespace Learning.RepeatedGame

open ZeroSumGame

section Integrable

variable {𝒳 𝒴 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒳]
  [MeasurableSingletonClass 𝒴] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : Ω → 𝒳} {Y : Ω → 𝒴}

/-- A bounded function of two random variables with values in countable spaces with measurable
singletons is integrable. -/
lemma integrable_comp_of_abs_le [Countable 𝒳] [Countable 𝒴] {f : 𝒳 → 𝒴 → ℝ} {C : ℝ}
    (hf : ∀ x y, |f x y| ≤ C) (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω ↦ f (X ω) (Y ω)) P :=
  Integrable.of_bound ((measurable_of_countable (Function.uncurry f)).comp
    (hX.prodMk hY)).aestronglyMeasurable C (ae_of_all _ fun ω ↦ hf (X ω) (Y ω))

/-- A function of two random variables with values in finite spaces with measurable singletons is
integrable. -/
lemma integrable_comp_of_finite [Finite 𝒳] [Finite 𝒴] (f : 𝒳 → 𝒴 → ℝ) (hX : Measurable X)
    (hY : Measurable Y) :
    Integrable (fun ω ↦ f (X ω) (Y ω)) P := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun p : 𝒳 × 𝒴 ↦ |f p.1 p.2|).bddAbove
  exact integrable_comp_of_abs_le (fun x y ↦ hC ⟨(x, y), rfl⟩) hX hY

end Integrable

variable {𝒳 𝒴 Ω : Type*} [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳] [Nonempty 𝒴]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {u : 𝒳 → 𝒴 → ℝ} {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴}

omit [Nonempty 𝒳] [Nonempty 𝒴] in
/-- The Nash regret is the pure-strategy maximin regret plus `Δ^mix T`, for actions in spaces with
measurable singletons. -/
lemma nashRegret_eq_psmr_add [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒴]
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t)) (T : ℕ) :
    nashRegret u X Y P T = psmr u X Y P T + mixGap u * T := by
  have hint : Integrable (fun ω ↦ ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))) P :=
    integrable_finsetSum _ fun t _ ↦
      integrable_comp_of_finite (fun x y ↦ pureMaximin u - u x y) (hX t) (hY t)
  have h : (fun ω ↦ ∑ t ∈ range T, (nashValue u - u (X t ω) (Y t ω))) =
      fun ω ↦ ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) + mixGap u * T := by
    ext ω
    simp only [mixGap, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  rw [nashRegret, h, integral_add hint (integrable_const _), integral_const, psmr]
  simp

/-- The Nash regret is at most the external regret, for actions in spaces with measurable
singletons: a maximin mixed strategy guarantees `v^Nash` against every action of the adversary. -/
lemma nashRegret_le_externalRegret [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒴]
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t)) (T : ℕ) :
    nashRegret u X Y P T ≤ externalRegret u X Y P T := by
  obtain ⟨p, hp, hpv⟩ := exists_forall_nashValue_le u
  have hint (x : 𝒳) :
      Integrable (fun ω ↦ ∑ t ∈ range T, (u x (Y t ω) - u (X t ω) (Y t ω))) P :=
    integrable_finsetSum _ fun t _ ↦
      integrable_comp_of_finite (fun x' y ↦ u x y - u x' y) (hX t) (hY t)
  have hbdd : BddAbove (Set.range (externalRegretAgainst u X Y P T)) :=
    (Set.finite_range _).bddAbove
  calc nashRegret u X Y P T
      ≤ P[fun ω ↦ ∑ x, p x * ∑ t ∈ range T, (u x (Y t ω) - u (X t ω) (Y t ω))] := by
        refine integral_mono (integrable_finsetSum _ fun t _ ↦
          integrable_comp_of_finite (fun x y ↦ nashValue u - u x y) (hX t) (hY t))
          (integrable_finsetSum _ fun x _ ↦ (hint x).const_mul _) fun ω ↦ ?_
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun t _ ↦ ?_
        calc nashValue u - u (X t ω) (Y t ω)
            ≤ ∑ x, p x * u x (Y t ω) - u (X t ω) (Y t ω) := by linarith [hpv (Y t ω)]
          _ = ∑ x, p x * (u x (Y t ω) - u (X t ω) (Y t ω)) := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
    _ = ∑ x, p x * externalRegretAgainst u X Y P T x := by
        rw [integral_finsetSum _ fun x _ ↦ (hint x).const_mul _]
        simp_rw [integral_const_mul]
        rfl
    _ ≤ ∑ x, p x * externalRegret u X Y P T :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (le_ciSup hbdd x) (hp.1 x)
    _ = externalRegret u X Y P T := by rw [← Finset.sum_mul, hp.2, one_mul]

variable [DecidableEq 𝒴]

omit [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳] [Nonempty 𝒴] in
/-- For a PSNE `(x₀, y₀)`, `ER_T(x₀) - PSMR_T ≥ Δᶜ_min E[#{t < T : y_t ≠ y₀}]`. -/
lemma IsPSNE.colGapMin_mul_le [Finite 𝒳] [Finite 𝒴] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {x₀ : 𝒳} {y₀ : 𝒴} (h : IsPSNE u x₀ y₀)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t)) (T : ℕ) :
    colGapMin u x₀ y₀ * P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] ≤
      externalRegretAgainst u X Y P T x₀ - psmr u X Y P T := by
  have h1 : Integrable (fun ω ↦ ∑ t ∈ range T, (u x₀ (Y t ω) - u (X t ω) (Y t ω))) P :=
    integrable_finsetSum _ fun t _ ↦
      integrable_comp_of_finite (fun x y ↦ u x₀ y - u x y) (hX t) (hY t)
  have h2 : Integrable (fun ω ↦ ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))) P :=
    integrable_finsetSum _ fun t _ ↦
      integrable_comp_of_finite (fun x y ↦ pureMaximin u - u x y) (hX t) (hY t)
  have h3 : Integrable (fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1) P :=
    integrable_finsetSum _ fun t _ ↦
      integrable_comp_of_finite (fun x y ↦ if y = y₀ then (0 : ℝ) else 1) (hX t) (hY t)
  rw [externalRegretAgainst, psmr, ← integral_sub h1 h2, ← integral_const_mul]
  refine integral_mono (h3.const_mul _) (h1.sub h2) fun ω ↦ ?_
  -- `u x₀ y_t - v* = Δᶜ_{y_t} ≥ Δᶜ_min 𝟙{y_t ≠ y₀}`
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, h.pureMaximin_eq]
  refine Finset.sum_le_sum fun t _ ↦ ?_
  split_ifs with hy
  · simp [hy]
  · rw [mul_one, sub_sub_sub_cancel_right]
    exact ciInf_le (Set.finite_range _).bddBelow (⟨Y t ω, hy⟩ : {y' // y' ≠ y₀})

omit [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳] [Nonempty 𝒴] in
/-- For a strict PSNE `(x₀, y₀)`, `ER_T(x₀) - PSMR_T ≥ Δᶜ_min E[#{t < T : y_t ≠ y₀}]`. -/
lemma IsStrictPSNE.colGapMin_mul_le [Finite 𝒳] [Finite 𝒴] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {x₀ : 𝒳} {y₀ : 𝒴} (h : IsStrictPSNE u x₀ y₀)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t)) (T : ℕ) :
    colGapMin u x₀ y₀ * P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] ≤
      externalRegretAgainst u X Y P T x₀ - psmr u X Y P T :=
  IsPSNE.colGapMin_mul_le h.isPSNE hX hY T

omit [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳] [Nonempty 𝒴] in
/-- For utilities in `[-1, 1]` and any `(x₀, y₀)`, `E[∑_t Δʳ_{x_t}] - ER_T(x₀) ≤
4 E[#{t < T : y_t ≠ y₀}]`, where `Δʳ_x = u x₀ y₀ - u x y₀`. -/
lemma integral_sum_rowGap_sub_le [Countable 𝒳] [Countable 𝒴] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {x₀ : 𝒳} {y₀ : 𝒴}
    (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t)) (T : ℕ) :
    P[fun ω ↦ ∑ t ∈ range T, rowGap u x₀ y₀ (X t ω)] - externalRegretAgainst u X Y P T x₀ ≤
      4 * P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] := by
  have hu' : ∀ x y, |u x y| ≤ 1 := fun x y ↦ abs_le.2 (hu x y)
  have h1 : Integrable (fun ω ↦ ∑ t ∈ range T, rowGap u x₀ y₀ (X t ω)) P :=
    integrable_finsetSum _ fun t _ ↦ integrable_comp_of_abs_le (C := 2)
      (f := fun x (_ : 𝒴) ↦ rowGap u x₀ y₀ x) (fun x y ↦ by
        simp only [rowGap]
        exact (abs_sub _ _).trans (by linarith [hu' x₀ y₀, hu' x y₀])) (hX t) (hY t)
  have h2 : Integrable (fun ω ↦ ∑ t ∈ range T, (u x₀ (Y t ω) - u (X t ω) (Y t ω))) P :=
    integrable_finsetSum _ fun t _ ↦ integrable_comp_of_abs_le (C := 2)
      (f := fun x y ↦ u x₀ y - u x y) (fun x y ↦
        (abs_sub _ _).trans (by linarith [hu' x₀ y, hu' x y])) (hX t) (hY t)
  have h3 : Integrable (fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1) P :=
    integrable_finsetSum _ fun t _ ↦ integrable_comp_of_abs_le (C := 1)
      (f := fun _ y ↦ if y = y₀ then (0 : ℝ) else 1) (fun x y ↦ by split_ifs <;> simp)
      (hX t) (hY t)
  rw [externalRegretAgainst, ← integral_sub h1 h2, ← integral_const_mul]
  refine integral_mono (h1.sub h2) (h3.const_mul _) fun ω ↦ ?_
  -- the summand `u x₀ y₀ - u x_t y₀ - u x₀ y_t + u x_t y_t` vanishes if `y_t = y₀` and is at most
  -- `4` otherwise
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun t _ ↦ ?_
  simp only [rowGap]
  split_ifs with hy
  · simp [hy]
  · linarith [(hu x₀ y₀).2, (hu (X t ω) y₀).1, (hu x₀ (Y t ω)).1, (hu (X t ω) (Y t ω)).2]

omit [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳] [Nonempty 𝒴] in
/-- For a PSNE `(x₀, y₀)` and utilities in `[-1, 1]`,
`E[∑_t Δʳ_{x_t}] - ER_T(x₀) ≤ 4 E[#{t < T : y_t ≠ y₀}]` (the equilibrium property is not needed,
`integral_sum_rowGap_sub_le`). -/
@[nolint unusedArguments]
lemma IsPSNE.integral_sum_rowGap_sub_le [Finite 𝒳] [Finite 𝒴] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {x₀ : 𝒳} {y₀ : 𝒴} (_h : IsPSNE u x₀ y₀)
    (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t)) (T : ℕ) :
    P[fun ω ↦ ∑ t ∈ range T, rowGap u x₀ y₀ (X t ω)] - externalRegretAgainst u X Y P T x₀ ≤
      4 * P[fun ω ↦ ∑ t ∈ range T, if Y t ω = y₀ then (0 : ℝ) else 1] :=
  Learning.RepeatedGame.integral_sum_rowGap_sub_le hu hX hY T

end Learning.RepeatedGame
