/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.RepeatedGame
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

/-!
# Optimistic pure maximin learners in repeated games

Tools for the analysis of the learners of a repeated zero-sum game which play the pure maximin
action `argmax_x min_y U(x, y)` of upper confidence bounds `U` of the utility (Maximin-UCB,
Maximin-LinUCB).

## Main statements

* `Learning.ZeroSumGame.pureMaximin_le_of_le`: **optimism**. If `u ≤ U` and `x₀` maximizes
  `x ↦ min_y U(x, y)`, then `v* ≤ U(x₀, y)` for every `y`.
* `Learning.ZeroSumGame.pureMaximin_le_of_forall_le`, `le_pureMaximin_of_forall_le`: bounds on the
  pure maximin value from bounds on the utility.
* `Learning.RepeatedGame.pairCount_succ`, `pairCount_le`,
  `sum_range_eq_sum_pairCount_mul`, `sum_pairCount`: the counts of action pairs of a run, and
  the decomposition `∑_{t < T} f(x_t, y_t) = ∑_{x, y} N_T(x, y) f(x, y)`.
* `Learning.RepeatedGame.psmr_le_add_mul_measureReal_compl`: if the pathwise regret is at most `B`
  on a measurable event `G` and at most `B + c` outside, then `PSMR_T ≤ B + c P(Gᶜ)` (the failure
  event of high-probability bounds).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Learning

namespace ZeroSumGame

variable {𝒳 𝒴 : Type*} [Nonempty 𝒳] [Nonempty 𝒴] {u : 𝒳 → 𝒴 → ℝ}

omit [Nonempty 𝒴] in
/-- The pure maximin value is attained: there is `x` with `min_y u x y = v*`. -/
lemma exists_iInf_eq_pureMaximin [Finite 𝒳] (u : 𝒳 → 𝒴 → ℝ) :
    ∃ x, ⨅ y, u x y = pureMaximin u :=
  exists_eq_ciSup_of_finite

/-- **Optimism of the pure maximin action of upper bounds.** If `u ≤ U` and `x₀` maximizes
`x ↦ min_y U(x, y)`, then `v* ≤ min_y U(x₀, y) ≤ U(x₀, y)` for every `y`. -/
lemma pureMaximin_le_of_le [Finite 𝒳] [Fintype 𝒴] {U : 𝒳 → 𝒴 → ℝ} (hU : ∀ x y, u x y ≤ U x y)
    {x₀ : 𝒳} (hx₀ : ∀ x, (fun y ↦ U x y).min ≤ (fun y ↦ U x₀ y).min) (y : 𝒴) :
    pureMaximin u ≤ U x₀ y := by
  obtain ⟨x, hx⟩ := exists_iInf_eq_pureMaximin u
  rw [← hx]
  refine le_trans ?_ ((hx₀ x).trans (Function.min_le _ y))
  exact le_inf' _ _ fun y' _ ↦ (ciInf_le (Set.finite_range _).bddBelow y').trans (hU x y')

/-- The pure maximin value is at most an upper bound of the utility. -/
lemma pureMaximin_le_of_forall_le [Finite 𝒴] {b : ℝ} (h : ∀ x y, u x y ≤ b) : pureMaximin u ≤ b :=
  ciSup_le fun _ ↦ (ciInf_le (Set.finite_range _).bddBelow (Classical.arbitrary 𝒴)).trans (h _ _)

/-- The pure maximin value is at least a lower bound of the utility. -/
lemma le_pureMaximin_of_forall_le [Finite 𝒳] {a : ℝ} (h : ∀ x y, a ≤ u x y) :
    a ≤ pureMaximin u :=
  (le_ciInf fun y ↦ h (Classical.arbitrary 𝒳) y).trans
    (le_ciSup (f := fun x ↦ ⨅ y, u x y) (Set.finite_range _).bddAbove _)

/-- If the utility takes values in `[-1, 1]`, the gaps `Δ_{xy} = v* - u x y` are at most `2`. -/
lemma pairGap_le_two [Finite 𝒴] (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) (x : 𝒳)
    (y : 𝒴) : pairGap u x y ≤ 2 := by
  have h1 := pureMaximin_le_of_forall_le (u := u) (b := 1) fun x y ↦ (hu x y).2
  have h2 := (hu x y).1
  unfold pairGap
  linarith

end ZeroSumGame

namespace RepeatedGame

open ZeroSumGame

variable {𝒳 𝒴 Ω : Type*} [DecidableEq 𝒳] [DecidableEq 𝒴] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴}
  {R : ℕ → Ω → ℝ}

/-! ### Counts of action pairs -/

/-- The count of the pair `(x, y)` after `t` rounds is the number of rounds `s < t` in which it
was played. -/
lemma pairCount_eq_sum_range (x : 𝒳) (y : 𝒴) (t : ℕ) (ω : Ω) :
    pairCount X Y R x y t ω = ∑ s ∈ range t, if X s ω = x ∧ Y s ω = y then 1 else 0 :=
  Fin.sum_univ_eq_sum_range (fun s ↦ if X s ω = x ∧ Y s ω = y then 1 else 0) t

/-- No pair has been played before the first round. -/
@[simp]
lemma pairCount_zero (x : 𝒳) (y : 𝒴) (ω : Ω) : pairCount X Y R x y 0 ω = 0 := by
  simp [pairCount_eq_sum_range]

/-- The count of a pair increases by one at the rounds in which it is played. -/
lemma pairCount_succ (x : 𝒳) (y : 𝒴) (t : ℕ) (ω : Ω) :
    pairCount X Y R x y (t + 1) ω
      = pairCount X Y R x y t ω + if X t ω = x ∧ Y t ω = y then 1 else 0 := by
  simp only [pairCount_eq_sum_range, sum_range_succ]

/-- The count of a pair after `t` rounds is at most `t`. -/
lemma pairCount_le (x : 𝒳) (y : 𝒴) (t : ℕ) (ω : Ω) : pairCount X Y R x y t ω ≤ t := by
  rw [pairCount_eq_sum_range]
  calc ∑ s ∈ range t, (if X s ω = x ∧ Y s ω = y then 1 else 0)
      ≤ ∑ s ∈ range t, 1 := sum_le_sum fun s _ ↦ by split_ifs <;> simp
    _ = t := by simp

section Fintype

variable [Fintype 𝒳] [Fintype 𝒴]

/-- **Decomposition of a sum over rounds by action pairs**:
`∑_{t < T} f(x_t, y_t) = ∑_{x, y} N_T(x, y) f(x, y)`. -/
lemma sum_range_eq_sum_pairCount_mul (f : 𝒳 → 𝒴 → ℝ) (T : ℕ) (ω : Ω) :
    ∑ t ∈ range T, f (X t ω) (Y t ω) = ∑ x, ∑ y, (pairCount X Y R x y T ω : ℝ) * f x y := by
  have h1 (t : ℕ) : f (X t ω) (Y t ω)
      = ∑ x, ∑ y, (if X t ω = x ∧ Y t ω = y then (1 : ℝ) else 0) * f x y := by
    simp [ite_and, ite_mul]
  calc ∑ t ∈ range T, f (X t ω) (Y t ω)
      = ∑ t ∈ range T, ∑ x, ∑ y, (if X t ω = x ∧ Y t ω = y then (1 : ℝ) else 0) * f x y :=
        sum_congr rfl fun t _ ↦ h1 t
    _ = ∑ x, ∑ y, ∑ t ∈ range T, (if X t ω = x ∧ Y t ω = y then (1 : ℝ) else 0) * f x y := by
        rw [sum_comm]
        exact sum_congr rfl fun x _ ↦ sum_comm
    _ = ∑ x, ∑ y, (pairCount X Y R x y T ω : ℝ) * f x y := by
        simp_rw [pairCount_eq_sum_range, Nat.cast_sum, sum_mul, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]

/-- The counts of all pairs after `T` rounds sum to `T`. -/
lemma sum_pairCount (T : ℕ) (ω : Ω) : ∑ x, ∑ y, (pairCount X Y R x y T ω : ℝ) = T := by
  have := sum_range_eq_sum_pairCount_mul (X := X) (Y := Y) (R := R) (fun _ _ ↦ (1 : ℝ)) T ω
  simpa using this.symm

end Fintype

/-! ### Measurability -/

variable [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒳]
  [MeasurableSingletonClass 𝒴] [MeasurableSpace Ω]

/-- The count of a pair after `t` rounds of a run is measurable. -/
lemma measurable_pairCount (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hR : ∀ n, Measurable (R n)) (x : 𝒳) (y : 𝒴) (t : ℕ) :
    Measurable (pairCount X Y R x y t) :=
  (measurable_histPairCount t x y).comp
    (measurable_history (fun _ ↦ measurable_const) hX (fun n ↦ (hY n).prodMk (hR n)) t)

/-- The reward sum of a pair after `t` rounds of a run is measurable. -/
lemma measurable_pairSum (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hR : ∀ n, Measurable (R n)) (x : 𝒳) (y : 𝒴) (t : ℕ) :
    Measurable (pairSum X Y R x y t) :=
  (measurable_histPairSum t x y).comp
    (measurable_history (fun _ ↦ measurable_const) hX (fun n ↦ (hY n).prodMk (hR n)) t)

/-! ### Bounds on the pure-strategy maximin regret -/

variable [Finite 𝒳] [Finite 𝒴] {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq 𝒳] [DecidableEq 𝒴] in
/-- The pathwise regret of a run is integrable. -/
lemma integrable_sum_pureMaximin_sub (u : 𝒳 → 𝒴 → ℝ) (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) (T : ℕ) :
    Integrable (fun ω ↦ ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))) P :=
  integrable_finsetSum _ fun t _ ↦
    (Integrable.of_finite (f := fun p : 𝒳 × 𝒴 ↦ pureMaximin u - u p.1 p.2)).comp_measurable
      ((hX t).prodMk (hY t))

omit [DecidableEq 𝒳] [DecidableEq 𝒴] in
/-- **The failure event of a high-probability regret bound.** If the pathwise regret is at most
`B` on a measurable event `G` and at most `B + c` outside of it, then
`PSMR_T ≤ B + c P(Gᶜ)`. -/
lemma psmr_le_add_mul_measureReal_compl (u : 𝒳 → 𝒴 → ℝ) (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) {T : ℕ} {G : Set Ω} (hG : MeasurableSet G) {B c : ℝ}
    (h : ∀ᵐ ω ∂P, ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))
      ≤ B + Gᶜ.indicator (fun _ ↦ c) ω) :
    psmr u X Y P T ≤ B + c * P.real Gᶜ := by
  unfold psmr
  calc ∫ ω, ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ∂P
      ≤ ∫ ω, (B + Gᶜ.indicator (fun _ ↦ c) ω) ∂P :=
        integral_mono_ae (integrable_sum_pureMaximin_sub u hX hY T)
          ((integrable_const B).add ((integrable_const c).indicator hG.compl)) h
    _ = B + c * P.real Gᶜ := by
        rw [integral_add (integrable_const B) ((integrable_const c).indicator hG.compl),
          integral_const, integral_indicator_const _ hG.compl]
        simp [mul_comm]

omit [DecidableEq 𝒳] [DecidableEq 𝒴] in
/-- If all the gaps are at most `c`, then `PSMR_T ≤ c T`. -/
lemma psmr_le_mul_of_pairGap_le (u : 𝒳 → 𝒴 → ℝ) (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) {c : ℝ} (hc : ∀ x y, pairGap u x y ≤ c) (T : ℕ) :
    psmr u X Y P T ≤ c * T := by
  have h := psmr_le_add_mul_measureReal_compl (P := P) u hX hY (T := T) MeasurableSet.univ
    (B := c * T) (c := 0) (ae_of_all _ fun ω ↦ ?_)
  · simpa using h
  calc ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω)) ≤ ∑ t ∈ range T, c :=
        sum_le_sum fun t _ ↦ hc _ _
    _ ≤ c * T + Set.univᶜ.indicator (fun _ ↦ (0 : ℝ)) ω := by simp [mul_comm]

end RepeatedGame

end Learning
