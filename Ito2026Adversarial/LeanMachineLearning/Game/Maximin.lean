/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.ZeroSum
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

/-!
# Maximin mixed strategies and the value of `2 × 2` games

For a zero-sum game `u : 𝒳 → 𝒴 → ℝ` on finite action sets, the mixed-strategy maximin value
`nashValue u = ⨆ p, ⨅ q, u(p, q)` is attained, and it can be computed from strategies that
equalize the utilities. For `2 × 2` games without pure-strategy Nash equilibrium, this gives the
classical closed form of the value.

## Main statements

* `exists_forall_nashValue_le`: there is a maximin mixed strategy `p` with
  `v^Nash ≤ ∑ x, p x * u x y` for every `y`;
* `le_nashValue_of_forall_le`, `nashValue_le_of_forall_le`: bounds on `v^Nash` from a mixed
  strategy of either player; `nashValue_eq_of_forall_eq`: the value of a game from equalizing
  strategies;
* `pureMaximin_fin_two`: `v* = max (min a b) (min c d)` for a `2 × 2` game `(a, b; c, d)`;
* `lt_and_lt_or_lt_and_lt_of_not_hasPSNE`: the entries of a `2 × 2` game without PSNE are
  cyclically ordered;
* `nashValue_eq_of_not_hasPSNE`: the value `(a d - b c) / (a - b - c + d)` of a `2 × 2` game
  without PSNE.

## Tags

zero-sum game, maximin, minimax, Nash equilibrium, value of a game
-/

@[expose] public section

open Finset

namespace Learning.ZeroSumGame

section PureMaximin

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

end PureMaximin

section Maximin

variable {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] {u : 𝒳 → 𝒴 → ℝ}

/-- The expected utility of a mixed strategy of the row player against a pure strategy `y` of the
column player. -/
lemma mixedUtility_single_right [DecidableEq 𝒴] (u : 𝒳 → 𝒴 → ℝ) (p : EuclideanSpace ℝ 𝒳)
    (y : 𝒴) : mixedUtility u p (EuclideanSpace.single y 1) = ∑ x, p x * u x y := by
  simp [mixedUtility, PiLp.single_apply]

/-- The expected utility as an average, over the column strategy, of the expected utilities
against pure strategies. -/
lemma mixedUtility_eq_sum_mul_sum (u : 𝒳 → 𝒴 → ℝ) (p : EuclideanSpace ℝ 𝒳)
    (q : EuclideanSpace ℝ 𝒴) : mixedUtility u p q = ∑ y, q y * ∑ x, p x * u x y := by
  simp only [mixedUtility, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- The expected utility as an average, over the row strategy, of the expected utilities of
pure strategies. -/
lemma mixedUtility_eq_sum_mul_sum' (u : 𝒳 → 𝒴 → ℝ) (p : EuclideanSpace ℝ 𝒳)
    (q : EuclideanSpace ℝ 𝒴) : mixedUtility u p q = ∑ x, p x * ∑ y, q y * u x y := by
  simp only [mixedUtility, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  ring

/-- The utilities of a mixed strategy of the row player against all mixed strategies of the column
player are bounded below. -/
lemma bddBelow_range_mixedUtility {p : EuclideanSpace ℝ 𝒳} (hp : p ∈ simplex 𝒳) :
    BddBelow (Set.range fun q : simplex 𝒴 ↦ mixedUtility u p q) :=
  ⟨-∑ x, ∑ y, |u x y|, by
    rintro _ ⟨q, rfl⟩
    exact neg_le_of_abs_le (abs_mixedUtility_le hp q.2)⟩

/-- The guaranteed utilities `⨅ q, u(p, q)` of the mixed strategies `p` are bounded above. -/
lemma bddAbove_range_iInf_mixedUtility [Nonempty 𝒴] :
    BddAbove (Set.range fun p : simplex 𝒳 ↦ ⨅ q : simplex 𝒴, mixedUtility u p q) := by
  obtain ⟨q₀⟩ := (inferInstance : Nonempty (simplex 𝒴))
  refine ⟨∑ x, ∑ y, |u x y|, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact (ciInf_le (bddBelow_range_mixedUtility p.2) q₀).trans
    (le_of_abs_le (abs_mixedUtility_le p.2 q₀.2))

/-- A mixed strategy `p` of the row player that guarantees `v` against every pure strategy of the
column player shows that `v ≤ v^Nash`. -/
lemma le_nashValue_of_forall_le [Nonempty 𝒴] {p : EuclideanSpace ℝ 𝒳} (hp : p ∈ simplex 𝒳)
    {v : ℝ} (h : ∀ y, v ≤ ∑ x, p x * u x y) : v ≤ nashValue u := by
  refine le_ciSup_of_le bddAbove_range_iInf_mixedUtility ⟨p, hp⟩ (le_ciInf fun q ↦ ?_)
  rw [mixedUtility_eq_sum_mul_sum]
  calc v = ∑ y, (q : EuclideanSpace ℝ 𝒴) y * v := by rw [← Finset.sum_mul, q.2.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (h y) (q.2.1 y)

/-- A mixed strategy `q` of the column player that holds every pure strategy of the row player to
at most `v` shows that `v^Nash ≤ v`. -/
lemma nashValue_le_of_forall_le [Nonempty 𝒳] {q : EuclideanSpace ℝ 𝒴} (hq : q ∈ simplex 𝒴)
    {v : ℝ} (h : ∀ x, ∑ y, q y * u x y ≤ v) : nashValue u ≤ v := by
  refine ciSup_le fun p ↦ (ciInf_le (bddBelow_range_mixedUtility p.2) ⟨q, hq⟩).trans ?_
  rw [mixedUtility_eq_sum_mul_sum']
  calc ∑ x, (p : EuclideanSpace ℝ 𝒳) x * ∑ y, q y * u x y
      ≤ ∑ x, (p : EuclideanSpace ℝ 𝒳) x * v :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (p.2.1 x)
    _ = v := by rw [← Finset.sum_mul, p.2.2, one_mul]

/-- **Value of a game from equalizing strategies**: if the mixed strategies `p` and `q` give the
utility `v` against every pure strategy of the other player, then `v^Nash = v`. -/
lemma nashValue_eq_of_forall_eq [Nonempty 𝒳] [Nonempty 𝒴] {p : EuclideanSpace ℝ 𝒳}
    {q : EuclideanSpace ℝ 𝒴} (hp : p ∈ simplex 𝒳) (hq : q ∈ simplex 𝒴) {v : ℝ}
    (hpv : ∀ y, ∑ x, p x * u x y = v) (hqv : ∀ x, ∑ y, q y * u x y = v) : nashValue u = v :=
  le_antisymm (nashValue_le_of_forall_le hq fun x ↦ (hqv x).le)
    (le_nashValue_of_forall_le hp fun y ↦ (hpv y).ge)

/-- **Maximin mixed strategies exist**: the supremum defining `v^Nash` is attained, by a mixed
strategy `p` that guarantees `v^Nash` against every pure strategy of the column player. -/
lemma exists_forall_nashValue_le [Nonempty 𝒳] [Nonempty 𝒴] (u : 𝒳 → 𝒴 → ℝ) :
    ∃ p ∈ simplex 𝒳, ∀ y, nashValue u ≤ ∑ x, p x * u x y := by
  classical
  -- `g p = min_y u(p, y)` is continuous, hence attains its maximum on the compact simplex
  set g : EuclideanSpace ℝ 𝒳 → ℝ := fun p ↦ univ.inf' univ_nonempty fun y ↦ ∑ x, p x * u x y
  have hg : Continuous g := Continuous.finset_inf'_apply _ fun y _ ↦ by fun_prop
  obtain ⟨⟨p₀, hp₀⟩⟩ := (inferInstance : Nonempty (simplex 𝒳))
  obtain ⟨p, hp, hmax⟩ := isCompact_simplex.exists_isMaxOn ⟨p₀, hp₀⟩ hg.continuousOn
  have hle : nashValue u ≤ g p := by
    refine ciSup_le fun p' ↦ le_trans ?_ (hmax p'.2)
    refine Finset.le_inf' _ _ fun y _ ↦ ?_
    rw [← mixedUtility_single_right]
    exact ciInf_le (bddBelow_range_mixedUtility p'.2) ⟨_, single_mem_simplex y⟩
  exact ⟨p, hp, fun y ↦ hle.trans (Finset.inf'_le (fun y ↦ ∑ x, p x * u x y) (mem_univ y))⟩

end Maximin

/-! ### Games with two actions per player

For a `2 × 2` game we write `a = u 0 0`, `b = u 0 1`, `c = u 1 0`, `d = u 1 1`. -/

section TwoByTwo

variable {u : Fin 2 → Fin 2 → ℝ}

/-- The pure-strategy maximin value of a `2 × 2` game is
`max (min (u 0 0) (u 0 1)) (min (u 1 0) (u 1 1))`. -/
lemma pureMaximin_fin_two (u : Fin 2 → Fin 2 → ℝ) :
    pureMaximin u = max (min (u 0 0) (u 0 1)) (min (u 1 0) (u 1 1)) := by
  have hinf (x : Fin 2) : ⨅ y, u x y = min (u x 0) (u x 1) :=
    le_antisymm (le_min (ciInf_le (Set.finite_range _).bddBelow 0)
      (ciInf_le (Set.finite_range _).bddBelow 1))
      (le_ciInf (Fin.forall_fin_two.2 ⟨min_le_left _ _, min_le_right _ _⟩))
  simp_rw [pureMaximin, hinf]
  have hbdd := (Set.finite_range fun x : Fin 2 ↦ min (u x 0) (u x 1)).bddAbove
  exact le_antisymm (ciSup_le (Fin.forall_fin_two.2 ⟨le_max_left _ _, le_max_right _ _⟩))
    (max_le (le_ciSup hbdd 0) (le_ciSup hbdd 1))

/-- A `2 × 2` game without pure-strategy Nash equilibrium has cyclically ordered entries: either
both diagonal entries are larger than both off-diagonal entries, or the reverse. -/
lemma lt_and_lt_or_lt_and_lt_of_not_hasPSNE (h : ¬ HasPSNE u) :
    (u 0 1 < u 0 0 ∧ u 1 0 < u 0 0 ∧ u 0 1 < u 1 1 ∧ u 1 0 < u 1 1) ∨
      (u 0 0 < u 0 1 ∧ u 0 0 < u 1 0 ∧ u 1 1 < u 0 1 ∧ u 1 1 < u 1 0) := by
  have hpsne (x y : Fin 2) (h1 : ∀ x', u x' y ≤ u x y) (h2 : ∀ y', u x y ≤ u x y') : False :=
    h ⟨x, y, h1, h2⟩
  have h00 (h1 : u 1 0 ≤ u 0 0) (h2 : u 0 0 ≤ u 0 1) : False :=
    hpsne 0 0 (Fin.forall_fin_two.2 ⟨le_rfl, h1⟩) (Fin.forall_fin_two.2 ⟨le_rfl, h2⟩)
  have h01 (h1 : u 1 1 ≤ u 0 1) (h2 : u 0 1 ≤ u 0 0) : False :=
    hpsne 0 1 (Fin.forall_fin_two.2 ⟨le_rfl, h1⟩) (Fin.forall_fin_two.2 ⟨h2, le_rfl⟩)
  have h10 (h1 : u 0 0 ≤ u 1 0) (h2 : u 1 0 ≤ u 1 1) : False :=
    hpsne 1 0 (Fin.forall_fin_two.2 ⟨h1, le_rfl⟩) (Fin.forall_fin_two.2 ⟨le_rfl, h2⟩)
  have h11 (h1 : u 0 1 ≤ u 1 1) (h2 : u 1 1 ≤ u 1 0) : False :=
    hpsne 1 1 (Fin.forall_fin_two.2 ⟨h1, le_rfl⟩) (Fin.forall_fin_two.2 ⟨h2, le_rfl⟩)
  rcases lt_or_ge (u 1 0) (u 0 0) with hca | hac
  · have hba : u 0 1 < u 0 0 := lt_of_not_ge fun h' ↦ h00 hca.le h'
    have hbd : u 0 1 < u 1 1 := lt_of_not_ge fun h' ↦ h01 h' hba.le
    have hcd : u 1 0 < u 1 1 := lt_of_not_ge fun h' ↦ h11 hbd.le h'
    exact Or.inl ⟨hba, hca, hbd, hcd⟩
  · have hdc : u 1 1 < u 1 0 := lt_of_not_ge fun h' ↦ h10 hac h'
    have hdb : u 1 1 < u 0 1 := lt_of_not_ge fun h' ↦ h11 h' hdc.le
    have hab : u 0 0 < u 0 1 := lt_of_not_ge fun h' ↦ h01 hdb.le h'
    have hac' : u 0 0 < u 1 0 := lt_of_not_ge fun h' ↦ h00 h' hab.le
    exact Or.inr ⟨hab, hac', hdb, hdc⟩

/-- **Value of a `2 × 2` game without pure-strategy Nash equilibrium**: for the entries
`a = u 0 0`, `b = u 0 1`, `c = u 1 0`, `d = u 1 1`, `v^Nash = (a d - b c) / (a - b - c + d)`.
The maximin strategy `(d - c, a - b) / (a - b - c + d)` of the row player and the minimax strategy
`(d - b, a - c) / (a - b - c + d)` of the column player equalize the utilities. -/
lemma nashValue_eq_of_not_hasPSNE (h : ¬ HasPSNE u) :
    nashValue u = (u 0 0 * u 1 1 - u 0 1 * u 1 0) / (u 0 0 - u 0 1 - u 1 0 + u 1 1) := by
  -- the four weights `e / D` below have numerators `e` of the sign of the denominator `D`
  have hw : ∀ e ∈ ({u 1 1 - u 1 0, u 0 0 - u 0 1, u 1 1 - u 0 1, u 0 0 - u 1 0} : Set ℝ),
      0 ≤ e / (u 0 0 - u 0 1 - u 1 0 + u 1 1) := by
    rcases lt_and_lt_or_lt_and_lt_of_not_hasPSNE h with h' | h'
    · rintro e (rfl | rfl | rfl | rfl | rfl) <;> exact div_nonneg (by linarith) (by linarith)
    · rintro e (rfl | rfl | rfl | rfl | rfl) <;>
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
  have hD : u 0 0 - u 0 1 - u 1 0 + u 1 1 ≠ 0 := by
    rcases lt_and_lt_or_lt_and_lt_of_not_hasPSNE h with h' | h' <;> linarith
  refine nashValue_eq_of_forall_eq
    (p := WithLp.toLp 2 ![(u 1 1 - u 1 0) / (u 0 0 - u 0 1 - u 1 0 + u 1 1),
      (u 0 0 - u 0 1) / (u 0 0 - u 0 1 - u 1 0 + u 1 1)])
    (q := WithLp.toLp 2 ![(u 1 1 - u 0 1) / (u 0 0 - u 0 1 - u 1 0 + u 1 1),
      (u 0 0 - u 1 0) / (u 0 0 - u 0 1 - u 1 0 + u 1 1)]) ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_
  · exact Fin.forall_fin_two.2 ⟨hw _ (by simp), hw _ (by simp)⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · exact Fin.forall_fin_two.2 ⟨hw _ (by simp), hw _ (by simp)⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;>
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;>
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring

end TwoByTwo

end Learning.ZeroSumGame
