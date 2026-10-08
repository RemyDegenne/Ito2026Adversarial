/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.Convex.Simplex
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Two-player zero-sum games

A two-player zero-sum game with action sets `𝒳` (the row player, or learner) and `𝒴` (the column
player, or adversary) is a utility function `u : 𝒳 → 𝒴 → ℝ`: `u x y` is the reward of the row
player when the actions `x` and `y` are played, and `-u x y` the reward of the column player.

## Main definitions

* `IsPSNE u x y`, `IsStrictPSNE u x y`, `HasPSNE u`: pure-strategy Nash equilibria
  `u x' y ≤ u x y ≤ u x y'` (strict when `x' ≠ x`, `y' ≠ y`).
* `pureMaximin u = ⨆ x, ⨅ y, u x y`: the pure-strategy maximin value `v*`, the value that a
  deterministic row player can guarantee. It is the value of a PSNE when one exists
  (`IsPSNE.pureMaximin_eq`).
* `mixedUtility u p q = ∑ x y, p x * q y * u x y`: the expected utility of the mixed strategies
  `p`, `q` (elements of `simplex`), the bilinear form `pᵀ U q` of the payoff matrix
  (`mixedUtility_eq_dotProduct_mulVec`); `IsMSNE u p q`: mixed-strategy Nash equilibria;
  `nashValue u = ⨆ p, ⨅ q, mixedUtility u p q`: the mixed-strategy maximin value, which is the
  value `v^Nash` of all Nash equilibria (von Neumann's minimax theorem). It is at least the
  pure-strategy maximin value (`pureMaximin_le_nashValue`, so that `mixGap_nonneg`).
* Gaps: for a PSNE `(x, y)`, `rowGap u x y x' = u x y - u x' y` and
  `colGap u x y y' = u x y' - u x y` (`Δʳ_{x'}`, `Δᶜ_{y'}`), with minima over `x' ≠ x`, `y' ≠ y`
  (`rowGapMin`, `colGapMin`); `mixGap u = nashValue u - pureMaximin u` (`Δ^mix`);
  `pairGap u x y = pureMaximin u - u x y` (`Δ_{xy}`).
-/

@[expose] public section

open Finset

namespace Learning.ZeroSumGame

variable {𝒳 𝒴 : Type*} {u : 𝒳 → 𝒴 → ℝ} {x : 𝒳} {y : 𝒴}

/-- `(x, y)` is a pure-strategy Nash equilibrium of `u`: `u x' y ≤ u x y ≤ u x y'` for all `x'`,
`y'`. -/
def IsPSNE (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) : Prop :=
  (∀ x', u x' y ≤ u x y) ∧ ∀ y', u x y ≤ u x y'

/-- `(x, y)` is a strict pure-strategy Nash equilibrium of `u`: `u x' y < u x y < u x y'` for all
`x' ≠ x`, `y' ≠ y`. -/
def IsStrictPSNE (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) : Prop :=
  (∀ x' ≠ x, u x' y < u x y) ∧ ∀ y' ≠ y, u x y < u x y'

lemma IsStrictPSNE.isPSNE (h : IsStrictPSNE u x y) : IsPSNE u x y := by
  refine ⟨fun x' ↦ ?_, fun y' ↦ ?_⟩
  · by_cases hx : x' = x
    · simp [hx]
    · exact (h.1 x' hx).le
  · by_cases hy : y' = y
    · simp [hy]
    · exact (h.2 y' hy).le

/-- The game `u` has a pure-strategy Nash equilibrium. -/
def HasPSNE (u : 𝒳 → 𝒴 → ℝ) : Prop := ∃ x y, IsPSNE u x y

/-- The pure-strategy maximin value `v* = max_x min_y u x y`. -/
noncomputable def pureMaximin (u : 𝒳 → 𝒴 → ℝ) : ℝ := ⨆ x, ⨅ y, u x y

lemma IsPSNE.iInf_eq [Finite 𝒴] (h : IsPSNE u x y) : ⨅ y', u x y' = u x y :=
  have : Nonempty 𝒴 := ⟨y⟩
  le_antisymm (ciInf_le (Set.finite_range _).bddBelow y) (le_ciInf h.2)

/-- The pure-strategy maximin value is the value of any pure-strategy Nash equilibrium. -/
lemma IsPSNE.pureMaximin_eq [Finite 𝒳] [Finite 𝒴] (h : IsPSNE u x y) :
    pureMaximin u = u x y := by
  have : Nonempty 𝒳 := ⟨x⟩
  refine le_antisymm (ciSup_le fun x' ↦ ?_) ?_
  · exact (ciInf_le (Set.finite_range _).bddBelow y).trans (h.1 x')
  · rw [← h.iInf_eq]
    exact le_ciSup (f := fun x ↦ ⨅ y', u x y') (Set.finite_range _).bddAbove x

/-- The sub-optimality gap `Δʳ_{x'} = u x y - u x' y` of the row action `x'` at the equilibrium
`(x, y)`. -/
def rowGap (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) (x' : 𝒳) : ℝ := u x y - u x' y

/-- The sub-optimality gap `Δᶜ_{y'} = u x y' - u x y` of the column action `y'` at the
equilibrium `(x, y)`. -/
def colGap (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) (y' : 𝒴) : ℝ := u x y' - u x y

lemma IsStrictPSNE.rowGap_pos (h : IsStrictPSNE u x y) {x' : 𝒳} (hx' : x' ≠ x) :
    0 < rowGap u x y x' :=
  sub_pos.2 (h.1 x' hx')

lemma IsStrictPSNE.colGap_pos (h : IsStrictPSNE u x y) {y' : 𝒴} (hy' : y' ≠ y) :
    0 < colGap u x y y' :=
  sub_pos.2 (h.2 y' hy')

/-- The minimal row gap `Δʳ_min = min_{x' ≠ x} Δʳ_{x'}`. -/
noncomputable def rowGapMin (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) : ℝ :=
  ⨅ x' : {x' // x' ≠ x}, rowGap u x y x'

/-- The minimal column gap `Δᶜ_min = min_{y' ≠ y} Δᶜ_{y'}`. -/
noncomputable def colGapMin (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) : ℝ :=
  ⨅ y' : {y' // y' ≠ y}, colGap u x y y'

/-- The gap `Δ_{xy} = v* - u x y` of the action pair `(x, y)` to the pure-strategy maximin value
(possibly negative). -/
noncomputable def pairGap (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳) (y : 𝒴) : ℝ := pureMaximin u - u x y

/-! ### Mixed strategies -/

section Mixed

variable [Fintype 𝒳] [Fintype 𝒴]

/-- The expected utility `∑ x y, p x * q y * u x y` of the mixed strategies `p` and `q`. -/
def mixedUtility (u : 𝒳 → 𝒴 → ℝ) (p : EuclideanSpace ℝ 𝒳) (q : EuclideanSpace ℝ 𝒴) : ℝ :=
  ∑ x, ∑ y, p x * q y * u x y

open Matrix in
/-- The expected utility is the bilinear form `pᵀ U q` of the payoff matrix `U = (u x y)`. -/
lemma mixedUtility_eq_dotProduct_mulVec (u : 𝒳 → 𝒴 → ℝ) (p : EuclideanSpace ℝ 𝒳)
    (q : EuclideanSpace ℝ 𝒴) : mixedUtility u p q = p.ofLp ⬝ᵥ (Matrix.of u *ᵥ q.ofLp) := by
  simp only [mixedUtility, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  ring

/-- The expected utility of a pure strategy `x` of the row player against a mixed strategy. -/
lemma mixedUtility_single_left [DecidableEq 𝒳] (u : 𝒳 → 𝒴 → ℝ) (x : 𝒳)
    (q : EuclideanSpace ℝ 𝒴) : mixedUtility u (EuclideanSpace.single x 1) q = ∑ y, q y * u x y := by
  simp [mixedUtility, PiLp.single_apply]

/-- The expected utility of mixed strategies in the simplex is bounded by `∑ x y, |u x y|`. -/
lemma abs_mixedUtility_le {p : EuclideanSpace ℝ 𝒳} {q : EuclideanSpace ℝ 𝒴} (hp : p ∈ simplex 𝒳)
    (hq : q ∈ simplex 𝒴) : |mixedUtility u p q| ≤ ∑ x, ∑ y, |u x y| := by
  unfold mixedUtility
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ ↦ ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
  have hpx : p x ≤ 1 := le_one_of_mem_simplex hp x
  have hqy : q y ≤ 1 := le_one_of_mem_simplex hq y
  rw [abs_mul, abs_mul, abs_of_nonneg (hp.1 x), abs_of_nonneg (hq.1 y)]
  calc p x * q y * |u x y| ≤ 1 * 1 * |u x y| :=
        mul_le_mul (mul_le_mul hpx hqy (hq.1 y) zero_le_one) le_rfl (abs_nonneg _) (by norm_num)
    _ = |u x y| := by ring

/-- `(p, q)` is a mixed-strategy Nash equilibrium of `u`: `p`, `q` are distributions and
`u(p', q) ≤ u(p, q) ≤ u(p, q')` for all distributions `p'`, `q'`. -/
def IsMSNE (u : 𝒳 → 𝒴 → ℝ) (p : EuclideanSpace ℝ 𝒳) (q : EuclideanSpace ℝ 𝒴) : Prop :=
  p ∈ simplex 𝒳 ∧ q ∈ simplex 𝒴 ∧
    (∀ p' ∈ simplex 𝒳, mixedUtility u p' q ≤ mixedUtility u p q) ∧
    ∀ q' ∈ simplex 𝒴, mixedUtility u p q ≤ mixedUtility u p q'

/-- The mixed-strategy maximin value `max_p min_q u(p, q)`, which is the value `v^Nash` of the
Nash equilibria of the game (von Neumann's minimax theorem). -/
noncomputable def nashValue (u : 𝒳 → 𝒴 → ℝ) : ℝ :=
  ⨆ p : simplex 𝒳, ⨅ q : simplex 𝒴, mixedUtility u p q

/-- The gap `Δ^mix = v^Nash - v*` between the Nash value and the pure-strategy maximin value. -/
noncomputable def mixGap (u : 𝒳 → 𝒴 → ℝ) : ℝ := nashValue u - pureMaximin u

/-- The mixed-strategy maximin value is at least the pure-strategy maximin value. -/
lemma pureMaximin_le_nashValue [Nonempty 𝒳] [Nonempty 𝒴] (u : 𝒳 → 𝒴 → ℝ) :
    pureMaximin u ≤ nashValue u := by
  classical
  have hbdd (p : simplex 𝒳) :
      BddBelow (Set.range fun q : simplex 𝒴 ↦ mixedUtility u p q) :=
    ⟨-∑ x, ∑ y, |u x y|, by
      rintro _ ⟨q, rfl⟩
      exact neg_le_of_abs_le (abs_mixedUtility_le p.2 q.2)⟩
  have hbdd' : BddAbove (Set.range fun p : simplex 𝒳 ↦
      ⨅ q : simplex 𝒴, mixedUtility u p q) := by
    obtain ⟨q₀⟩ := (inferInstance : Nonempty (simplex 𝒴))
    refine ⟨∑ x, ∑ y, |u x y|, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (ciInf_le (hbdd p) q₀).trans (le_of_abs_le (abs_mixedUtility_le p.2 q₀.2))
  refine ciSup_le fun x ↦
    le_trans ?_ (le_ciSup hbdd' ⟨EuclideanSpace.single x 1, single_mem_simplex x⟩)
  refine le_ciInf fun q ↦ ?_
  rw [mixedUtility_single_left]
  calc ⨅ y, u x y = ∑ y, (q : EuclideanSpace ℝ 𝒴) y * ⨅ y, u x y := by
        rw [← Finset.sum_mul, q.2.2, one_mul]
    _ ≤ ∑ y, (q : EuclideanSpace ℝ 𝒴) y * u x y := Finset.sum_le_sum fun y _ ↦
      mul_le_mul_of_nonneg_left (ciInf_le (Set.finite_range _).bddBelow y) (q.2.1 y)

lemma mixGap_nonneg [Nonempty 𝒳] [Nonempty 𝒴] (u : 𝒳 → 𝒴 → ℝ) : 0 ≤ mixGap u :=
  sub_nonneg.2 (pureMaximin_le_nashValue u)

end Mixed

end Learning.ZeroSumGame
