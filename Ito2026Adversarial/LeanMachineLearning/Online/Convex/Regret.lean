/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.Convex.Simplex
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Regret of online learning

In online learning, at each round `t = 0, 1, …` the learner plays a point `x t` of a set `α`,
then the environment reveals a loss function `f t : α → ℝ` and the learner suffers `f t (x t)`.
The performance over `T` rounds is measured by the regret against a fixed comparator `u`,
`ocoRegret f x T u = ∑_{t < T} f t (x t) - ∑_{t < T} f t u`.

The protocol is stated for plain sequences: the loss sequence is oblivious (fixed in advance) and
an algorithm is described by the sequence of its iterates. The runs of the deterministic
algorithms of the LML framework are related to these sequences by
`OnlineLearner.action_ae_eq_iterate` (`Online/Convex/OnlineLearner.lean`).

## Main definitions

* `ocoRegret f x T u`: the regret of the plays `x` against the comparator `u` for the losses `f`
  (the regret of online convex optimization, although the definition needs no convexity);
* `linRegret ℓ w T u`: the regret of online linear optimization, `ocoRegret` for the linear
  losses `⟪ℓ t, ·⟫` of a real inner product space;
* `cumLoss ℓ t₁ t₂ = ∑_{t₁ ≤ t < t₂} ℓ t`: the cumulative loss between two rounds;
* `gradSeq f x t = ∇f t (x t)`: the gradient feedback of round `t`;
* the experts problem: `expertRegret ℓ w T`, the regret of the weights `w` against the best
  fixed expert for the loss vectors `ℓ : ℕ → ι → ℝ`; for loss vectors in `EuclideanSpace ℝ ι`,
  `LossesIn ℓ s T` (all the coordinates lie in `s`) and `IsBestCoord ℓ T j` (`j` is a best
  expert in hindsight).

## Main results

* `ocoRegret_eq_sum_sub`, `ocoRegret_succ`, `ocoRegret_add` (additivity in the horizon),
  `ocoRegret_sub_ocoRegret` (change of comparator), `ocoRegret_add_losses`,
  `ocoRegret_const_mul`, `ocoRegret_add_const` (dependence on the losses);
* `ocoRegret_le_sum_of_hasSubgradientWithinAt`, `ocoRegret_le_linRegret_gradSeq`: the regret of
  convex losses is at most the regret of their linearizations (with LML's subgradients);
* `linRegret_eq_sum_inner_sub`, `linRegret_eq_sub_inner_cumLoss`, `linRegret_add`,
  `linRegret_sub_linRegret`;
* `expertRegret_eq_iSup_ocoRegret`: the expert regret is the largest regret against a vertex of
  the simplex; `IsBestCoord.linRegret_le`: on the simplex, the regret is largest against the
  vertex of a best expert.
-/

@[expose] public section

open Finset
open scoped RealInnerProductSpace

namespace Learning

/-! ### Regret for general losses -/

section General

variable {α : Type*} {f g : ℕ → α → ℝ} {x : ℕ → α} {T : ℕ} {u : α}

/-- The regret `∑_{t < T} f t (x t) - ∑_{t < T} f t u` of the plays `x` against the comparator
`u` over `T` rounds of the losses `f`. -/
noncomputable def ocoRegret (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) : ℝ :=
  ∑ t ∈ range T, f t (x t) - ∑ t ∈ range T, f t u

lemma ocoRegret_eq_sum_sub (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    ocoRegret f x T u = ∑ t ∈ range T, (f t (x t) - f t u) := by
  simp [ocoRegret, sum_sub_distrib]

@[simp]
lemma ocoRegret_zero (f : ℕ → α → ℝ) (x : ℕ → α) (u : α) : ocoRegret f x 0 u = 0 := by
  simp [ocoRegret]

lemma ocoRegret_succ (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    ocoRegret f x (T + 1) u = ocoRegret f x T u + (f T (x T) - f T u) := by
  simp only [ocoRegret_eq_sum_sub, sum_range_succ]

/-- The regret is additive in the horizon: the regret over `T₁ + T₂` rounds is the regret over
the first `T₁` rounds plus the regret over the next `T₂` rounds. -/
lemma ocoRegret_add (f : ℕ → α → ℝ) (x : ℕ → α) (T₁ T₂ : ℕ) (u : α) :
    ocoRegret f x (T₁ + T₂) u =
      ocoRegret f x T₁ u + ocoRegret (fun t ↦ f (T₁ + t)) (fun t ↦ x (T₁ + t)) T₂ u := by
  simp only [ocoRegret_eq_sum_sub, sum_range_add]

/-- The regret of the constant plays `u` against `u` is zero. -/
@[simp]
lemma ocoRegret_const_self (f : ℕ → α → ℝ) (T : ℕ) (u : α) : ocoRegret f (fun _ ↦ u) T u = 0 := by
  simp [ocoRegret]

/-- Changing the comparator changes the regret by the difference of the cumulative losses of the
comparators. -/
lemma ocoRegret_sub_ocoRegret (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u v : α) :
    ocoRegret f x T u - ocoRegret f x T v = ∑ t ∈ range T, (f t v - f t u) := by
  simp only [ocoRegret, sum_sub_distrib]
  ring

lemma ocoRegret_add_losses (f g : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    ocoRegret (fun t a ↦ f t a + g t a) x T u = ocoRegret f x T u + ocoRegret g x T u := by
  simp only [ocoRegret, sum_add_distrib]
  ring

lemma ocoRegret_const_mul (c : ℝ) (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    ocoRegret (fun t a ↦ c * f t a) x T u = c * ocoRegret f x T u := by
  simp only [ocoRegret, ← mul_sum, mul_sub]

/-- Adding a constant to the loss of each round does not change the regret. -/
@[simp]
lemma ocoRegret_add_const (f : ℕ → α → ℝ) (c : ℕ → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    ocoRegret (fun t a ↦ f t a + c t) x T u = ocoRegret f x T u := by
  simp [ocoRegret_eq_sum_sub]

/-- The regret for losses precomposed with a map `φ` is the regret of the images by `φ`. -/
lemma ocoRegret_comp {β : Type*} (f : ℕ → α → ℝ) (φ : β → α) (x : ℕ → β) (T : ℕ) (u : β) :
    ocoRegret (fun t b ↦ f t (φ b)) x T u = ocoRegret f (fun t ↦ φ (x t)) T (φ u) := rfl

/-- Comparison of the regrets of the same plays for two loss sequences. -/
lemma ocoRegret_le_ocoRegret (h : ∀ t < T, f t (x t) - f t u ≤ g t (x t) - g t u) :
    ocoRegret f x T u ≤ ocoRegret g x T u := by
  rw [ocoRegret_eq_sum_sub, ocoRegret_eq_sum_sub]
  exact sum_le_sum fun t ht ↦ h t (mem_range.1 ht)

end General

/-- **Linearization of the regret.** If `G t` is a subgradient on `K` of the loss `f t` at the
play `x t` for every round `t < T`, the regret against a comparator `u ∈ K` is at most
`∑_{t < T} G t (x t - u)`. -/
lemma ocoRegret_le_sum_of_hasSubgradientWithinAt {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {f : ℕ → E → ℝ} {x : ℕ → E} {T : ℕ} {u : E} {G : ℕ → E →L[ℝ] ℝ}
    {K : Set E} (hG : ∀ t < T, HasSubgradientWithinAt (f t) (G t) K (x t)) (hu : u ∈ K) :
    ocoRegret f x T u ≤ ∑ t ∈ range T, G t (x t - u) := by
  rw [ocoRegret_eq_sum_sub]
  refine sum_le_sum fun t ht ↦ ?_
  have h := hasSubgradientWithinAt_iff_le.1 (hG t (mem_range.1 ht)) u hu
  simp only [map_sub] at h ⊢
  linarith

/-! ### Cumulative losses -/

section CumLoss

variable {M : Type*} [AddCommMonoid M] (ℓ : ℕ → M)

/-- The cumulative loss `ℓ_{t₁:t₂} = ∑_{t₁ ≤ t < t₂} ℓ t` between the rounds `t₁` and `t₂`. -/
def cumLoss (ℓ : ℕ → M) (t₁ t₂ : ℕ) : M := ∑ t ∈ Ico t₁ t₂, ℓ t

@[simp]
lemma cumLoss_self (t : ℕ) : cumLoss ℓ t t = 0 := by simp [cumLoss]

lemma cumLoss_zero_left (T : ℕ) : cumLoss ℓ 0 T = ∑ t ∈ range T, ℓ t := by
  rw [cumLoss, range_eq_Ico]

lemma cumLoss_add_cumLoss {t₁ t₂ t₃ : ℕ} (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) :
    cumLoss ℓ t₁ t₂ + cumLoss ℓ t₂ t₃ = cumLoss ℓ t₁ t₃ :=
  sum_Ico_consecutive ℓ h₁₂ h₂₃

lemma cumLoss_succ {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) : cumLoss ℓ t₁ (t₂ + 1) = cumLoss ℓ t₁ t₂ + ℓ t₂ :=
  sum_Ico_succ_top h ℓ

end CumLoss

/-! ### Online linear optimization -/

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regret of online linear optimization: the regret `∑_{t < T} ⟪ℓ t, w t⟫ - ∑_{t < T} ⟪ℓ t, u⟫`
of the iterates `w` against `u` for the linear losses `⟪ℓ t, ·⟫` (`linRegret_eq_ocoRegret`). -/
noncomputable def linRegret (ℓ w : ℕ → E) (T : ℕ) (u : E) : ℝ :=
  ocoRegret (fun t v ↦ ⟪ℓ t, v⟫) w T u

/-- The regret of online linear optimization is `ocoRegret` for the linear losses `⟪ℓ t, ·⟫`. -/
lemma linRegret_eq_ocoRegret (ℓ w : ℕ → E) (T : ℕ) (u : E) :
    linRegret ℓ w T u = ocoRegret (fun t v ↦ ⟪ℓ t, v⟫) w T u := rfl

lemma linRegret_eq_sum_inner_sub (ℓ w : ℕ → E) (T : ℕ) (u : E) :
    linRegret ℓ w T u = ∑ t ∈ range T, ⟪ℓ t, w t - u⟫ := by
  simp [linRegret, ocoRegret_eq_sum_sub, inner_sub_right]

lemma linRegret_eq_sub_inner_cumLoss (ℓ w : ℕ → E) (T : ℕ) (u : E) :
    linRegret ℓ w T u = ∑ t ∈ range T, ⟪ℓ t, w t⟫ - ⟪cumLoss ℓ 0 T, u⟫ := by
  simp [linRegret, ocoRegret, cumLoss_zero_left, sum_inner]

@[simp]
lemma linRegret_zero (ℓ w : ℕ → E) (u : E) : linRegret ℓ w 0 u = 0 := ocoRegret_zero _ _ _

lemma linRegret_succ (ℓ w : ℕ → E) (T : ℕ) (u : E) :
    linRegret ℓ w (T + 1) u = linRegret ℓ w T u + ⟪ℓ T, w T - u⟫ := by
  simp [linRegret, ocoRegret_succ, inner_sub_right]

/-- The regret of online linear optimization is additive in the horizon. -/
lemma linRegret_add (ℓ w : ℕ → E) (T₁ T₂ : ℕ) (u : E) :
    linRegret ℓ w (T₁ + T₂) u =
      linRegret ℓ w T₁ u + linRegret (fun t ↦ ℓ (T₁ + t)) (fun t ↦ w (T₁ + t)) T₂ u :=
  ocoRegret_add _ _ _ _ _

/-- Changing the comparator from `v` to `u` changes the regret by `⟪ℓ_{0:T}, v - u⟫`. -/
lemma linRegret_sub_linRegret (ℓ w : ℕ → E) (T : ℕ) (u v : E) :
    linRegret ℓ w T u - linRegret ℓ w T v = ⟪cumLoss ℓ 0 T, v - u⟫ := by
  simp [linRegret, ocoRegret_sub_ocoRegret, cumLoss_zero_left, sum_inner, inner_sub_right]

variable [CompleteSpace E]

/-- The gradient feedback of round `t`: the gradient `∇f t (x t)` of the loss of round `t` at the
point played at round `t`. -/
noncomputable def gradSeq (f : ℕ → E → ℝ) (x : ℕ → E) (t : ℕ) : E := gradient (f t) (x t)

lemma inner_gradSeq (f : ℕ → E → ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    ⟪gradSeq f x t, v⟫ = fderiv ℝ (f t) (x t) v := by
  simp [gradSeq, gradient, InnerProductSpace.toDual_symm_apply]

/-- **Linearization of the regret of convex losses.** For losses `f t` convex on `K` and
differentiable at the plays `x t ∈ K`, the regret against `u ∈ K` is at most the regret of online
linear optimization for the gradient feedback `∇f t (x t)`. -/
lemma ocoRegret_le_linRegret_gradSeq {f : ℕ → E → ℝ} {x : ℕ → E} {T : ℕ} {u : E} {K : Set E}
    (hf : ∀ t < T, ConvexOn ℝ K (f t)) (hd : ∀ t < T, DifferentiableAt ℝ (f t) (x t))
    (hx : ∀ t < T, x t ∈ K) (hu : u ∈ K) :
    ocoRegret f x T u ≤ linRegret (gradSeq f x) x T u := by
  refine (ocoRegret_le_sum_of_hasSubgradientWithinAt (G := fun t ↦ fderiv ℝ (f t) (x t))
    (fun t ht ↦ (hd t ht).hasFDerivAt.hasSubgradientWithinAt (hf t ht) (hx t ht)) hu).trans_eq ?_
  simp [linRegret_eq_sum_inner_sub, inner_gradSeq]

end Linear

/-! ### The experts problem -/

section Experts

variable {ι : Type*}

/-- The regret of the weights `w` against the best fixed expert over `T` rounds of the loss
vectors `ℓ`: `∑_{t < T} ∑_i w t i * ℓ t i - min_i ∑_{t < T} ℓ t i`. It is the largest regret
(`ocoRegret`) of the linear losses `p ↦ ∑_i p i * ℓ t i` against a vertex of the simplex
(`expertRegret_eq_iSup_ocoRegret`). -/
noncomputable def expertRegret [Fintype ι] (ℓ w : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ∑ i, w t i * ℓ t i - ⨅ i, ∑ t ∈ range T, ℓ t i

section Fintype

variable [Fintype ι] [DecidableEq ι]

/-- The regret against the expert `i`, a vertex of the simplex. -/
lemma ocoRegret_single_eq (ℓ w : ℕ → ι → ℝ) (T : ℕ) (i : ι) :
    ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) w T (Pi.single i 1) =
      ∑ t ∈ range T, ∑ j, w t j * ℓ t j - ∑ t ∈ range T, ℓ t i := by
  simp [ocoRegret, Pi.single_apply]

lemma ocoRegret_single_le_expertRegret (ℓ w : ℕ → ι → ℝ) (T : ℕ) (i : ι) :
    ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) w T (Pi.single i 1) ≤ expertRegret ℓ w T := by
  rw [ocoRegret_single_eq, expertRegret]
  gcongr
  exact ciInf_le (Set.finite_range _).bddBelow i

/-- The expert regret is the largest regret against a vertex of the simplex. -/
lemma expertRegret_eq_iSup_ocoRegret [Nonempty ι] (ℓ w : ℕ → ι → ℝ) (T : ℕ) :
    expertRegret ℓ w T = ⨆ i, ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) w T (Pi.single i 1) := by
  refine le_antisymm ?_ (ciSup_le fun i ↦ ocoRegret_single_le_expertRegret ℓ w T i)
  obtain ⟨i, hi⟩ := Finite.exists_min fun i : ι ↦ ∑ t ∈ range T, ℓ t i
  have h : ⨅ i, ∑ t ∈ range T, ℓ t i = ∑ t ∈ range T, ℓ t i :=
    le_antisymm (ciInf_le (Set.finite_range _).bddBelow i) (le_ciInf hi)
  calc expertRegret ℓ w T
      = ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) w T (Pi.single i 1) := by
        rw [ocoRegret_single_eq, expertRegret, h]
    _ ≤ ⨆ i, ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) w T (Pi.single i 1) :=
        le_ciSup (f := fun i ↦ ocoRegret (fun t p ↦ ∑ j, p j * ℓ t j) w T (Pi.single i 1))
          (Set.finite_range _).bddAbove i

end Fintype

variable {ℓ : ℕ → EuclideanSpace ℝ ι} {s s' : Set ℝ} {T T' : ℕ}

/-- The loss vectors `ℓ t`, `t < T`, have all their coordinates in `s`. -/
def LossesIn (ℓ : ℕ → EuclideanSpace ℝ ι) (s : Set ℝ) (T : ℕ) : Prop :=
  ∀ t < T, ∀ i, ℓ t i ∈ s

lemma LossesIn.mono (h : LossesIn ℓ s T) (hs : s ⊆ s') : LossesIn ℓ s' T :=
  fun t ht i ↦ hs (h t ht i)

lemma LossesIn.of_le (h : LossesIn ℓ s T) (hT : T' ≤ T) : LossesIn ℓ s T' :=
  fun t ht ↦ h t (ht.trans_le hT)

/-- The coordinate `j` has the smallest cumulative loss `∑_{t < T} ℓ t j` over `T` rounds: it is
a best expert in hindsight. -/
def IsBestCoord (ℓ : ℕ → EuclideanSpace ℝ ι) (T : ℕ) (j : ι) : Prop :=
  ∀ i, ∑ t ∈ range T, ℓ t j ≤ ∑ t ∈ range T, ℓ t i

lemma exists_isBestCoord [Finite ι] [Nonempty ι] (ℓ : ℕ → EuclideanSpace ℝ ι) (T : ℕ) :
    ∃ j, IsBestCoord ℓ T j :=
  Finite.exists_min _

/-- On the simplex, the regret of online linear optimization is largest against the vertex of a
best expert in hindsight. -/
lemma IsBestCoord.linRegret_le [Fintype ι] [DecidableEq ι] {j : ι} (hj : IsBestCoord ℓ T j)
    (w : ℕ → EuclideanSpace ℝ ι) {u : EuclideanSpace ℝ ι} (hu : u ∈ simplex ι) :
    linRegret ℓ w T u ≤ linRegret ℓ w T (EuclideanSpace.single j 1) := by
  rw [← sub_nonpos, linRegret_sub_linRegret, inner_sub_right, sub_nonpos]
  have hL (i : ι) : (cumLoss ℓ 0 T) i = ∑ t ∈ range T, ℓ t i := by simp [cumLoss_zero_left]
  calc ⟪cumLoss ℓ 0 T, EuclideanSpace.single j 1⟫
      = ∑ i, u i * ∑ t ∈ range T, ℓ t j := by
        rw [← sum_mul, hu.2, one_mul, EuclideanSpace.inner_single_right, hL]
        simp
    _ ≤ ∑ i, u i * ∑ t ∈ range T, ℓ t i :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hj i) (hu.1 i)
    _ = ⟪cumLoss ℓ 0 T, u⟫ := by
        simp [PiLp.inner_apply, hL]

end Experts

end Learning
