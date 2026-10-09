/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.SimplexFTRL

/-!
# Regret of follow-the-regularized-leader on the simplex

Follow-the-regularized-leader (FTRL) on the probability simplex of `EuclideanSpace ℝ ι`, for
rewards (gains) `g t` and time-varying regularizers `ψ t`: at round `t`, play a maximizer `p t`
of `q ↦ ⟪q, G t⟫ + ψ t q` over the simplex, where `G t = ∑_{s < t} g s` is the cumulative reward.
The value of this maximization is `ftrlValue (ψ t) (G t)` (`SimplexFTRL.lean`).

## Main statements

* `ftrlValue_eq_of_isMaxOn`, `le_ftrlValue_of_isMaxOn`, `ftrlValue_le_of_forall_le`: the value
  function at a maximizer, the Fenchel–Young inequality, and upper bounds;
* `sum_inner_sub_le_ftrl`: the **FTRL decomposition** of the regret against any `q` in the
  simplex into a penalty term (the increments of the regularizers at `p t` and at `q`) and a
  stability term (`ftrlValue (ψ t) (G (t + 1)) - ftrlValue (ψ t) (G t) - ⟪p t, g t⟫`);
* `sum_inner_sub_le_ftrl_smul`: the same for the regularizers `(η t)⁻¹ • φ` of FTRL with
  learning rates `η t`, whose penalty term is `∑ ((η t)⁻¹ - (η (t - 1))⁻¹) (φ (p t) - φ q)`;
* `hasGradientAt_ftrlValue`, `ftrlSimplex_eq`: if every FTRL objective `⟪·, θ⟫ + φ` has a
  maximizer `P θ` on the simplex with quadratic growth, then `ftrlValue φ` has gradient `P θ`
  at `θ` and the FTRL distribution `ftrlSimplex φ θ` (defined as that gradient) is `P θ`.

## Implementation notes

The decomposition is stated for `T + 1` rounds, so that the penalty term at round `t + 1` reads
the regularizers `ψ (t + 1)` and `ψ t` without subtraction of indices; the round `0` has the
penalty `ψ 0 (p 0) - ψ 0 q` (the regularizer before round `0` being `0`).
-/

@[expose] public section

open Finset Filter Asymptotics
open scoped RealInnerProductSpace Topology

namespace Learning

variable {ι : Type*} [Fintype ι]

/-- A point of the simplex has Euclidean norm at most `1`. -/
lemma norm_le_one_of_mem_simplex {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) : ‖q‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
  calc ∑ i, ‖q i‖ ^ 2 ≤ ∑ i, q i := by
        refine sum_le_sum fun i _ ↦ ?_
        rw [Real.norm_eq_abs, sq_abs, sq]
        exact mul_le_of_le_one_left (hq.1 i) (le_one_of_mem_simplex hq i)
    _ = 1 := hq.2

/-- The inner product of a point of the simplex with the constant vector `c` is `c`. -/
lemma inner_const_of_mem_simplex {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (c : ℝ) :
    ⟪q, WithLp.toLp 2 (fun _ ↦ c)⟫ = c := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← mul_sum, hq.2, mul_one]

section Value

variable {ψ : EuclideanSpace ℝ ι → ℝ} {θ p : EuclideanSpace ℝ ι}

/-- If the FTRL objective `⟪·, θ⟫ + ψ` has a maximizer `p` on the simplex, the objective at any
other `θ'` is bounded above on the simplex by `⟪p, θ⟫ + ψ p + ‖θ' - θ‖`. -/
lemma inner_add_le_of_isMaxOn (hmax : ∀ q ∈ simplex ι, ⟪q, θ⟫ + ψ q ≤ ⟪p, θ⟫ + ψ p)
    {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (θ' : EuclideanSpace ℝ ι) :
    ⟪q, θ'⟫ + ψ q ≤ ⟪p, θ⟫ + ψ p + ‖θ' - θ‖ := by
  have h1 : ⟪q, θ'⟫ = ⟪q, θ⟫ + ⟪q, θ' - θ⟫ := by rw [inner_sub_right]; ring
  have h2 : ⟪q, θ' - θ⟫ ≤ ‖θ' - θ‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_simplex hq))
  linarith [hmax q hq]

/-- The value function is bounded above by any upper bound of the FTRL objective on the
simplex. -/
lemma ftrlValue_le_of_forall_le [Nonempty ι] {C : ℝ}
    (h : ∀ q ∈ simplex ι, ⟪q, θ⟫ + ψ q ≤ C) : ftrlValue ψ θ ≤ C := by
  obtain ⟨q₀, hq₀⟩ := (inferInstance : Nonempty (simplex ι))
  have hle : fenchelConjugateOn (simplex ι) (-ψ) θ ≤ (C : EReal) :=
    fenchelConjugateOn_le fun q hq ↦ by
      simp only [Pi.neg_apply, sub_neg_eq_add, EReal.coe_le_coe_iff]
      exact h q hq
  have hbot : fenchelConjugateOn (simplex ι) (-ψ) θ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_fenchelConjugateOn (-ψ) hq₀ θ)
  unfold ftrlValue
  calc (fenchelConjugateOn (simplex ι) (-ψ) θ).toReal ≤ (C : EReal).toReal :=
        EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top C)
    _ = C := EReal.toReal_coe C

/-- **Fenchel–Young inequality** for the value function: if the FTRL objective at `θ` has a
maximizer `p` on the simplex, then `⟪q, θ'⟫ + ψ q ≤ ftrlValue ψ θ'` for all `θ'` and all `q` in
the simplex. -/
lemma le_ftrlValue_of_isMaxOn (hmax : ∀ q ∈ simplex ι, ⟪q, θ⟫ + ψ q ≤ ⟪p, θ⟫ + ψ p)
    {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (θ' : EuclideanSpace ℝ ι) :
    ⟪q, θ'⟫ + ψ q ≤ ftrlValue ψ θ' := by
  have hle : fenchelConjugateOn (simplex ι) (-ψ) θ' ≤ ((⟪p, θ⟫ + ψ p + ‖θ' - θ‖ : ℝ) : EReal) :=
    fenchelConjugateOn_le fun q' hq' ↦ by
      simp only [Pi.neg_apply, sub_neg_eq_add, EReal.coe_le_coe_iff]
      exact inner_add_le_of_isMaxOn hmax hq' θ'
  have hge := le_fenchelConjugateOn (-ψ) hq θ'
  simp only [Pi.neg_apply, sub_neg_eq_add] at hge
  unfold ftrlValue
  calc ⟪q, θ'⟫ + ψ q = ((⟪q, θ'⟫ + ψ q : ℝ) : EReal).toReal := (EReal.toReal_coe _).symm
    _ ≤ (fenchelConjugateOn (simplex ι) (-ψ) θ').toReal :=
        EReal.toReal_le_toReal hge (EReal.coe_ne_bot _)
          (ne_top_of_le_ne_top (EReal.coe_ne_top _) hle)

/-- The value function at `θ` is the FTRL objective at a maximizer `p`. -/
lemma ftrlValue_eq_of_isMaxOn (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, ⟪q, θ⟫ + ψ q ≤ ⟪p, θ⟫ + ψ p) :
    ftrlValue ψ θ = ⟪p, θ⟫ + ψ p := by
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simpa using hp.2
  exact le_antisymm (ftrlValue_le_of_forall_le hmax) (le_ftrlValue_of_isMaxOn hmax hp θ)

end Value

/-! ### The FTRL decomposition -/

section Decomposition

variable (ψ : ℕ → EuclideanSpace ℝ ι → ℝ) (g p : ℕ → EuclideanSpace ℝ ι)

/-- Telescoping of the value functions along FTRL: the value `ftrlValue (ψ T) (G (T + 1))` after
`T + 1` rounds is at most the sum of the gains `⟪p t, g t⟫` of the plays, of the stability terms
and of the increments `ψ (t + 1) (p (t + 1)) - ψ t (p (t + 1))` of the regularizers. -/
lemma ftrlValue_le_sum (hp : ∀ t, p t ∈ simplex ι)
    (hmax : ∀ t, ∀ q ∈ simplex ι,
      ⟪q, ∑ s ∈ range t, g s⟫ + ψ t q ≤ ⟪p t, ∑ s ∈ range t, g s⟫ + ψ t (p t)) (T : ℕ) :
    ftrlValue (ψ T) (∑ s ∈ range (T + 1), g s) ≤
      ψ 0 (p 0) + ∑ t ∈ range T, (ψ (t + 1) (p (t + 1)) - ψ t (p (t + 1)))
        + ∑ t ∈ range (T + 1), ⟪p t, g t⟫
        + ∑ t ∈ range (T + 1), (ftrlValue (ψ t) (∑ s ∈ range (t + 1), g s)
            - ftrlValue (ψ t) (∑ s ∈ range t, g s) - ⟪p t, g t⟫) := by
  induction T with
  | zero =>
    have h0 := ftrlValue_eq_of_isMaxOn (hp 0) (hmax 0)
    simp only [range_zero, sum_empty, inner_zero_right, zero_add] at h0
    simp only [zero_add, range_one, sum_singleton, range_zero, sum_empty, h0]
    ring_nf
    rfl
  | succ T ih =>
    have hV := ftrlValue_eq_of_isMaxOn (hp (T + 1)) (hmax (T + 1))
    have hW := le_ftrlValue_of_isMaxOn (hmax T) (hp (T + 1)) (∑ s ∈ range (T + 1), g s)
    rw [sum_range_succ (fun t ↦ ψ (t + 1) (p (t + 1)) - ψ t (p (t + 1))),
      sum_range_succ (fun t ↦ ⟪p t, g t⟫) (T + 1),
      sum_range_succ (fun t ↦ ftrlValue (ψ t) (∑ s ∈ range (t + 1), g s)
        - ftrlValue (ψ t) (∑ s ∈ range t, g s) - ⟪p t, g t⟫) (T + 1)]
    linarith

/-- **FTRL decomposition.** Let `p t` maximize `q ↦ ⟪q, G t⟫ + ψ t q` over the simplex, where
`G t = ∑_{s < t} g s`. For every `q` in the simplex, the regret
`∑_{t ≤ T} ⟪q - p t, g t⟫` is at most the penalty term
`ψ 0 (p 0) - ψ 0 q + ∑_{t < T} ((ψ (t + 1) - ψ t) (p (t + 1)) - (ψ (t + 1) - ψ t) q)`
plus the stability term
`∑_{t ≤ T} (ftrlValue (ψ t) (G (t + 1)) - ftrlValue (ψ t) (G t) - ⟪p t, g t⟫)`. -/
lemma sum_inner_sub_le_ftrl (hp : ∀ t, p t ∈ simplex ι)
    (hmax : ∀ t, ∀ q ∈ simplex ι,
      ⟪q, ∑ s ∈ range t, g s⟫ + ψ t q ≤ ⟪p t, ∑ s ∈ range t, g s⟫ + ψ t (p t))
    {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪q - p t, g t⟫ ≤
      ψ 0 (p 0) - ψ 0 q
        + ∑ t ∈ range T, ((ψ (t + 1) (p (t + 1)) - ψ t (p (t + 1))) - (ψ (t + 1) q - ψ t q))
        + ∑ t ∈ range (T + 1), (ftrlValue (ψ t) (∑ s ∈ range (t + 1), g s)
            - ftrlValue (ψ t) (∑ s ∈ range t, g s) - ⟪p t, g t⟫) := by
  have h1 := ftrlValue_le_sum ψ g p hp hmax T
  have h2 := le_ftrlValue_of_isMaxOn (hmax T) hq (∑ s ∈ range (T + 1), g s)
  have h3 : ∑ t ∈ range (T + 1), ⟪q - p t, g t⟫ =
      ⟪q, ∑ s ∈ range (T + 1), g s⟫ - ∑ t ∈ range (T + 1), ⟪p t, g t⟫ := by
    simp only [inner_sub_left, sum_sub_distrib, inner_sum]
  have h4 : ψ T q = ψ 0 q + ∑ t ∈ range T, (ψ (t + 1) q - ψ t q) := by
    rw [sum_range_sub (fun t ↦ ψ t q)]
    ring
  rw [sum_sub_distrib]
  linarith

/-- **FTRL decomposition for learning rates.** For the regularizers `(η t)⁻¹ • φ` (FTRL with
regularizer `φ` and learning rates `η t`), the penalty term of `sum_inner_sub_le_ftrl` is
`(η 0)⁻¹ (φ (p 0) - φ q) + ∑_{t < T} ((η (t + 1))⁻¹ - (η t)⁻¹) (φ (p (t + 1)) - φ q)`. -/
lemma sum_inner_sub_le_ftrl_smul (φ : EuclideanSpace ℝ ι → ℝ) (η : ℕ → ℝ)
    (hp : ∀ t, p t ∈ simplex ι)
    (hmax : ∀ t, ∀ q ∈ simplex ι, ⟪q, ∑ s ∈ range t, g s⟫ + (η t)⁻¹ * φ q
      ≤ ⟪p t, ∑ s ∈ range t, g s⟫ + (η t)⁻¹ * φ (p t))
    {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪q - p t, g t⟫ ≤
      (η 0)⁻¹ * (φ (p 0) - φ q)
        + ∑ t ∈ range T, ((η (t + 1))⁻¹ - (η t)⁻¹) * (φ (p (t + 1)) - φ q)
        + ∑ t ∈ range (T + 1), (ftrlValue ((η t)⁻¹ • φ) (∑ s ∈ range (t + 1), g s)
            - ftrlValue ((η t)⁻¹ • φ) (∑ s ∈ range t, g s) - ⟪p t, g t⟫) := by
  have h := sum_inner_sub_le_ftrl (fun t ↦ (η t)⁻¹ • φ) g p hp hmax hq T
  simp only [Pi.smul_apply, smul_eq_mul] at h
  convert h using 3
  · ring
  · refine sum_congr rfl fun t _ ↦ ?_
    ring

end Decomposition

/-! ### The FTRL distribution as the gradient of the value function -/

section Gradient

variable {φ : EuclideanSpace ℝ ι → ℝ} {P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {μ : ℝ}

/-- If every FTRL objective `⟪·, θ⟫ + φ` has a maximizer `P θ` on the simplex with quadratic
growth, `⟪q, θ⟫ + φ q + μ ‖q - P θ‖² ≤ ⟪P θ, θ⟫ + φ (P θ)`, then the value function is
approximated to second order by its linearization at `θ`:
`0 ≤ ftrlValue φ θ' - ftrlValue φ θ - ⟪P θ, θ' - θ⟫ ≤ ‖θ' - θ‖² / (2 μ)`. -/
lemma abs_ftrlValue_sub_sub_le (hμ : 0 < μ) (hP : ∀ θ, P θ ∈ simplex ι)
    (hgrowth : ∀ θ, ∀ q ∈ simplex ι,
      ⟪q, θ⟫ + φ q + μ * ‖q - P θ‖ ^ 2 ≤ ⟪P θ, θ⟫ + φ (P θ))
    (θ θ' : EuclideanSpace ℝ ι) :
    |ftrlValue φ θ' - ftrlValue φ θ - ⟪P θ, θ' - θ⟫| ≤ ‖θ' - θ‖ ^ 2 / (2 * μ) := by
  have hmax (θ : EuclideanSpace ℝ ι) : ∀ q ∈ simplex ι, ⟪q, θ⟫ + φ q ≤ ⟪P θ, θ⟫ + φ (P θ) :=
    fun q hq ↦ by nlinarith [hgrowth θ q hq, sq_nonneg ‖q - P θ‖]
  have h1 := hgrowth θ (P θ') (hP θ')
  have h2 := hgrowth θ' (P θ) (hP θ)
  rw [ftrlValue_eq_of_isMaxOn (hP θ') (hmax θ'), ftrlValue_eq_of_isMaxOn (hP θ) (hmax θ)]
  have hn : ‖P θ - P θ'‖ = ‖P θ' - P θ‖ := norm_sub_rev _ _
  have hinner : ⟪P θ' - P θ, θ' - θ⟫ = ⟪P θ', θ'⟫ - ⟪P θ', θ⟫ - ⟪P θ, θ'⟫ + ⟪P θ, θ⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hcs : ⟪P θ' - P θ, θ' - θ⟫ ≤ ‖P θ' - P θ‖ * ‖θ' - θ‖ := real_inner_le_norm _ _
  -- the maximizers are `1 / (2 μ)`-Lipschitz
  have hlip : 2 * μ * ‖P θ' - P θ‖ ^ 2 ≤ ‖P θ' - P θ‖ * ‖θ' - θ‖ := by
    rw [hn] at h2
    linarith
  have hlip' : ‖P θ' - P θ‖ * ‖θ' - θ‖ ≤ ‖θ' - θ‖ ^ 2 / (2 * μ) := by
    rw [le_div_iff₀ (by positivity)]
    rcases (norm_nonneg (P θ' - P θ)).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
      positivity
    · have : 2 * μ * ‖P θ' - P θ‖ ≤ ‖θ' - θ‖ := by nlinarith
      nlinarith [norm_nonneg (θ' - θ)]
  have hinner' : ⟪P θ, θ' - θ⟫ = ⟪P θ, θ'⟫ - ⟪P θ, θ⟫ := inner_sub_right _ _ _
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg ‖P θ - P θ'‖]
  · nlinarith [sq_nonneg ‖P θ' - P θ‖]

/-- If every FTRL objective `⟪·, θ⟫ + φ` has a maximizer `P θ` on the simplex with quadratic
growth, then the value function `ftrlValue φ` has gradient `P θ` at `θ` (Danskin's theorem). -/
lemma hasGradientAt_ftrlValue (hμ : 0 < μ) (hP : ∀ θ, P θ ∈ simplex ι)
    (hgrowth : ∀ θ, ∀ q ∈ simplex ι,
      ⟪q, θ⟫ + φ q + μ * ‖q - P θ‖ ^ 2 ≤ ⟪P θ, θ⟫ + φ (P θ))
    (θ : EuclideanSpace ℝ ι) :
    HasGradientAt (ftrlValue φ) (P θ) θ := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h ↦ ftrlValue φ (θ + h) - ftrlValue φ θ
      - (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) (P θ)) h) =O[𝓝 0]
      fun h ↦ ‖h‖ ^ 2 := by
    refine IsBigO.of_bound (1 / (2 * μ)) (Eventually.of_forall fun h ↦ ?_)
    have := abs_ftrlValue_sub_sub_le hμ hP hgrowth θ (θ + h)
    simp only [add_sub_cancel_left, InnerProductSpace.toDual_apply_apply] at this ⊢
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    calc _ ≤ ‖h‖ ^ 2 / (2 * μ) := this
      _ = 1 / (2 * μ) * ‖h‖ ^ 2 := by ring
  refine hO.trans_isLittleO ?_
  exact (isLittleO_norm_pow_id one_lt_two)

/-- If every FTRL objective `⟪·, θ⟫ + φ` has a maximizer `P θ` on the simplex with quadratic
growth, the FTRL distribution `ftrlSimplex φ θ` is `P θ`. -/
lemma ftrlSimplex_eq [Nonempty ι] (hμ : 0 < μ) (hP : ∀ θ, P θ ∈ simplex ι)
    (hgrowth : ∀ θ, ∀ q ∈ simplex ι,
      ⟪q, θ⟫ + φ q + μ * ‖q - P θ‖ ^ 2 ≤ ⟪P θ, θ⟫ + φ (P θ))
    (θ : EuclideanSpace ℝ ι) :
    ftrlSimplex φ θ = ⟨P θ, hP θ⟩ := by
  unfold ftrlSimplex
  rw [(hasGradientAt_ftrlValue hμ hP hgrowth θ).gradient, toSet_of_mem (hP θ)]

end Gradient

end Learning
