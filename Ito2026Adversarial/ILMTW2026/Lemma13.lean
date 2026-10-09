/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.LeanMachineLearning.EllipticalPotential
public import Ito2026Adversarial.LeanMachineLearning.Game.Concentration
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.Linear.ConfidenceEllipsoid

/-!
# Lemma 13: confidence ellipsoid of Maximin-LinUCB

With probability at least `1 - δ`, for all `t`, the matrix `A` of the bilinear game lies in the
ellipsoid `{A' | ‖vec(A') - vec(Â_t)‖_{V_t} ≤ β_t}` around the ridge regression estimate `Â_t`.

The proof: the ridge state of a run is the ridge state of the features `a_s = vec(x_s y_sᵀ)` and
of the rewards (`linState_eq_ridgeState`); the error of the ridge estimate is at most
`‖S_t‖_{V_t⁻¹} + √λ ‖vec(A)‖` (`Bandits.Linear.sqrt_mahalanobisSq_sub_ridgeEstimate_le`), where
`S_t` is the sum of the noises times the features; the self-normalized bound for the rewards of a
repeated game (`IsAlgEnvSeq.probReal_forall_mahalanobisSq_inv_regGram_le_ge`) bounds
`‖S_t‖²_{V_t⁻¹}` by `2 log(1/δ) + log(det V_t / λ^d)`, the determinant bound
(`Learning.log_det_regGram_le`, with `‖a_s‖ = ‖x_s‖ ‖y_s‖ ≤ 1`) bounds the last term by
`d log(1 + t/(dλ))`, and `‖vec(A)‖² ≤ d_y ≤ d` since the columns of `A` have norm at most `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix
open scoped RealInnerProductSpace

universe u

namespace Ito2026Adversarial

section Features

variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

/-- `‖vec(x yᵀ)‖ = ‖x‖ ‖y‖`. -/
lemma norm_pairFeature (x : EuclideanSpace ℝ ιx) (y : EuclideanSpace ℝ ιy) :
    ‖pairFeature x y‖ = ‖x‖ * ‖y‖ := by
  have h : ‖pairFeature x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_mul_sum]
    simp [pairFeature, mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- `u(x, y) = ⟪vec(x yᵀ), vec(A)⟫`: the bilinear utility is linear in the feature of the pair. -/
lemma inner_pairFeature_vecMatrix (A : Matrix ιx ιy ℝ) (x : EuclideanSpace ℝ ιx)
    (y : EuclideanSpace ℝ ιy) :
    ⟪pairFeature x y, vecMatrix A⟫ = bilinearUtility A x y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, pairFeature, vecMatrix, bilinearUtility,
    dotProduct, Fintype.sum_prod_type, mulVec, Finset.mul_sum, star_trivial]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- If the matrix `A` has operator norm at most `1`, then `‖vec(A)‖² ≤ d_x d_y`. -/
lemma norm_vecMatrix_sq_le {A : Matrix ιx ιy ℝ}
    (hA : ∀ y : EuclideanSpace ℝ ιy,
      ‖(WithLp.toLp 2 (A *ᵥ WithLp.ofLp y) : EuclideanSpace ℝ ιx)‖ ≤ ‖y‖) :
    ‖vecMatrix A‖ ^ 2 ≤ Fintype.card ιx * Fintype.card ιy := by
  classical
  have hcol : ∀ j, ∑ i, A i j ^ 2 ≤ 1 := by
    intro j
    have h := hA (WithLp.toLp 2 (Pi.single j 1))
    have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℝ)) : EuclideanSpace ℝ ιy)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [Pi.single_apply]
    rw [h1, ← sq_le_one_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq] at h
    simpa [mulVec_single_one] using h
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [vecMatrix]
  rcases isEmpty_or_nonempty ιx with hx | hx
  · simp
  calc ∑ j, ∑ i, A i j ^ 2 ≤ ∑ _j : ιy, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ hcol j
    _ = Fintype.card ιy := by simp
    _ ≤ Fintype.card ιx * Fintype.card ιy := by
      have : (1 : ℝ) ≤ Fintype.card ιx := by exact_mod_cast Fintype.card_pos
      nlinarith

end Features

/-- The ridge state of Maximin-LinUCB along a run is the ridge state of the features
`vec(φ(x_s) ψ(y_s)ᵀ)` and of the rewards of the run. -/
lemma linState_eq_ridgeState {ιx ιy : Type*} [DecidableEq ιx] [DecidableEq ιy] {𝒳 𝒴 : Type*}
    (φ : 𝒳 → EuclideanSpace ℝ ιx) (ψ : 𝒴 → EuclideanSpace ℝ ιy) {Ω : Type*} (lam : ℝ)
    (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴) (R : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    linState φ ψ lam X Y R t ω = Bandits.Linear.ridgeState lam
      (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) (fun s ↦ R s ω) t :=
  Bandits.Linear.stateProcess_ridgeUpdate lam
    (fun r : Round Unit 𝒳 (𝒴 × ℝ) ↦ pairFeature (φ r.action) (ψ r.feedback.1))
    (fun r ↦ r.feedback.2) (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, R t ω)) t ω

/-- `log(det V_t / λ^d) ≤ d log(1 + t / (d λ))` for the regularized Gram matrix of features of
norm at most `1`. -/
lemma log_det_regGram_div_le {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : 0 < lam)
    {x : ℕ → EuclideanSpace ℝ ι} {t : ℕ} (hx : ∀ s < t, ‖x s‖ ≤ 1) :
    log ((regGram lam x t).det / lam ^ Fintype.card ι) ≤
      Fintype.card ι * log (1 + t / (Fintype.card ι * lam)) := by
  have h := log_det_regGram_le hlam hx
  rw [one_pow, one_mul] at h
  rw [log_div (det_regGram_pos hlam x t).ne' (pow_pos hlam _).ne', log_pow]
  have key : (Fintype.card ι : ℝ) * log (lam + t / Fintype.card ι) =
      Fintype.card ι * log lam + Fintype.card ι * log (1 + t / (Fintype.card ι * lam)) := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hd | hd
    · simp [hd]
    have hd' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    rw [← mul_add, ← log_mul hlam.ne' (by positivity)]
    congr 2
    field_simp
  linarith

/-- **Lemma 13** (Ito, Luo, Maiti, Tsuchiya, Wu 2026; confidence ellipsoid). In a run of any
informed player in a bilinear game, against any adaptive adversary and with reward noise of
conditional mean `u` and rewards in `[-1, 1]`, for `λ > 0` and `δ ∈ (0, 1)`, with probability at
least `1 - δ`, for all `t`, `‖vec(A) - V_t⁻¹ b_t‖_{V_t} ≤ β_t`, where `(V_t, b_t)` is the ridge
regression state after `t` rounds and `β_t = linRadius (d_x d_y) λ δ t`. -/
theorem probReal_forall_sqrt_mahalanobisSq_le_ge {dx dy : ℕ}
    {mx my : ℕ} (φ : Fin mx → EuclideanSpace ℝ (Fin dx))
    (ψ : Fin my → EuclideanSpace ℝ (Fin dy)) (A : Matrix (Fin dx) (Fin dy) ℝ)
    (hA : IsBilinearGame φ ψ A)
    (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
    [∀ n, IsMarkovKernel (R n)]
    (hR : RewardKernel.HasMean R (bilinearGame φ ψ A))
    (hR' : RewardKernel.RewardsIn R (Set.Icc (-1) 1)) (alg : Player (Fin mx) (Fin my))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ P.real {ω | ∀ t,
      √(mahalanobisSq (linState φ ψ lam X Y Rw t ω).1
        (vecMatrix A - Bandits.Linear.ridgeEstimate (linState φ ψ lam X Y Rw t ω))) ≤
      linRadius (dx * dy) lam δ t} := by
  have hcard : Fintype.card (Fin dx × Fin dy) = dx * dy := by simp
  have hbound := h.probReal_forall_mahalanobisSq_inv_regGram_le_ge
    (u := bilinearGame φ ψ A) (measurable_of_countable _) hR hR'
    (fun x y ↦ pairFeature (φ x) (ψ y)) (measurable_of_countable _) hlam hδ.1
  refine hbound.trans (measureReal_mono fun ω hω t ↦ ?_)
  have hωt := hω t
  rw [linState_eq_ridgeState, Bandits.Linear.ridgeState_fst]
  refine (Bandits.Linear.sqrt_mahalanobisSq_sub_ridgeEstimate_le hlam (vecMatrix A) _ _ t).trans ?_
  have hnoise : ∀ s, Rw s ω - ⟪pairFeature (φ (X s ω)) (ψ (Y s ω)), vecMatrix A⟫ =
      Rw s ω - bilinearGame φ ψ A (X s ω) (Y s ω) := fun s ↦ by
    rw [inner_pairFeature_vecMatrix]
    rfl
  simp_rw [hnoise]
  have hlogdet := log_det_regGram_div_le hlam
    (x := fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) (t := t) fun s _ ↦ by
      rw [norm_pairFeature]
      nlinarith [hA.norm_le_x (X s ω), hA.norm_le_y (Y s ω), norm_nonneg (φ (X s ω)),
        norm_nonneg (ψ (Y s ω))]
  rw [hcard] at hωt hlogdet
  unfold linRadius
  rw [add_comm (√(lam * _))]
  gcongr ?_ + ?_
  · refine Real.sqrt_le_sqrt ?_
    push_cast at hωt hlogdet ⊢
    linarith
  · rw [Real.sqrt_mul hlam.le]
    gcongr
    rw [← Real.sqrt_sq (norm_nonneg (vecMatrix A))]
    refine Real.sqrt_le_sqrt ?_
    have := norm_vecMatrix_sq_le hA.opNorm_le
    simpa using this

end Ito2026Adversarial
