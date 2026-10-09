/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.LeanMachineLearning.Game.Concentration

/-!
# Lemma 11: confidence bounds of Maximin-UCB

For a fixed action pair `(x, y)`, with probability at least `1 - δ`, the empirical mean of the
rewards of the rounds in which `(x, y)` was played is within
`√((4 log(1/δ) + 2 log(1 + N_t(x, y))) / N_t(x, y))` of `u x y`, simultaneously for all `t` with
`N_t(x, y) > 0`.

The proof applies the self-normalized bound for the rewards of a repeated game
(`IsAlgEnvSeq.probReal_forall_mahalanobisSq_inv_regGram_le_ge`) in dimension one, with the
feature `𝟙{(x_s, y_s) = (x, y)}` and `λ = 1`: then `V_t = 1 + N_t(x, y)` and
`S_t = R_t(x, y) - N_t(x, y) u(x, y)`, so that with probability at least `1 - δ`, for all `t`,
`S_t² / (1 + N_t) ≤ 2 log(1/δ) + log(1 + N_t)` (the Gaussian mixture of the paper), and
`1 + N_t ≤ 2 N_t` when `N_t > 0`. The paper's assumption that the utilities lie in `[-1, 1]` is
not needed: it follows from the other hypotheses, the utilities being the means of rewards in
`[-1, 1]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

universe u

namespace Ito2026Adversarial

/-- The squared Mahalanobis norm for the inverse of a `1 × 1` matrix `M`:
`‖v‖²_{M⁻¹} = v² / M`. -/
lemma mahalanobisSq_inv_unit {M : Matrix Unit Unit ℝ} (hM : M () () ≠ 0)
    (v : EuclideanSpace ℝ Unit) :
    Matrix.mahalanobisSq M⁻¹ v = v () ^ 2 / M () () := by
  have hdet : IsUnit M.det := by rw [Matrix.det_unique]; exact hM.isUnit
  have h1 : (M * M⁻¹) () () = 1 := by rw [Matrix.mul_nonsing_inv M hdet]; rfl
  rw [Matrix.mul_apply, Fintype.sum_unique] at h1
  have hinv : M⁻¹ () () = (M () ())⁻¹ := eq_inv_of_mul_eq_one_right h1
  simp [Matrix.mahalanobisSq, dotProduct, Matrix.mulVec, hinv]
  ring

/-- **Lemma 11** (Ito, Luo, Maiti, Tsuchiya, Wu 2026). In a run of any informed player against
any adaptive adversary, with reward noise of conditional mean `u` and rewards in `[-1, 1]`, for
every action pair `(x, y)` and `δ ∈ (0, 1)`, with probability at least `1 - δ`, for all `t` with
`N_t(x, y) > 0`,
`|u x y - R_t(x, y) / N_t(x, y)| ≤ √((4 log(1/δ) + 2 log(1 + N_t(x, y))) / N_t(x, y))`, where
`N_t(x, y)` and `R_t(x, y)` are the number of rounds among the first `t` in which `(x, y)` was
played and the sum of their rewards. -/
theorem probReal_forall_abs_sub_div_le_ge {mx my : ℕ} (u : Fin mx → Fin my → ℝ)
    (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
    [∀ n, IsMarkovKernel (R n)] (hR : RewardKernel.HasMean R u)
    (hR' : RewardKernel.RewardsIn R (Set.Icc (-1) 1)) (alg : Player (Fin mx) (Fin my))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (x : Fin mx) (y : Fin my) {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ P.real {ω | ∀ t, 0 < pairCount X Y Rw x y t ω →
      |u x y - pairSum X Y Rw x y t ω / pairCount X Y Rw x y t ω| ≤
        √((4 * log (1 / δ) + 2 * log (1 + pairCount X Y Rw x y t ω))
          / pairCount X Y Rw x y t ω)} := by
  classical
  -- the indicator feature of the pair `(x, y)`, in dimension one
  set ind : Fin mx → Fin my → ℝ := fun x' y' ↦ if x' = x ∧ y' = y then 1 else 0 with hind
  set f : Fin mx → Fin my → EuclideanSpace ℝ Unit := fun x' y' ↦ WithLp.toLp 2 fun _ ↦ ind x' y'
    with hf
  have hbound := h.probReal_forall_mahalanobisSq_inv_regGram_le_ge
    (u := u) (measurable_of_countable _) hR hR' f (measurable_of_countable _) one_pos hδ.1
  refine hbound.trans (measureReal_mono fun ω hω t ht ↦ ?_)
  have hωt := hω t
  set N : ℝ := (pairCount X Y Rw x y t ω : ℝ) with hN
  set Rs : ℝ := pairSum X Y Rw x y t ω with hRs
  have hind_sq : ∀ x' y', ind x' y' * ind x' y' = ind x' y' := fun x' y' ↦ by
    simp only [hind]
    split_ifs <;> simp
  have hNsum : N = ∑ s ∈ range t, ind (X s ω) (Y s ω) := by
    simp only [hN, pairCount, histPairCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, hind]
    exact Fin.sum_univ_eq_sum_range (fun s ↦ if X s ω = x ∧ Y s ω = y then (1 : ℝ) else 0) t
  have hRsum : Rs = ∑ s ∈ range t, ind (X s ω) (Y s ω) * Rw s ω := by
    simp only [hRs, pairSum, histPairSum, hind, ite_mul, one_mul, zero_mul]
    exact Fin.sum_univ_eq_sum_range (fun s ↦ if X s ω = x ∧ Y s ω = y then Rw s ω else 0) t
  have hV : regGram 1 (fun s ↦ f (X s ω) (Y s ω)) t () () = 1 + N := by
    simp [regGram, gram, outerSelf, Matrix.sum_apply, hf, hNsum, Matrix.vecMulVec_apply,
      hind_sq]
  have hS : (∑ s ∈ range t, (Rw s ω - u (X s ω) (Y s ω)) • f (X s ω) (Y s ω)) () =
      Rs - N * u x y := by
    rw [hRsum, hNsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, hf,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [hind]
    split_ifs with hs
    · rw [hs.1, hs.2]
      ring
    · ring
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNpos : (1 : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 ht.ne'
  rw [mahalanobisSq_inv_unit (by rw [hV]; linarith), hS, hV, Matrix.det_unique,
    show (default : Unit) = () from rfl, hV, Fintype.card_unit, one_pow, div_one] at hωt
  -- conclude
  have hL : 0 < log (1 / δ) := log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 hδ)
  have hlog : 0 ≤ log (1 + N) := log_nonneg (by linarith)
  have hsq : (Rs - N * u x y) ^ 2 ≤ N * (4 * log (1 / δ) + 2 * log (1 + N)) := by
    rw [div_le_iff₀ (by linarith)] at hωt
    nlinarith
  apply Real.abs_le_sqrt
  rw [le_div_iff₀ (by linarith)]
  have : (u x y - Rs / N) ^ 2 * N = (Rs - N * u x y) ^ 2 / N := by
    field_simp
    ring
  rw [this, div_le_iff₀ (by linarith)]
  nlinarith

end Ito2026Adversarial
