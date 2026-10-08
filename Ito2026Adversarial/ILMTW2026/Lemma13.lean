/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting

/-!
# Lemma 13: confidence ellipsoid of Maximin-LinUCB

With probability at least `1 - δ`, for all `t`, the matrix `A` of the bilinear game lies in the
ellipsoid `{A' | ‖vec(A') - vec(Â_t)‖_{V_t} ≤ β_t}` around the ridge regression estimate `Â_t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix

universe u

namespace Ito2026Adversarial

/-- **Lemma 13** (Ito, Luo, Maiti, Tsuchiya, Wu 2026; confidence ellipsoid). In a run of any
informed player in a bilinear game, against any adaptive adversary and with reward noise of
conditional mean `u` and rewards in `[-1, 1]`, for `λ > 0` and `δ ∈ (0, 1)`, with probability at
least `1 - δ`, for all `t`, `‖vec(A) - V_t⁻¹ b_t‖_{V_t} ≤ β_t`, where `(V_t, b_t)` is the ridge
regression state after `t` rounds and `β_t = linRadius (d_x d_y) λ δ t`. -/
theorem probReal_forall_sqrt_mahalanobisSq_le_ge {dx dy : ℕ}
    {mx my : ℕ} [NeZero mx] [NeZero my] (φ : Fin mx → EuclideanSpace ℝ (Fin dx))
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
  sorry

end Ito2026Adversarial
