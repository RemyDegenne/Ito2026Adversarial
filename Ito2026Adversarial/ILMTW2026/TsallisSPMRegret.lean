/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.TsallisSPMPath
public import Ito2026Adversarial.LeanMachineLearning.Game.UninformedRunIntegral
public import Ito2026Adversarial.ILMTW2026.TsallisINFRegret

/-!
# Regret of Tsallis-FTRL-SPM in a repeated game

The expected regret of Tsallis-FTRL with stability-penalty matching (`tsallisSPM`) in a run against
an adaptive adversary, for a game which is linear in the features of the learner's actions
(`u x y = ⟪φ x, w y⟫`, for instance a bilinear game) with rewards in `[-1, 1]`
(Ito, Tsuchiya, Honda 2024, Section 4 and Proposition 16).

## Main definitions

* `spmStateHist n h`: the state `(G_n, β_n)` of `tsallisSPM` after the history `h` of the game;
* `spmWeights n h`: the distribution of the action of round `n`.

## Main statements

* `externalRegretAgainst_tsallisSPM_le`: `ER_T(x) ≤ β₁ φ_α(p̂_0) + βbar φ_{1-α}(p̂_0)
  + (16 + 8 c) E[∑_{t < T} z_t / β_t]` (FTRL decomposition, stability-penalty matching,
  unbiased linear estimates, exploration cost `2 γ_t = 8 c z_t / β_t`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix
open scoped RealInnerProductSpace ENNReal

namespace Ito2026Adversarial

section Run

variable {ιx : Type*} [Fintype ιx] [DecidableEq ιx] {mx my : ℕ} [NeZero mx]
  (φ : Fin mx → EuclideanSpace ℝ ιx) (α β₁ βbar : ℝ) (p₀ : simplex (Fin mx)) (c : ℝ)

/-- The state `(G_n, β_n)` of Tsallis-FTRL-SPM after the history `h` of `n` rounds of the game
(the learner sees only its rewards). -/
noncomputable def spmStateHist (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) :
    EuclideanSpace ℝ (Fin mx) × ℝ :=
  foldHistIdx (fun _ ↦ spmUpdate φ α βbar p₀ c) (0, β₁) n (Hist.mapFeedback Prod.snd h)

/-- The distribution of the action of round `n` of Tsallis-FTRL-SPM after the history `h`. -/
noncomputable def spmWeights (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) : Fin mx → ℝ :=
  (spmDist α βbar (Fintype.card ιx) p₀ c (spmStateHist φ α β₁ βbar p₀ c n h) : Fin mx → ℝ)

/-- The state is a measurable function of the history. -/
lemma measurable_spmStateHist (n : ℕ) :
    Measurable (spmStateHist (my := my) φ α β₁ βbar p₀ c n) := by
  unfold spmStateHist
  refine (measurable_foldHistIdx ?_ _ n).comp
    (Hist.measurable_map measurable_id measurable_id measurable_snd n)
  exact measurable_spmUpdate φ α βbar p₀ c (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)

/-- The weights are a measurable function of the history. -/
lemma measurable_spmWeights (n : ℕ) : Measurable (spmWeights (my := my) φ α β₁ βbar p₀ c n) :=
  measurable_coe_simplex.comp ((measurable_spmDist α βbar _ p₀ c).comp
    (measurable_spmStateHist φ α β₁ βbar p₀ c n))

/-- Tsallis-FTRL-SPM, as an uninformed player of the game, draws its action from
`spmWeights`. -/
lemma policy_ofUninformed_tsallisSPM (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) :
    (Player.ofUninformed (tsallisSPM φ α β₁ βbar p₀ c) : Player (Fin mx) (Fin my)).policy n
      (h, ()) = weightedMeasure (spmWeights φ α β₁ βbar p₀ c n h) := rfl

/-- The weights are nonnegative. -/
lemma spmWeights_nonneg (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) (x : Fin mx) :
    0 ≤ spmWeights φ α β₁ βbar p₀ c n h x :=
  (spmDist α βbar (Fintype.card ιx) p₀ c (spmStateHist φ α β₁ βbar p₀ c n h)).2.1 x

/-- The weights sum to `1`. -/
lemma sum_spmWeights (n : ℕ) (h : Hist Unit (Fin mx) (Fin my × ℝ) n) :
    ∑ x, spmWeights φ α β₁ βbar p₀ c n h x = 1 :=
  (spmDist α βbar (Fintype.card ιx) p₀ c (spmStateHist φ α β₁ βbar p₀ c n h)).2.2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Fin mx} {Y : ℕ → Ω → Fin my}
  {Rw : ℕ → Ω → ℝ}

/-- Along a run, the state after the history of `n` rounds is `spmState` of the rounds
`((), x_s, r_s)` of the learner. -/
lemma spmStateHist_history (n : ℕ) (ω : Ω) :
    spmStateHist φ α β₁ βbar p₀ c n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω)
      = spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) n :=
  foldHistIdx_eq_spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) n

/-! ### Expectations along a run -/

/-- Along a run, the state of round `t` is measurable. -/
lemma measurable_spmState_run (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hRw : ∀ t, Measurable (Rw t)) (t : ℕ) :
    Measurable fun ω ↦ spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t := by
  have : (fun ω ↦ spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t)
      = fun ω ↦ spmStateHist (my := my) φ α β₁ βbar p₀ c t
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω) :=
    funext fun ω ↦ (spmStateHist_history φ α β₁ βbar p₀ c t ω).symm
  rw [this]
  exact (measurable_spmStateHist φ α β₁ βbar p₀ c t).comp
    (measurable_history (fun _ ↦ measurable_const) hX (fun t ↦ (hY t).prodMk (hRw t)) t)

/-- Along a run, the estimate of round `t` is measurable. -/
lemma measurable_spmEstimateAt_run (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hRw : ∀ t, Measurable (Rw t)) (t : ℕ) :
    Measurable fun ω ↦ spmEstimateAt φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t :=
  measurable_spmEstimate φ ((measurable_spmDist α βbar _ p₀ c).comp
    (measurable_spmState_run (my := my) φ α β₁ βbar p₀ c hX hY hRw t))
    (measurable_const.prodMk ((hX t).prodMk (hRw t)))


variable {φ α β₁ βbar p₀ c} {u : Fin mx → Fin my → ℝ} {w : Fin my → ιx → ℝ}
  {opp : Player (Fin my) (Fin mx)} {R : RewardKernel (Fin mx) (Fin my)} [∀ n, IsMarkovKernel (R n)]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The played distribution** (`lem:uninformed_run`): in a run of Tsallis-FTRL-SPM, for
`|f| ≤ M`, `E[f(x_t, y_t)] = E[∑ x, p_t x f(x, y_t)]`. -/
lemma integral_comp_action_tsallisSPM
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
      (Player.ofUninformed (tsallisSPM φ α β₁ βbar p₀ c)) (gameEnv opp R) P)
    (t : ℕ) (f : Fin mx → Fin my → ℝ) {M : ℝ} (hf : ∀ x y, |f x y| ≤ M) :
    ∫ ω, f (X t ω) (Y t ω) ∂P
      = ∫ ω, ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx)) x
          * f x (Y t ω) ∂P := by
  have key := h.integral_gameAction_eq_sum (policy_ofUninformed_tsallisSPM φ α β₁ βbar p₀ c)
    (spmWeights_nonneg φ α β₁ βbar p₀ c) (sum_spmWeights φ α β₁ βbar p₀ c)
    (measurable_spmWeights φ α β₁ βbar p₀ c) t (f := fun q ↦ f q.2.1 q.2.2)
    ((measurable_of_countable (Function.uncurry f)).comp measurable_snd) (M := M)
    (ae_of_all _ fun ω x ↦ hf _ _)
  simp only at key
  rw [key]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  simp only [spmWeights, spmStateHist_history]

omit [NeZero mx] in
/-- `|single x 1 i - p i| ≤ 1` for a point `p` of the simplex. -/
lemma abs_single_sub_le_one {p : EuclideanSpace ℝ (Fin mx)} (hp : p ∈ simplex (Fin mx))
    (x i : Fin mx) : |(EuclideanSpace.single x (1 : ℝ) - p) i| ≤ 1 := by
  rw [PiLp.sub_apply, abs_le]
  have h0 := hp.1 i
  have h1 := le_one_of_mem_simplex hp i
  by_cases hi : i = x
  · subst hi
    simp only [PiLp.single_apply, ite_true]
    constructor <;> linarith
  · simp only [PiLp.single_apply, hi, ite_false]
    constructor <;> linarith

variable (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx)) (hV : HasVarianceRatio φ p₀ c)
  (h𝒳 : 2 ≤ mx) (hu : ∀ x y, u x y = WithLp.ofLp (φ x) ⬝ᵥ w y)
  (hu1 : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hRu : R.HasMean u) (hR : R.RewardsIn (Set.Icc (-1) 1))
  (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
      (Player.ofUninformed (tsallisSPM φ α β₁ βbar p₀ c)) (gameEnv opp R) P)
include hP hV h𝒳 h

include hR in
/-- Almost surely, the bilinear forms of the inverse design matrix of round `t` are bounded by
the deterministic bound `B_{t+1}`. -/
lemma ae_abs_dotProduct_inv_le (t : ℕ) :
    ∀ᵐ ω ∂P, ∀ a b : Fin mx, |WithLp.ofLp (φ a) ⬝ᵥ
        (designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
            EuclideanSpace ℝ (Fin mx)))⁻¹
          *ᵥ WithLp.ofLp (φ b)| ≤ spmBound α β₁ βbar mx (t + 1) := by
  have h𝒳' : 2 ≤ Fintype.card (Fin mx) := by simpa using h𝒳
  filter_upwards [h.ae_forall_gameReward_mem measurableSet_Icc hR] with ω hω a b
  have hB := (spmState_le_spmBound hP hV h𝒳' (fun s ↦ ((), X s ω, Rw s ω))
    (fun s ↦ abs_le.2 ⟨(hω s).1, (hω s).2⟩) t).2.2
  rw [Fintype.card_fin] at hB
  exact (abs_dotProduct_inv_designOf_spmDist_le φ hP hV (le_spmState_snd hP _ t) h𝒳' a b).trans hB

include hu hu1 hRu hR in
/-- **Unbiasedness of the estimates** (`lem:uninformed_run`): in a run of Tsallis-FTRL-SPM in a
game `u x y = ⟪φ x, w y⟫`, `E[⟪e_x - p̂_t, g_t⟫] = E[u x y_t - ∑ i, p̂_t i u i y_t]`. -/
lemma integral_inner_spmEstimateAt (t : ℕ) (x : Fin mx) :
    ∫ ω, ⟪EuclideanSpace.single x (1 : ℝ) - (spmHat α βbar
        (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx)),
        spmEstimateAt φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t⟫ ∂P
      = ∫ ω, (u x (Y t ω) - ∑ i, (spmHat α βbar
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx)) i
          * u i (Y t ω)) ∂P := by
  have h𝒳' : 2 ≤ Fintype.card (Fin mx) := by simpa using h𝒳
  set stH := spmStateHist (my := my) φ α β₁ βbar p₀ c t with hstH
  set H := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t with hH
  set k : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my → ℝ := fun q ↦
    ⟪EuclideanSpace.single x (1 : ℝ) - (spmHat α βbar (stH q.1) : EuclideanSpace ℝ (Fin mx)),
      spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH q.1)) ((), q.2.1, 1)⟫ with hk
  have hstm : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my ↦ stH q.1 :=
    (measurable_spmStateHist φ α β₁ βbar p₀ c t).comp measurable_fst
  have hkm : Measurable k := by
    have h1 : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my ↦
        (spmHat α βbar (stH q.1) : EuclideanSpace ℝ (Fin mx)) :=
      measurable_subtype_coe.comp ((measurable_spmHat α βbar).comp hstm)
    have h2 : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my ↦
        spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH q.1)) ((), q.2.1, (1 : ℝ)) :=
      measurable_spmEstimate φ ((measurable_spmDist α βbar _ p₀ c).comp hstm) (by fun_prop)
    exact (measurable_const.sub h1).inner h2
  have hpt (ω : Ω) : ⟪EuclideanSpace.single x (1 : ℝ) - (spmHat α βbar
        (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx)),
        spmEstimateAt φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t⟫
      = Rw t ω * k (H ω, X t ω, Y t ω) := by
    simp only [hk, hstH, hH, spmStateHist_history]
    rw [spmEstimateAt, spmEstimate_eq_smul, inner_smul_right]
    rfl
  -- a.s. bounds
  have hkb : ∀ᵐ ω ∂P, ∀ x', |k (H ω, x', Y t ω)| ≤ mx * spmBound α β₁ βbar mx (t + 1) := by
    filter_upwards [ae_abs_dotProduct_inv_le hP hV h𝒳 hR h t] with ω hω x'
    simp only [hk, hstH, hH, spmStateHist_history]
    rw [PiLp.inner_apply]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |⟪(EuclideanSpace.single x (1 : ℝ) - (spmHat α βbar
            (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
              EuclideanSpace ℝ (Fin mx))) i,
          (spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c
            (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t)) ((), x', 1)) i⟫|
        ≤ ∑ _i : Fin mx, spmBound α β₁ βbar mx (t + 1) := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [RCLike.inner_apply, conj_trivial, abs_mul, spmEstimate_one_apply]
          calc _ ≤ spmBound α β₁ βbar mx (t + 1) * 1 :=
                mul_le_mul (hω x' i) (abs_single_sub_le_one (spmHat α βbar _).2 x i)
                  (abs_nonneg _) ((abs_nonneg _).trans (hω x' i))
            _ = spmBound α β₁ βbar mx (t + 1) := mul_one _
      _ = mx * spmBound α β₁ βbar mx (t + 1) := by simp
  have hum : Measurable (Function.uncurry u) := measurable_of_countable _
  have h1 := h.integral_gameReward_mul hum hu1 hRu hR t hkm
    (M := mx * spmBound α β₁ βbar mx (t + 1))
    (by filter_upwards [hkb] with ω hω using hω _)
  have h2 := h.integral_gameAction_eq_sum (policy_ofUninformed_tsallisSPM φ α β₁ βbar p₀ c)
    (spmWeights_nonneg φ α β₁ βbar p₀ c) (sum_spmWeights φ α β₁ βbar p₀ c)
    (measurable_spmWeights φ α β₁ βbar p₀ c) t (f := fun q ↦ u q.2.1 q.2.2 * k q)
    ((hum.comp measurable_snd).mul hkm) (M := mx * spmBound α β₁ βbar mx (t + 1)) (by
      filter_upwards [hkb] with ω hω x'
      rw [abs_mul]
      have : |u x' (Y t ω)| ≤ 1 := abs_le.2 ⟨(hu1 _ _).1, (hu1 _ _).2⟩
      calc |u x' (Y t ω)| * |k (H ω, x', Y t ω)|
          ≤ 1 * (mx * spmBound α β₁ βbar mx (t + 1)) :=
            mul_le_mul this (hω x') (abs_nonneg _) zero_le_one
        _ = _ := one_mul _)
  simp only at h1 h2
  calc _ = ∫ ω, Rw t ω * k (H ω, X t ω, Y t ω) ∂P := integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ ω, u (X t ω) (Y t ω) * k (H ω, X t ω, Y t ω) ∂P := h1
    _ = _ := h2
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
      simp only [spmWeights, hk, hstH, spmStateHist_history]
      have hdet : IsUnit (designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
            EuclideanSpace ℝ (Fin mx))).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp
          (posDef_designOf_spmDist φ hP hV (le_spmState_snd hP _ t) h𝒳').isUnit
      rw [sum_mul_inner_spmEstimate φ _ hdet hu]
      simp only [PiLp.sub_apply, PiLp.single_apply, sub_mul, sum_sub_distrib, ite_mul, one_mul,
        zero_mul, sum_ite_eq', Finset.mem_univ, ite_true]

include hR in
/-- **Expected stability term** (Ito, Tsuchiya, Honda 2024, Eq. (135)): in a run,
`E[4 / ((1 - α) β_t) q*_t ^ (1 - α) ∑ i, p̂_t i g_t i²] ≤ E[8 z_t / β_t]` (second moment of the
linear estimates and the trace identity). -/
lemma integral_stability_le (t : ℕ) :
    ∫ ω, 4 / ((1 - α) * (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2)
        * qStar (spmHat α βbar (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
          EuclideanSpace ℝ (Fin mx)) ^ (1 - α)
        * ∑ i, (spmHat α βbar (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
          EuclideanSpace ℝ (Fin mx)) i
          * spmEstimateAt φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t i ^ 2 ∂P
      ≤ ∫ ω, 8 * (zCoef α (Fintype.card ιx) (spmHat α βbar
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx))
          / (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2) ∂P := by
  have h𝒳' : 2 ≤ Fintype.card (Fin mx) := by simpa using h𝒳
  have h1α := hP.one_sub_pos
  have hd := hP.d_pos
  set stH := spmStateHist (my := my) φ α β₁ βbar p₀ c t with hstH
  set H := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t with hH
  -- functions of the history
  set K : Hist Unit (Fin mx) (Fin my × ℝ) t → ℝ := fun hh ↦ 4 / ((1 - α) * (stH hh).2)
    * qStar (spmHat α βbar (stH hh) : EuclideanSpace ℝ (Fin mx)) ^ (1 - α) with hK
  set ph : Hist Unit (Fin mx) (Fin my × ℝ) t → EuclideanSpace ℝ (Fin mx) := fun hh ↦
    (spmHat α βbar (stH hh) : EuclideanSpace ℝ (Fin mx)) with hph
  set F : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my × ℝ → ℝ≥0∞ := fun q ↦
    ENNReal.ofReal (K q.1 * ∑ i, ph q.1 i
      * spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH q.1)) ((), q.2.1, q.2.2.2) i ^ 2)
    with hF
  have hstm : Measurable stH := measurable_spmStateHist φ α β₁ βbar p₀ c t
  have hFm : Measurable F := by
    have hph : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my × ℝ ↦
        ph q.1 := measurable_subtype_coe.comp ((measurable_spmHat α βbar).comp
          (hstm.comp measurable_fst))
    have hK : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my × ℝ ↦
        K q.1 := by
      refine (measurable_const.div (measurable_const.mul
        (measurable_snd.comp (hstm.comp measurable_fst)))).mul ?_
      exact (measurable_qStar.comp hph).pow_const _
    have hg : Measurable fun q : Hist Unit (Fin mx) (Fin my × ℝ) t × Fin mx × Fin my × ℝ ↦
        spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH q.1)) ((), q.2.1, q.2.2.2) :=
      measurable_spmEstimate φ ((measurable_spmDist α βbar _ p₀ c).comp
        (hstm.comp measurable_fst)) (by fun_prop)
    refine ENNReal.measurable_ofReal.comp (hK.mul (Finset.measurable_sum _ fun i _ ↦ ?_))
    exact ((PiLp.continuous_apply 2 _ i).measurable.comp hph).mul
      (((PiLp.continuous_apply 2 _ i).measurable.comp hg).pow_const 2)
  have key := h.lintegral_gameRound_of_weighted (policy_ofUninformed_tsallisSPM φ α β₁ βbar p₀ c)
    t hFm
  -- the state of a history has `β ≥ β₁`
  have hβH (hh : Hist Unit (Fin mx) (Fin my × ℝ) t) : β₁ ≤ (stH hh).2 :=
    le_foldHistIdx_spmUpdate_snd hP t _
  have hK0 (hh : Hist Unit (Fin mx) (Fin my × ℝ) t) : 0 ≤ K hh := by
    have := hP.beta₁_pos.trans_le (hβH hh)
    have := Real.rpow_nonneg (qStar_nonneg (spmHat α βbar (stH hh)).2) (1 - α)
    simp only [hK]
    positivity
  set G : Hist Unit (Fin mx) (Fin my × ℝ) t → Fin mx → ℝ := fun hh x ↦ K hh * ∑ i, ph hh i
    * spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH hh)) ((), x, 1) i ^ 2 with hG
  have hG0 (hh : Hist Unit (Fin mx) (Fin my × ℝ) t) (x : Fin mx) : 0 ≤ G hh x :=
    mul_nonneg (hK0 hh) (sum_nonneg fun i _ ↦
      mul_nonneg ((spmHat α βbar (stH hh)).2.1 i) (sq_nonneg _))
  -- the inner integrals
  have hinner (hh : Hist Unit (Fin mx) (Fin my × ℝ) t) (x : Fin mx) (y : Fin my) :
      ∫⁻ r, F (hh, x, y, r) ∂(R t (hh, x, y)) ≤ ENNReal.ofReal (G hh x) := by
    calc ∫⁻ r, F (hh, x, y, r) ∂(R t (hh, x, y))
        ≤ ∫⁻ _r, ENNReal.ofReal (G hh x) ∂(R t (hh, x, y)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hR t hh x y] with r hr
          refine ENNReal.ofReal_le_ofReal ?_
          have e : K hh * ∑ i, ph hh i * spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c
              (stH hh)) ((), x, r) i ^ 2 = r ^ 2 * G hh x := by
            have e0 : spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH hh)) ((), x, r)
                = r • spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH hh)) ((), x, 1) :=
              spmEstimate_eq_smul φ _ ((), x, r)
            rw [e0]
            simp only [hG, PiLp.smul_apply, smul_eq_mul, mul_pow, mul_sum]
            exact sum_congr rfl fun i _ ↦ by ring
          rw [e]
          have : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
          nlinarith [hG0 hh x]
      _ = ENNReal.ofReal (G hh x) := by rw [lintegral_const, measure_univ, mul_one]
  -- the conditional expectation given the history
  have hcond (hh : Hist Unit (Fin mx) (Fin my × ℝ) t) :
      ∑ x, ENNReal.ofReal (spmWeights φ α β₁ βbar p₀ c t hh x)
          * ∫⁻ y, ∫⁻ r, F (hh, x, y, r) ∂(R t (hh, x, y))
            ∂(opp.policy t (Hist.swapPlayers hh, ()))
        ≤ ENNReal.ofReal (8 * (zCoef α (Fintype.card ιx) (ph hh) / (stH hh).2)) := by
    calc ∑ x, ENNReal.ofReal (spmWeights φ α β₁ βbar p₀ c t hh x)
          * ∫⁻ y, ∫⁻ r, F (hh, x, y, r) ∂(R t (hh, x, y))
            ∂(opp.policy t (Hist.swapPlayers hh, ()))
        ≤ ∑ x, ENNReal.ofReal (spmWeights φ α β₁ βbar p₀ c t hh x) * ENNReal.ofReal (G hh x) := by
          refine sum_le_sum fun x _ ↦ mul_le_mul_right ?_ _
          calc ∫⁻ y, ∫⁻ r, F (hh, x, y, r) ∂(R t (hh, x, y))
                ∂(opp.policy t (Hist.swapPlayers hh, ()))
              ≤ ∫⁻ _y, ENNReal.ofReal (G hh x) ∂(opp.policy t (Hist.swapPlayers hh, ())) :=
                lintegral_mono fun y ↦ hinner hh x y
            _ = ENNReal.ofReal (G hh x) := by rw [lintegral_const, measure_univ, mul_one]
      _ = ENNReal.ofReal (∑ x, spmWeights φ α β₁ βbar p₀ c t hh x * G hh x) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun x _ ↦
            mul_nonneg (spmWeights_nonneg φ α β₁ βbar p₀ c t hh x) (hG0 hh x)]
          exact sum_congr rfl fun x _ ↦
            (ENNReal.ofReal_mul (spmWeights_nonneg φ α β₁ βbar p₀ c t hh x)).symm
      _ ≤ ENNReal.ofReal (8 * (zCoef α (Fintype.card ιx) (ph hh) / (stH hh).2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpd := posDef_designOf_spmDist φ hP hV (hβH hh) h𝒳'
          have hdet : IsUnit (designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH hh) :
              EuclideanSpace ℝ (Fin mx))).det :=
            (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
          have e1 : ∑ x, spmWeights φ α β₁ βbar p₀ c t hh x * G hh x
              = K hh * ∑ i, ph hh i * (WithLp.ofLp (φ i) ⬝ᵥ (designOf φ (spmDist α βbar
                (Fintype.card ιx) p₀ c (stH hh) : EuclideanSpace ℝ (Fin mx)))⁻¹
                  *ᵥ WithLp.ofLp (φ i)) := by
            rw [← sum_mul_sum_sq_spmEstimate φ _ hdet, mul_sum]
            refine sum_congr rfl fun x _ ↦ ?_
            simp only [hG, spmWeights]
            ring
          have e2 := sum_mul_dotProduct_inv_le φ (spmDist α βbar (Fintype.card ιx) p₀ c (stH hh))
            hpd (q := fun i ↦ ph hh i) (fun i ↦ by
              have := half_le_spmDist hP (hβH hh) h𝒳' (p₀ := p₀) i
              simp only [hph]
              linarith)
          rw [e1]
          have hβ0 : 0 < (stH hh).2 := hP.beta₁_pos.trans_le (hβH hh)
          calc K hh * ∑ i, ph hh i * (WithLp.ofLp (φ i) ⬝ᵥ (designOf φ (spmDist α βbar
                (Fintype.card ιx) p₀ c (stH hh) : EuclideanSpace ℝ (Fin mx)))⁻¹
                  *ᵥ WithLp.ofLp (φ i))
              ≤ K hh * (2 * Fintype.card ιx) := mul_le_mul_of_nonneg_left e2 (hK0 hh)
            _ = 8 * (zCoef α (Fintype.card ιx) (ph hh) / (stH hh).2) := by
                simp only [hK, zCoef_eq, hph]
                field_simp
                ring
  -- conclusion
  have hβ₁ := hP.beta₁_pos
  set V : Ω → ℝ := fun ω ↦ 4 / ((1 - α) * (spmState φ α β₁ βbar p₀ c
      (fun s ↦ ((), X s ω, Rw s ω)) t).2)
        * qStar (spmHat α βbar (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
          EuclideanSpace ℝ (Fin mx)) ^ (1 - α)
        * ∑ i, (spmHat α βbar (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
          EuclideanSpace ℝ (Fin mx)) i
          * spmEstimateAt φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t i ^ 2 with hV
  set Z : Ω → ℝ := fun ω ↦ 8 * (zCoef α (Fintype.card ιx) (spmHat α βbar
      (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx))
      / (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2) with hZ
  have hVF (ω : Ω) : ENNReal.ofReal (V ω) = F (H ω, X t ω, Y t ω, Rw t ω) := by
    simp only [hV, hF, hK, hph, hstH, hH, spmStateHist_history]
    rfl
  have hZF (ω : Ω) : Z ω = 8 * (zCoef α (Fintype.card ιx) (ph (H ω)) / (stH (H ω)).2) := by
    simp only [hZ, hph, hstH, hH, spmStateHist_history]
  have hHm : Measurable H := h.measurable_history t
  have hZm : Measurable Z := by
    have : Measurable fun hh ↦ 8 * (zCoef α (Fintype.card ιx) (ph hh) / (stH hh).2) :=
      measurable_const.mul (((measurable_zCoef α _).comp (measurable_subtype_coe.comp
        ((measurable_spmHat α βbar).comp hstm))).div (measurable_snd.comp hstm))
    have heq : Z = fun ω ↦ 8 * (zCoef α (Fintype.card ιx) (ph (H ω)) / (stH (H ω)).2) :=
      funext hZF
    rw [heq]
    exact this.comp hHm
  have hV0 (ω : Ω) : 0 ≤ V ω := by
    have := hK0 (H ω)
    simp only [hK, hstH, hH, spmStateHist_history] at this
    refine mul_nonneg this (sum_nonneg fun i _ ↦ mul_nonneg ((spmHat α βbar _).2.1 i)
      (sq_nonneg _))
  have hZ0 (ω : Ω) : 0 ≤ Z ω := by
    rw [hZF]
    have := hP.beta₁_pos.trans_le (hβH (H ω))
    have := zCoef_nonneg hP (spmHat α βbar (stH (H ω))).2
    positivity
  have hZb (ω : Ω) : Z ω ≤ 8 * (Fintype.card ιx / (1 - α) / β₁) := by
    rw [hZF]
    have hβ0 := hP.beta₁_pos.trans_le (hβH (H ω))
    have hz := zCoef_le hP (spmHat α βbar (stH (H ω))).2
    have hz0 := zCoef_nonneg hP (spmHat α βbar (stH (H ω))).2
    have h1 : zCoef α (Fintype.card ιx) (ph (H ω)) / (stH (H ω)).2
        ≤ Fintype.card ιx / (1 - α) / β₁ :=
      calc _ ≤ Fintype.card ιx / (1 - α) / (stH (H ω)).2 := div_le_div_of_nonneg_right hz hβ0.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hP.beta₁_pos (hβH (H ω))
    linarith
  have hVm : AEMeasurable V P := by
    refine (ENNReal.measurable_toReal.comp_aemeasurable
      (hFm.comp (hHm.prodMk ((h.measurable_action t).prodMk
        ((h.measurable_feedback t).fst.prodMk (h.measurable_feedback t).snd)))).aemeasurable).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp only [Function.comp_apply, ← hVF, ENNReal.toReal_ofReal (hV0 ω)]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hV0) hVm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hZ0) hZm.aestronglyMeasurable]
  refine ENNReal.toReal_mono ?_ ?_
  · refine ne_top_of_le_ne_top (b := ENNReal.ofReal (8 * (Fintype.card ιx / (1 - α) / β₁)))
      ENNReal.ofReal_ne_top ?_
    calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P
        ≤ ∫⁻ _ω, ENNReal.ofReal (8 * (Fintype.card ιx / (1 - α) / β₁)) ∂P :=
          lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (hZb ω)
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  · calc ∫⁻ ω, ENNReal.ofReal (V ω) ∂P = ∫⁻ ω, F (H ω, X t ω, Y t ω, Rw t ω) ∂P :=
          lintegral_congr fun ω ↦ hVF ω
      _ = _ := key
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P := lintegral_mono fun ω ↦ by
          rw [hZF]
          exact hcond (H ω)

include hu hu1 hRu hR in
/-- **Regret of Tsallis-FTRL-SPM against an action** (Ito, Tsuchiya, Honda 2024, Eq. (24),
Proposition 16 and Section 4.3): in a run against an adaptive adversary in a game
`u x y = ⟪φ x, w y⟫` with rewards in `[-1, 1]`,
`ER_T(x) ≤ β₁ φ_α(p̂_0) + βbar φ_{1-α}(p̂_0) + (16 + 8 c) E[∑_{t < T} z_t / β_t]`. -/
lemma externalRegretAgainst_tsallisSPM_le (T : ℕ) (x : Fin mx) :
    externalRegretAgainst u X Y P T x
      ≤ β₁ * tsallisEntropy α (spmHat (𝒳 := Fin mx) α βbar (0, β₁) : EuclideanSpace ℝ (Fin mx))
        + βbar * tsallisEntropy (1 - α)
            (spmHat (𝒳 := Fin mx) α βbar (0, β₁) : EuclideanSpace ℝ (Fin mx))
        + (16 + 8 * c) * ∫ ω, ∑ t ∈ range T, zCoef α (Fintype.card ιx) (spmHat α βbar
            (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx))
            / (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2 ∂P := by
  have h𝒳' : 2 ≤ Fintype.card (Fin mx) := by simpa using h𝒳
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hRw : ∀ t, Measurable (Rw t) := fun t ↦ (h.measurable_feedback t).snd
  have hβ₁ := hP.beta₁_pos
  have h1α := hP.one_sub_pos
  have hd := hP.d_pos
  have hc := hP.c_pos
  set st : Ω → ℕ → EuclideanSpace ℝ (Fin mx) × ℝ := fun ω t ↦
    spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t with hst
  set ph : Ω → ℕ → EuclideanSpace ℝ (Fin mx) := fun ω t ↦
    (spmHat α βbar (st ω t) : EuclideanSpace ℝ (Fin mx)) with hph
  set g : Ω → ℕ → EuclideanSpace ℝ (Fin mx) := fun ω t ↦
    spmEstimateAt φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t with hg
  set zb : Ω → ℕ → ℝ := fun ω t ↦ zCoef α (Fintype.card ιx) (ph ω t) / (st ω t).2 with hzb
  set D : Ω → ℕ → ℝ := fun ω t ↦ ⟪EuclideanSpace.single x (1 : ℝ) - ph ω t, g ω t⟫ with hD
  set Vs : Ω → ℕ → ℝ := fun ω t ↦ 4 / ((1 - α) * (st ω t).2) * qStar (ph ω t) ^ (1 - α)
    * ∑ i, ph ω t i * g ω t i ^ 2 with hVs
  set C₀ := β₁ * tsallisEntropy α (spmHat (𝒳 := Fin mx) α βbar (0, β₁) :
      EuclideanSpace ℝ (Fin mx))
    + βbar * tsallisEntropy (1 - α) (spmHat (𝒳 := Fin mx) α βbar (0, β₁) :
      EuclideanSpace ℝ (Fin mx)) with hC₀
  -- measurability
  have hstm (t : ℕ) : Measurable fun ω ↦ st ω t :=
    measurable_spmState_run (my := my) φ α β₁ βbar p₀ c hX hY hRw t
  have hphm (t : ℕ) : Measurable fun ω ↦ ph ω t :=
    measurable_subtype_coe.comp ((measurable_spmHat α βbar).comp (hstm t))
  have hgm (t : ℕ) : Measurable fun ω ↦ g ω t :=
    measurable_spmEstimateAt_run (my := my) φ α β₁ βbar p₀ c hX hY hRw t
  have hzbm (t : ℕ) : Measurable fun ω ↦ zb ω t :=
    ((measurable_zCoef α _).comp (hphm t)).div (measurable_snd.comp (hstm t))
  have hDm (t : ℕ) : Measurable fun ω ↦ D ω t :=
    (measurable_const.sub (hphm t)).inner (hgm t)
  have hVm (t : ℕ) : Measurable fun ω ↦ Vs ω t := by
    refine ((measurable_const.div (measurable_const.mul (measurable_snd.comp (hstm t)))).mul
      ((measurable_qStar.comp (hphm t)).pow_const _)).mul
      (Finset.measurable_sum _ fun i _ ↦ ?_)
    exact ((PiLp.continuous_apply 2 _ i).measurable.comp (hphm t)).mul
      (((PiLp.continuous_apply 2 _ i).measurable.comp (hgm t)).pow_const 2)
  -- bounds
  have hβst (ω : Ω) (t : ℕ) : β₁ ≤ (st ω t).2 := le_spmState_snd hP _ t
  have hzb0 (ω : Ω) (t : ℕ) : 0 ≤ zb ω t :=
    div_nonneg (zCoef_nonneg hP (spmHat α βbar (st ω t)).2) (hβ₁.trans_le (hβst ω t)).le
  have hzbb (ω : Ω) (t : ℕ) : zb ω t ≤ Fintype.card ιx / (1 - α) / β₁ :=
    calc zb ω t ≤ Fintype.card ιx / (1 - α) / (st ω t).2 :=
          div_le_div_of_nonneg_right (zCoef_le hP (spmHat α βbar (st ω t)).2)
            (hβ₁.trans_le (hβst ω t)).le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hβ₁ (hβst ω t)
  have hzbi (t : ℕ) : Integrable (fun ω ↦ zb ω t) P :=
    integrable_of_ae_abs_le (hzbm t).aestronglyMeasurable (M := Fintype.card ιx / (1 - α) / β₁)
      (ae_of_all _ fun ω ↦ by rw [abs_of_nonneg (hzb0 ω t)]; exact hzbb ω t)
  have hRall := h.ae_forall_gameReward_mem measurableSet_Icc hR
  have hgb : ∀ᵐ ω ∂P, ∀ t i, |g ω t i| ≤ spmBound α β₁ βbar mx (t + 1) := by
    filter_upwards [hRall] with ω hω t i
    have hr : ∀ s, |((fun s ↦ ((), X s ω, Rw s ω)) s : Round Unit (Fin mx) ℝ).2.2| ≤ 1 :=
      fun s ↦ abs_le.2 ⟨(hω s).1, (hω s).2⟩
    have hB := (spmState_le_spmBound hP hV h𝒳' (fun s ↦ ((), X s ω, Rw s ω)) hr t).2.2
    rw [Fintype.card_fin] at hB
    exact (abs_spmEstimate_le φ hP hV (hβst ω t) h𝒳' (hr t) i).trans hB
  have hDi (t : ℕ) : Integrable (fun ω ↦ D ω t) P := by
    refine integrable_of_ae_abs_le (hDm t).aestronglyMeasurable
      (M := mx * spmBound α β₁ βbar mx (t + 1)) ?_
    filter_upwards [hgb] with ω hω
    simp only [hD, PiLp.inner_apply]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |⟪(EuclideanSpace.single x (1 : ℝ) - ph ω t) i, g ω t i⟫|
        ≤ ∑ _i : Fin mx, spmBound α β₁ βbar mx (t + 1) := sum_le_sum fun i _ ↦ by
          rw [RCLike.inner_apply, conj_trivial, abs_mul]
          calc |g ω t i| * |(EuclideanSpace.single x (1 : ℝ) - ph ω t) i|
              ≤ spmBound α β₁ βbar mx (t + 1) * 1 :=
                mul_le_mul (hω t i) (abs_single_sub_le_one (spmHat α βbar _).2 x i)
                  (abs_nonneg _) ((abs_nonneg _).trans (hω t i))
            _ = _ := mul_one _
      _ = _ := by simp
  have hVi (t : ℕ) : Integrable (fun ω ↦ Vs ω t) P := by
    refine integrable_of_ae_abs_le (hVm t).aestronglyMeasurable
      (M := 4 / ((1 - α) * β₁) * spmBound α β₁ βbar mx (t + 1) ^ 2) ?_
    filter_upwards [hgb] with ω hω
    have hβ0 : 0 < (st ω t).2 := hβ₁.trans_le (hβst ω t)
    have hq1 : qStar (ph ω t) ^ (1 - α) ≤ 1 :=
      Real.rpow_le_one (qStar_nonneg (spmHat α βbar (st ω t)).2)
        ((qStar_le_half _).trans (by norm_num)) h1α.le
    have hq0 : 0 ≤ qStar (ph ω t) ^ (1 - α) :=
      Real.rpow_nonneg (qStar_nonneg (spmHat α βbar (st ω t)).2) _
    have hsum : ∑ i, ph ω t i * g ω t i ^ 2 ≤ spmBound α β₁ βbar mx (t + 1) ^ 2 := by
      calc ∑ i, ph ω t i * g ω t i ^ 2 ≤ ∑ i, ph ω t i * spmBound α β₁ βbar mx (t + 1) ^ 2 :=
            sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hω t i) 2)
              ((spmHat α βbar (st ω t)).2.1 i)
        _ = spmBound α β₁ βbar mx (t + 1) ^ 2 := by
            rw [← sum_mul, (spmHat α βbar (st ω t)).2.2, one_mul]
    have hsum0 : 0 ≤ ∑ i, ph ω t i * g ω t i ^ 2 :=
      sum_nonneg fun i _ ↦ mul_nonneg ((spmHat α βbar (st ω t)).2.1 i) (sq_nonneg _)
    have hK : 4 / ((1 - α) * (st ω t).2) ≤ 4 / ((1 - α) * β₁) := by
      gcongr
      exact hβst ω t
    have hK0 : 0 ≤ 4 / ((1 - α) * (st ω t).2) := by positivity
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hK0 hq0) hsum0)]
    calc 4 / ((1 - α) * (st ω t).2) * qStar (ph ω t) ^ (1 - α) * ∑ i, ph ω t i * g ω t i ^ 2
        ≤ 4 / ((1 - α) * β₁) * 1 * spmBound α β₁ βbar mx (t + 1) ^ 2 := by
          gcongr
      _ = _ := by ring
  -- step 1: the regret of a round
  have hstep (t : ℕ) : ∫ ω, (u x (Y t ω) - u (X t ω) (Y t ω)) ∂P
      ≤ ∫ ω, D ω t ∂P + 8 * c * ∫ ω, zb ω t ∂P := by
    have hu1' : ∀ x y, |u x y| ≤ 1 := fun x y ↦ abs_le.2 ⟨(hu1 x y).1, (hu1 x y).2⟩
    have hint1 : Integrable (fun ω ↦ u x (Y t ω)) P :=
      integrable_of_ae_abs_le ((measurable_of_countable (u x)).comp (hY t)).aestronglyMeasurable
        (M := 1) (ae_of_all _ fun ω ↦ hu1' _ _)
    have hint2 : Integrable (fun ω ↦ u (X t ω) (Y t ω)) P :=
      integrable_of_ae_abs_le ((measurable_of_countable (Function.uncurry u)).comp
        ((hX t).prodMk (hY t))).aestronglyMeasurable (M := 1) (ae_of_all _ fun ω ↦ hu1' _ _)
    have hpdm : Measurable fun ω ↦ (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
        EuclideanSpace ℝ (Fin mx)) :=
      measurable_subtype_coe.comp ((measurable_spmDist α βbar _ p₀ c).comp (hstm t))
    have hint3 : Integrable (fun ω ↦ ∑ x', (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
        EuclideanSpace ℝ (Fin mx)) x' * u x' (Y t ω)) P := by
      refine integrable_of_ae_abs_le ?_ (M := 1) (ae_of_all _ fun ω ↦ ?_)
      · exact (Finset.measurable_sum _ fun x' _ ↦ ((PiLp.continuous_apply 2 _ x').measurable.comp
          hpdm).mul ((measurable_of_countable (u x')).comp (hY t))).aestronglyMeasurable
      · calc |∑ x', (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
              EuclideanSpace ℝ (Fin mx)) x' * u x' (Y t ω)|
            ≤ ∑ x', |(spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
              EuclideanSpace ℝ (Fin mx)) x' * u x' (Y t ω)| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ x', (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
              EuclideanSpace ℝ (Fin mx)) x' * 1 := sum_le_sum fun x' _ ↦ by
                rw [abs_mul, abs_of_nonneg ((spmDist α βbar _ p₀ c (st ω t)).2.1 x')]
                exact mul_le_mul_of_nonneg_left (hu1' _ _)
                  ((spmDist α βbar _ p₀ c (st ω t)).2.1 x')
          _ = 1 := by rw [← sum_mul, (spmDist α βbar _ p₀ c (st ω t)).2.2, one_mul]
    have hact := integral_comp_action_tsallisSPM h t u hu1'
    have hunb := integral_inner_spmEstimateAt hP hV h𝒳 hu hu1 hRu hR h t x
    have hphm' : Measurable fun ω ↦ ∑ i, ph ω t i * u i (Y t ω) :=
      Finset.measurable_sum _ fun i _ ↦ ((PiLp.continuous_apply 2 _ i).measurable.comp
        (hphm t)).mul ((measurable_of_countable (u i)).comp (hY t))
    have hint4 : Integrable (fun ω ↦ u x (Y t ω) - ∑ i, ph ω t i * u i (Y t ω)) P := by
      refine integrable_of_ae_abs_le ((((measurable_of_countable (u x)).comp (hY t)).sub
        hphm').aestronglyMeasurable) (M := 2) (ae_of_all _ fun ω ↦ ?_)
      have : |∑ i, ph ω t i * u i (Y t ω)| ≤ 1 := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |ph ω t i * u i (Y t ω)| ≤ ∑ i, ph ω t i * 1 := sum_le_sum fun i _ ↦ by
              rw [abs_mul, abs_of_nonneg ((spmHat α βbar (st ω t)).2.1 i)]
              exact mul_le_mul_of_nonneg_left (hu1' _ _) ((spmHat α βbar (st ω t)).2.1 i)
          _ = 1 := by rw [← sum_mul, (spmHat α βbar (st ω t)).2.2, one_mul]
      calc |u x (Y t ω) - ∑ i, ph ω t i * u i (Y t ω)|
          ≤ |u x (Y t ω)| + |∑ i, ph ω t i * u i (Y t ω)| := abs_sub _ _
        _ ≤ 2 := by linarith [hu1' x (Y t ω)]
    -- pointwise: the exploration costs at most `2 γ_t`
    have hpt (ω : Ω) : u x (Y t ω) - ∑ x', (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
        EuclideanSpace ℝ (Fin mx)) x' * u x' (Y t ω)
        ≤ (u x (Y t ω) - ∑ i, ph ω t i * u i (Y t ω)) + 8 * c * zb ω t := by
      rw [coe_spmDist hP (hβst ω t) h𝒳']
      set γ := 4 * c * zCoef α (Fintype.card ιx) (ph ω t) / (st ω t).2 with hγ
      have hγ0 : 0 ≤ γ := (gamma_pos hP (hβst ω t) h𝒳').le
      have hzbγ : γ = 4 * c * zb ω t := by simp only [hγ, hzb]; ring
      have hs1 : |∑ i, ph ω t i * u i (Y t ω)| ≤ 1 := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |ph ω t i * u i (Y t ω)| ≤ ∑ i, ph ω t i * 1 := sum_le_sum fun i _ ↦ by
              rw [abs_mul, abs_of_nonneg ((spmHat α βbar (st ω t)).2.1 i)]
              exact mul_le_mul_of_nonneg_left (hu1' _ _) ((spmHat α βbar (st ω t)).2.1 i)
          _ = 1 := by rw [← sum_mul, (spmHat α βbar (st ω t)).2.2, one_mul]
      have hs2 : |∑ i, (p₀ : EuclideanSpace ℝ (Fin mx)) i * u i (Y t ω)| ≤ 1 := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |(p₀ : EuclideanSpace ℝ (Fin mx)) i * u i (Y t ω)|
            ≤ ∑ i, (p₀ : EuclideanSpace ℝ (Fin mx)) i * 1 := sum_le_sum fun i _ ↦ by
              rw [abs_mul, abs_of_nonneg (p₀.2.1 i)]
              exact mul_le_mul_of_nonneg_left (hu1' _ _) (p₀.2.1 i)
          _ = 1 := by rw [← sum_mul, p₀.2.2, one_mul]
      have e : ∑ x', ((1 - γ) • ph ω t + γ • (p₀ : EuclideanSpace ℝ (Fin mx))) x' * u x' (Y t ω)
          = (1 - γ) * ∑ i, ph ω t i * u i (Y t ω)
            + γ * ∑ i, (p₀ : EuclideanSpace ℝ (Fin mx)) i * u i (Y t ω) := by
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
          mul_sum]
        congr 1 <;> exact sum_congr rfl fun i _ ↦ by ring
      rw [e]
      have h1 := neg_abs_le (∑ i, ph ω t i * u i (Y t ω))
      have h2 := neg_abs_le (∑ i, (p₀ : EuclideanSpace ℝ (Fin mx)) i * u i (Y t ω))
      have h3 := le_abs_self (∑ i, ph ω t i * u i (Y t ω))
      nlinarith
    calc ∫ ω, (u x (Y t ω) - u (X t ω) (Y t ω)) ∂P
        = ∫ ω, u x (Y t ω) ∂P - ∫ ω, u (X t ω) (Y t ω) ∂P := integral_sub hint1 hint2
      _ = ∫ ω, u x (Y t ω) ∂P - ∫ ω, ∑ x', (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
            EuclideanSpace ℝ (Fin mx)) x' * u x' (Y t ω) ∂P := by rw [hact]
      _ = ∫ ω, (u x (Y t ω) - ∑ x', (spmDist α βbar (Fintype.card ιx) p₀ c (st ω t) :
            EuclideanSpace ℝ (Fin mx)) x' * u x' (Y t ω)) ∂P := (integral_sub hint1 hint3).symm
      _ ≤ ∫ ω, ((u x (Y t ω) - ∑ i, ph ω t i * u i (Y t ω)) + 8 * c * zb ω t) ∂P :=
          integral_mono (hint1.sub hint3) (hint4.add ((hzbi t).const_mul _)) hpt
      _ = ∫ ω, (u x (Y t ω) - ∑ i, ph ω t i * u i (Y t ω)) ∂P + 8 * c * ∫ ω, zb ω t ∂P := by
          rw [integral_add hint4 ((hzbi t).const_mul _), integral_const_mul]
      _ = ∫ ω, D ω t ∂P + 8 * c * ∫ ω, zb ω t ∂P := by rw [← hunb]
  -- step 2: the pathwise bound
  have hpath : ∫ ω, ∑ t ∈ range T, D ω t ∂P
      ≤ C₀ + ∑ t ∈ range T, (8 * ∫ ω, zb ω t ∂P + ∫ ω, Vs ω t ∂P) := by
    have hbound : ∀ᵐ ω ∂P, ∑ t ∈ range T, D ω t
        ≤ C₀ + ∑ t ∈ range T, (8 * zb ω t + Vs ω t) := by
      filter_upwards [hRall] with ω hω
      have := sum_inner_spmEstimateAt_le hP hV h𝒳' (fun s ↦ ((), X s ω, Rw s ω))
        (fun s ↦ abs_le.2 ⟨(hω s).1, (hω s).2⟩) x T
      simp only [hD, hph, hg, hzb, hVs, hst, hC₀]
      convert this using 3
    have hi : Integrable (fun ω ↦ C₀ + ∑ t ∈ range T, (8 * zb ω t + Vs ω t)) P :=
      (integrable_const _).add (integrable_finsetSum _ fun t _ ↦
        ((hzbi t).const_mul _).add (hVi t))
    calc ∫ ω, ∑ t ∈ range T, D ω t ∂P
        ≤ ∫ ω, (C₀ + ∑ t ∈ range T, (8 * zb ω t + Vs ω t)) ∂P :=
          integral_mono_ae (integrable_finsetSum _ fun t _ ↦ hDi t) hi hbound
      _ = C₀ + ∑ t ∈ range T, (8 * ∫ ω, zb ω t ∂P + ∫ ω, Vs ω t ∂P) := by
          have hti (t : ℕ) : Integrable (fun ω ↦ 8 * zb ω t + Vs ω t) P :=
            ((hzbi t).const_mul _).add (hVi t)
          have hsi : Integrable (fun ω ↦ ∑ t ∈ range T, (8 * zb ω t + Vs ω t)) P :=
            integrable_finsetSum _ fun t _ ↦ hti t
          have h1 : ∫ ω, (C₀ + ∑ t ∈ range T, (8 * zb ω t + Vs ω t)) ∂P
              = ∫ _ω, C₀ ∂P + ∫ ω, ∑ t ∈ range T, (8 * zb ω t + Vs ω t) ∂P :=
            integral_add (integrable_const _) hsi
          rw [h1, integral_const, integral_finsetSum _ fun t _ ↦ hti t]
          simp only [probReal_univ, smul_eq_mul, one_mul]
          congr 1
          refine sum_congr rfl fun t _ ↦ ?_
          rw [integral_add ((hzbi t).const_mul _) (hVi t), integral_const_mul]
  -- step 3: the stability terms
  have hstab (t : ℕ) : ∫ ω, Vs ω t ∂P ≤ 8 * ∫ ω, zb ω t ∂P := by
    have := integral_stability_le hP hV h𝒳 hR h t
    rw [integral_const_mul] at this
    exact this
  -- conclusion
  have hER : externalRegretAgainst u X Y P T x
      = ∑ t ∈ range T, ∫ ω, (u x (Y t ω) - u (X t ω) (Y t ω)) ∂P := by
    rw [externalRegretAgainst, integral_finsetSum]
    intro t _
    have hu1' : ∀ x y, |u x y| ≤ 1 := fun x y ↦ abs_le.2 ⟨(hu1 x y).1, (hu1 x y).2⟩
    exact integrable_of_ae_abs_le ((((measurable_of_countable (u x)).comp (hY t)).sub
      ((measurable_of_countable (Function.uncurry u)).comp ((hX t).prodMk (hY t))))
        |>.aestronglyMeasurable) (M := 2) (ae_of_all _ fun ω ↦ by
          have := hu1' x (Y t ω)
          have := hu1' (X t ω) (Y t ω)
          calc |u x (Y t ω) - u (X t ω) (Y t ω)| ≤ |u x (Y t ω)| + |u (X t ω) (Y t ω)| :=
                abs_sub _ _
            _ ≤ 2 := by linarith)
  have hsumD : ∑ t ∈ range T, ∫ ω, D ω t ∂P = ∫ ω, ∑ t ∈ range T, D ω t ∂P :=
    (integral_finsetSum _ fun t _ ↦ hDi t).symm
  have hsumZ : ∫ ω, ∑ t ∈ range T, zb ω t ∂P = ∑ t ∈ range T, ∫ ω, zb ω t ∂P :=
    integral_finsetSum _ fun t _ ↦ hzbi t
  rw [hER, hsumZ]
  calc ∑ t ∈ range T, ∫ ω, (u x (Y t ω) - u (X t ω) (Y t ω)) ∂P
      ≤ ∑ t ∈ range T, (∫ ω, D ω t ∂P + 8 * c * ∫ ω, zb ω t ∂P) := sum_le_sum fun t _ ↦ hstep t
    _ = ∫ ω, ∑ t ∈ range T, D ω t ∂P + ∑ t ∈ range T, 8 * c * ∫ ω, zb ω t ∂P := by
        rw [sum_add_distrib, hsumD]
    _ ≤ C₀ + ∑ t ∈ range T, (8 * ∫ ω, zb ω t ∂P + 8 * ∫ ω, zb ω t ∂P)
          + ∑ t ∈ range T, 8 * c * ∫ ω, zb ω t ∂P := by
        gcongr ?_ + _
        refine hpath.trans ?_
        gcongr with t ht
        exact hstab t
    _ = C₀ + (16 + 8 * c) * ∑ t ∈ range T, ∫ ω, zb ω t ∂P := by
        rw [add_assoc, ← sum_add_distrib, mul_sum]
        congr 1
        exact sum_congr rfl fun t _ ↦ by ring

include hu hu1 hRu hR in
/-- **Worst-case regret of Tsallis-FTRL-SPM** (Ito, Tsuchiya, Honda 2024, Proposition 16): with
`H = (m ^ (1 - α) - 1) / α` and `C₀ = β₁ φ_α(p̂_0) + βbar φ_{1-α}(p̂_0)`,
`ER_T(x) ≤ C₀ + (16 + 8 c) (2 √(2 H T d / (1 - α)) + 2 d / ((1 - α) β₁))`. -/
lemma externalRegretAgainst_tsallisSPM_le_sqrt (T : ℕ) (x : Fin mx) :
    externalRegretAgainst u X Y P T x
      ≤ β₁ * tsallisEntropy α (spmHat (𝒳 := Fin mx) α βbar (0, β₁) : EuclideanSpace ℝ (Fin mx))
        + βbar * tsallisEntropy (1 - α)
            (spmHat (𝒳 := Fin mx) α βbar (0, β₁) : EuclideanSpace ℝ (Fin mx))
        + (16 + 8 * c) * (2 * √(2 * (((mx : ℝ) ^ (1 - α) - 1) / α)
            * (T * (Fintype.card ιx / (1 - α)))) + 2 * (Fintype.card ιx / (1 - α)) / β₁) := by
  have h𝒳' : 2 ≤ Fintype.card (Fin mx) := by simpa using h𝒳
  refine (externalRegretAgainst_tsallisSPM_le hP hV h𝒳 hu hu1 hRu hR h T x).trans ?_
  have hc := hP.c_pos
  gcongr
  calc ∫ ω, ∑ t ∈ range T, zCoef α (Fintype.card ιx) (spmHat α βbar
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx))
          / (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2 ∂P
      ≤ ∫ _ω, (2 * √(2 * (((mx : ℝ) ^ (1 - α) - 1) / α)
          * (T * (Fintype.card ιx / (1 - α)))) + 2 * (Fintype.card ιx / (1 - α)) / β₁) ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sum_nonneg fun t _ ↦
          div_nonneg (zCoef_nonneg hP (spmHat α βbar _).2)
            (hP.beta₁_pos.trans_le (le_spmState_snd hP _ t)).le) (integrable_const _)
          (ae_of_all _ fun ω ↦ ?_)
        have := sum_zCoef_div_le_sqrt (φ := φ) hP h𝒳' (p₀ := p₀) (fun s ↦ ((), X s ω, Rw s ω)) T
        rwa [Fintype.card_fin] at this
    _ = _ := by simp

include hu hu1 hRu hR in
/-- **Self-bounding regret of Tsallis-FTRL-SPM** (Ito, Tsuchiya, Honda 2024, Eqs. (116) to
(118)): if `Δ ≥ 0` and `Δ x ≥ Δmin > 0` for `x ≠ x₀`, then for every number of levels `J`,
`ER_T(x₀) ≤ C₀ + (16 + 8 c) (4 √(J W E[∑_{t < T} Δ x_t]) + 2 √(2 H / 2 ^ J T d / (1 - α))
+ 2 d / ((1 - α) β₁))` with `W = 2 d m ^ (1 - α) / (α (1 - α) Δmin)`. -/
lemma externalRegretAgainst_tsallisSPM_le_self (T J : ℕ) {x₀ : Fin mx} {Δ : Fin mx → ℝ}
    {Δmin : ℝ} (hΔmin : 0 < Δmin) (hΔ0 : ∀ x, 0 ≤ Δ x) (hΔ : ∀ x, x ≠ x₀ → Δmin ≤ Δ x) :
    externalRegretAgainst u X Y P T x₀
      ≤ β₁ * tsallisEntropy α (spmHat (𝒳 := Fin mx) α βbar (0, β₁) : EuclideanSpace ℝ (Fin mx))
        + βbar * tsallisEntropy (1 - α)
            (spmHat (𝒳 := Fin mx) α βbar (0, β₁) : EuclideanSpace ℝ (Fin mx))
        + (16 + 8 * c) * (4 * √(J * (2 * Fintype.card ιx * (mx : ℝ) ^ (1 - α)
              / (α * (1 - α) * Δmin)) * ∫ ω, ∑ t ∈ range T, Δ (X t ω) ∂P)
            + 2 * √(2 * ((((mx : ℝ) ^ (1 - α) - 1) / α) / 2 ^ J)
              * (T * (Fintype.card ιx / (1 - α))))
            + 2 * (Fintype.card ιx / (1 - α)) / β₁) := by
  have h𝒳' : 2 ≤ Fintype.card (Fin mx) := by simpa using h𝒳
  have hX : ∀ t, Measurable (X t) := h.measurable_action
  have hY : ∀ t, Measurable (Y t) := fun t ↦ (h.measurable_feedback t).fst
  have hRw : ∀ t, Measurable (Rw t) := fun t ↦ (h.measurable_feedback t).snd
  refine (externalRegretAgainst_tsallisSPM_le hP hV h𝒳 hu hu1 hRu hR h T x₀).trans ?_
  have hc := hP.c_pos
  have hα0 := hP.alpha_pos
  have h1α := hP.one_sub_pos
  have hd := hP.d_pos
  set W := 2 * Fintype.card ιx * (mx : ℝ) ^ (1 - α) / (α * (1 - α) * Δmin) with hW
  have hW0 : 0 ≤ W := by
    have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) mx) (1 - α)
    positivity
  set B := 2 * √(2 * ((((mx : ℝ) ^ (1 - α) - 1) / α) / 2 ^ J)
    * (T * (Fintype.card ιx / (1 - α)))) + 2 * (Fintype.card ιx / (1 - α)) / β₁ with hB
  set S : Ω → ℝ := fun ω ↦ ∑ t ∈ range T, ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
      (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx)) x
      * Δ x with hS
  have hS0 (ω : Ω) : 0 ≤ S ω := sum_nonneg fun t _ ↦ sum_nonneg fun x _ ↦
    mul_nonneg ((spmDist α βbar _ p₀ c _).2.1 x) (hΔ0 x)
  set M := ∑ x, Δ x with hM
  have hΔM (x : Fin mx) : Δ x ≤ M :=
    single_le_sum (f := Δ) (fun x _ ↦ hΔ0 x) (Finset.mem_univ x)
  have hSb (ω : Ω) : S ω ≤ T * M := by
    calc S ω ≤ ∑ _t ∈ range T, M := sum_le_sum fun t _ ↦ by
          calc ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
                (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
                  EuclideanSpace ℝ (Fin mx)) x * Δ x
              ≤ ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
                (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
                  EuclideanSpace ℝ (Fin mx)) x * M :=
                sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hΔM x)
                  ((spmDist α βbar _ p₀ c _).2.1 x)
            _ = M := by rw [← sum_mul, (spmDist α βbar _ p₀ c _).2.2, one_mul]
      _ = T * M := by simp
  have hSm : Measurable S := by
    refine Finset.measurable_sum _ fun t _ ↦ Finset.measurable_sum _ fun x _ ↦ ?_
    exact ((PiLp.continuous_apply 2 _ x).measurable.comp (measurable_subtype_coe.comp
      ((measurable_spmDist α βbar _ p₀ c).comp
        (measurable_spmState_run (my := my) φ α β₁ βbar p₀ c hX hY hRw t)))).mul
      measurable_const
  have hSi : Integrable S P :=
    integrable_of_ae_abs_le hSm.aestronglyMeasurable (M := T * M)
      (ae_of_all _ fun ω ↦ by rw [abs_of_nonneg (hS0 ω)]; exact hSb ω)
  -- `E[S] = E[∑_t Δ x_t]`
  have hES : ∫ ω, S ω ∂P = ∫ ω, ∑ t ∈ range T, Δ (X t ω) ∂P := by
    have hΔb : ∀ x (y : Fin my), |(fun x (_ : Fin my) ↦ Δ x) x y| ≤ M := fun x y ↦ by
      rw [abs_of_nonneg (hΔ0 x)]
      exact hΔM x
    rw [integral_finsetSum _ fun t _ ↦ ?_, integral_finsetSum _ fun t _ ↦ ?_]
    · refine sum_congr rfl fun t _ ↦ ?_
      rw [integral_comp_action_tsallisSPM h t (fun x _ ↦ Δ x) hΔb]
    · exact integrable_of_ae_abs_le ((measurable_of_countable Δ).comp (hX t)).aestronglyMeasurable
        (M := M) (ae_of_all _ fun ω ↦ hΔb _ (Y t ω))
    · refine integrable_of_ae_abs_le (Finset.measurable_sum _ fun x _ ↦
        ((PiLp.continuous_apply 2 _ x).measurable.comp (measurable_subtype_coe.comp
          ((measurable_spmDist α βbar _ p₀ c).comp
            (measurable_spmState_run (my := my) φ α β₁ βbar p₀ c hX hY hRw t)))).mul
          measurable_const).aestronglyMeasurable (M := M) (ae_of_all _ fun ω ↦ ?_)
      rw [abs_of_nonneg (sum_nonneg fun x _ ↦ mul_nonneg ((spmDist α βbar _ p₀ c _).2.1 x)
        (hΔ0 x))]
      calc ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
            (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
              EuclideanSpace ℝ (Fin mx)) x * Δ x
          ≤ ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
            (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) :
              EuclideanSpace ℝ (Fin mx)) x * M :=
            sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hΔM x)
              ((spmDist α βbar _ p₀ c _).2.1 x)
        _ = M := by rw [← sum_mul, (spmDist α βbar _ p₀ c _).2.2, one_mul]
  -- pathwise bound
  have hpath (ω : Ω) : ∑ t ∈ range T, zCoef α (Fintype.card ιx) (spmHat α βbar
        (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx))
        / (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2
      ≤ 4 * √(J * W * S ω) + B := by
    have h1 := sum_zCoef_div_le_levels (φ := φ) hP h𝒳' (p₀ := p₀) (fun s ↦ ((), X s ω, Rw s ω)) J T
    have h2 := sum_tsallisEntropy_mul_zCoef_le (φ := φ) hP h𝒳' (p₀ := p₀) (c := c)
      (fun s ↦ ((), X s ω, Rw s ω)) T hΔmin hΔ0 hΔ
    rw [Fintype.card_fin] at h1 h2
    refine h1.trans ?_
    rw [add_assoc]
    refine add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)) le_rfl
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg J)
  have hsqi : Integrable (fun ω ↦ √(J * W * S ω)) P :=
    integrable_of_ae_abs_le (measurable_const.mul hSm).sqrt.aestronglyMeasurable
      (M := √(J * W * (T * M))) (ae_of_all _ fun ω ↦ by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hSb ω) (by positivity)))
  have hJensen := integral_sqrt_le_sqrt_integral (P := P) (Z := fun ω ↦ J * W * S ω)
    (fun ω ↦ mul_nonneg (by positivity) (hS0 ω)) (hSi.const_mul _) hsqi
  rw [integral_const_mul, hES] at hJensen
  gcongr
  calc ∫ ω, ∑ t ∈ range T, zCoef α (Fintype.card ιx) (spmHat α βbar
          (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t) : EuclideanSpace ℝ (Fin mx))
          / (spmState φ α β₁ βbar p₀ c (fun s ↦ ((), X s ω, Rw s ω)) t).2 ∂P
      ≤ ∫ ω, (4 * √(J * W * S ω) + B) ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sum_nonneg fun t _ ↦
          div_nonneg (zCoef_nonneg hP (spmHat α βbar _).2)
            (hP.beta₁_pos.trans_le (le_spmState_snd hP _ t)).le)
          ((hsqi.const_mul 4).add (integrable_const B)) (ae_of_all _ hpath)
    _ = 4 * ∫ ω, √(J * W * S ω) ∂P + B := by
        rw [integral_add (hsqi.const_mul 4) (integrable_const B), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 4 * √(J * W * ∫ ω, ∑ t ∈ range T, Δ (X t ω) ∂P) + B := by gcongr
    _ = _ := by rw [hB]; ring

end Run

end Ito2026Adversarial
