/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.RepeatedGame
public import Ito2026Adversarial.Mathlib.MeasureTheory.Measure.Weighted
public import Ito2026Adversarial.Mathlib.Probability.HasCondDistrib
public import Ito2026Adversarial.Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The rounds of a run of a repeated game

In a run of a player `alg` against an adaptive opponent `opp` with reward kernel `R`
(`IsAlgEnvSeq … alg (gameEnv opp R) P`), the round `n` is drawn as follows given the history
`H n` of the first `n` rounds: the learner's action `x` from `alg.policy n (H n, ())`, the
opponent's action `y` from `opp.policy n (H n swapped, ())` (independently of `x`: the two players
move simultaneously), and the reward from `R n (H n, x, y)`.

## Main statements

* `Learning.IsAlgEnvSeq.lintegral_gameRound`: the integral of a function of
  `(H n, x_n, y_n, r_n)` is the integral over `H n` of the iterated integral against these three
  laws;
* `Learning.IsAlgEnvSeq.lintegral_gameRound_of_weighted`: the same for a learner drawing its
  action from weights `wt n (H n)` (for instance an uninformed learner sampling from a
  distribution computed from the past rewards, such as Tsallis-INF);
* `Learning.IsAlgEnvSeq.ae_gameReward_mem`: the rewards lie almost surely in the set given by
  `RewardKernel.RewardsIn`;
* `Learning.IsAlgEnvSeq.lintegral_gameAction_eq_sum`: for a learner with weights `wt`, the
  conditional law of `x_n` given the history and `y_n` is `wt n (H n)` (conditional independence
  of the actions of the two players);
* `Learning.IsAlgEnvSeq.lintegral_one_sub_gameReward_mul`: the reward has conditional mean
  `u x_n y_n` given the history and the actions of the round;
* `Learning.IsAlgEnvSeq.integral_gameReward_mul`, `Learning.IsAlgEnvSeq.integral_gameAction_eq_sum`:
  the signed versions of the last two statements, for almost surely bounded functions:
  `E[r_n k(H n, x_n, y_n)] = E[u x_n y_n k(H n, x_n, y_n)]` and
  `E[f(H n, x_n, y_n)] = E[∑ x, wt n (H n) x f(H n, x, y_n)]`.

## Tags

repeated game, bandit feedback, conditional distribution
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Learning.RepeatedGame

variable {𝒳 𝒴 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Player 𝒳 𝒴} {opp : Player 𝒴 𝒳}
  {R : RewardKernel 𝒳 𝒴} [∀ n, IsMarkovKernel (R n)]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴} {Rw : ℕ → Ω → ℝ}

/-- **One round of a repeated game.** In a run of `alg` against the opponent `opp` with reward
kernel `R`, the integral of a function of the history `H n`, the actions `x_n`, `y_n` and the
reward `r_n` of round `n` is the integral over `H n` of the iterated integral of the function
against the policy of `alg` at `H n`, the policy of `opp` at the swapped history (which does
not depend on `x_n`) and the reward kernel. -/
lemma _root_.Learning.IsAlgEnvSeq.lintegral_gameRound
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (n : ℕ) {F : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω, Rw n ω)
        ∂P =
      ∫⁻ ω, ∫⁻ x, ∫⁻ y, ∫⁻ r,
        F (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, y, r)
          ∂(R n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, y))
          ∂(opp.policy n (Hist.swapPlayers
            (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω), ()))
          ∂(alg.policy n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, ())) ∂P := by
  set H := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n with hH
  let F₁ : ((Hist Unit 𝒳 (𝒴 × ℝ) n × Unit) × 𝒳) × (𝒴 × ℝ) → ℝ≥0∞ :=
    fun z ↦ F (z.1.1.1, z.1.2, z.2.1, z.2.2)
  have hF₁ : Measurable F₁ := hF.comp (by fun_prop)
  have h1 := HasCondDistrib.lintegral_prodMk (h.hasCondDistrib_feedback n) hF₁
  let F₂ : (Hist Unit 𝒳 (𝒴 × ℝ) n × Unit) × 𝒳 → ℝ≥0∞ :=
    fun a ↦ ∫⁻ b, F₁ (a, b) ∂((gameEnv opp R).feedback n a)
  have hF₂ : Measurable F₂ := hF₁.lintegral_kernel_prod_right'
  have h2 := HasCondDistrib.lintegral_prodMk (h.hasCondDistrib_action n) hF₂
  change ∫⁻ ω, F₁ (((H ω, ()), X n ω), (Y n ω, Rw n ω)) ∂P = _
  rw [h1]
  change ∫⁻ ω, F₂ ((H ω, ()), X n ω) ∂P = _
  rw [h2]
  refine lintegral_congr fun ω ↦ lintegral_congr fun x ↦ ?_
  simp only [F₂, gameEnv]
  rw [Kernel.lintegral_compProd _ _ _ (f := fun b ↦ F₁ (((H ω, ()), x), b))
    (hF₁.comp measurable_prodMk_left)]
  simp only [Kernel.comap_apply, F₁]
  rfl

/-- In a run of a repeated game, the rewards lie almost surely in the set `s` of
`RewardKernel.RewardsIn R s`. -/
lemma _root_.Learning.IsAlgEnvSeq.ae_gameReward_mem {s : Set ℝ} (hs : MeasurableSet s)
    (hR : R.RewardsIn s)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (n : ℕ) : ∀ᵐ ω ∂P, Rw n ω ∈ s := by
  have hm : Measurable (Rw n) := measurable_snd.comp (h.measurable_feedback n)
  rw [ae_iff]
  have key := h.lintegral_gameRound n (F := fun q ↦ sᶜ.indicator 1 q.2.2.2)
    ((measurable_one.indicator hs.compl).comp (by fun_prop))
  simp only at key
  have h0 : ∀ q : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴, ∫⁻ r, sᶜ.indicator 1 r ∂(R n q) = 0 := by
    intro q
    rw [lintegral_indicator_one hs.compl]
    exact (ae_iff.1 (hR n q.1 q.2.1 q.2.2))
  simp only [h0, lintegral_zero] at key
  change P (Rw n ⁻¹' sᶜ) = 0
  rw [← lintegral_indicator_one (hs.compl.preimage hm), ← key]
  rfl

/-- In a run of a repeated game, almost surely all the rewards lie in the set `s` of
`RewardKernel.RewardsIn R s`. -/
lemma _root_.Learning.IsAlgEnvSeq.ae_forall_gameReward_mem {s : Set ℝ} (hs : MeasurableSet s)
    (hR : R.RewardsIn s)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P) :
    ∀ᵐ ω ∂P, ∀ t, Rw t ω ∈ s :=
  ae_all_iff.2 fun t ↦ h.ae_gameReward_mem hs hR t

/-- **Conditional mean of the reward.** If the reward kernel has conditional mean `u` and
rewards in `[-1, 1]`, then `E[(1 - r_n) k(H n, x_n, y_n)] = E[(1 - u x_n y_n) k(H n, x_n, y_n)]`
for every measurable `k ≥ 0`. -/
lemma _root_.Learning.IsAlgEnvSeq.lintegral_one_sub_gameReward_mul {u : 𝒳 → 𝒴 → ℝ}
    (hu : Measurable (Function.uncurry u)) (hRu : R.HasMean u)
    (hR : R.RewardsIn (Set.Icc (-1) 1))
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (n : ℕ) {k : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 → ℝ≥0∞} (hk : Measurable k) :
    ∫⁻ ω, ENNReal.ofReal (1 - Rw n ω) *
        k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P =
      ∫⁻ ω, ENNReal.ofReal (1 - u (X n ω) (Y n ω)) *
        k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P := by
  have hk' : Measurable fun q : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 × ℝ ↦ k (q.1, q.2.1, q.2.2.1) :=
    hk.comp (by fun_prop)
  have h1 := h.lintegral_gameRound n
    (F := fun q ↦ ENNReal.ofReal (1 - q.2.2.2) * k (q.1, q.2.1, q.2.2.1))
    ((ENNReal.measurable_ofReal.comp (measurable_const.sub (by fun_prop))).mul hk')
  have hum : Measurable fun q : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 × ℝ ↦ u q.2.1 q.2.2.1 :=
    hu.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have h2 := h.lintegral_gameRound n
    (F := fun q ↦ ENNReal.ofReal (1 - u q.2.1 q.2.2.1) * k (q.1, q.2.1, q.2.2.1))
    ((ENNReal.measurable_ofReal.comp (measurable_const.sub hum)).mul hk')
  simp only at h1 h2
  rw [h1, h2]
  refine lintegral_congr fun ω ↦ lintegral_congr fun x ↦ lintegral_congr fun y ↦ ?_
  set q := (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, y)
  have hint : Integrable (fun r ↦ 1 - r) (R n q) := by
    refine Integrable.of_bound (by fun_prop) 2 ?_
    filter_upwards [hR n q.1 q.2.1 q.2.2] with r hr
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hr.1, hr.2]
  have hnn : 0 ≤ᵐ[R n q] fun r ↦ 1 - r := by
    filter_upwards [hR n q.1 q.2.1 q.2.2] with r hr
    simp only [Pi.zero_apply, sub_nonneg]
    exact hr.2
  have hmean : ∫ r, (1 - r) ∂(R n q) = 1 - u x y := by
    have hint' : Integrable (fun r : ℝ ↦ r) (R n q) :=
      ((integrable_const 1).sub hint).congr (ae_of_all _ fun r ↦ by simp)
    rw [integral_sub (integrable_const _) hint', integral_const, hRu n q.1 q.2.1 q.2.2]
    simp [q]
  rw [lintegral_mul_const (k q) (f := fun r ↦ ENNReal.ofReal (1 - r))
      (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)),
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hmean, lintegral_const, measure_univ,
    mul_one]

section Weighted

variable [Fintype 𝒳] [MeasurableSingletonClass 𝒳]
  {wt : (n : ℕ) → Hist Unit 𝒳 (𝒴 × ℝ) n → 𝒳 → ℝ}

/-- **One round of a repeated game, for a learner with weights.** If the learner draws its
action of round `n` from the weights `wt n (H n)` of the history, the integral of a function of
`(H n, x_n, y_n, r_n)` is the integral of `∑ x, wt n (H n) x ∫∫ F(H n, x, y, r) dR dopp`. -/
lemma _root_.Learning.IsAlgEnvSeq.lintegral_gameRound_of_weighted
    (hwt : ∀ n h, alg.policy n (h, ()) = weightedMeasure (wt n h))
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (n : ℕ) {F : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω, Rw n ω)
        ∂P =
      ∫⁻ ω, ∑ x, ENNReal.ofReal
          (wt n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x) *
        ∫⁻ y, ∫⁻ r, F (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, y, r)
          ∂(R n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, y))
          ∂(opp.policy n (Hist.swapPlayers
            (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω), ())) ∂P := by
  rw [h.lintegral_gameRound n hF]
  refine lintegral_congr fun ω ↦ ?_
  rw [hwt, lintegral_weightedMeasure_eq_sum]

/-- **Conditional law of the learner's action.** For a learner with weights `wt` (nonnegative,
summing to `1`), the conditional law of `x_n` given the history `H n` and the opponent's action
`y_n` is `wt n (H n)`: for every measurable `f ≥ 0`,
`E[f(H n, x_n, y_n)] = E[∑ x, wt n (H n) x f(H n, x, y_n)]`. -/
lemma _root_.Learning.IsAlgEnvSeq.lintegral_gameAction_eq_sum
    (hwt : ∀ n h, alg.policy n (h, ()) = weightedMeasure (wt n h))
    (hwt0 : ∀ n h x, 0 ≤ wt n h x) (hwt1 : ∀ n h, ∑ x, wt n h x = 1)
    (hwtm : ∀ n, Measurable (wt n))
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    (n : ℕ) {f : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P =
      ∫⁻ ω, ∑ x, ENNReal.ofReal
          (wt n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x) *
        f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, Y n ω) ∂P := by
  have h1 := h.lintegral_gameRound_of_weighted hwt n (F := fun q ↦ f (q.1, q.2.1, q.2.2.1))
    (hf.comp (by fun_prop))
  have hG : Measurable fun q : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 × ℝ ↦
      ∑ x, ENNReal.ofReal (wt n q.1 x) * f (q.1, x, q.2.2.1) := by
    refine Finset.measurable_sum _ fun x _ ↦ ?_
    exact (ENNReal.measurable_ofReal.comp ((measurable_pi_apply x).comp
      ((hwtm n).comp measurable_fst))).mul (hf.comp (by fun_prop))
  have h2 := h.lintegral_gameRound_of_weighted hwt n hG
  simp only at h1 h2
  rw [h1, h2]
  refine lintegral_congr fun ω ↦ ?_
  set Hn := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω
  have hsum : ∑ x, ENNReal.ofReal (wt n Hn x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ hwt0 n Hn x), hwt1, ENNReal.ofReal_one]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [← sum_mul, hsum, one_mul, lintegral_finsetSum _ fun x _ ↦ ?_]
  · refine sum_congr rfl fun x _ ↦ ?_
    rw [lintegral_const_mul (ENNReal.ofReal (wt n Hn x)) (f := fun y ↦ f (Hn, x, y))
      (hf.comp (by fun_prop))]
  · exact measurable_const.mul (hf.comp (by fun_prop))

end Weighted

/-! ### Signed expectations -/

section Reward

variable {u : 𝒳 → 𝒴 → ℝ} (hu : Measurable (Function.uncurry u))
  (hu1 : ∀ x y, u x y ∈ Set.Icc (-1) 1) (hRu : R.HasMean u)
  (hR : R.RewardsIn (Set.Icc (-1) 1))
  (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
include hu hu1 hRu hR h

/-- `E[r_n k] = E[u x_n y_n k]` for a nonnegative, almost surely bounded `k(H n, x_n, y_n)`. -/
private lemma integral_gameReward_mul_of_nonneg (n : ℕ)
    {k : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 → ℝ} (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q) {M : ℝ}
    (hM : ∀ᵐ ω ∂P,
      k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ≤ M) :
    ∫ ω, Rw n ω * k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P
      = ∫ ω, u (X n ω) (Y n ω)
          * k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P := by
  set K : Ω → ℝ := fun ω ↦
    k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) with hK
  have hKm : Measurable K := hk.comp ((h.measurable_history n).prodMk
    ((h.measurable_action n).prodMk (h.measurable_feedback n).fst))
  have hRwm : Measurable (Rw n) := (h.measurable_feedback n).snd
  have hum : Measurable fun ω ↦ u (X n ω) (Y n ω) :=
    hu.comp ((h.measurable_action n).prodMk (h.measurable_feedback n).fst)
  have hRae := h.ae_gameReward_mem measurableSet_Icc hR n
  have hKb : ∀ᵐ ω ∂P, |K ω| ≤ M := by
    filter_upwards [hM] with ω hω
    rwa [abs_of_nonneg (hk0 _)]
  have hM0 : ∀ᵐ ω ∂P, 0 ≤ M := by
    filter_upwards [hM] with ω hω
    exact (hk0 _).trans hω
  have key := h.lintegral_one_sub_gameReward_mul hu hRu hR n
    (k := fun q ↦ ENNReal.ofReal (k q)) (ENNReal.measurable_ofReal.comp hk)
  have e1 : ∫ ω, (1 - Rw n ω) * K ω ∂P = ∫ ω, (1 - u (X n ω) (Y n ω)) * K ω ∂P := by
    refine integral_eq_of_lintegral_ofReal_eq
      ((measurable_const.sub hRwm).mul hKm).aestronglyMeasurable
      ((measurable_const.sub hum).mul hKm).aestronglyMeasurable ?_ ?_ ?_
    · filter_upwards [hRae] with ω hω
      exact mul_nonneg (sub_nonneg.2 hω.2) (hk0 _)
    · exact ae_of_all _ fun ω ↦ mul_nonneg (sub_nonneg.2 (hu1 _ _).2) (hk0 _)
    · rw [lintegral_congr_ae (g := fun ω ↦ ENNReal.ofReal (1 - Rw n ω) * ENNReal.ofReal (K ω))
        (by filter_upwards [hRae] with ω hω; exact ENNReal.ofReal_mul (sub_nonneg.2 hω.2)),
        lintegral_congr (g := fun ω ↦ ENNReal.ofReal (1 - u (X n ω) (Y n ω))
          * ENNReal.ofReal (K ω)) (fun ω ↦ ENNReal.ofReal_mul (sub_nonneg.2 (hu1 _ _).2))]
      exact key
  have hKi : Integrable K P := Integrable.of_ae_abs_le hKm.aestronglyMeasurable hKb
  have h1i : Integrable (fun ω ↦ (1 - Rw n ω) * K ω) P := by
    refine Integrable.of_ae_abs_le ((measurable_const.sub hRwm).mul hKm).aestronglyMeasurable
      (M := 2 * M) ?_
    filter_upwards [hRae, hKb] with ω hω hKω
    rw [abs_mul]
    have : |1 - Rw n ω| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hω.1, hω.2]
    nlinarith [abs_nonneg (K ω), abs_nonneg (1 - Rw n ω)]
  have h2i : Integrable (fun ω ↦ (1 - u (X n ω) (Y n ω)) * K ω) P := by
    refine Integrable.of_ae_abs_le ((measurable_const.sub hum).mul hKm).aestronglyMeasurable
      (M := 2 * M) ?_
    filter_upwards [hKb] with ω hKω
    rw [abs_mul]
    have := hu1 (X n ω) (Y n ω)
    have : |1 - u (X n ω) (Y n ω)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    nlinarith [abs_nonneg (K ω), abs_nonneg (1 - u (X n ω) (Y n ω))]
  calc ∫ ω, Rw n ω * K ω ∂P = ∫ ω, (K ω - (1 - Rw n ω) * K ω) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω ↦ by ring)
    _ = ∫ ω, K ω ∂P - ∫ ω, (1 - Rw n ω) * K ω ∂P := integral_sub hKi h1i
    _ = ∫ ω, K ω ∂P - ∫ ω, (1 - u (X n ω) (Y n ω)) * K ω ∂P := by rw [e1]
    _ = ∫ ω, (K ω - (1 - u (X n ω) (Y n ω)) * K ω) ∂P := (integral_sub hKi h2i).symm
    _ = ∫ ω, u (X n ω) (Y n ω) * K ω ∂P := integral_congr_ae (ae_of_all _ fun ω ↦ by ring)

/-- **Conditional mean of the reward, signed version**: `E[r_n k(H n, x_n, y_n)]
= E[u x_n y_n k(H n, x_n, y_n)]` for a measurable `k` which is almost surely bounded along the
run. -/
lemma _root_.Learning.IsAlgEnvSeq.integral_gameReward_mul (n : ℕ)
    {k : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 → ℝ} (hk : Measurable k) {M : ℝ}
    (hM : ∀ᵐ ω ∂P,
      |k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω)| ≤ M) :
    ∫ ω, Rw n ω * k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P
      = ∫ ω, u (X n ω) (Y n ω)
          * k (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P := by
  set H := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n with hH
  have hp := integral_gameReward_mul_of_nonneg hu hu1 hRu hR h n (k := fun q ↦ max (k q) 0)
    (hk.max measurable_const) (fun q ↦ le_max_right _ _) (M := M) (by
      filter_upwards [hM] with ω hω
      exact max_le ((le_abs_self _).trans hω) ((abs_nonneg _).trans hω))
  have hn := integral_gameReward_mul_of_nonneg hu hu1 hRu hR h n (k := fun q ↦ max (-k q) 0)
    (hk.neg.max measurable_const) (fun q ↦ le_max_right _ _) (M := M) (by
      filter_upwards [hM] with ω hω
      exact max_le ((neg_le_abs _).trans hω) ((abs_nonneg _).trans hω))
  have hKm : Measurable fun ω ↦ k (H ω, X n ω, Y n ω) := hk.comp ((h.measurable_history n).prodMk
    ((h.measurable_action n).prodMk (h.measurable_feedback n).fst))
  have hRwm : Measurable (Rw n) := (h.measurable_feedback n).snd
  have hum : Measurable fun ω ↦ u (X n ω) (Y n ω) :=
    hu.comp ((h.measurable_action n).prodMk (h.measurable_feedback n).fst)
  have hRae := h.ae_gameReward_mem measurableSet_Icc hR n
  have hsplit (a b : ℝ) : a * b = a * max b 0 - a * max (-b) 0 := by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hb, max_eq_right (by linarith)]
      ring
  have hi (v : Ω → ℝ) (hv : Measurable v) (hvb : ∀ᵐ ω ∂P, |v ω| ≤ 1) (g : ℝ → ℝ)
      (hg : Measurable g) (hgb : ∀ b, |g b| ≤ |b|) :
      Integrable (fun ω ↦ v ω * g (k (H ω, X n ω, Y n ω))) P := by
    refine Integrable.of_ae_abs_le (hv.mul (hg.comp hKm)).aestronglyMeasurable (M := M) ?_
    filter_upwards [hvb, hM] with ω h1 h2
    rw [abs_mul]
    calc |v ω| * |g (k (H ω, X n ω, Y n ω))| ≤ 1 * M :=
          mul_le_mul h1 ((hgb _).trans h2) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hRb : ∀ᵐ ω ∂P, |Rw n ω| ≤ 1 := by
    filter_upwards [hRae] with ω hω
    exact abs_le.2 ⟨hω.1, hω.2⟩
  have hub : ∀ᵐ ω ∂P, |u (X n ω) (Y n ω)| ≤ 1 :=
    ae_of_all _ fun ω ↦ abs_le.2 ⟨(hu1 _ _).1, (hu1 _ _).2⟩
  have hgp : ∀ b : ℝ, |max b 0| ≤ |b| := fun b ↦ by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb, abs_zero]; exact abs_nonneg b
    · rw [max_eq_left hb]
  have hgn : ∀ b : ℝ, |max (-b) 0| ≤ |b| := fun b ↦ by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_left (by linarith), abs_neg]
    · rw [max_eq_right (by linarith), abs_zero]; exact abs_nonneg b
  calc ∫ ω, Rw n ω * k (H ω, X n ω, Y n ω) ∂P
      = ∫ ω, (Rw n ω * max (k (H ω, X n ω, Y n ω)) 0
          - Rw n ω * max (-k (H ω, X n ω, Y n ω)) 0) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω ↦ hsplit _ _)
    _ = ∫ ω, Rw n ω * max (k (H ω, X n ω, Y n ω)) 0 ∂P
          - ∫ ω, Rw n ω * max (-k (H ω, X n ω, Y n ω)) 0 ∂P :=
        integral_sub (hi _ hRwm hRb _ (measurable_id.max measurable_const) hgp)
          (hi _ hRwm hRb _ (measurable_id.neg.max measurable_const) hgn)
    _ = ∫ ω, u (X n ω) (Y n ω) * max (k (H ω, X n ω, Y n ω)) 0 ∂P
          - ∫ ω, u (X n ω) (Y n ω) * max (-k (H ω, X n ω, Y n ω)) 0 ∂P := by
        rw [hp, hn]
    _ = ∫ ω, (u (X n ω) (Y n ω) * max (k (H ω, X n ω, Y n ω)) 0
          - u (X n ω) (Y n ω) * max (-k (H ω, X n ω, Y n ω)) 0) ∂P :=
        (integral_sub (hi _ hum hub _ (measurable_id.max measurable_const) hgp)
          (hi _ hum hub _ (measurable_id.neg.max measurable_const) hgn)).symm
    _ = ∫ ω, u (X n ω) (Y n ω) * k (H ω, X n ω, Y n ω) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω ↦ (hsplit _ _).symm)

end Reward

section Action

variable [Fintype 𝒳] [MeasurableSingletonClass 𝒳] {wt : (n : ℕ) → Hist Unit 𝒳 (𝒴 × ℝ) n → 𝒳 → ℝ}
  (hwt : ∀ n h, alg.policy n (h, ()) = weightedMeasure (wt n h))
  (hwt0 : ∀ n h x, 0 ≤ wt n h x) (hwt1 : ∀ n h, ∑ x, wt n h x = 1)
  (hwtm : ∀ n, Measurable (wt n))
  (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
include hwt hwt0 hwt1 hwtm h

/-- The nonnegative version of `integral_gameAction_eq_sum`. -/
private lemma integral_gameAction_eq_sum_of_nonneg (n : ℕ)
    {f : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 → ℝ} (hf : Measurable f) (hf0 : ∀ q, 0 ≤ f q) :
    ∫ ω, f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P
      = ∫ ω, ∑ x, wt n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x
          * f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, Y n ω) ∂P := by
  set H := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n with hH
  have hHm : Measurable H := h.measurable_history n
  have hYm : Measurable (Y n) := (h.measurable_feedback n).fst
  have key := h.lintegral_gameAction_eq_sum hwt hwt0 hwt1 hwtm n
    (f := fun q ↦ ENNReal.ofReal (f q)) (ENNReal.measurable_ofReal.comp hf)
  refine integral_eq_of_lintegral_ofReal_eq
    (hf.comp (hHm.prodMk ((h.measurable_action n).prodMk hYm))).aestronglyMeasurable ?_
    (ae_of_all _ fun ω ↦ hf0 _) (ae_of_all _ fun ω ↦ sum_nonneg fun x _ ↦
      mul_nonneg (hwt0 _ _ _) (hf0 _)) ?_
  · refine (Finset.measurable_sum _ fun x _ ↦ ?_).aestronglyMeasurable
    exact ((measurable_pi_apply x).comp ((hwtm n).comp hHm)).mul
      (hf.comp (hHm.prodMk (measurable_const.prodMk hYm)))
  · rw [key]
    refine lintegral_congr fun ω ↦ ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ ↦ mul_nonneg (hwt0 _ _ _) (hf0 _)]
    exact sum_congr rfl fun x _ ↦ (ENNReal.ofReal_mul (hwt0 _ _ _)).symm

/-- **Conditional law of the learner's action, signed version**: for a measurable `f` with
`f(H n, x, y_n)` almost surely bounded uniformly in `x`,
`E[f(H n, x_n, y_n)] = E[∑ x, wt n (H n) x f(H n, x, y_n)]`. -/
lemma _root_.Learning.IsAlgEnvSeq.integral_gameAction_eq_sum (n : ℕ)
    {f : Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴 → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ ω ∂P, ∀ x,
      |f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, Y n ω)| ≤ M) :
    ∫ ω, f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, X n ω, Y n ω) ∂P
      = ∫ ω, ∑ x, wt n (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x
          * f (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, x, Y n ω) ∂P := by
  set H := history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n with hH
  have hHm : Measurable H := h.measurable_history n
  have hYm : Measurable (Y n) := (h.measurable_feedback n).fst
  have hXm : Measurable (X n) := h.measurable_action n
  have hp := integral_gameAction_eq_sum_of_nonneg hwt hwt0 hwt1 hwtm h n
    (f := fun q ↦ max (f q) 0) (hf.max measurable_const) (fun q ↦ le_max_right _ _)
  have hn := integral_gameAction_eq_sum_of_nonneg hwt hwt0 hwt1 hwtm h n
    (f := fun q ↦ max (-f q) 0) (hf.neg.max measurable_const) (fun q ↦ le_max_right _ _)
  have hsplit (b : ℝ) : b = max b 0 - max (-b) 0 := by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hb, max_eq_right (by linarith)]
      ring
  have hbp (b : ℝ) : |max b 0| ≤ |b| := by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb, abs_zero]; exact abs_nonneg b
    · rw [max_eq_left hb]
  have hbn (b : ℝ) : |max (-b) 0| ≤ |b| := by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_left (by linarith), abs_neg]
    · rw [max_eq_right (by linarith), abs_zero]; exact abs_nonneg b
  have hint1 (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ b, |g b| ≤ |b|) :
      Integrable (fun ω ↦ g (f (H ω, X n ω, Y n ω))) P := by
    refine Integrable.of_ae_abs_le
      (hg.comp (hf.comp (hHm.prodMk (hXm.prodMk hYm)))).aestronglyMeasurable (M := M) ?_
    filter_upwards [hM] with ω hω
    exact (hgb _).trans (hω _)
  have hint2 (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ b, |g b| ≤ |b|) :
      Integrable (fun ω ↦ ∑ x, wt n (H ω) x * g (f (H ω, x, Y n ω))) P := by
    refine Integrable.of_ae_abs_le ?_ (M := M) ?_
    · refine (Finset.measurable_sum _ fun x _ ↦ ?_).aestronglyMeasurable
      exact ((measurable_pi_apply x).comp ((hwtm n).comp hHm)).mul
        (hg.comp (hf.comp (hHm.prodMk (measurable_const.prodMk hYm))))
    · filter_upwards [hM] with ω hω
      calc |∑ x, wt n (H ω) x * g (f (H ω, x, Y n ω))|
          ≤ ∑ x, |wt n (H ω) x * g (f (H ω, x, Y n ω))| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, wt n (H ω) x * M := sum_le_sum fun x _ ↦ by
            rw [abs_mul, abs_of_nonneg (hwt0 _ _ _)]
            exact mul_le_mul_of_nonneg_left ((hgb _).trans (hω x)) (hwt0 _ _ _)
        _ = M := by rw [← sum_mul, hwt1, one_mul]
  calc ∫ ω, f (H ω, X n ω, Y n ω) ∂P
      = ∫ ω, (max (f (H ω, X n ω, Y n ω)) 0 - max (-f (H ω, X n ω, Y n ω)) 0) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω ↦ hsplit _)
    _ = ∫ ω, max (f (H ω, X n ω, Y n ω)) 0 ∂P - ∫ ω, max (-f (H ω, X n ω, Y n ω)) 0 ∂P :=
        integral_sub (hint1 _ (measurable_id.max measurable_const) hbp)
          (hint1 _ (measurable_id.neg.max measurable_const) hbn)
    _ = ∫ ω, ∑ x, wt n (H ω) x * max (f (H ω, x, Y n ω)) 0 ∂P
          - ∫ ω, ∑ x, wt n (H ω) x * max (-f (H ω, x, Y n ω)) 0 ∂P := by rw [hp, hn]
    _ = ∫ ω, (∑ x, wt n (H ω) x * max (f (H ω, x, Y n ω)) 0
          - ∑ x, wt n (H ω) x * max (-f (H ω, x, Y n ω)) 0) ∂P :=
        (integral_sub (hint2 _ (measurable_id.max measurable_const) hbp)
          (hint2 _ (measurable_id.neg.max measurable_const) hbn)).symm
    _ = ∫ ω, ∑ x, wt n (H ω) x * f (H ω, x, Y n ω) ∂P := by
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        simp only
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun x _ ↦ by rw [← mul_sub, ← hsplit]

end Action

end Learning.RepeatedGame
