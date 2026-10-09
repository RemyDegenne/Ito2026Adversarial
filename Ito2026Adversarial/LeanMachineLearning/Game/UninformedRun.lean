/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.RepeatedGame
public import Ito2026Adversarial.Mathlib.MeasureTheory.Measure.Weighted

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
  `u x_n y_n` given the history and the actions of the round.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Learning.RepeatedGame

variable {𝒳 𝒴 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Player 𝒳 𝒴} {opp : Player 𝒴 𝒳}
  {R : RewardKernel 𝒳 𝒴} [∀ n, IsMarkovKernel (R n)]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴} {Rw : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- The integral of a function of `(Z, W)` is the integral of its integral against the
conditional law of `W` given `Z`. -/
private lemma lintegral_comp_of_hasCondDistrib {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {Z : Ω → α} {W : Ω → β} {κ : Kernel α β} [IsSFiniteKernel κ]
    [SFinite P] (h : HasCondDistrib W Z κ P) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (Z ω, W ω) ∂P = ∫⁻ ω, ∫⁻ b, f (Z ω, b) ∂κ (Z ω) ∂P := by
  rw [HasLaw.lintegral_comp h hf.aemeasurable, Measure.lintegral_compProd hf,
    lintegral_map' (hf.lintegral_kernel_prod_right').aemeasurable h.aemeasurable_fst]

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
  have h1 := lintegral_comp_of_hasCondDistrib (h.hasCondDistrib_feedback n) hF₁
  let F₂ : (Hist Unit 𝒳 (𝒴 × ℝ) n × Unit) × 𝒳 → ℝ≥0∞ :=
    fun a ↦ ∫⁻ b, F₁ (a, b) ∂((gameEnv opp R).feedback n a)
  have hF₂ : Measurable F₂ := hF₁.lintegral_kernel_prod_right'
  have h2 := lintegral_comp_of_hasCondDistrib (h.hasCondDistrib_action n) hF₂
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

/-- The integral against `weightedMeasure p` is the weighted sum `∑ x, p x * f x`. -/
lemma lintegral_weightedMeasure_eq_sum {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : ι → ℝ) (f : ι → ℝ≥0∞) :
    ∫⁻ x, f x ∂(weightedMeasure p) = ∑ x, ENNReal.ofReal (p x) * f x := by
  simp only [weightedMeasure, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]

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

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
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

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒳] in
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

end Learning.RepeatedGame
