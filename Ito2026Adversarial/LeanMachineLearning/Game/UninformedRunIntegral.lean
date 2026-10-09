/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.UninformedRun

/-!
# Signed expectations in the rounds of a repeated game

Integral (signed) versions of the conditional-expectation identities of
`Game/UninformedRun.lean`, for functions which are almost surely bounded along the run: in a
run of a learner drawing its action from weights `wt n (H n)` against an adaptive opponent with
reward kernel of conditional mean `u` and rewards in `[-1, 1]`,

* `Learning.IsAlgEnvSeq.integral_gameReward_mul`: `E[r_n k(H n, x_n, y_n)] = E[u x_n y_n k(H n,
  x_n, y_n)]`;
* `Learning.IsAlgEnvSeq.integral_gameAction_eq_sum`: `E[f(H n, x_n, y_n)] = E[∑ x, wt n (H n) x
  f(H n, x, y_n)]` (the conditional law of `x_n` given the history and `y_n` is `wt n (H n)`);
* `Learning.IsAlgEnvSeq.ae_forall_gameReward_mem`: almost surely all the rewards lie in `[-1, 1]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Learning.RepeatedGame

variable {𝒳 𝒴 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Player 𝒳 𝒴} {opp : Player 𝒴 𝒳}
  {R : RewardKernel 𝒳 𝒴} [∀ n, IsMarkovKernel (R n)]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴} {Rw : ℕ → Ω → ℝ}

/-- In a run of a repeated game, almost surely all the rewards lie in the set `s` of
`RewardKernel.RewardsIn R s`. -/
lemma _root_.Learning.IsAlgEnvSeq.ae_forall_gameReward_mem {s : Set ℝ} (hs : MeasurableSet s)
    (hR : R.RewardsIn s)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P) :
    ∀ᵐ ω ∂P, ∀ t, Rw t ω ∈ s :=
  ae_all_iff.2 fun t ↦ h.ae_gameReward_mem hs hR t

/-- An almost surely bounded, almost everywhere strongly measurable function is integrable. -/
lemma integrable_of_ae_abs_le {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {M : ℝ}
    (hM : ∀ᵐ ω ∂P, |f ω| ≤ M) : Integrable f P :=
  Integrable.of_bound hf M (by filter_upwards [hM] with ω hω; rwa [Real.norm_eq_abs])

omit [IsProbabilityMeasure P] in
/-- Two almost surely nonnegative functions with the same Lebesgue integral of `ofReal` have the
same integral. -/
lemma integral_eq_of_lintegral_ofReal_eq {f g : Ω → ℝ} (hfm : AEStronglyMeasurable f P)
    (hgm : AEStronglyMeasurable g P) (hf : 0 ≤ᵐ[P] f) (hg : 0 ≤ᵐ[P] g)
    (heq : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P) :
    ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
  rw [integral_eq_lintegral_of_nonneg_ae hf hfm, integral_eq_lintegral_of_nonneg_ae hg hgm, heq]

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
  have hKi : Integrable K P := integrable_of_ae_abs_le hKm.aestronglyMeasurable hKb
  have h1i : Integrable (fun ω ↦ (1 - Rw n ω) * K ω) P := by
    refine integrable_of_ae_abs_le ((measurable_const.sub hRwm).mul hKm).aestronglyMeasurable
      (M := 2 * M) ?_
    filter_upwards [hRae, hKb] with ω hω hKω
    rw [abs_mul]
    have : |1 - Rw n ω| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hω.1, hω.2]
    nlinarith [abs_nonneg (K ω), abs_nonneg (1 - Rw n ω)]
  have h2i : Integrable (fun ω ↦ (1 - u (X n ω) (Y n ω)) * K ω) P := by
    refine integrable_of_ae_abs_le ((measurable_const.sub hum).mul hKm).aestronglyMeasurable
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
    refine integrable_of_ae_abs_le (hv.mul (hg.comp hKm)).aestronglyMeasurable (M := M) ?_
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
    refine integrable_of_ae_abs_le
      (hg.comp (hf.comp (hHm.prodMk (hXm.prodMk hYm)))).aestronglyMeasurable (M := M) ?_
    filter_upwards [hM] with ω hω
    exact (hgb _).trans (hω _)
  have hint2 (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ b, |g b| ≤ |b|) :
      Integrable (fun ω ↦ ∑ x, wt n (H ω) x * g (f (H ω, x, Y n ω))) P := by
    refine integrable_of_ae_abs_le ?_ (M := M) ?_
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
