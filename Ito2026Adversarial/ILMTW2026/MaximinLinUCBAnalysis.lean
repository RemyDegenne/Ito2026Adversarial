/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Lemma13
public import Ito2026Adversarial.LeanMachineLearning.EllipticalPotential
public import Ito2026Adversarial.LeanMachineLearning.Game.Optimism
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.Linear.Optimism

/-!
# Analysis of Maximin-LinUCB

The steps of the proof of Theorem 12.

* Bilinear games: `bilinearGame_eq_inner` (`u x y = ⟪vec(x yᵀ), vec(A)⟫`),
  `IsBilinearGame.bilinearGame_mem_Icc` (utilities in `[-1, 1]`),
  `IsBilinearGame.norm_pairFeature_le` (`‖vec(x yᵀ)‖ ≤ 1`).
* The radii: `linRadius_mono`, `one_le_linRadius`, `linRadius_sq_le`
  (`β_T² ≤ 12 d log T` for `λ = 1`, `δ = 1 / T`).
* `linGoodEvent`: the event of Lemma 13, which fails with probability at most `δ`
  (`measureReal_compl_linGoodEvent_le`).
* `linState_fst`: the matrix of the ridge state is the regularized Gram matrix of the features
  `a_t = vec(x_t y_tᵀ)` of the run.
* `pureMaximin_sub_le_of_mem_linGoodEvent`: on the good event, for the run of Maximin-LinUCB of
  Theorem 12, `v* - u(x_t, y_t) ≤ 2 β_T √(min(1, ‖a_t‖²_{V_t⁻¹}))` for `t < T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame Matrix

open scoped RealInnerProductSpace

namespace Ito2026Adversarial

/-! ### Bilinear games -/

section Bilinear

variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

/-- If `‖A y‖ ≤ ‖y‖` for all `y`, then `|⟪x, A y⟫| ≤ ‖x‖ ‖y‖`. -/
lemma abs_bilinearUtility_le {A : Matrix ιx ιy ℝ}
    (hA : ∀ y : EuclideanSpace ℝ ιy,
      ‖(WithLp.toLp 2 (A *ᵥ WithLp.ofLp y) : EuclideanSpace ℝ ιx)‖ ≤ ‖y‖)
    (x : EuclideanSpace ℝ ιx) (y : EuclideanSpace ℝ ιy) :
    |bilinearUtility A x y| ≤ ‖x‖ * ‖y‖ := by
  have : bilinearUtility A x y
      = ⟪(WithLp.toLp 2 (A *ᵥ WithLp.ofLp y) : EuclideanSpace ℝ ιx), x⟫ := by
    rw [bilinearUtility, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  rw [this]
  exact (abs_real_inner_le_norm _ _).trans (by rw [mul_comm]; gcongr; exact hA y)

variable {𝒳 𝒴 : Type*} {φ : 𝒳 → EuclideanSpace ℝ ιx} {ψ : 𝒴 → EuclideanSpace ℝ ιy}
  {A : Matrix ιx ιy ℝ}

/-- The utility of a bilinear game is `u(x, y) = ⟪vec(x yᵀ), vec(A)⟫`. -/
lemma bilinearGame_eq_inner (φ : 𝒳 → EuclideanSpace ℝ ιx) (ψ : 𝒴 → EuclideanSpace ℝ ιy)
    (A : Matrix ιx ιy ℝ) (x : 𝒳) (y : 𝒴) :
    bilinearGame φ ψ A x y = ⟪pairFeature (φ x) (ψ y), vecMatrix A⟫ :=
  (inner_pairFeature_vecMatrix A (φ x) (ψ y)).symm

/-- The utilities of a bilinear game lie in `[-1, 1]`. -/
lemma IsBilinearGame.bilinearGame_mem_Icc (hA : IsBilinearGame φ ψ A) (x : 𝒳) (y : 𝒴) :
    bilinearGame φ ψ A x y ∈ Set.Icc (-1) 1 := by
  have h1 : ‖φ x‖ * ‖ψ y‖ ≤ 1 := by
    have := hA.norm_le_x x
    have := hA.norm_le_y y
    nlinarith [norm_nonneg (φ x), norm_nonneg (ψ y)]
  have h := (abs_bilinearUtility_le hA.opNorm_le (φ x) (ψ y)).trans h1
  exact ⟨(abs_le.1 h).1, (abs_le.1 h).2⟩

/-- The features `vec(x yᵀ)` of the action pairs of a bilinear game have norm at most `1`. -/
lemma IsBilinearGame.norm_pairFeature_le (hA : IsBilinearGame φ ψ A) (x : 𝒳) (y : 𝒴) :
    ‖pairFeature (φ x) (ψ y)‖ ≤ 1 := by
  rw [norm_pairFeature]
  have := hA.norm_le_x x
  have := hA.norm_le_y y
  nlinarith [norm_nonneg (φ x), norm_nonneg (ψ y)]

omit [Fintype ιx] [Fintype ιy] in
/-- A bilinear game in dimension `0` is the zero game. -/
lemma bilinearGame_eq_zero [Fintype ιx] [Fintype ιy] [IsEmpty (ιx × ιy)] (x : 𝒳) (y : 𝒴) :
    bilinearGame φ ψ A x y = 0 := by
  rw [bilinearGame_eq_inner, Subsingleton.elim (pairFeature (φ x) (ψ y)) 0, inner_zero_left]

end Bilinear

/-! ### The radii of Maximin-LinUCB -/

section Radius

/-- The radius `β_t` is nondecreasing in `t`. -/
lemma linRadius_mono (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (δ : ℝ) : Monotone (linRadius d lam δ) := by
  intro t t' htt'
  unfold linRadius
  have ht : (t : ℝ) ≤ t' := by exact_mod_cast htt'
  have hdl : 0 ≤ (d : ℝ) * lam := mul_nonneg (Nat.cast_nonneg d) hlam
  have h1 : (t : ℝ) / (d * lam) ≤ t' / (d * lam) := div_le_div_of_nonneg_right ht hdl
  have h2 : log (1 + t / (d * lam)) ≤ log (1 + t' / (d * lam)) :=
    log_le_log (by have := div_nonneg (Nat.cast_nonneg t) hdl; linarith) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) d)
  exact add_le_add_right (sqrt_le_sqrt (by linarith)) _

/-- For `d ≥ 1` and `λ = 1`, the radius `β_t ≥ √d` is at least `1`. -/
lemma one_le_linRadius {d : ℕ} (hd : 1 ≤ d) (δ : ℝ) (t : ℕ) : 1 ≤ linRadius d 1 δ t := by
  unfold linRadius
  have : (1 : ℝ) ≤ √(1 * d) := by
    rw [one_mul, one_le_sqrt]
    exact_mod_cast hd
  linarith [sqrt_nonneg (((2 : ℕ) : ℝ) * log (1 / δ) + d * log (1 + t / (d * 1)))]

/-- `log(1 + T / d) ≤ 2 log T` for `d ≥ 1`, `T ≥ 2`. -/
lemma log_one_add_div_le {d T : ℕ} (hd : 1 ≤ d) (hT : 2 ≤ T) :
    log (1 + T / (d * 1)) ≤ 2 * log T := by
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : 2 * log (T : ℝ) = log ((T : ℝ) ^ 2) := by rw [log_pow]; norm_num
  rw [h2]
  refine log_le_log (by positivity) ?_
  rw [mul_one]
  calc 1 + (T : ℝ) / d ≤ 1 + T := by gcongr; exact div_le_self (by positivity) hd0
    _ ≤ (T : ℝ) ^ 2 := by nlinarith

/-- `β_T² ≤ 12 d log T` for the radius of Theorem 12 (`λ = 1`, `δ = 1 / T`), `d ≥ 1`, `T ≥ 2`. -/
lemma linRadius_sq_le {d T : ℕ} (hd : 1 ≤ d) (hT : 2 ≤ T) :
    linRadius d 1 (1 / T) T ^ 2 ≤ 12 * d * log T := by
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogT : 1 / 2 ≤ log (T : ℝ) := by
    have h2 : 1 - (2 : ℝ)⁻¹ ≤ log 2 := one_sub_inv_le_log_of_pos (by norm_num)
    have := log_le_log (by norm_num) hT0
    linarith
  have hlog := log_one_add_div_le hd hT
  have hlog0 : 0 ≤ log (1 + (T : ℝ) / (d * 1)) := log_nonneg (by
    have : (0 : ℝ) ≤ T / (d * 1) := by positivity
    linarith)
  unfold linRadius
  rw [one_div_one_div, one_mul, Nat.cast_ofNat]
  set a := 2 * log (T : ℝ) + d * log (1 + T / (d * 1)) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha4 : a ≤ 4 * d * log T := by
    have : 2 * log (T : ℝ) ≤ 2 * d * log T := by nlinarith
    have : d * log (1 + (T : ℝ) / (d * 1)) ≤ d * (2 * log T) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have h1 : √(d : ℝ) ^ 2 = d := sq_sqrt (by positivity)
  have h2 : √a ^ 2 = a := sq_sqrt ha0
  nlinarith [sq_nonneg (√(d : ℝ) - √a)]

end Radius

/-! ### The good event and the ridge state -/

section GoodEvent

variable {mx my dx dy : ℕ} {φ : Fin mx → EuclideanSpace ℝ (Fin dx)}
  {ψ : Fin my → EuclideanSpace ℝ (Fin dy)} {A : Matrix (Fin dx) (Fin dy) ℝ} {Ω : Type*}
  {X : ℕ → Ω → Fin mx} {Y : ℕ → Ω → Fin my} {Rw : ℕ → Ω → ℝ}

/-- The matrix of the ridge state after `t` rounds of a run is the regularized Gram matrix of the
features `a_s = vec(x_s y_sᵀ)` of the run. -/
lemma linState_fst (lam : ℝ) (t : ℕ) (ω : Ω) :
    (linState φ ψ lam X Y Rw t ω).1
      = regGram lam (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t := by
  have h := Bandits.Linear.stateProcess_ridgeUpdate lam
    (fun r : Round Unit (Fin mx) (Fin my × ℝ) ↦ pairFeature (φ r.action) (ψ r.feedback.1))
    (fun r ↦ r.feedback.2) (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω
  exact congrArg Prod.fst h

variable (φ ψ A) in
/-- The good event of Maximin-LinUCB: the confidence ellipsoids of Lemma 13 contain `vec(A)` at
all times. -/
def linGoodEvent (lam δ : ℝ) (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my) (Rw : ℕ → Ω → ℝ) :
    Set Ω :=
  {ω | ∀ t, √(mahalanobisSq (linState φ ψ lam X Y Rw t ω).1
      (vecMatrix A - Bandits.Linear.ridgeEstimate (linState φ ψ lam X Y Rw t ω))) ≤
    linRadius (dx * dy) lam δ t}

/-- The good event of Maximin-LinUCB is measurable. -/
lemma measurableSet_linGoodEvent [MeasurableSpace Ω] (lam δ : ℝ) (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) (hR : ∀ n, Measurable (Rw n)) :
    MeasurableSet (linGoodEvent φ ψ A lam δ X Y Rw) := by
  have hs (t : ℕ) : Measurable (linState φ ψ lam X Y Rw t) :=
    measurable_stateProcess (by fun_prop) _ (fun _ ↦ measurable_const) hX
      (fun n ↦ (hY n).prodMk (hR n)) t
  refine measurableSet_setOfPred.2 (Measurable.forall fun t ↦ ?_)
  have := hs t
  exact measurableSet_setOfPred.1 (measurableSet_le (by fun_prop) measurable_const)

/-- The good event of Maximin-LinUCB fails with probability at most `δ` (Lemma 13). -/
lemma measureReal_compl_linGoodEvent_le [NeZero mx] [NeZero my] (hA : IsBilinearGame φ ψ A)
    (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
    [∀ n, IsMarkovKernel (R n)] (hR : RewardKernel.HasMean R (bilinearGame φ ψ A))
    (hR' : RewardKernel.RewardsIn R (Set.Icc (-1) 1)) (alg : Player (Fin mx) (Fin my))
    {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : δ ∈ Set.Ioo 0 1) :
    P.real (linGoodEvent φ ψ A lam δ X Y Rw)ᶜ ≤ δ := by
  have hX := h.measurable_action
  have hY (n : ℕ) : Measurable (Y n) := (h.measurable_feedback n).fst
  have hRw (n : ℕ) : Measurable (Rw n) := (h.measurable_feedback n).snd
  rw [measureReal_compl (measurableSet_linGoodEvent lam δ hX hY hRw), probReal_univ]
  have := probReal_forall_sqrt_mahalanobisSq_le_ge φ ψ A hA opp R hR hR' alg P X Y Rw h hlam hδ
  unfold linGoodEvent
  linarith

/-- **One round of Maximin-LinUCB.** On the good event, at a round `t < T` of the run of
Maximin-LinUCB of Theorem 12 (whose action maximizes `x ↦ min_y U_t(x, y)`),
`v* - u(x_t, y_t) ≤ 2 β_T √(min(1, ‖a_t‖²_{V_t⁻¹}))`: optimism `v* ≤ U_t(x_t, y_t)`, the bound
`U_t(x_t, y_t) ≤ u(x_t, y_t) + 2 β_{t+1} ‖a_t‖_{V_t⁻¹}` and `v* - u ≤ 2 ≤ 2 β_T`. -/
lemma pureMaximin_sub_le_of_mem_linGoodEvent [NeZero mx] [NeZero my]
    (hA : IsBilinearGame φ ψ A) {T : ℕ}
    (hd : 1 ≤ dx * dy) {ω : Ω} (hω : ω ∈ linGoodEvent φ ψ A 1 (1 / T) X Y Rw) {t : ℕ}
    (ht : t < T)
    (hmax : ∀ x, (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (t + 1))
          (linState φ ψ 1 X Y Rw t ω) (φ x) (ψ y)).min
        ≤ (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (t + 1))
          (linState φ ψ 1 X Y Rw t ω) (φ (X t ω)) (ψ y)).min) :
    pureMaximin (bilinearGame φ ψ A) - bilinearGame φ ψ A (X t ω) (Y t ω)
      ≤ 2 * linRadius (dx * dy) 1 (1 / T) T * √(min 1 (mahalanobisSq
        (regGram 1 (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t)⁻¹
        (pairFeature (φ (X t ω)) (ψ (Y t ω))))) := by
  set S := linState φ ψ 1 X Y Rw t ω with hS
  set β := linRadius (dx * dy) 1 (1 / T) (t + 1) with hβ_def
  set B := linRadius (dx * dy) 1 (1 / T) T with hB_def
  have hS1 : S.1 = regGram 1 (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t := linState_fst 1 t ω
  have hV : S.1.PosDef := hS1 ▸ posDef_regGram one_pos _ t
  have hθ : √(mahalanobisSq S.1 (vecMatrix A - Bandits.Linear.ridgeEstimate S))
      ≤ linRadius (dx * dy) 1 (1 / T) t := hω t
  have hβ : linRadius (dx * dy) 1 (1 / T) t ≤ β := linRadius_mono _ zero_le_one _ (Nat.le_succ t)
  have hβB : β ≤ B := linRadius_mono _ zero_le_one _ ht
  have hB1 : 1 ≤ B := one_le_linRadius hd _ _
  have hU (x : Fin mx) (y : Fin my) :
      bilinearGame φ ψ A x y ≤ linIndex β S (φ x) (ψ y) := by
    rw [bilinearGame_eq_inner]
    exact Bandits.Linear.inner_le_ucbIndex hV hθ hβ _
  have hopt := pureMaximin_le_of_le hU hmax (Y t ω)
  have hup := Bandits.Linear.ucbIndex_le_inner_add hV hθ hβ
    (pairFeature (φ (X t ω)) (ψ (Y t ω)))
  rw [← bilinearGame_eq_inner, hS1] at hup
  have h2 : pureMaximin (bilinearGame φ ψ A) - bilinearGame φ ψ A (X t ω) (Y t ω) ≤ 2 :=
    pairGap_le_two hA.bilinearGame_mem_Icc _ _
  set w := mahalanobisSq (regGram 1 (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t)⁻¹
    (pairFeature (φ (X t ω)) (ψ (Y t ω))) with hw
  have hw0 : 0 ≤ w := mahalanobisSq_inv_regGram_nonneg one_pos _ t _
  change linIndex β S (φ (X t ω)) (ψ (Y t ω)) ≤ _ at hup
  rcases le_total w 1 with hw1 | hw1
  · rw [min_eq_right hw1]
    have : β * √w ≤ B * √w := mul_le_mul_of_nonneg_right hβB (sqrt_nonneg _)
    linarith
  · rw [min_eq_left hw1, sqrt_one]
    linarith

/-- **Elliptical potential of the run.** For `d = d_x d_y ≥ 1` and `T ≥ 2`,
`∑_{t < T} min(1, ‖a_t‖²_{V_t⁻¹}) ≤ 4 d log T`. -/
lemma sum_min_one_mahalanobisSq_le (hA : IsBilinearGame φ ψ A) {T : ℕ} (hT : 2 ≤ T)
    (hd : 1 ≤ dx * dy) (ω : Ω) :
    ∑ t ∈ range T, min 1 (mahalanobisSq
        (regGram 1 (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t)⁻¹
        (pairFeature (φ (X t ω)) (ψ (Y t ω))))
      ≤ 4 * (dx * dy : ℕ) * log T := by
  refine (sum_min_one_mahalanobisSq_inv_regGram_le_card_mul_log one_pos
    (L := 1) fun t _ ↦ hA.norm_pairFeature_le _ _).trans ?_
  have hcard : Fintype.card (Fin dx × Fin dy) = dx * dy := by simp
  rw [hcard, one_pow, one_mul]
  have := log_one_add_div_le hd hT
  have hd0 : (0 : ℝ) ≤ (dx * dy : ℕ) := Nat.cast_nonneg _
  nlinarith

/-- **Worst-case pathwise bound for Maximin-LinUCB.** On the good event, in the run of
Maximin-LinUCB of Theorem 12, the regret of the first `T` rounds is at most
`2 β_T √T √(4 d log T)` (Cauchy–Schwarz and the elliptical potential). -/
lemma sum_pureMaximin_sub_le_of_mem_linGoodEvent [NeZero mx] [NeZero my]
    (hA : IsBilinearGame φ ψ A) {T : ℕ} (hT : 2 ≤ T) (hd : 1 ≤ dx * dy) {ω : Ω}
    (hω : ω ∈ linGoodEvent φ ψ A 1 (1 / T) X Y Rw)
    (hmax : ∀ n < T, ∀ x, (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ x) (ψ y)).min
        ≤ (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ (X n ω)) (ψ y)).min) :
    ∑ t ∈ range T, (pureMaximin (bilinearGame φ ψ A) - bilinearGame φ ψ A (X t ω) (Y t ω))
      ≤ 2 * linRadius (dx * dy) 1 (1 / T) T * (√T * √(4 * (dx * dy : ℕ) * log T)) := by
  set w : ℕ → ℝ := fun t ↦ min 1 (mahalanobisSq
    (regGram 1 (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t)⁻¹
    (pairFeature (φ (X t ω)) (ψ (Y t ω)))) with hw
  have hw0 (t : ℕ) : 0 ≤ w t :=
    le_min zero_le_one (mahalanobisSq_inv_regGram_nonneg one_pos _ t _)
  have hCS : ∑ t ∈ range T, √(w t) ≤ √T * √(∑ t ∈ range T, w t) := by
    have := Real.sum_sqrt_mul_sqrt_le (range T) (f := fun _ ↦ (1 : ℝ)) (g := w)
      (fun _ ↦ zero_le_one) hw0
    simpa using this
  have hB0 : 0 ≤ linRadius (dx * dy) 1 (1 / T) T := zero_le_one.trans (one_le_linRadius hd _ _)
  calc ∑ t ∈ range T, (pureMaximin (bilinearGame φ ψ A) - bilinearGame φ ψ A (X t ω) (Y t ω))
      ≤ ∑ t ∈ range T, 2 * linRadius (dx * dy) 1 (1 / T) T * √(w t) :=
        sum_le_sum fun t ht ↦ pureMaximin_sub_le_of_mem_linGoodEvent hA hd hω
          (mem_range.1 ht) (hmax t (mem_range.1 ht))
    _ = 2 * linRadius (dx * dy) 1 (1 / T) T * ∑ t ∈ range T, √(w t) := by rw [mul_sum]
    _ ≤ 2 * linRadius (dx * dy) 1 (1 / T) T * (√T * √(4 * (dx * dy : ℕ) * log T)) := by
        gcongr
        exact hCS.trans (by gcongr; exact sum_min_one_mahalanobisSq_le hA hT hd ω)

/-- If `r ≤ 0` or `Δ ≤ r`, and `r ≤ b`, then `r ≤ b² / Δ`. -/
lemma le_sq_div_of_le {r b Δ : ℝ} (hΔ : 0 < Δ) (hr : r ≤ 0 ∨ Δ ≤ r) (hrb : r ≤ b) :
    r ≤ b ^ 2 / Δ := by
  rcases hr with hr | hr
  · exact hr.trans (by positivity)
  · rw [le_div_iff₀ hΔ]
    nlinarith

/-- **Instance-dependent pathwise bound for Maximin-LinUCB.** On the good event, in the run of
Maximin-LinUCB of Theorem 12, for a gap threshold `Δ > 0`, the regret of the first `T` rounds is
at most `4 β_T² (4 d log T) / Δ`: `v* - u ≤ (v* - u)² / Δ` off `(0, Δ)`. -/
lemma sum_pureMaximin_sub_le_div_of_mem_linGoodEvent [NeZero mx] [NeZero my]
    (hA : IsBilinearGame φ ψ A) {T : ℕ} (hT : 2 ≤ T) (hd : 1 ≤ dx * dy) {ω : Ω}
    (hω : ω ∈ linGoodEvent φ ψ A 1 (1 / T) X Y Rw)
    (hmax : ∀ n < T, ∀ x, (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ x) (ψ y)).min
        ≤ (fun y ↦ linIndex (linRadius (dx * dy) 1 (1 / T) (n + 1))
          (linState φ ψ 1 X Y Rw n ω) (φ (X n ω)) (ψ y)).min)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : IsGapThreshold (bilinearGame φ ψ A) Δ) :
    ∑ t ∈ range T, (pureMaximin (bilinearGame φ ψ A) - bilinearGame φ ψ A (X t ω) (Y t ω))
      ≤ 4 * linRadius (dx * dy) 1 (1 / T) T ^ 2 * (4 * (dx * dy : ℕ) * log T) / Δ := by
  set w : ℕ → ℝ := fun t ↦ min 1 (mahalanobisSq
    (regGram 1 (fun s ↦ pairFeature (φ (X s ω)) (ψ (Y s ω))) t)⁻¹
    (pairFeature (φ (X t ω)) (ψ (Y t ω)))) with hw
  have hw0 (t : ℕ) : 0 ≤ w t :=
    le_min zero_le_one (mahalanobisSq_inv_regGram_nonneg one_pos _ t _)
  set B := linRadius (dx * dy) 1 (1 / T) T with hB
  calc ∑ t ∈ range T, (pureMaximin (bilinearGame φ ψ A) - bilinearGame φ ψ A (X t ω) (Y t ω))
      ≤ ∑ t ∈ range T, (2 * B * √(w t)) ^ 2 / Δ :=
        sum_le_sum fun t ht ↦ le_sq_div_of_le hΔ (hgap _ _)
          (pureMaximin_sub_le_of_mem_linGoodEvent hA hd hω (mem_range.1 ht)
            (hmax t (mem_range.1 ht)))
    _ = 4 * B ^ 2 * (∑ t ∈ range T, w t) / Δ := by
        rw [mul_sum, sum_div]
        refine sum_congr rfl fun t _ ↦ ?_
        rw [mul_pow, mul_pow, sq_sqrt (hw0 t)]
        ring
    _ ≤ 4 * B ^ 2 * (4 * (dx * dy : ℕ) * log T) / Δ := by
        gcongr
        exact sum_min_one_mahalanobisSq_le hA hT hd ω

end GoodEvent

end Ito2026Adversarial
