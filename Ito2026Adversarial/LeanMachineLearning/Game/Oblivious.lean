/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.RepeatedGame
public import Ito2026Adversarial.Mathlib.Probability.Distributions.TwoPoint

/-!
# Oblivious opponents in repeated games

An *oblivious* opponent plays `y_t ∼ q t` independently of the past rounds, for a fixed sequence
`q` of distributions on its actions (`Player.oblivious q`). Against such an opponent, with a reward
noise `ν : Kernel (𝒳 × 𝒴) ℝ` that does not depend on the past (`stationaryReward ν`), the opponent's
action of a round is independent of the past and of the learner's action, and an *uninformed*
learner (which sees only its actions and rewards) faces a non-stationary bandit: the reward of the
action `x` at round `t` has the law `obliviousBandit q ν t x`, the mixture over `y ∼ q t` of the
noise laws `ν (x, y)`.

For the two-point noise `twoPointNoise u` (reward `±1` with mean `u x y`), the mixture is the
two-point law of the mixed mean `∑ y, q t {y} u x y` (`obliviousBandit_twoPointNoise`).

## Main definitions

* `Player.oblivious q`: the opponent playing `y_t ∼ q t` independently of the past.
* `twoPointNoise u`: the noise model with reward `r ∼ twoPoint (u x y)`, on countable action sets.
* `obliviousBandit q ν t`: the reward kernel of round `t` of the non-stationary bandit faced by an
  uninformed learner against `Player.oblivious q` with noise `ν`.

## Main statements

* `IsAlgEnvSeq.hasCondDistrib_oblivious`, `IsAlgEnvSeq.hasLaw_oblivious`: against an oblivious
  opponent, `y_t ∼ q t` independently of the past and of `x_t`.
* `IsAlgEnvSeq.psmr_eq_sum_oblivious`: the PSMR against an oblivious opponent, on finite action
  sets, in terms of the laws of the learner's actions.
* `IsAlgEnvSeq.isAlgEnvSeq_banditSeq_oblivious`: the actions and rewards of an uninformed learner
  against an oblivious opponent form a run of the learner against the non-stationary bandit
  `Environment.banditSeq (obliviousBandit q ν)`.

## Tags

repeated game, oblivious adversary, non-stationary bandit
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Learning.RepeatedGame

variable {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

/-! ### Oblivious opponents and two-point noise -/

/-- The oblivious opponent which plays `y_t ∼ q t` at round `t`, independently of the past. -/
noncomputable def Player.oblivious (q : ℕ → Measure 𝒴) [∀ n, IsProbabilityMeasure (q n)] :
    Player 𝒴 𝒳 where
  policy n := Kernel.const _ (q n)

/-- The policy of the oblivious opponent at round `n` is the constant kernel `q n`. -/
@[simp]
lemma Player.policy_oblivious (q : ℕ → Measure 𝒴) [∀ n, IsProbabilityMeasure (q n)] (n : ℕ) :
    (Player.oblivious (𝒳 := 𝒳) q).policy n = Kernel.const _ (q n) := rfl

section TwoPoint

variable [Countable 𝒳] [Countable 𝒴] [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒴]

/-- The two-point noise model: the reward of the action pair `(x, y)` is `±1` with mean `u x y`,
with law `twoPoint (u x y)`. -/
noncomputable def twoPointNoise (u : 𝒳 → 𝒴 → ℝ) : Kernel (𝒳 × 𝒴) ℝ :=
  Kernel.ofFunOfCountable fun p ↦ twoPoint (u p.1 p.2)

/-- The law of the reward of the pair `(x, y)` under the two-point noise. -/
@[simp]
lemma twoPointNoise_apply (u : 𝒳 → 𝒴 → ℝ) (p : 𝒳 × 𝒴) :
    twoPointNoise u p = twoPoint (u p.1 p.2) := rfl

instance (u : 𝒳 → 𝒴 → ℝ) : IsMarkovKernel (twoPointNoise u) :=
  ⟨fun p ↦ by rw [twoPointNoise_apply]; infer_instance⟩

/-- The two-point noise has conditional mean `u`. -/
lemma hasMean_stationaryReward_twoPointNoise {u : 𝒳 → 𝒴 → ℝ}
    (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) :
    (stationaryReward (twoPointNoise u)).HasMean u := by
  intro n h x y
  simp [stationaryReward, Kernel.comap_apply, integral_twoPoint (hu x y)]

/-- The rewards of the two-point noise lie in `[-1, 1]`. -/
lemma rewardsIn_stationaryReward_twoPointNoise (u : 𝒳 → 𝒴 → ℝ) :
    (stationaryReward (twoPointNoise u)).RewardsIn (Set.Icc (-1) 1) := by
  intro n h x y
  simpa [stationaryReward, Kernel.comap_apply] using ae_mem_Icc_twoPoint (u x y)

end TwoPoint

/-- The reward kernel of round `t` of the non-stationary bandit faced by an uninformed learner
against the oblivious opponent `Player.oblivious q` with reward noise `ν`: the reward of the action
`x` has the law of the mixture of `ν (x, y)` over `y ∼ q t`. -/
noncomputable def obliviousBandit (q : ℕ → Measure 𝒴) (ν : Kernel (𝒳 × 𝒴) ℝ) (t : ℕ) :
    Kernel 𝒳 ℝ :=
  (Kernel.const 𝒳 (q t) ⊗ₖ ν).snd

variable {q : ℕ → Measure 𝒴} [∀ n, IsProbabilityMeasure (q n)] {ν : Kernel (𝒳 × 𝒴) ℝ}
  [IsMarkovKernel ν]

instance (t : ℕ) : IsMarkovKernel (obliviousBandit q ν t) := by
  unfold obliviousBandit; infer_instance

/-- The probability of a set under the mixture `obliviousBandit q ν t x`. -/
lemma obliviousBandit_apply (t : ℕ) (x : 𝒳) {s : Set ℝ} (hs : MeasurableSet s) :
    obliviousBandit q ν t x s = ∫⁻ y, ν (x, y) s ∂(q t) := by
  rw [obliviousBandit, Kernel.snd_apply' _ _ hs, Kernel.compProd_apply (measurable_snd hs),
    Kernel.const_apply]
  rfl

/-- Against an oblivious opponent with two-point noise, the reward of the action `x` at round `t`
has the two-point law of the mixed mean `∑ y, q t {y} u x y`. -/
lemma obliviousBandit_twoPointNoise [Fintype 𝒴] [Countable 𝒳] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {u : 𝒳 → 𝒴 → ℝ} (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1)
    (t : ℕ) (x : 𝒳) :
    obliviousBandit q (twoPointNoise u) t x = twoPoint (∑ y, (q t).real {y} * u x y) := by
  rw [← sum_smul_twoPoint (fun _ _ ↦ measureReal_nonneg) (by simp) fun y _ ↦ hu x y]
  ext s hs
  rw [obliviousBandit_apply t x hs, lintegral_fintype, Measure.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, ofReal_measureReal, twoPointNoise_apply, mul_comm]

end Learning.RepeatedGame

/-! ### Runs against an oblivious opponent -/

namespace Learning

open RepeatedGame

variable {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
  {q : ℕ → Measure 𝒴} [∀ n, IsProbabilityMeasure (q n)] {ν : Kernel (𝒳 × 𝒴) ℝ} [IsMarkovKernel ν]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴} {Rw : ℕ → Ω → ℝ}

/-- Against an oblivious opponent, the opponent's action of round `n` has the law `q n` given the
past rounds and the learner's action of round `n`. -/
lemma IsAlgEnvSeq.hasCondDistrib_oblivious {pl : Player 𝒳 𝒴} {R : RewardKernel 𝒳 𝒴}
    [∀ n, IsMarkovKernel (R n)]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) pl
      (gameEnv (Player.oblivious q) R) P) (n : ℕ) :
    HasCondDistrib (Y n)
      (fun ω ↦ ((history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω, ()), X n ω))
      (Kernel.const _ (q n)) P := by
  have h_fst := (h.hasCondDistrib_feedback n).fst
  rwa [gameEnv, Kernel.fst_compProd, Player.policy_oblivious, Kernel.comap_const] at h_fst

/-- Against an oblivious opponent, the opponent's action of round `n` has the law `q n`,
independently of the learner's action. -/
lemma IsAlgEnvSeq.hasLaw_oblivious {pl : Player 𝒳 𝒴} {R : RewardKernel 𝒳 𝒴}
    [∀ n, IsMarkovKernel (R n)]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) pl
      (gameEnv (Player.oblivious q) R) P) (n : ℕ) :
    HasLaw (fun ω ↦ (X n ω, Y n ω)) ((P.map (X n)).prod (q n)) P := by
  have h' : HasCondDistrib (Y n) (X n) (Kernel.const _ (q n)) P :=
    HasCondDistrib.comp_right (f := Prod.snd) (hf := measurable_snd)
      (by rw [Kernel.comap_const]; exact h.hasCondDistrib_oblivious n)
  rw [HasCondDistrib, Measure.compProd_const] at h'
  exact h'

/-- Against an oblivious opponent, the expectation of a function of the two actions of round `n`
is the expectation over `x_n` (with its law under `P`) and `y ∼ q n` independently. -/
lemma IsAlgEnvSeq.integral_oblivious [Fintype 𝒳] [Fintype 𝒴] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {pl : Player 𝒳 𝒴} {R : RewardKernel 𝒳 𝒴}
    [∀ n, IsMarkovKernel (R n)]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) pl
      (gameEnv (Player.oblivious q) R) P) (n : ℕ) (g : 𝒳 → 𝒴 → ℝ) :
    ∫ ω, g (X n ω) (Y n ω) ∂P = ∑ x, P.real (X n ⁻¹' {x}) * ∑ y, (q n).real {y} * g x y := by
  have h_int := (h.hasLaw_oblivious n).integral_comp (f := fun p ↦ g p.1 p.2)
    (measurable_of_finite _).aestronglyMeasurable
  refine h_int.trans ?_
  rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← Set.singleton_prod_singleton, measureReal_prod_prod,
    map_measureReal_apply (h.measurable_action n) (measurableSet_singleton x), smul_eq_mul]
  ring

/-- The pure-strategy maximin regret against an oblivious opponent, in terms of the laws of the
learner's actions. -/
lemma IsAlgEnvSeq.psmr_eq_sum_oblivious [Fintype 𝒳] [Fintype 𝒴] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass 𝒴] {pl : Player 𝒳 𝒴} {R : RewardKernel 𝒳 𝒴}
    [∀ n, IsMarkovKernel (R n)]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) pl
      (gameEnv (Player.oblivious q) R) P) (u : 𝒳 → 𝒴 → ℝ) (T : ℕ) :
    psmr u X Y P T = ∑ t ∈ range T,
      ∑ x, P.real (X t ⁻¹' {x}) * ∑ y, (q t).real {y} * (ZeroSumGame.pureMaximin u - u x y) := by
  simp only [psmr]
  rw [integral_finsetSum _ fun t _ ↦ ?_]
  · exact Finset.sum_congr rfl fun t _ ↦
      h.integral_oblivious t fun x y ↦ ZeroSumGame.pureMaximin u - u x y
  · exact (h.hasLaw_oblivious t).integrable_comp
      (f := fun p ↦ ZeroSumGame.pureMaximin u - u p.1 p.2) Integrable.of_finite

/-- **Observations of an uninformed learner against an oblivious opponent.** In a run of an
uninformed learner against the oblivious opponent `Player.oblivious q` with a reward noise `ν` that
does not depend on the past, the actions and rewards of the learner form a run of the learner
against the non-stationary bandit `Environment.banditSeq (obliviousBandit q ν)`. -/
lemma IsAlgEnvSeq.isAlgEnvSeq_banditSeq_oblivious {alg : Algorithm Unit 𝒳 ℝ}
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) (Player.ofUninformed alg)
      (gameEnv (Player.oblivious q) (stationaryReward ν)) P) :
    IsAlgEnvSeq (fun _ _ ↦ ()) X Rw alg (Environment.banditSeq (obliviousBandit q ν)) P where
  measurable_obs _ := measurable_const
  measurable_action := h.measurable_action
  measurable_feedback n := (h.measurable_feedback n).snd
  hasCondDistrib_obs n := hasCondDistrib_unit
    (Learning.measurable_history (fun _ ↦ measurable_const) h.measurable_action
      (fun n ↦ (h.measurable_feedback n).snd) n).aemeasurable _ _
  hasCondDistrib_action n := h.hasCondDistrib_action_comapFeedback n
  hasCondDistrib_feedback n := by
    have h_snd := (h.hasCondDistrib_feedback n).snd
    have h_eq : ((gameEnv (Player.oblivious q) (stationaryReward ν)).feedback n).snd
        = (obliviousBandit q ν n).comap Prod.snd measurable_snd := by
      ext p s hs
      rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply, obliviousBandit_apply _ _ hs, gameEnv,
        Kernel.compProd_apply (measurable_snd hs)]
      rfl
    rw [h_eq] at h_snd
    exact HasCondDistrib.comp_right (κ := (obliviousBandit q ν n).prodMkLeft _)
      (f := fun p : (Hist Unit 𝒳 (𝒴 × ℝ) n × Unit) × 𝒳 ↦
        ((Hist.mapFeedback Prod.snd p.1.1, p.1.2), p.2)) (hf := by fun_prop) h_snd

end Learning
