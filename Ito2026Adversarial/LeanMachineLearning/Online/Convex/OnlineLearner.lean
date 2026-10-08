/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.Algorithms.Stateful
public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.ObliviousEnv

/-!
# Deterministic online learners

A deterministic online learning algorithm with internal state `σ` plays, at each round, an
action `play s x` computed from its state `s` and the side information `x` available before
playing, and then updates its state to `update s y` from the feedback `y` it receives (a loss
vector, a loss function, a sample, ...). `OnlineLearner σ 𝓧 𝓨 𝒜` bundles the initial state, the
play and update maps and their measurability, so that learners can be used as components of
measurable sequential algorithms.

## Main definitions

* `L.state y t`: the state before round `t`, after the feedbacks `y 0, …, y (t - 1)`;
* `L.iterate x y t = L.play (L.state y t) (x t)`: the action played at round `t`;
* `L.toAlgorithm : Algorithm 𝓧 𝒜 𝓨`: the learner as an algorithm of the LML framework, the
  deterministic stateful algorithm (`Algorithm.detStateful`) which receives the side information
  as the observation of the round, plays the learner's action and updates its state with the
  feedback of the round.

## Main results

* `OnlineLearner.stateProcess_algUpdate`: along a run, the state of the algorithm is the state of
  the learner after the realized feedbacks;
* `OnlineLearner.action_ae_eq_iterate_feedback` (from `action_detStateful_ae_all_eq`):
  in every run `(O, X, Y)` of `L.toAlgorithm`, against any environment (for instance the i.i.d.
  environment `Environment.const μ` of stochastic optimization, or an adaptive adversary), the
  actions are almost surely the iterates of the learner on the realized observations and feedbacks:
  `X n = L.iterate (O · ω) (Y · ω) n`.
* `OnlineLearner.action_ae_eq_iterate`: its special case for a learner without side information
  run against the oblivious environment `Environment.ofSeq y` revealing a fixed sequence `y`: the
  actions are almost surely the iterates `L.iterate (fun _ ↦ ()) y`. This is the bridge between the
  sequence-level descriptions of online learning algorithms (regret bounds, `ocoRegret`) and
  their runs in the framework.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {σ 𝓧 𝓨 𝒜 : Type*} [MeasurableSpace σ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
  [MeasurableSpace 𝒜]

/-- A deterministic online learner with state `σ`, side information `𝓧` (seen before playing),
feedback `𝓨` (received after playing) and actions `𝒜`. -/
structure OnlineLearner (σ 𝓧 𝓨 𝒜 : Type*) [MeasurableSpace σ] [MeasurableSpace 𝓧]
    [MeasurableSpace 𝓨] [MeasurableSpace 𝒜] where
  /-- The initial state. -/
  init : σ
  /-- The action played from the state and the side information. -/
  play : σ → 𝓧 → 𝒜
  /-- The state update from the feedback. -/
  update : σ → 𝓨 → σ
  measurable_play : Measurable fun p : σ × 𝓧 ↦ play p.1 p.2
  measurable_update : Measurable fun p : σ × 𝓨 ↦ update p.1 p.2

namespace OnlineLearner

variable (L : OnlineLearner σ 𝓧 𝓨 𝒜)

/-- The state of the learner before round `t`, after the feedbacks `y 0, …, y (t - 1)`. -/
def state (y : ℕ → 𝓨) : ℕ → σ
  | 0 => L.init
  | t + 1 => L.update (state y t) (y t)

@[simp] lemma state_zero (y : ℕ → 𝓨) : L.state y 0 = L.init := rfl

lemma state_succ (y : ℕ → 𝓨) (t : ℕ) : L.state y (t + 1) = L.update (L.state y t) (y t) := rfl

/-- The state before round `t` depends only on the feedbacks of the rounds before `t`. -/
lemma state_congr {y y' : ℕ → 𝓨} {t : ℕ} (h : ∀ s < t, y s = y' s) :
    L.state y t = L.state y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [state_succ, state_succ, ih fun s hs ↦ h s (hs.trans (Nat.lt_succ_self t)),
      h t (Nat.lt_succ_self t)]

/-- The action played at round `t` on the side information `x` and the feedbacks `y`. -/
def iterate (x : ℕ → 𝓧) (y : ℕ → 𝓨) (t : ℕ) : 𝒜 := L.play (L.state y t) (x t)

lemma iterate_def (x : ℕ → 𝓧) (y : ℕ → 𝓨) (t : ℕ) :
    L.iterate x y t = L.play (L.state y t) (x t) := rfl

/-- The state after `t` rounds is a measurable function of the feedbacks. -/
@[fun_prop]
lemma measurable_state (t : ℕ) : Measurable fun y : ℕ → 𝓨 ↦ L.state y t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact L.measurable_update.comp (ih.prodMk (measurable_pi_apply t))

/-! ### Learners as algorithms -/

/-- The state update of the algorithm of a learner: update the state with the feedback of the
round. -/
def algUpdate (s : σ) (r : Round 𝓧 𝒜 𝓨) : σ := L.update s r.feedback

@[fun_prop]
lemma measurable_algUpdate {X : Type*} [MeasurableSpace X] {s : X → σ} {r : X → Round 𝓧 𝒜 𝓨}
    (hs : Measurable s) (hr : Measurable r) : Measurable fun x ↦ L.algUpdate (s x) (r x) :=
  L.measurable_update.comp (hs.prodMk (Round.measurable_feedback.comp hr))

/-- A learner as an LML algorithm: the deterministic stateful algorithm with the learner's
state, which observes the side information of the round, plays `L.play s x` and updates its
state with the feedback of the round. -/
noncomputable def toAlgorithm : Algorithm 𝓧 𝒜 𝓨 :=
  Algorithm.detStateful L.init (fun _ ↦ L.algUpdate) (by fun_prop) (fun _ s x ↦ L.play s x)
    (L.measurable_play.comp measurable_snd)

instance : Algorithm.IsDeterministic L.toAlgorithm := by
  unfold toAlgorithm
  infer_instance

/-- Along a run of the algorithm of a learner, the state of the algorithm (LML's
`stateProcess`) is the state of the learner after the realized feedbacks. -/
lemma stateProcess_algUpdate {Ω : Type*} (O : ℕ → Ω → 𝓧) (X : ℕ → Ω → 𝒜) (Y : ℕ → Ω → 𝓨)
    (n : ℕ) (ω : Ω) :
    stateProcess (fun _ ↦ L.algUpdate) L.init O X Y n ω = L.state (fun t ↦ Y t ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateProcess_succ, ih]
    rfl

/-- In every run of the algorithm of a learner, against any environment, the actions are almost
surely the iterates of the learner on the realized observations and feedbacks. -/
lemma action_ae_eq_iterate_feedback [MeasurableEq 𝒜] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {env : Environment 𝓧 𝒜 𝓨} {O : ℕ → Ω → 𝓧}
    {X : ℕ → Ω → 𝒜} {Y : ℕ → Ω → 𝓨} (h : IsAlgEnvSeq O X Y L.toAlgorithm env P) :
    ∀ᵐ ω ∂P, ∀ n, X n ω = L.iterate (fun t ↦ O t ω) (fun t ↦ Y t ω) n := by
  filter_upwards [IsAlgEnvSeq.action_detStateful_ae_all_eq h] with ω hω n
  rw [hω n, stateProcess_algUpdate]
  rfl

/-- In a run of the algorithm of a learner without side information against the environment
`Environment.ofSeq y` revealing the fixed sequence `y`, the actions are almost surely the iterates
of the learner on `y`. -/
lemma action_ae_eq_iterate (L : OnlineLearner σ Unit 𝓨 𝒜) [MeasurableEq 𝒜] [MeasurableEq 𝓨]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (y : ℕ → 𝓨)
    {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝒜} {Y : ℕ → Ω → 𝓨}
    (h : IsAlgEnvSeq O X Y L.toAlgorithm (Environment.ofSeq y) P) :
    ∀ᵐ ω ∂P, ∀ n, X n ω = L.iterate (fun _ ↦ ()) y n := by
  filter_upwards [L.action_ae_eq_iterate_feedback h, feedback_ofSeq_ae_eq h] with ω hX hY n
  rw [hX n, show (fun t ↦ Y t ω) = y from funext hY]

end OnlineLearner

end Learning
