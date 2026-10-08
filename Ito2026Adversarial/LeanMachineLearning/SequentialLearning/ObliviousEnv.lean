/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.EvaluationEnv
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFun

/-!
# Environments that ignore the action

Two environments in which the feedback does not depend on the action played, both special cases
of LML's oblivious environments:

* `Environment.ofSeq y : Environment Unit 𝓐 𝓨` reveals the fixed sequence `y n` at round `n` (an
  oblivious adversary with committed losses: the feedback of round `n` is the loss vector `y n`,
  whatever the point played). It is LML's `Environment.evalSeq` of the constant functions
  `fun _ ↦ y n`, hence oblivious with deterministic feedback.
* `Environment.const μ : Environment Unit 𝓐 𝓨` draws the feedback i.i.d. with law `μ` whatever the
  action: LML's `Environment.bandit` with the constant kernel `μ`. A run of an algorithm `alg` in
  this environment (`IsAlgEnvSeq O A Y alg (Environment.const μ) P`) is a sequence of observations
  `Y n` that are i.i.d. with law `μ` together with actions `A n` that are *predictable*: each
  `A (n + 1)` is drawn (by the algorithm, possibly at random) from the history of the first `n + 1`
  rounds, and `Y (n + 1)` is independent of that history and of `A (n + 1)`. This is the setting of
  sequential testing by betting, in which the action is the fraction of the current wealth bet
  on the next observation, and of online learning with stochastic losses.

Two properties of general environments:

* `Environment.FeedbackIgnoresAction env`: the feedback kernels do not read the action of the
  current round (a non-anticipating, possibly adaptive, adversary committing its losses before
  the action); `Environment.ofSeq` and `Environment.const` have it. It is the adaptive-adversary
  slot of the taxonomy of `LIBRARY_STATUS_REVIEW.md` (§3.4); it is independent of LML's
  `Environment.IsOblivious` (the observations have fixed laws and the feedback kernels read *only*
  the current observation and action).
* `Environment.FeedbackIn env s`: the feedbacks lie in the set `s` almost surely;
  `Environment.ObsIn env s`: the same for the observations.

The names `Environment.ofSeq`, `Environment.const` and `Environment.FeedbackIgnoresAction` are the
ones that LML's `SequentialLearning/README.md` recommends for these constructions, which LML does
not have yet.

## Main statements

* `feedback_ofSeq_ae_eq`: in every run against `Environment.ofSeq y`, the feedbacks are almost
  surely the sequence `y`.
* `IsAlgEnvSeq.hasLaw_feedback_const`, `IsAlgEnvSeq.indepFun_feedback_const`,
  `IsAlgEnvSeq.iIndepFun_feedback_const`: in every run against `Environment.const μ`, the feedbacks
  are i.i.d. with law `μ`, and the feedback of a round is independent of the past rounds and of the
  observation and action of that round.
* `IsAlgEnvSeq.ae_feedback_mem`, `IsAlgEnvSeq.ae_obs_mem`: in every run against an environment
  with `FeedbackIn env s` (resp. `ObsIn env s`), the feedbacks (resp. observations) lie in `s`
  almost surely.
* `IsAlgEnvSeq.hasCondDistrib_feedback_of_eq_comap`,
  `IsAlgEnvSeq.hasCondDistrib_feedback_of_feedbackIgnoresAction`: in a run against an environment
  whose feedback kernel reads only a statistic of the round (for instance, does not read the
  action), the feedback has the corresponding conditional law given that statistic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-! ### Properties of environments -/

/-- The feedback kernels of the environment do not read the action of the current round: the
feedback of a round is drawn given the past rounds and the current observation only (the
environment is *non-anticipating*, as an adversary committing its losses before the action). -/
def Environment.FeedbackIgnoresAction (env : Environment 𝓞 𝓐 𝓨) : Prop :=
  ∀ n, ∃ κ : Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) 𝓨, env.feedback n = κ.comap Prod.fst measurable_fst

/-- The feedbacks of the environment lie in the set `s`, almost surely. -/
def Environment.FeedbackIn (env : Environment 𝓞 𝓐 𝓨) (s : Set 𝓨) : Prop :=
  ∀ n p, ∀ᵐ y ∂(env.feedback n p), y ∈ s

lemma Environment.FeedbackIn.mono {env : Environment 𝓞 𝓐 𝓨} {s t : Set 𝓨} (h : env.FeedbackIn s)
    (hst : s ⊆ t) : env.FeedbackIn t :=
  fun n p ↦ (h n p).mono fun _ hy ↦ hst hy

/-- The observations of the environment lie in the set `s`, almost surely. -/
def Environment.ObsIn (env : Environment 𝓞 𝓐 𝓨) (s : Set 𝓞) : Prop :=
  ∀ n h, ∀ᵐ o ∂(env.obs n h), o ∈ s

lemma Environment.ObsIn.mono {env : Environment 𝓞 𝓐 𝓨} {s t : Set 𝓞} (h : env.ObsIn s)
    (hst : s ⊆ t) : env.ObsIn t :=
  fun n p ↦ (h n p).mono fun _ ho ↦ hst ho

/-! ### The environment revealing a fixed sequence -/

/-- The oblivious environment revealing the fixed sequence `y n` at round `n`, whatever the
action played. -/
noncomputable def Environment.ofSeq (y : ℕ → 𝓨) : Environment Unit 𝓐 𝓨 :=
  Environment.evalSeq (fun n (_ : 𝓐) ↦ y n) fun _ ↦ measurable_const

instance (y : ℕ → 𝓨) : (Environment.ofSeq (𝓐 := 𝓐) y).HasDeterministicFeedback := by
  unfold Environment.ofSeq
  infer_instance

instance (y : ℕ → 𝓨) : (Environment.ofSeq (𝓐 := 𝓐) y).IsOblivious := by
  unfold Environment.ofSeq
  infer_instance

@[simp]
lemma obs_ofSeq (y : ℕ → 𝓨) (n : ℕ) :
    (Environment.ofSeq (𝓐 := 𝓐) y).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_ofSeq (y : ℕ → 𝓨) (n : ℕ) :
    (Environment.ofSeq (𝓐 := 𝓐) y).feedback n
      = Kernel.deterministic (fun _ ↦ y n) measurable_const := rfl

@[simp]
lemma feedbackCondObsAction_ofSeq (y : ℕ → 𝓨) (n : ℕ) :
    (Environment.ofSeq (𝓐 := 𝓐) y).feedbackCondObsAction n
      = Kernel.deterministic (fun _ ↦ y n) measurable_const :=
  feedbackCondObsAction_evalSeq n

lemma feedbackIgnoresAction_ofSeq (y : ℕ → 𝓨) :
    (Environment.ofSeq (𝓐 := 𝓐) y).FeedbackIgnoresAction := by
  intro n
  refine ⟨Kernel.deterministic (fun _ ↦ y n) measurable_const, ?_⟩
  ext p s hs
  simp [Kernel.deterministic_apply, Kernel.comap_apply]

lemma feedbackIn_ofSeq [MeasurableSingletonClass 𝓨] {y : ℕ → 𝓨} {s : Set 𝓨}
    (hy : ∀ n, y n ∈ s) : (Environment.ofSeq (𝓐 := 𝓐) y).FeedbackIn s := by
  intro n p
  rw [feedback_ofSeq, Kernel.deterministic_apply, ae_dirac_eq]
  exact hy n

/-! ### The i.i.d. environment -/

/-- The environment in which the observations are i.i.d. with law `μ`, whatever the actions: the
stationary environment with the constant kernel `μ`. -/
noncomputable def Environment.const (μ : Measure 𝓨) [IsProbabilityMeasure μ] :
    Environment Unit 𝓐 𝓨 :=
  Environment.bandit (Kernel.const 𝓐 μ)

instance (μ : Measure 𝓨) [IsProbabilityMeasure μ] : (Environment.const (𝓐 := 𝓐) μ).IsOblivious := by
  unfold Environment.const
  infer_instance

@[simp]
lemma obs_const (μ : Measure 𝓨) [IsProbabilityMeasure μ] (n : ℕ) :
    (Environment.const (𝓐 := 𝓐) μ).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_const (μ : Measure 𝓨) [IsProbabilityMeasure μ] (n : ℕ) :
    (Environment.const (𝓐 := 𝓐) μ).feedback n = Kernel.const _ μ := by
  ext p : 1
  simp [Environment.const]

@[simp]
lemma feedbackCondObsAction_const (μ : Measure 𝓨) [IsProbabilityMeasure μ] (n : ℕ) :
    (Environment.const (𝓐 := 𝓐) μ).feedbackCondObsAction n = Kernel.const _ μ := by
  refine Environment.feedbackCondObsAction_eq_of_feedback_eq _ ?_
  ext p : 1
  simp

lemma feedbackIgnoresAction_const (μ : Measure 𝓨) [IsProbabilityMeasure μ] :
    (Environment.const (𝓐 := 𝓐) μ).FeedbackIgnoresAction := by
  intro n
  refine ⟨Kernel.const _ μ, ?_⟩
  ext p s hs
  simp

lemma feedbackIn_const {μ : Measure 𝓨} [IsProbabilityMeasure μ] {s : Set 𝓨}
    (hμ : ∀ᵐ y ∂μ, y ∈ s) : (Environment.const (𝓐 := 𝓐) μ).FeedbackIn s := by
  intro n p
  simpa using hμ

/-! ### Runs -/

/-- In a run against `Environment.ofSeq y`, the feedbacks are almost surely the sequence `y`. -/
lemma feedback_ofSeq_ae_eq [MeasurableEq 𝓨] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {y : ℕ → 𝓨} {alg : Algorithm Unit 𝓐 𝓨} {O : ℕ → Ω → Unit}
    {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq y) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = y n := by
  rw [ae_all_iff]
  intro n
  filter_upwards [Environment.HasDeterministicFeedback.feedback_ae_eq h n] with ω hω
  rw [hω]
  simp [Environment.ofSeq]

namespace IsAlgEnvSeq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section General

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐}
  {Y : ℕ → Ω → 𝓨}

/-- In a run against an environment whose feedbacks lie in the measurable set `s`, the feedbacks
lie in `s` almost surely. -/
lemma ae_feedback_mem (h : IsAlgEnvSeq O A Y alg env P) {s : Set 𝓨} (henv : env.FeedbackIn s)
    (hs : MeasurableSet s) (n : ℕ) :
    ∀ᵐ ω ∂P, Y n ω ∈ s := by
  have h_law := h.hasCondDistrib_feedback n
  have h1 : ∀ᵐ q ∂(P.map (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⊗ₘ env.feedback n),
      q.2 ∈ s :=
    Measure.ae_compProd_of_ae_ae (measurable_snd hs) (ae_of_all _ fun p ↦ henv n p)
  rw [← h_law.map_eq] at h1
  exact ae_of_ae_map h_law.aemeasurable h1

/-- In a run against an environment whose observations lie in the measurable set `s`, the
observations lie in `s` almost surely. -/
lemma ae_obs_mem (h : IsAlgEnvSeq O A Y alg env P) {s : Set 𝓞} (henv : env.ObsIn s)
    (hs : MeasurableSet s) (n : ℕ) :
    ∀ᵐ ω ∂P, O n ω ∈ s := by
  have h_law := h.hasCondDistrib_obs n
  have h1 : ∀ᵐ q ∂(P.map (history O A Y n) ⊗ₘ env.obs n), q.2 ∈ s :=
    Measure.ae_compProd_of_ae_ae (measurable_snd hs) (ae_of_all _ fun p ↦ henv n p)
  rw [← h_law.map_eq] at h1
  exact ae_of_ae_map h_law.aemeasurable h1

/-- In a run against an environment whose feedback kernel of round `n` reads only a statistic
`f` of the history, the observation and the action of round `n` (`env.feedback n = κ.comap f`),
the feedback of round `n` has conditional law `κ` given that statistic. -/
lemma hasCondDistrib_feedback_of_eq_comap (h : IsAlgEnvSeq O A Y alg env P) {n : ℕ}
    {𝓩 : Type*} [MeasurableSpace 𝓩] {f : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 → 𝓩} (hf : Measurable f)
    {κ : Kernel 𝓩 𝓨} [IsSFiniteKernel κ] (hκ : env.feedback n = κ.comap f hf) :
    HasCondDistrib (Y n) (fun ω ↦ f ((history O A Y n ω, O n ω), A n ω)) κ P := by
  have h1 := h.hasCondDistrib_feedback n
  rw [hκ] at h1
  exact h1.comp_right

/-- **Feedback of an environment ignoring the action** (`lem:feedback_ignores_action_cond`). In a
run against an environment whose feedback kernel of round `n` does not read the action of the
round, `env.feedback n = κ.comap Prod.fst` (`Environment.FeedbackIgnoresAction`), the feedback of
round `n` has conditional law `κ` given the history and the observation of round `n` (and, by
definition of a run, `κ.comap Prod.fst` given the history, the observation and the action). -/
lemma hasCondDistrib_feedback_of_feedbackIgnoresAction (h : IsAlgEnvSeq O A Y alg env P)
    {n : ℕ} {κ : Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) 𝓨} [IsSFiniteKernel κ]
    (hκ : env.feedback n = κ.comap Prod.fst measurable_fst) :
    HasCondDistrib (Y n) (fun ω ↦ (history O A Y n ω, O n ω)) κ P :=
  h.hasCondDistrib_feedback_of_eq_comap measurable_fst hκ

end General

variable {alg : Algorithm Unit 𝓐 𝓨} {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {μ : Measure 𝓨} [IsProbabilityMeasure μ]

/-- In a run against `Environment.const μ`, the feedback of every round has law `μ`. -/
lemma hasLaw_feedback_const (h : IsAlgEnvSeq O A Y alg (Environment.const μ) P) (n : ℕ) :
    HasLaw (Y n) μ P :=
  (h.hasCondDistrib_feedback_bandit n).hasLaw_of_const

/-- In a run against `Environment.const μ`, the feedback of round `n` is independent of the past
rounds and of the observation and the action of round `n`. -/
lemma indepFun_feedback_const (h : IsAlgEnvSeq O A Y alg (Environment.const μ) P) (n : ℕ) :
    IndepFun (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) (Y n) P := by
  have h1 := h.hasCondDistrib_feedback n
  rw [feedback_const] at h1
  exact h1.indepFun_of_const

/-- **Runs against `Environment.const μ`.** The feedbacks of a run against `Environment.const μ` are
mutually independent (and have law `μ`, `hasLaw_feedback_const`), whatever the algorithm. -/
lemma iIndepFun_feedback_const (h : IsAlgEnvSeq O A Y alg (Environment.const μ) P) :
    iIndepFun Y P := by
  have hY := h.measurable_feedback
  rw [iIndepFun_nat_iff_forall_indepFun fun n ↦ (hY n).aemeasurable]
  intro n
  change Y (n + 1) ⟂ᵢ[P] (fun (q : (Hist Unit 𝓐 𝓨 (n + 1) × Unit) × 𝓐) (i : Finset.Iic n) ↦
      (q.1.1 ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩).feedback) ∘
    (fun ω ↦ ((history O A Y (n + 1) ω, O (n + 1) ω), A (n + 1) ω))
  exact (h.indepFun_feedback_const (n + 1)).symm.comp measurable_id (by fun_prop)

end IsAlgEnvSeq

end Learning
