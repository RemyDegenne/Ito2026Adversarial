/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.Announce
public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.FactorsThrough
public import LeanMachineLearning.SequentialLearning.Deterministic

/-!
# Stateful algorithms

Many online learning algorithms maintain a state (a cumulative estimate, counts, a regression
state, ...) updated at each round from the round played (observation, action and feedback), and
choose the next action from the current state and the current observation.

## Main definitions

* `foldHistIdx upd s0 t h`: the state after the `t` rounds of history `h`, starting from `s0`
  and updating at round `t` by `upd t`; `foldHist upd s0` is the case of a time-independent
  update.
* `Algorithm.stateful s0 upd hupd π`: the algorithm whose action at round `n` is drawn from the
  kernel `π n` applied to the current state and the current observation.
* `Algorithm.detStateful s0 upd hupd a ha`: the deterministic version, playing `a n s o` from the
  state `s` and the observation `o` (an instance of LML's `Algorithm.deterministic`).
* `stateProcess upd s0 O A Y t`: the state after `t` rounds of a run `(O, A, Y)`, as a random
  variable.

## Main statements

* `factorsThrough_stateful`: a stateful algorithm factors through its state and the
  current observation.
* `Algorithm.detStateful_eq_stateful`: the deterministic version is the stateful
  algorithm with Dirac policy kernels.
* `ignoresAnnounced_stateful`: a stateful algorithm announcing a variable that neither
  its state update nor the action marginal of its policy reads ignores its announcements, so that
  its runs project to runs of the behavioral algorithm
  (`IsAlgEnvSeq.isAlgEnvSeq_of_ignoresAnnounced`).
* `IsAlgEnvSeq.hasCondDistrib_action_stateful`: in a run of `Algorithm.stateful`, the
  action of round `n` has conditional distribution `π n` given the state `stateProcess … n` and
  the observation of round `n`.
* `IsAlgEnvSeq.action_detStateful_ae_eq`: in a run of `Algorithm.detStateful`, the action
  of round `n` is almost surely `a n (stateProcess … n) (O n)`.

## Measurability contract

The constructors take the measurability of the update and of the policy as functions of the
tuple `(round index, state, round)` (resp. `(round index, state, observation)`), which are the
goals `fun_prop` proves for concrete algorithms once the measurability lemmas of their building
blocks are tagged `@[fun_prop]`; the constructors do the remaining compositions with the history
once and for all. The measurability of the state (`measurable_foldHistIdx`, `measurable_foldHist`,
`measurable_stateProcess`) is available to `fun_prop`.

## Memory form

`Algorithm.stateful s0 upd hupd π` is the projection of the memory algorithm
`Algorithm.statefulMemory s0 upd hupd π`, which announces its state
(`IsAlgEnvSeq.isAlgEnvSeq_stateful_of_statefulMemory`, `SequentialLearning/Memory.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 𝓞' 𝓐' 𝓨' σ Ω : Type*}

/-! ### Folding a history -/

/-- The state after the `t` rounds of history `h`, starting from `s0` and updating at round `t`
by `upd t`. -/
def foldHistIdx (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) : (t : ℕ) → Hist 𝓞 𝓐 𝓨 t → σ
  | 0, _ => s0
  | t + 1, h => upd t (foldHistIdx upd s0 t fun i ↦ h i.castSucc) (h (Fin.last t))

/-- The state after the `t` rounds of history `h`, starting from `s0` and updating by `upd`. -/
def foldHist (upd : σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) : (t : ℕ) → Hist 𝓞 𝓐 𝓨 t → σ :=
  foldHistIdx (fun _ ↦ upd) s0

lemma foldHist_def (upd : σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) :
    foldHist upd s0 = foldHistIdx (fun _ ↦ upd) s0 := rfl

@[simp]
lemma foldHistIdx_zero (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (h : Hist 𝓞 𝓐 𝓨 0) :
    foldHistIdx upd s0 0 h = s0 := rfl

lemma foldHistIdx_succ (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (t : ℕ)
    (h : Hist 𝓞 𝓐 𝓨 (t + 1)) :
    foldHistIdx upd s0 (t + 1) h =
      upd t (foldHistIdx upd s0 t fun i ↦ h i.castSucc) (h (Fin.last t)) := rfl

@[simp]
lemma foldHist_zero (upd : σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (h : Hist 𝓞 𝓐 𝓨 0) :
    foldHist upd s0 0 h = s0 := rfl

lemma foldHist_succ (upd : σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (t : ℕ) (h : Hist 𝓞 𝓐 𝓨 (t + 1)) :
    foldHist upd s0 (t + 1) h =
      upd (foldHist upd s0 t fun i ↦ h i.castSucc) (h (Fin.last t)) := rfl

/-- Folding a history whose rounds are transformed by `g` is folding the original history with
the update precomposed with `g`. With `g = Round.map fo fa fy`, this compares the states of an
algorithm along a history and along its transport by `Hist.map fo fa fy`. -/
lemma foldHistIdx_comp (upd : ℕ → σ → Round 𝓞' 𝓐' 𝓨' → σ) (g : Round 𝓞 𝓐 𝓨 → Round 𝓞' 𝓐' 𝓨')
    (s0 : σ) (t : ℕ) (h : Hist 𝓞 𝓐 𝓨 t) :
    foldHistIdx upd s0 t (fun i ↦ g (h i)) = foldHistIdx (fun n s r ↦ upd n s (g r)) s0 t h := by
  induction t with
  | zero => rfl
  | succ t ih => rw [foldHistIdx_succ, foldHistIdx_succ, ih]

/-- Folding a history whose rounds are transformed by `g` is folding the original history with
the update precomposed with `g`. -/
lemma foldHist_comp (upd : σ → Round 𝓞' 𝓐' 𝓨' → σ) (g : Round 𝓞 𝓐 𝓨 → Round 𝓞' 𝓐' 𝓨')
    (s0 : σ) (t : ℕ) (h : Hist 𝓞 𝓐 𝓨 t) :
    foldHist upd s0 t (fun i ↦ g (h i)) = foldHist (fun s r ↦ upd s (g r)) s0 t h :=
  foldHistIdx_comp _ g s0 t h

/-! ### The state along a run -/

/-- The state after `t` rounds of the run `(O, A, Y)`, as a function of `ω`. -/
def stateProcess (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (Y : ℕ → Ω → 𝓨) (t : ℕ) (ω : Ω) : σ :=
  foldHistIdx upd s0 t (history O A Y t ω)

@[simp]
lemma stateProcess_zero (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (O : ℕ → Ω → 𝓞)
    (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) :
    stateProcess upd s0 O A Y 0 = fun _ ↦ s0 := rfl

/-- The state after round `t` is the update of the state before it with the round `t`. -/
lemma stateProcess_succ (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ) (s0 : σ) (O : ℕ → Ω → 𝓞)
    (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (t : ℕ) (ω : Ω) :
    stateProcess upd s0 O A Y (t + 1) ω
      = upd t (stateProcess upd s0 O A Y t ω) (O t ω, A t ω, Y t ω) := rfl

variable [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] [MeasurableSpace σ]

@[fun_prop]
lemma measurable_foldHistIdx {upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ}
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (s0 : σ) (t : ℕ) :
    Measurable (foldHistIdx upd s0 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact hupd.comp (measurable_const.prodMk
      ((ih.comp (Measurable.of_eval fun i ↦ measurable_pi_apply _)).prodMk
        (measurable_pi_apply _)))

@[fun_prop]
lemma measurable_foldHist {upd : σ → Round 𝓞 𝓐 𝓨 → σ}
    (hupd : Measurable fun p : σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2) (s0 : σ) (t : ℕ) :
    Measurable (foldHist upd s0 t) :=
  measurable_foldHistIdx (hupd.comp measurable_snd) s0 t

/-! ### Stateful algorithms -/

/-- The stateful algorithm with initial state `s0`, state update `upd` and policy `π`: the action
at round `n` is drawn from `π n` applied to the current state and the current observation. -/
noncomputable def Algorithm.stateful (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2)
    (π : ℕ → Kernel (σ × 𝓞) 𝓐) [∀ n, IsMarkovKernel (π n)] : Algorithm 𝓞 𝓐 𝓨 where
  policy n := (π n).comap (fun p ↦ (foldHistIdx upd s0 n p.1, p.2))
    (((measurable_foldHistIdx hupd s0 n).comp measurable_fst).prodMk measurable_snd)

@[simp]
lemma Algorithm.policy_stateful (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2)
    (π : ℕ → Kernel (σ × 𝓞) 𝓐) [∀ n, IsMarkovKernel (π n)] (n : ℕ) :
    (Algorithm.stateful s0 upd hupd π).policy n
      = (π n).comap (fun p ↦ (foldHistIdx upd s0 n p.1, p.2))
        (((measurable_foldHistIdx hupd s0 n).comp measurable_fst).prodMk measurable_snd) := rfl

/-- A stateful algorithm factors through its state and the current observation. -/
lemma factorsThrough_stateful (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2)
    (π : ℕ → Kernel (σ × 𝓞) 𝓐) [∀ n, IsMarkovKernel (π n)] :
    (Algorithm.stateful s0 upd hupd π).FactorsThrough (𝓑 := fun _ ↦ σ × 𝓞)
      fun n p ↦ (foldHistIdx upd s0 n p.1, p.2) :=
  fun n ↦ ⟨π n, fun _ ↦ rfl⟩

/-- The deterministic stateful algorithm with initial state `s0`, state update `upd` and action
`a n s o` at round `n` from the state `s` and the observation `o`. -/
noncomputable def Algorithm.detStateful (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (a : ℕ → σ → 𝓞 → 𝓐)
    (ha : Measurable fun p : ℕ × σ × 𝓞 ↦ a p.1 p.2.1 p.2.2) : Algorithm 𝓞 𝓐 𝓨 :=
  Algorithm.deterministic (fun n p ↦ a n (foldHistIdx upd s0 n p.1) p.2) fun n ↦
    ha.comp (measurable_const.prodMk
      (((measurable_foldHistIdx hupd s0 n).comp measurable_fst).prodMk measurable_snd))

instance (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (a : ℕ → σ → 𝓞 → 𝓐)
    (ha : Measurable fun p : ℕ × σ × 𝓞 ↦ a p.1 p.2.1 p.2.2) :
    Algorithm.IsDeterministic (Algorithm.detStateful s0 upd hupd a ha) :=
  inferInstanceAs (Algorithm.IsDeterministic (Algorithm.deterministic _ _))

@[simp]
lemma Algorithm.policy_detStateful (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (a : ℕ → σ → 𝓞 → 𝓐)
    (ha : Measurable fun p : ℕ × σ × 𝓞 ↦ a p.1 p.2.1 p.2.2) (n : ℕ) :
    (Algorithm.detStateful s0 upd hupd a ha).policy n
      = Kernel.deterministic (fun p ↦ a n (foldHistIdx upd s0 n p.1) p.2)
        (ha.comp (measurable_const.prodMk
          (((measurable_foldHistIdx hupd s0 n).comp measurable_fst).prodMk measurable_snd))) :=
  rfl

/-- The deterministic stateful algorithm is the stateful algorithm whose policy kernels are the
Dirac kernels at the actions `a n s o`. -/
lemma Algorithm.detStateful_eq_stateful (s0 : σ) (upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (a : ℕ → σ → 𝓞 → 𝓐)
    (ha : Measurable fun p : ℕ × σ × 𝓞 ↦ a p.1 p.2.1 p.2.2) :
    Algorithm.detStateful s0 upd hupd a ha = Algorithm.stateful s0 upd hupd fun n ↦
      Kernel.deterministic (fun p : σ × 𝓞 ↦ a n p.1 p.2)
        (ha.comp (measurable_const.prodMk measurable_id)) :=
  Algorithm.ext (funext fun _ ↦ Kernel.ext fun _ ↦ rfl)

/-- **Announcing stateful algorithms.** A stateful algorithm announcing a variable in `𝓩`, whose
state update ignores the announced variables and whose policy `πZ` has second marginal `π`,
ignores its announcements, with behavioral algorithm the stateful algorithm with policy `π`. -/
lemma ignoresAnnounced_stateful {𝓩 : Type*} [MeasurableSpace 𝓩] (s0 : σ)
    {updZ : ℕ → σ → Round 𝓞 (𝓩 × 𝓐) 𝓨 → σ}
    (hupdZ : Measurable fun p : ℕ × σ × Round 𝓞 (𝓩 × 𝓐) 𝓨 ↦ updZ p.1 p.2.1 p.2.2)
    {upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ}
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2)
    (h_upd : ∀ n s r, updZ n s r = upd n s (Round.mapAction Prod.snd r))
    {πZ : ℕ → Kernel (σ × 𝓞) (𝓩 × 𝓐)} [∀ n, IsMarkovKernel (πZ n)]
    {π : ℕ → Kernel (σ × 𝓞) 𝓐} [∀ n, IsMarkovKernel (π n)] (h_π : ∀ n, (πZ n).snd = π n) :
    (Algorithm.stateful s0 updZ hupdZ πZ).IgnoresAnnounced (Algorithm.stateful s0 upd hupd π) := by
  intro n
  ext p : 1
  have h_state :
      foldHistIdx updZ s0 n p.1 = foldHistIdx upd s0 n (Hist.mapAction Prod.snd p.1) := by
    obtain rfl : updZ = fun n s r ↦ upd n s (Round.mapAction Prod.snd r) := by
      funext n s r
      exact h_upd n s r
    exact (foldHistIdx_comp upd (Round.mapAction Prod.snd) s0 n p.1).symm
  rw [Kernel.snd_apply, Algorithm.policy_stateful, Kernel.comap_apply, ← Kernel.snd_apply, h_π,
    Algorithm.policy_stateful, Kernel.comap_apply, Kernel.comap_apply, h_state]

/-! ### Measurability of the state along a run -/

variable [MeasurableSpace Ω]

@[fun_prop]
lemma measurable_stateProcess {upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ}
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (s0 : σ)
    {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} (hO : ∀ n, Measurable (O n))
    (hA : ∀ n, Measurable (A n)) (hY : ∀ n, Measurable (Y n)) (t : ℕ) :
    Measurable (stateProcess upd s0 O A Y t) :=
  (measurable_foldHistIdx hupd s0 t).comp (measurable_history hO hA hY t)

/-! ### Runs of stateful algorithms -/

namespace IsAlgEnvSeq

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {s0 : σ} {upd : ℕ → σ → Round 𝓞 𝓐 𝓨 → σ}

/-- The state after round `t` is measurable with respect to the σ-algebra of the first `t + 1`
rounds. -/
lemma measurable_stateProcess_succ_filtration (h : IsAlgEnvSeq O A Y alg env P)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (t : ℕ) :
    Measurable[h.filtration t] (stateProcess upd s0 O A Y (t + 1)) :=
  (measurable_foldHistIdx hupd s0 (t + 1)).comp (h.measurable_history_succ_filtration t)

/-- The state before round `t` is measurable with respect to the σ-algebra of the first `t`
rounds and the observation of round `t`. -/
lemma measurable_stateProcess_filtrationObs (h : IsAlgEnvSeq O A Y alg env P)
    (hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2) (t : ℕ) :
    Measurable[h.filtrationObs t] (stateProcess upd s0 O A Y t) :=
  (measurable_foldHistIdx hupd s0 t).comp (h.measurable_history_filtrationObs t)

/-- **Runs of a stateful algorithm.** In a run of `Algorithm.stateful s0 upd hupd π`, the action
of round `n` has conditional distribution `π n` given the state `stateProcess upd s0 O A Y n` and
the observation of round `n`. -/
lemma hasCondDistrib_action_stateful
    {hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2}
    {π : ℕ → Kernel (σ × 𝓞) 𝓐} [∀ n, IsMarkovKernel (π n)]
    (h : IsAlgEnvSeq O A Y (Algorithm.stateful s0 upd hupd π) env P) (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (stateProcess upd s0 O A Y n ω, O n ω)) (π n) P :=
  HasCondDistrib.comp_right (f := fun p : Hist 𝓞 𝓐 𝓨 n × 𝓞 ↦ (foldHistIdx upd s0 n p.1, p.2))
    (hf := ((measurable_foldHistIdx hupd s0 n).comp measurable_fst).prodMk measurable_snd)
    (h.hasCondDistrib_action n)

variable [IsProbabilityMeasure P] [MeasurableEq 𝓐] {a : ℕ → σ → 𝓞 → 𝓐}
  {hupd : Measurable fun p : ℕ × σ × Round 𝓞 𝓐 𝓨 ↦ upd p.1 p.2.1 p.2.2}
  {ha : Measurable fun p : ℕ × σ × 𝓞 ↦ a p.1 p.2.1 p.2.2}

/-- **Runs of a deterministic stateful algorithm.** In a run of `Algorithm.detStateful`, the action
of round `n` is almost surely `a n s (O n)` for the state `s = stateProcess upd s0 O A Y n`. -/
lemma action_detStateful_ae_eq
    (h : IsAlgEnvSeq O A Y (Algorithm.detStateful s0 upd hupd a ha) env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ a n (stateProcess upd s0 O A Y n ω) (O n ω) :=
  action_deterministic_ae_eq h n

/-- In a run of `Algorithm.detStateful`, almost surely, the action of every round `n` is
`a n s (O n)` for the state `s = stateProcess upd s0 O A Y n`. -/
lemma action_detStateful_ae_all_eq
    (h : IsAlgEnvSeq O A Y (Algorithm.detStateful s0 upd hupd a ha) env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = a n (stateProcess upd s0 O A Y n ω) (O n ω) :=
  action_deterministic_ae_all_eq h

end IsAlgEnvSeq

end Learning
