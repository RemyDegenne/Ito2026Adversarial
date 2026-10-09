/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Game.ZeroSum
public import Ito2026Adversarial.LeanMachineLearning.Online.Convex.Regret
public import LeanMachineLearning.SequentialLearning.Comap
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Repeated zero-sum games with bandit feedback

A learner repeatedly plays a zero-sum game `u : 𝒳 → 𝒴 → ℝ` against an adaptive opponent. At each
round `t`, the learner plays `x_t ∈ 𝒳` and the opponent simultaneously plays `y_t ∈ 𝒴`, both as
functions (possibly randomized) of the past; the learner then receives a noisy reward `r_t` with
conditional mean `u x_t y_t`.

## Modelling

* A round of the learner is a `Round Unit 𝒳 (𝒴 × ℝ)`: no observation, the action `x_t`, and as
  feedback the pair `(y_t, r_t)` of the opponent's action and the reward. The *informed* learner
  sees all of it; the *uninformed* learner, an `Algorithm Unit 𝒳 ℝ`, sees only the reward and is
  lifted to a `Player 𝒳 𝒴` by `Player.ofUninformed` (`Algorithm.comapFeedback Prod.snd`).
* The opponent is itself a player of the game with the roles exchanged: an `Algorithm`
  `Player 𝒴 𝒳` playing `y_t` given the past rounds `(y_s, (x_s, r_s))` (`Round.swapPlayers`,
  `Hist.swapPlayers`). Since it acts through its policy on the past rounds, it does not see
  `x_t`: the two players move simultaneously.
* The rewards are drawn from a reward kernel `R : RewardKernel 𝒳 𝒴`, a family of kernels from
  (past rounds, `x_t`, `y_t`) to `ℝ`: `R.HasMean u` says that the conditional mean of the reward is
  `u x_t y_t` (the noise is a martingale difference sequence), `R.RewardsIn s` that the rewards
  lie in `s`. `stationaryReward ν` is the reward kernel of a noise model `ν : Kernel (𝒳 × 𝒴) ℝ`
  that does not depend on the past.
* `gameEnv opp R : Environment Unit 𝒳 (𝒴 × ℝ)` is the environment of the learner: the feedback
  of a round is `(y_t, r_t)` with `y_t` drawn from the policy of `opp` on the swapped history and
  `r_t` from `R`.
* Performance of a run `(X, Y)` of actions of the two players under the law `P`:
  `psmr u X Y P T`, the *pure-strategy maximin regret* `E[∑_{t<T} (v* - u x_t y_t)]`;
  `externalRegret u X Y P T = ⨆ x, E[∑_{t<T} (u x y_t - u x_t y_t)]`, the expectation of the
  regret `ocoRegret` of the actions for the losses `-u · y_t`
  (`externalRegretAgainst_eq_integral_ocoRegret`);
  `nashRegret u X Y P T = E[∑_{t<T} (v^Nash - u x_t y_t)]`.
* Counts: `histPairCount h x y`, `histPairSum h x y` are the number of rounds of the history `h`
  in which `(x, y)` was played and the sum of the rewards received in those rounds;
  `pairCount X Y R x y t`, `pairSum X Y R x y t` are the same quantities after `t` rounds of a run.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory

namespace Learning.RepeatedGame

open ZeroSumGame

variable {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

/-- A player of the repeated game with actions `𝒳`, against an opponent with actions `𝒴`: an
algorithm that observes, after each round, the opponent's action and the reward. -/
abbrev Player (𝒳 𝒴 : Type*) [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] :=
  Algorithm Unit 𝒳 (𝒴 × ℝ)

/-- A round `(x, (y, r))` seen from the opponent: `(y, (x, r))`. -/
def Round.swapPlayers (r : Round Unit 𝒳 (𝒴 × ℝ)) : Round Unit 𝒴 (𝒳 × ℝ) :=
  ((), r.feedback.1, (r.action, r.feedback.2))

@[fun_prop]
lemma Round.measurable_swapPlayers :
    Measurable (Round.swapPlayers (𝒳 := 𝒳) (𝒴 := 𝒴)) := by
  unfold Round.swapPlayers
  fun_prop

/-- A history seen from the opponent. -/
def Hist.swapPlayers {n : ℕ} (h : Hist Unit 𝒳 (𝒴 × ℝ) n) : Hist Unit 𝒴 (𝒳 × ℝ) n :=
  fun i ↦ Round.swapPlayers (h i)

@[fun_prop]
lemma Hist.measurable_swapPlayers (n : ℕ) :
    Measurable (Hist.swapPlayers (𝒳 := 𝒳) (𝒴 := 𝒴) (n := n)) := by
  unfold Hist.swapPlayers
  fun_prop

/-- A reward kernel: the law of the reward of a round given the past rounds and the two actions
of the round. -/
abbrev RewardKernel (𝒳 𝒴 : Type*) [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] :=
  (n : ℕ) → Kernel (Hist Unit 𝒳 (𝒴 × ℝ) n × 𝒳 × 𝒴) ℝ

/-- The reward kernel of a noise model `ν : Kernel (𝒳 × 𝒴) ℝ` that does not depend on the past
rounds. -/
noncomputable def stationaryReward (ν : Kernel (𝒳 × 𝒴) ℝ) : RewardKernel 𝒳 𝒴 :=
  fun _ ↦ ν.comap Prod.snd measurable_snd

instance (ν : Kernel (𝒳 × 𝒴) ℝ) [IsMarkovKernel ν] (n : ℕ) :
    IsMarkovKernel (stationaryReward ν n) := by
  unfold stationaryReward; infer_instance

/-- The reward kernel has conditional mean `u x y`: the noise `r_t - u x_t y_t` is a martingale
difference sequence. -/
def RewardKernel.HasMean (R : RewardKernel 𝒳 𝒴) (u : 𝒳 → 𝒴 → ℝ) : Prop :=
  ∀ n (h : Hist Unit 𝒳 (𝒴 × ℝ) n) x y, ∫ r, r ∂(R n (h, x, y)) = u x y

/-- The rewards lie in the set `s` almost surely. -/
def RewardKernel.RewardsIn (R : RewardKernel 𝒳 𝒴) (s : Set ℝ) : Prop :=
  ∀ n (h : Hist Unit 𝒳 (𝒴 × ℝ) n) x y, ∀ᵐ r ∂(R n (h, x, y)), r ∈ s

/-- The environment of the learner playing against the opponent `opp` with reward kernel `R`: the
feedback of a round is `(y, r)` with `y` drawn from the policy of `opp` on the past rounds (seen
from the opponent) and `r` from `R`. -/
noncomputable def gameEnv (opp : Player 𝒴 𝒳) (R : RewardKernel 𝒳 𝒴) [∀ n, IsMarkovKernel (R n)] :
    Environment Unit 𝒳 (𝒴 × ℝ) where
  obs _ := Kernel.const _ (Measure.dirac ())
  feedback n :=
    ((opp.policy n).comap
      (fun p : (Hist Unit 𝒳 (𝒴 × ℝ) n × Unit) × 𝒳 ↦ (Hist.swapPlayers p.1.1, ())) (by fun_prop))
    ⊗ₖ ((R n).comap (fun q : ((Hist Unit 𝒳 (𝒴 × ℝ) n × Unit) × 𝒳) × 𝒴 ↦ (q.1.1.1, q.1.2, q.2))
      (by fun_prop))

/-- An uninformed learner, which observes only the rewards, as a player of the repeated game
(ignoring the opponent's actions in the feedback). -/
noncomputable def Player.ofUninformed (alg : Algorithm Unit 𝒳 ℝ) : Player 𝒳 𝒴 :=
  alg.comapFeedback Prod.snd measurable_snd

/-! ### Regrets -/

section Regret

omit [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The pure-strategy maximin regret `PSMR_T = E[∑_{t<T} (v* - u x_t y_t)]` of the run `(X, Y)`
under `P`. -/
noncomputable def psmr (u : 𝒳 → 𝒴 → ℝ) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴) (P : Measure Ω)
    (T : ℕ) : ℝ :=
  P[fun ω ↦ ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))]

/-- The expected regret `E[∑_{t<T} (u x y_t - u x_t y_t)]` against the fixed action `x`. -/
noncomputable def externalRegretAgainst (u : 𝒳 → 𝒴 → ℝ) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴)
    (P : Measure Ω) (T : ℕ) (x : 𝒳) : ℝ :=
  P[fun ω ↦ ∑ t ∈ range T, (u x (Y t ω) - u (X t ω) (Y t ω))]

/-- The expected regret against `x` is the expectation of the regret `ocoRegret` of the actions
`X` against `x` for the losses `x' ↦ -u x' y_t`. -/
lemma externalRegretAgainst_eq_integral_ocoRegret (u : 𝒳 → 𝒴 → ℝ) (X : ℕ → Ω → 𝒳)
    (Y : ℕ → Ω → 𝒴) (P : Measure Ω) (T : ℕ) (x : 𝒳) :
    externalRegretAgainst u X Y P T x =
      P[fun ω ↦ ocoRegret (fun t x' ↦ -u x' (Y t ω)) (fun t ↦ X t ω) T x] := by
  simp only [externalRegretAgainst, ocoRegret_eq_sum_sub, sub_neg_eq_add, neg_add_eq_sub]

/-- The external regret `ER_T = ⨆ x, E[∑_{t<T} (u x y_t - u x_t y_t)]`. -/
noncomputable def externalRegret (u : 𝒳 → 𝒴 → ℝ) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴)
    (P : Measure Ω) (T : ℕ) : ℝ :=
  ⨆ x, externalRegretAgainst u X Y P T x

/-- The Nash-value regret `NR_T = E[∑_{t<T} (v^Nash - u x_t y_t)]`. -/
noncomputable def nashRegret [Fintype 𝒳] [Fintype 𝒴] (u : 𝒳 → 𝒴 → ℝ) (X : ℕ → Ω → 𝒳)
    (Y : ℕ → Ω → 𝒴) (P : Measure Ω) (T : ℕ) : ℝ :=
  P[fun ω ↦ ∑ t ∈ range T, (nashValue u - u (X t ω) (Y t ω))]

end Regret

/-! ### Counts of action pairs -/

section Counts

variable [DecidableEq 𝒳] [DecidableEq 𝒴]

/-- The number of rounds of the history `h` in which the pair `(x, y)` was played. -/
def histPairCount {n : ℕ} (h : Hist Unit 𝒳 (𝒴 × ℝ) n) (x : 𝒳) (y : 𝒴) : ℕ :=
  ∑ i, if (h i).action = x ∧ (h i).feedback.1 = y then 1 else 0

/-- The sum of the rewards of the rounds of the history `h` in which the pair `(x, y)` was
played. -/
def histPairSum {n : ℕ} (h : Hist Unit 𝒳 (𝒴 × ℝ) n) (x : 𝒳) (y : 𝒴) : ℝ :=
  ∑ i, if (h i).action = x ∧ (h i).feedback.1 = y then (h i).feedback.2 else 0

variable [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒴]

omit [DecidableEq 𝒳] [DecidableEq 𝒴] in
lemma measurableSet_pair {n : ℕ} (i : Fin n) (x : 𝒳) (y : 𝒴) :
    MeasurableSet {h : Hist Unit 𝒳 (𝒴 × ℝ) n | (h i).action = x ∧ (h i).feedback.1 = y} :=
  ((Round.measurable_action.comp (measurable_pi_apply i)) (measurableSet_singleton x)).inter
    ((measurable_fst.comp (Round.measurable_feedback.comp (measurable_pi_apply i)))
      (measurableSet_singleton y))

@[fun_prop]
lemma measurable_histPairCount (n : ℕ) (x : 𝒳) (y : 𝒴) :
    Measurable fun h : Hist Unit 𝒳 (𝒴 × ℝ) n ↦ histPairCount h x y :=
  Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (measurableSet_pair i x y) measurable_const measurable_const

@[fun_prop]
lemma measurable_histPairSum (n : ℕ) (x : 𝒳) (y : 𝒴) :
    Measurable fun h : Hist Unit 𝒳 (𝒴 × ℝ) n ↦ histPairSum h x y :=
  Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (measurableSet_pair i x y)
      (measurable_snd.comp (Round.measurable_feedback.comp (measurable_pi_apply i)))
      measurable_const

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The number of rounds among the first `t` of the run `(X, Y, R)` in which `(x, y)` was
played. -/
def pairCount (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴) (R : ℕ → Ω → ℝ) (x : 𝒳) (y : 𝒴) (t : ℕ)
    (ω : Ω) : ℕ :=
  histPairCount (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, R t ω)) t ω) x y

/-- The sum of the rewards of the rounds among the first `t` of the run `(X, Y, R)` in which
`(x, y)` was played. -/
def pairSum (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴) (R : ℕ → Ω → ℝ) (x : 𝒳) (y : 𝒴) (t : ℕ)
    (ω : Ω) : ℝ :=
  histPairSum (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, R t ω)) t ω) x y

end Counts

section CountLemmas

omit [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

variable {Ω : Type*} [DecidableEq 𝒳] [DecidableEq 𝒴] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴}
  {R : ℕ → Ω → ℝ}

/-- The count of the pair `(x, y)` after `t` rounds is the number of rounds `s < t` in which it
was played. -/
lemma pairCount_eq_sum_range (x : 𝒳) (y : 𝒴) (t : ℕ) (ω : Ω) :
    pairCount X Y R x y t ω = ∑ s ∈ range t, if X s ω = x ∧ Y s ω = y then 1 else 0 :=
  Fin.sum_univ_eq_sum_range (fun s ↦ if X s ω = x ∧ Y s ω = y then 1 else 0) t

/-- No pair has been played before the first round. -/
@[simp]
lemma pairCount_zero (x : 𝒳) (y : 𝒴) (ω : Ω) : pairCount X Y R x y 0 ω = 0 := by
  simp [pairCount_eq_sum_range]

/-- The count of a pair increases by one at the rounds in which it is played. -/
lemma pairCount_succ (x : 𝒳) (y : 𝒴) (t : ℕ) (ω : Ω) :
    pairCount X Y R x y (t + 1) ω
      = pairCount X Y R x y t ω + if X t ω = x ∧ Y t ω = y then 1 else 0 := by
  simp only [pairCount_eq_sum_range, sum_range_succ]

/-- The count of a pair after `t` rounds is at most `t`. -/
lemma pairCount_le (x : 𝒳) (y : 𝒴) (t : ℕ) (ω : Ω) : pairCount X Y R x y t ω ≤ t := by
  rw [pairCount_eq_sum_range]
  calc ∑ s ∈ range t, (if X s ω = x ∧ Y s ω = y then 1 else 0)
      ≤ ∑ s ∈ range t, 1 := sum_le_sum fun s _ ↦ by split_ifs <;> simp
    _ = t := by simp

section Fintype

variable [Fintype 𝒳] [Fintype 𝒴]

/-- **Decomposition of a sum over rounds by action pairs**:
`∑_{t < T} f(x_t, y_t) = ∑_{x, y} N_T(x, y) f(x, y)`. -/
lemma sum_range_eq_sum_pairCount_mul (f : 𝒳 → 𝒴 → ℝ) (T : ℕ) (ω : Ω) :
    ∑ t ∈ range T, f (X t ω) (Y t ω) = ∑ x, ∑ y, (pairCount X Y R x y T ω : ℝ) * f x y := by
  have h1 (t : ℕ) : f (X t ω) (Y t ω)
      = ∑ x, ∑ y, (if X t ω = x ∧ Y t ω = y then (1 : ℝ) else 0) * f x y := by
    simp [ite_and, ite_mul]
  calc ∑ t ∈ range T, f (X t ω) (Y t ω)
      = ∑ t ∈ range T, ∑ x, ∑ y, (if X t ω = x ∧ Y t ω = y then (1 : ℝ) else 0) * f x y :=
        sum_congr rfl fun t _ ↦ h1 t
    _ = ∑ x, ∑ y, ∑ t ∈ range T, (if X t ω = x ∧ Y t ω = y then (1 : ℝ) else 0) * f x y := by
        rw [sum_comm]
        exact sum_congr rfl fun x _ ↦ sum_comm
    _ = ∑ x, ∑ y, (pairCount X Y R x y T ω : ℝ) * f x y := by
        simp_rw [pairCount_eq_sum_range, Nat.cast_sum, sum_mul, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]

/-- The counts of all pairs after `T` rounds sum to `T`. -/
lemma sum_pairCount (T : ℕ) (ω : Ω) : ∑ x, ∑ y, (pairCount X Y R x y T ω : ℝ) = T := by
  have := sum_range_eq_sum_pairCount_mul (X := X) (Y := Y) (R := R) (fun _ _ ↦ (1 : ℝ)) T ω
  simpa using this.symm

end Fintype

end CountLemmas

section CountMeasurability

variable [DecidableEq 𝒳] [DecidableEq 𝒴] [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒴]
  {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → 𝒴} {R : ℕ → Ω → ℝ}

/-- The count of a pair after `t` rounds of a run is measurable. -/
lemma measurable_pairCount (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hR : ∀ n, Measurable (R n)) (x : 𝒳) (y : 𝒴) (t : ℕ) :
    Measurable (pairCount X Y R x y t) :=
  (measurable_histPairCount t x y).comp
    (measurable_history (fun _ ↦ measurable_const) hX (fun n ↦ (hY n).prodMk (hR n)) t)

/-- The reward sum of a pair after `t` rounds of a run is measurable. -/
lemma measurable_pairSum (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hR : ∀ n, Measurable (R n)) (x : 𝒳) (y : 𝒴) (t : ℕ) :
    Measurable (pairSum X Y R x y t) :=
  (measurable_histPairSum t x y).comp
    (measurable_history (fun _ ↦ measurable_const) hX (fun n ↦ (hY n).prodMk (hR n)) t)

end CountMeasurability

end Learning.RepeatedGame
