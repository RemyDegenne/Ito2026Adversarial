/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Lemma11
public import Ito2026Adversarial.LeanMachineLearning.Game.Maximin
public import Ito2026Adversarial.LeanMachineLearning.Game.Regret

/-!
# Analysis of Maximin-UCB

The steps of the proof of Theorem 4.

* `ucbGoodEvent u δ X Y Rw`: the event on which the confidence bounds of Lemma 11 hold for all
  action pairs and all times; its complement has probability at most `m_x m_y δ`
  (`measureReal_compl_ucbGoodEvent_le`).
* `le_ucbIndex_of_mem_ucbGoodEvent`, `ucbIndex_le_of_mem_ucbGoodEvent`: on the good event,
  `u ≤ U_t ≤ u + 2 rad_t`.
* `pairCount_mul_sq_le_of_mem_ucbGoodEvent`: on the good event, for a run of Maximin-UCB with
  `δ = 1 / T`, every pair with `Δ_{xy} > 0` satisfies `N_T(x, y) Δ_{xy}² ≤ Δ_{xy}² + 24 log T`.
* `sum_pureMaximin_sub_le_of_mem_ucbGoodEvent`,
  `sum_pureMaximin_sub_le_sqrt_of_mem_ucbGoodEvent`: the instance-dependent and worst-case bounds
  on the pathwise regret on the good event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame

namespace Ito2026Adversarial

variable {mx my : ℕ} [NeZero mx] [NeZero my] {u : Fin mx → Fin my → ℝ} {Ω : Type*}
  {X : ℕ → Ω → Fin mx} {Y : ℕ → Ω → Fin my} {Rw : ℕ → Ω → ℝ}

/-- The event on which the confidence bounds of Lemma 11 hold for the action pair `(x, y)` at all
times. -/
def ucbPairEvent (u : Fin mx → Fin my → ℝ) (δ : ℝ) (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my)
    (Rw : ℕ → Ω → ℝ) (x : Fin mx) (y : Fin my) : Set Ω :=
  {ω | ∀ t, 0 < pairCount X Y Rw x y t ω →
    |u x y - pairSum X Y Rw x y t ω / pairCount X Y Rw x y t ω| ≤
      √((4 * log (1 / δ) + 2 * log (1 + pairCount X Y Rw x y t ω)) / pairCount X Y Rw x y t ω)}

/-- The good event of Maximin-UCB: the confidence bounds of Lemma 11 hold for all action pairs
and all times. -/
def ucbGoodEvent (u : Fin mx → Fin my → ℝ) (δ : ℝ) (X : ℕ → Ω → Fin mx) (Y : ℕ → Ω → Fin my)
    (Rw : ℕ → Ω → ℝ) : Set Ω :=
  ⋂ x, ⋂ y, ucbPairEvent u δ X Y Rw x y

omit [NeZero mx] [NeZero my] in
/-- The confidence event of a pair is measurable. -/
lemma measurableSet_ucbPairEvent [MeasurableSpace Ω] (u : Fin mx → Fin my → ℝ) (δ : ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (hR : ∀ n, Measurable (Rw n))
    (x : Fin mx) (y : Fin my) :
    MeasurableSet (ucbPairEvent u δ X Y Rw x y) := by
  have hN (t : ℕ) : Measurable fun ω ↦ (pairCount X Y Rw x y t ω : ℝ) :=
    measurable_from_nat.comp (measurable_pairCount hX hY hR x y t)
  have hS (t : ℕ) := measurable_pairSum hX hY hR x y t
  refine measurableSet_setOfPred.2 (Measurable.forall fun t ↦ Measurable.imp ?_ ?_)
  · exact measurableSet_setOfPred.1
      (measurableSet_lt measurable_const (measurable_pairCount hX hY hR x y t))
  · have := hN t
    have := hS t
    exact measurableSet_setOfPred.1 (measurableSet_le (by fun_prop) (by fun_prop))

omit [NeZero mx] [NeZero my] in
/-- The good event of Maximin-UCB is measurable. -/
lemma measurableSet_ucbGoodEvent [MeasurableSpace Ω] (u : Fin mx → Fin my → ℝ) (δ : ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (hR : ∀ n, Measurable (Rw n)) :
    MeasurableSet (ucbGoodEvent u δ X Y Rw) :=
  MeasurableSet.iInter fun x ↦ MeasurableSet.iInter fun y ↦
    measurableSet_ucbPairEvent u δ hX hY hR x y

/-- **Union bound over the action pairs** for the confidence bounds of Lemma 11: the good event
of Maximin-UCB fails with probability at most `m_x m_y δ`. -/
lemma measureReal_compl_ucbGoodEvent_le (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1)
    (opp : Player (Fin my) (Fin mx)) (R : RewardKernel (Fin mx) (Fin my))
    [∀ n, IsMarkovKernel (R n)] (hR : RewardKernel.HasMean R u)
    (hR' : RewardKernel.RewardsIn R (Set.Icc (-1) 1)) (alg : Player (Fin mx) (Fin my))
    {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) alg (gameEnv opp R) P)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    P.real (ucbGoodEvent u δ X Y Rw)ᶜ ≤ mx * my * δ := by
  have hX := h.measurable_action
  have hY (n : ℕ) : Measurable (Y n) := (h.measurable_feedback n).fst
  have hRw (n : ℕ) : Measurable (Rw n) := (h.measurable_feedback n).snd
  have hpair (x : Fin mx) (y : Fin my) : P.real (ucbPairEvent u δ X Y Rw x y)ᶜ ≤ δ := by
    rw [measureReal_compl (measurableSet_ucbPairEvent u δ hX hY hRw x y), probReal_univ]
    have := probReal_forall_abs_sub_div_le_ge u hu opp R hR hR' alg P X Y Rw h x y hδ
    unfold ucbPairEvent
    linarith
  calc P.real (ucbGoodEvent u δ X Y Rw)ᶜ
      = P.real (⋃ x, ⋃ y, (ucbPairEvent u δ X Y Rw x y)ᶜ) := by
        simp [ucbGoodEvent, Set.compl_iInter]
    _ ≤ ∑ x, P.real (⋃ y, (ucbPairEvent u δ X Y Rw x y)ᶜ) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ x, ∑ y, P.real (ucbPairEvent u δ X Y Rw x y)ᶜ :=
        sum_le_sum fun x _ ↦ measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : Fin mx, ∑ _y : Fin my, δ := sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ hpair x y
    _ = mx * my * δ := by simp [mul_assoc]

omit [NeZero mx] [NeZero my] in
/-- The upper confidence bound of Maximin-UCB at round `t` of a run, in terms of the counts and
reward sums of the run. -/
lemma ucbIndex_history (δ : ℝ) (t : ℕ) (ω : Ω) (x : Fin mx) (y : Fin my) :
    ucbIndex δ (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω) x y
      = if pairCount X Y Rw x y t ω = 0 then 1 else
        pairSum X Y Rw x y t ω / pairCount X Y Rw x y t ω
          + √((4 * log (1 / δ) + 2 * log (1 + pairCount X Y Rw x y t ω))
            / pairCount X Y Rw x y t ω) := by
  rw [ucbIndex, Nat.cast_ofNat]
  rfl

omit [NeZero mx] [NeZero my] in
/-- On the good event, the confidence bound of Lemma 11 holds for every pair already played. -/
lemma abs_sub_le_of_mem_ucbGoodEvent {δ : ℝ} {ω : Ω} (hω : ω ∈ ucbGoodEvent u δ X Y Rw)
    {t : ℕ} {x : Fin mx} {y : Fin my} (h0 : 0 < pairCount X Y Rw x y t ω) :
    |u x y - pairSum X Y Rw x y t ω / pairCount X Y Rw x y t ω| ≤
      √((4 * log (1 / δ) + 2 * log (1 + pairCount X Y Rw x y t ω)) / pairCount X Y Rw x y t ω) :=
  (Set.mem_iInter.1 (Set.mem_iInter.1 hω x) y) t h0

omit [NeZero mx] [NeZero my] in
/-- On the good event, the upper confidence bounds of Maximin-UCB are above the utility. -/
lemma le_ucbIndex_of_mem_ucbGoodEvent (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) {δ : ℝ} {ω : Ω}
    (hω : ω ∈ ucbGoodEvent u δ X Y Rw) (t : ℕ) (x : Fin mx) (y : Fin my) :
    u x y ≤ ucbIndex δ (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω) x y := by
  rw [ucbIndex_history]
  split_ifs with h0
  · exact (hu x y).2
  · have := (abs_le.1 (abs_sub_le_of_mem_ucbGoodEvent hω (Nat.pos_of_ne_zero h0))).2
    linarith

omit [NeZero mx] [NeZero my] in
/-- On the good event, the upper confidence bound of a pair already played exceeds its utility by
at most twice the confidence radius. -/
lemma ucbIndex_le_of_mem_ucbGoodEvent {δ : ℝ} {ω : Ω} (hω : ω ∈ ucbGoodEvent u δ X Y Rw)
    {t : ℕ} {x : Fin mx} {y : Fin my} (h0 : 0 < pairCount X Y Rw x y t ω) :
    ucbIndex δ (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω) x y
      ≤ u x y + 2 * √((4 * log (1 / δ) + 2 * log (1 + pairCount X Y Rw x y t ω))
        / pairCount X Y Rw x y t ω) := by
  rw [ucbIndex_history]
  simp only [h0.ne', ↓reduceIte]
  have := (abs_le.1 (abs_sub_le_of_mem_ucbGoodEvent hω h0)).1
  linarith

/-- **Number of plays of a pair with a positive gap.** On the good event, in a run of
Maximin-UCB with `δ = 1 / T` (whose action at each round maximizes `x ↦ min_y U_t(x, y)`), every
pair with `Δ_{xy} > 0` satisfies `N_T(x, y) Δ_{xy}² ≤ Δ_{xy}² + 24 log T`: at a round where it
is played, `v* ≤ U_t(x, y) ≤ u(x, y) + 2 rad_t`, so `N_t Δ_{xy}² ≤ 4 rad_t² N_t ≤ 24 log T`. -/
lemma pairCount_mul_sq_le_of_mem_ucbGoodEvent (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) {T : ℕ}
    (hT : 2 ≤ T) {ω : Ω} (hω : ω ∈ ucbGoodEvent u (1 / T) X Y Rw)
    (hmax : ∀ n < T, ∀ x,
      (fun y ↦ ucbIndex (1 / T) (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x y).min
        ≤ (fun y ↦ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) (X n ω) y).min)
    {x : Fin mx} {y : Fin my} (hxy : 0 < pairGap u x y) :
    pairCount X Y Rw x y T ω * pairGap u x y ^ 2 ≤ pairGap u x y ^ 2 + 24 * log T := by
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 ≤ log T := log_nonneg (by linarith)
  suffices h : ∀ t ≤ T, pairCount X Y Rw x y t ω * pairGap u x y ^ 2
      ≤ pairGap u x y ^ 2 + 24 * log T from h T le_rfl
  intro t
  induction t with
  | zero => intro _; simp only [pairCount_zero, Nat.cast_zero, zero_mul]; positivity
  | succ t ih =>
    intro ht
    rw [pairCount_succ]
    split_ifs with hp
    · obtain ⟨rfl, rfl⟩ := hp
      push_cast
      suffices h : pairCount X Y Rw (X t ω) (Y t ω) t ω * pairGap u (X t ω) (Y t ω) ^ 2
          ≤ 24 * log T by linarith
      set N := pairCount X Y Rw (X t ω) (Y t ω) t ω with hN
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0]; simp only [Nat.cast_zero, zero_mul]; positivity
      have hopt : pureMaximin u ≤ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) t ω) (X t ω) (Y t ω) :=
        pureMaximin_le_of_le (le_ucbIndex_of_mem_ucbGoodEvent hu hω t) (hmax t (by omega)) _
      have hU := ucbIndex_le_of_mem_ucbGoodEvent hω h0
      have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
      have hNt : (N : ℝ) + 1 ≤ T := by
        have := pairCount_le (X := X) (Y := Y) (R := Rw) (X t ω) (Y t ω) t ω
        exact_mod_cast (show N + 1 ≤ T by omega)
      have hlog1 : log (1 + N) ≤ log T := log_le_log (by linarith) (by linarith)
      have h1T : log (1 / (1 / (T : ℝ))) = log T := by rw [one_div_one_div]
      rw [h1T] at hU
      set r := √((4 * log T + 2 * log (1 + N)) / N) with hr
      have hr2 : r ^ 2 = (4 * log T + 2 * log (1 + N)) / N :=
        sq_sqrt (div_nonneg (by linarith [log_nonneg (show (1 : ℝ) ≤ 1 + N by linarith)])
          hNpos.le)
      have hgap : pairGap u (X t ω) (Y t ω) ≤ 2 * r := by unfold pairGap; linarith
      have hsq : pairGap u (X t ω) (Y t ω) ^ 2 ≤ 4 * r ^ 2 := by
        nlinarith [pow_le_pow_left₀ hxy.le hgap 2]
      rw [hr2] at hsq
      calc (N : ℝ) * pairGap u (X t ω) (Y t ω) ^ 2
          ≤ N * (4 * ((4 * log T + 2 * log (1 + N)) / N)) := by gcongr
        _ = 16 * log T + 8 * log (1 + N) := by field_simp; ring
        _ ≤ 24 * log T := by linarith
    · simp only [add_zero]
      exact ih (by omega)

/-- **Instance-dependent pathwise bound for Maximin-UCB.** On the good event, in a run of
Maximin-UCB with `δ = 1 / T`, the regret of the first `T` rounds is at most
`∑_{Δ_{xy} > 0} (Δ_{xy} + 24 log T / Δ_{xy})`. -/
lemma sum_pureMaximin_sub_le_of_mem_ucbGoodEvent (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1) {T : ℕ}
    (hT : 2 ≤ T) {ω : Ω} (hω : ω ∈ ucbGoodEvent u (1 / T) X Y Rw)
    (hmax : ∀ n < T, ∀ x,
      (fun y ↦ ucbIndex (1 / T) (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x y).min
        ≤ (fun y ↦ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) (X n ω) y).min) :
    ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))
      ≤ ∑ x, ∑ y, (if 0 < pairGap u x y then pairGap u x y + 24 * log T / pairGap u x y
        else 0) := by
  rw [sum_range_eq_sum_pairCount_mul (R := Rw) (fun x y ↦ pureMaximin u - u x y)]
  refine sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_
  change (pairCount X Y Rw x y T ω : ℝ) * pairGap u x y ≤ _
  split_ifs with h
  · have hN := pairCount_mul_sq_le_of_mem_ucbGoodEvent hu hT hω hmax h
    calc (pairCount X Y Rw x y T ω : ℝ) * pairGap u x y
        = (pairCount X Y Rw x y T ω * pairGap u x y ^ 2) / pairGap u x y := by
          field_simp
      _ ≤ (pairGap u x y ^ 2 + 24 * log T) / pairGap u x y := by gcongr
      _ = pairGap u x y + 24 * log T / pairGap u x y := by field_simp
  · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (not_lt.1 h)

/-- On the good event, in a run of Maximin-UCB with `δ = 1 / T`, the regret due to each pair is
at most `2 + √(24 log T N_T(x, y))`. -/
lemma pairCount_mul_pairGap_le_of_mem_ucbGoodEvent (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1)
    {T : ℕ} (hT : 2 ≤ T) {ω : Ω} (hω : ω ∈ ucbGoodEvent u (1 / T) X Y Rw)
    (hmax : ∀ n < T, ∀ x,
      (fun y ↦ ucbIndex (1 / T) (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x y).min
        ≤ (fun y ↦ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) (X n ω) y).min)
    (x : Fin mx) (y : Fin my) :
    (pairCount X Y Rw x y T ω : ℝ) * pairGap u x y
      ≤ 2 + √(24 * log T) * √(pairCount X Y Rw x y T ω) := by
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 ≤ log T := log_nonneg (by linarith)
  have hR : 0 ≤ 2 + √(24 * log T) * √(pairCount X Y Rw x y T ω) := by positivity
  rcases le_or_gt (pairGap u x y) 0 with h | h
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h).trans hR
  have hN := pairCount_mul_sq_le_of_mem_ucbGoodEvent hu hT hω hmax h
  have h2 := pairGap_le_two hu x y
  set N : ℝ := (pairCount X Y Rw x y T ω : ℝ) with hN_def
  set Δ := pairGap u x y with hΔ
  rcases lt_or_ge N 1 with hN1 | hN1
  · have h0 : pairCount X Y Rw x y T ω = 0 := by
      have : (pairCount X Y Rw x y T ω : ℝ) < 1 := hN1
      exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
    rw [hN_def, h0, Nat.cast_zero, zero_mul]
    positivity
  have h1 : ((N - 1) * Δ) ^ 2 ≤ 24 * log T * N := by
    have ha : (N - 1) * Δ ^ 2 ≤ 24 * log T := by linarith
    calc ((N - 1) * Δ) ^ 2 = (N - 1) * ((N - 1) * Δ ^ 2) := by ring
      _ ≤ (N - 1) * (24 * log T) := mul_le_mul_of_nonneg_left ha (by linarith)
      _ ≤ 24 * log T * N := by nlinarith
  have h3 : (N - 1) * Δ ≤ √(24 * log T) * √N := by
    rw [← sqrt_mul (by positivity)]
    exact (le_abs_self _).trans (abs_le_sqrt h1)
  linarith

/-- **Worst-case pathwise bound for Maximin-UCB.** On the good event, in a run of Maximin-UCB with
`δ = 1 / T`, the regret of the first `T` rounds is at most `2 m_x m_y + √(24 m_x m_y T log T)`
(Cauchy–Schwarz over the action pairs). -/
lemma sum_pureMaximin_sub_le_sqrt_of_mem_ucbGoodEvent (hu : ∀ x y, u x y ∈ Set.Icc (-1) 1)
    {T : ℕ} (hT : 2 ≤ T) {ω : Ω} (hω : ω ∈ ucbGoodEvent u (1 / T) X Y Rw)
    (hmax : ∀ n < T, ∀ x,
      (fun y ↦ ucbIndex (1 / T) (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) x y).min
        ≤ (fun y ↦ ucbIndex (1 / T)
          (history (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) n ω) (X n ω) y).min) :
    ∑ t ∈ range T, (pureMaximin u - u (X t ω) (Y t ω))
      ≤ 2 * mx * my + √(24 * log T) * (√(mx * my) * √T) := by
  rw [sum_range_eq_sum_pairCount_mul (R := Rw) (fun x y ↦ pureMaximin u - u x y)]
  have hCS : ∑ x, ∑ y, √(pairCount X Y Rw x y T ω : ℝ) ≤ √(mx * my) * √T := by
    have := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin mx × Fin my))
      (f := fun _ ↦ (1 : ℝ)) (g := fun p ↦ (pairCount X Y Rw p.1 p.2 T ω : ℝ))
      (fun _ ↦ zero_le_one) (fun _ ↦ Nat.cast_nonneg _)
    simp only [sqrt_one, one_mul, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at this
    simp only [Fintype.sum_prod_type] at this
    rw [sum_pairCount] at this
    push_cast at this
    exact this
  calc ∑ x, ∑ y, (pairCount X Y Rw x y T ω : ℝ) * (pureMaximin u - u x y)
      ≤ ∑ x : Fin mx, ∑ y : Fin my, (2 + √(24 * log T) * √(pairCount X Y Rw x y T ω)) :=
        sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦
          pairCount_mul_pairGap_le_of_mem_ucbGoodEvent hu hT hω hmax x y
    _ = 2 * mx * my + √(24 * log T) * ∑ x, ∑ y, √(pairCount X Y Rw x y T ω : ℝ) := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_sum]
        ring
    _ ≤ 2 * mx * my + √(24 * log T) * (√(mx * my) * √T) := by gcongr

end Ito2026Adversarial
