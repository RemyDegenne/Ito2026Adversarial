/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Lemma9
public import Ito2026Adversarial.LeanMachineLearning.Game.Oblivious
public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.BretagnolleHuber
public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The construction of the lower bound for uninformed learners (Theorem 2)

The two games of the proof of Theorem 2 (Ito, Luo, Maiti, Tsuchiya, Wu 2026, Appendix C) are the
`2 × 2` games `lbGame Δr Δc K b` whose row `b` is `(-Δr, K - Δr)` and whose other row is `(0, Δc)`:
`lbGame Δr Δc K 1` is the paper's `A` and `lbGame Δr Δc K 0` its `B`. The other row and the first
column form a strict PSNE with value `0` and gaps `Δr`, `Δc`. The adversary is oblivious: it plays
`y_t ∼ (1 - ε, ε)` for `t < T'` and `y* = 0` afterwards (`lbOppLaw ε T'`), and the rewards are
two-point (`twoPointNoise`).

Against this adversary, an uninformed learner faces in the game `lbGame Δr Δc K b` the
non-stationary bandit with two-point rewards of means `lbMean Δr Δc K b ε` before `T'`; the two
bandits (`b = 0, 1`) differ by `δ = ε Δc - K ε + Δr` in each arm, so that by the divergence
decomposition and Lemma 9 the laws of the histories of the first `T'` rounds are at divergence at
most `T' δ²`. When `T' δ² ≤ 1`, the Bretagnolle–Huber inequality shows that the learner plays the
bad row `b` in at least `T' / 12` of the first `T'` rounds in expectation in one of the two games,
which gives a PSMR of at least `T' ((Δr - K ε) / 12 - (11 / 12) ε Δc)` there
(`exists_psmr_ge_of_le_one`).

## Main definitions

* `lbGame Δr Δc K b`: the games of the lower bound.
* `lbOppLaw ε T' n`: the law of the adversary's action at round `n`.
* `lbMean Δr Δc K b e x`: the mean utility of the row `x` against the mixed strategy `(1 - e, e)`.

## Main statements

* `isStrictPSNE_lbGame`, `rowGapMin_lbGame`, `colGapMin_lbGame`: the strict PSNE and its gaps.
* `psmr_lbGame_ge`: the PSMR in terms of the expected number of rounds in which the
  bad row is played.
* `klDiv_map_history_lbGame_le`: the divergence between the laws of the histories of
  the first `T'` rounds in the two games.
* `exists_psmr_ge_of_le_one`: the lower bound for given parameters `K`, `ε`, `T'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real Learning Learning.ZeroSumGame
  Learning.RepeatedGame InformationTheory unitInterval

universe u

namespace Ito2026Adversarial

/-! ### The games and the adversary -/

/-- The games of the lower bound: the row `b` is `(-Δr, K - Δr)` and the other row is `(0, Δc)`.
`lbGame Δr Δc K 1` is the paper's game `A` and `lbGame Δr Δc K 0` its game `B`. -/
def lbGame (Δr Δc K : ℝ) (b x y : Fin 2) : ℝ :=
  if x = b then (if y = 0 then -Δr else K - Δr) else (if y = 0 then 0 else Δc)

/-- The law of the action of the adversary of the lower bound at round `n`: `(1 - ε, ε)` for
`n < T'` and the equilibrium action `0` afterwards. -/
noncomputable def lbOppLaw (ε : I) (T' n : ℕ) : Measure (Fin 2) :=
  bernoulliMeasure 1 0 (if n < T' then ε else 0)

instance (ε : I) (T' n : ℕ) : IsProbabilityMeasure (lbOppLaw ε T' n) := by
  unfold lbOppLaw; infer_instance

/-- The mean utility of the row `x` of the game `lbGame Δr Δc K b` against the mixed strategy
`(1 - e, e)` of the adversary. -/
def lbMean (Δr Δc K : ℝ) (b : Fin 2) (e : ℝ) (x : Fin 2) : ℝ :=
  if x = b then K * e - Δr else e * Δc

variable {Δr Δc K : ℝ} {b x₀ : Fin 2}

/-- Two elements of `Fin 2` different from the same element are equal. -/
lemma fin_two_eq_of_ne {a x y : Fin 2} (hx : x ≠ a) (hy : y ≠ a) : x = y := by omega

/-- The infimum over the elements of `Fin 2` other than `a` is the value at the other element. -/
lemma iInf_ne_fin_two (f : Fin 2 → ℝ) {a c : Fin 2} (hc : c ≠ a) :
    ⨅ x : {x : Fin 2 // x ≠ a}, f x = f c := by
  let : Unique {x : Fin 2 // x ≠ a} :=
    { default := ⟨c, hc⟩, uniq := fun x ↦ Subtype.ext (fin_two_eq_of_ne x.2 hc) }
  exact ciInf_unique (ι := {x : Fin 2 // x ≠ a}) (s := fun x ↦ f x)

/-- The utilities of the games of the lower bound lie in `[-1, 1]`. -/
lemma lbGame_mem_Icc (hΔr : Δr ∈ Set.Ioc 0 1) (hΔc : Δc ∈ Set.Ioc 0 1)
    (hK : K - Δr ∈ Set.Icc (-1) 1) (b x y : Fin 2) : lbGame Δr Δc K b x y ∈ Set.Icc (-1) 1 := by
  obtain ⟨hΔr0, hΔr1⟩ := hΔr
  obtain ⟨hΔc0, hΔc1⟩ := hΔc
  unfold lbGame
  split_ifs
  · exact ⟨by linarith, by linarith⟩
  · exact hK
  · exact ⟨by norm_num, by norm_num⟩
  · exact ⟨by linarith, hΔc1⟩

/-- The good row `x₀ ≠ b` and the first column form a strict PSNE of `lbGame Δr Δc K b`. -/
lemma isStrictPSNE_lbGame (hΔr : 0 < Δr) (hΔc : 0 < Δc) (hx₀ : x₀ ≠ b) :
    IsStrictPSNE (lbGame Δr Δc K b) x₀ 0 := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · rw [fin_two_eq_of_ne hx hx₀.symm]
    simp [lbGame, hx₀, hΔr]
  · rw [fin_two_eq_of_ne hy (show (1 : Fin 2) ≠ 0 by decide)]
    simp [lbGame, hx₀, hΔc]

/-- The pure-strategy maximin value of the games of the lower bound is `0`. -/
lemma pureMaximin_lbGame (hΔr : 0 < Δr) (hΔc : 0 < Δc) (hx₀ : x₀ ≠ b) :
    pureMaximin (lbGame Δr Δc K b) = 0 := by
  rw [(isStrictPSNE_lbGame (K := K) hΔr hΔc hx₀).isPSNE.pureMaximin_eq]
  simp [lbGame, hx₀]

/-- The minimal row gap of the strict PSNE of `lbGame Δr Δc K b` is `Δr`. -/
lemma rowGapMin_lbGame (hx₀ : x₀ ≠ b) : rowGapMin (lbGame Δr Δc K b) x₀ 0 = Δr := by
  rw [rowGapMin, iInf_ne_fin_two (fun x ↦ rowGap (lbGame Δr Δc K b) x₀ 0 x) hx₀.symm]
  simp [rowGap, lbGame, hx₀]

/-- The minimal column gap of the strict PSNE of `lbGame Δr Δc K b` is `Δc`. -/
lemma colGapMin_lbGame (hx₀ : x₀ ≠ b) : colGapMin (lbGame Δr Δc K b) x₀ 0 = Δc := by
  rw [colGapMin, iInf_ne_fin_two (fun y ↦ colGap (lbGame Δr Δc K b) x₀ 0 y)
    (show (1 : Fin 2) ≠ 0 by decide)]
  simp [colGap, lbGame, hx₀]

/-- The expected utility of a row of `lbGame` against the mixed strategy `(1 - p, p)`, relative to
a value `v`. -/
lemma sum_bernoulliMeasure_mul_sub_lbGame (p : I) (v : ℝ) (b x : Fin 2) :
    ∑ y, (bernoulliMeasure 1 0 p).real {y} * (v - lbGame Δr Δc K b x y)
      = v - lbMean Δr Δc K b p x := by
  rw [Fin.sum_univ_two, bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _)
    (by simp) (by simp), bernoulliMeasure_real_apply_of_mem_of_notMem _
    (measurableSet_singleton _) (by simp) (by simp)]
  unfold lbGame lbMean
  split_ifs <;> simp_all <;> ring

/-- The expected utility of a row of `lbGame` against the mixed strategy `(1 - p, p)`. -/
lemma sum_bernoulliMeasure_mul_lbGame (p : I) (b x : Fin 2) :
    ∑ y, (bernoulliMeasure 1 0 p).real {y} * lbGame Δr Δc K b x y = lbMean Δr Δc K b p x := by
  have h := sum_bernoulliMeasure_mul_sub_lbGame (Δr := Δr) (Δc := Δc) (K := K) p 0 b x
  simp only [zero_sub, mul_neg, sum_neg_distrib, neg_inj] at h
  exact h

/-- Against the adversary of the lower bound, an uninformed learner in the game `lbGame Δr Δc K b`
faces the non-stationary bandit with two-point rewards of means `lbMean Δr Δc K b ε`
before `T'`. -/
lemma obliviousBandit_lbGame (hΔr : Δr ∈ Set.Ioc 0 1) (hΔc : Δc ∈ Set.Ioc 0 1)
    (hK : K - Δr ∈ Set.Icc (-1) 1) (ε : I) (T' n : ℕ) (b x : Fin 2) :
    obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K b)) n x
      = twoPoint (lbMean Δr Δc K b ((if n < T' then ε else 0 : I) : ℝ) x) := by
  rw [obliviousBandit_twoPointNoise (lbGame_mem_Icc hΔr hΔc hK b), lbOppLaw,
    sum_bernoulliMeasure_mul_lbGame]

/-! ### The PSMR in terms of the number of plays of the bad row -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → Fin 2} {Y : ℕ → Ω → Fin 2} {Rw : ℕ → Ω → ℝ} {ε : I} {T T' : ℕ}

/-- In the game `lbGame Δr Δc K b` against the adversary of the lower bound, the PSMR after `T ≥ T'`
rounds is at least `(Δr - K ε + ε Δc) N_b - T' ε Δc`, where `N_b` is the expected number of rounds
`t < T'` in which the bad row `b` is played. -/
lemma psmr_lbGame_ge {pl : Player (Fin 2) (Fin 2)}
    {R : RewardKernel (Fin 2) (Fin 2)} [∀ n, IsMarkovKernel (R n)]
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) pl
      (gameEnv (Player.oblivious (lbOppLaw ε T')) R) P)
    (hΔr : 0 < Δr) (hΔc : 0 < Δc) (hx₀ : x₀ ≠ b) (hT' : T' ≤ T) :
    (Δr - K * ε + ε * Δc) * ∑ t ∈ range T', P.real (X t ⁻¹' {b}) - T' * (ε * Δc)
      ≤ psmr (lbGame Δr Δc K b) X Y P T := by
  have hone (t : ℕ) : P.real (X t ⁻¹' {b}) + P.real (X t ⁻¹' {x₀}) = 1 := by
    have h_sum := sum_measureReal_singleton (μ := P.map (X t)) Finset.univ
    simp only [Finset.coe_univ, probReal_univ, Fin.sum_univ_two,
      map_measureReal_apply (h.measurable_action t) (measurableSet_singleton _)] at h_sum
    fin_cases b <;> fin_cases x₀ <;> simp_all [add_comm]
  have hterm (t : ℕ) : ∑ x, P.real (X t ⁻¹' {x}) * ∑ y, (lbOppLaw ε T' t).real {y} *
        (pureMaximin (lbGame Δr Δc K b) - lbGame Δr Δc K b x y)
      = P.real (X t ⁻¹' {b}) * (Δr - K * ((if t < T' then ε else 0 : I) : ℝ))
        - P.real (X t ⁻¹' {x₀}) * (((if t < T' then ε else 0 : I) : ℝ) * Δc) := by
    simp_rw [lbOppLaw, sum_bernoulliMeasure_mul_sub_lbGame, pureMaximin_lbGame hΔr hΔc hx₀]
    rw [Fin.sum_univ_two]
    fin_cases b <;> fin_cases x₀ <;> simp_all [lbMean] <;> ring
  have hA (t : ℕ) (ht : t ∈ range T') :
      P.real (X t ⁻¹' {b}) * (Δr - K * ((if t < T' then ε else 0 : I) : ℝ))
        - P.real (X t ⁻¹' {x₀}) * (((if t < T' then ε else 0 : I) : ℝ) * Δc)
      = (Δr - K * ε + ε * Δc) * P.real (X t ⁻¹' {b}) - ε * Δc := by
    simp only [mem_range.1 ht, ↓reduceIte]
    linear_combination (-(ε * Δc : ℝ)) * hone t
  have hB (t : ℕ) (ht : t ∈ Ico T' T) :
      0 ≤ P.real (X t ⁻¹' {b}) * (Δr - K * ((if t < T' then ε else 0 : I) : ℝ))
        - P.real (X t ⁻¹' {x₀}) * (((if t < T' then ε else 0 : I) : ℝ) * Δc) := by
    simp only [show ¬ t < T' by simp only [mem_Ico] at ht; omega, ↓reduceIte, Set.Icc.coe_zero,
      mul_zero, sub_zero, zero_mul]
    exact mul_nonneg measureReal_nonneg hΔr.le
  rw [h.psmr_eq_sum_oblivious, Finset.sum_congr rfl fun t _ ↦ hterm t,
    ← Finset.sum_range_add_sum_Ico _ hT', Finset.sum_congr rfl hA, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_const, card_range, nsmul_eq_mul]
  linarith [Finset.sum_nonneg hB]

/-! ### The divergence between the two games and the Bretagnolle–Huber inequality -/

section TwoRuns

variable {alg : Algorithm Unit (Fin 2) ℝ} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {X' : ℕ → Ω' → Fin 2} {Rw' : ℕ → Ω' → ℝ}

/-- In the first `T'` rounds, the two-point rewards of an arm of the two bandits faced by an
uninformed learner in the games `lbGame Δr Δc K 1` and `lbGame Δr Δc K 0` are at divergence at
most `δ²`, `δ = ε Δc - K ε + Δr` (Lemma 9). -/
lemma klDiv_obliviousBandit_lbGame_le (hΔr : Δr ∈ Set.Ioc 0 1) (hΔc : Δc ∈ Set.Ioc 0 1)
    (hK : K - Δr ∈ Set.Icc (-1) 1) (ha : |ε * Δc| ≤ 1 / 2) (hb : |K * ε - Δr| ≤ 1 / 2) {t : ℕ}
    (ht : t < T') (x : Fin 2) :
    klDiv (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 1)) t x)
        (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 0)) t x)
      ≤ ENNReal.ofReal ((ε * Δc - K * ε + Δr) ^ 2) := by
  rw [obliviousBandit_lbGame hΔr hΔc hK, obliviousBandit_lbGame hΔr hΔc hK]
  simp only [ht, ↓reduceIte]
  fin_cases x
  · refine (klDiv_twoPoint_le ha hb).trans (le_of_eq ?_)
    congr 1
    ring
  · refine (klDiv_twoPoint_le hb ha).trans (le_of_eq ?_)
    congr 1
    ring

/-- **Divergence decomposition for the lower bound.** The laws of the histories of the first `T'`
rounds of an uninformed learner against the two bandits of the games `lbGame Δr Δc K 1` and
`lbGame Δr Δc K 0` are at divergence at most `T' δ²`, `δ = ε Δc - K ε + Δr`. -/
lemma klDiv_map_history_lbGame_le (hΔr : Δr ∈ Set.Ioc 0 1)
    (hΔc : Δc ∈ Set.Ioc 0 1) (hK : K - Δr ∈ Set.Icc (-1) 1) (ha : |ε * Δc| ≤ 1 / 2)
    (hb : |K * ε - Δr| ≤ 1 / 2)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X Rw alg (Environment.banditSeq
      (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 1)))) P)
    (h' : IsAlgEnvSeq (fun _ _ ↦ ()) X' Rw' alg (Environment.banditSeq
      (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 0)))) P') :
    klDiv (P.map (history (fun _ _ ↦ ()) X Rw T')) (P'.map (history (fun _ _ ↦ ()) X' Rw' T'))
      ≤ ENNReal.ofReal (T' * (ε * Δc - K * ε + Δr) ^ 2) := by
  rw [h.klDiv_map_history_banditSeq h' T']
  calc ∑ t ∈ range T', ∫⁻ ω,
        klDiv (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 1)) t (X t ω))
          (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 0)) t (X t ω)) ∂P
      ≤ ∑ t ∈ range T', ENNReal.ofReal ((ε * Δc - K * ε + Δr) ^ 2) := by
        refine sum_le_sum fun t ht ↦ (lintegral_mono fun ω ↦
          klDiv_obliviousBandit_lbGame_le hΔr hΔc hK ha hb (mem_range.1 ht) (X t ω)).trans ?_
        simp
    _ = ENNReal.ofReal (T' * (ε * Δc - K * ε + Δr) ^ 2) := by
        rw [sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **Bretagnolle–Huber step of the lower bound.** If `T' δ² ≤ 1`, the expected number of rounds
`t < T'` in which an uninformed learner plays the row `1` against the bandit of the game
`lbGame Δr Δc K 1`, plus the expected number of rounds `t < T'` in which it plays the row `0`
against the bandit of the game `lbGame Δr Δc K 0`, is at least `T' / 6`. -/
lemma div_six_le_sum_lbGame (hΔr : Δr ∈ Set.Ioc 0 1)
    (hΔc : Δc ∈ Set.Ioc 0 1) (hK : K - Δr ∈ Set.Icc (-1) 1) (ha : |ε * Δc| ≤ 1 / 2)
    (hb : |K * ε - Δr| ≤ 1 / 2) (hδ : T' * ((ε : ℝ) * Δc - K * ε + Δr) ^ 2 ≤ 1)
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) X Rw alg (Environment.banditSeq
      (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 1)))) P)
    (h' : IsAlgEnvSeq (fun _ _ ↦ ()) X' Rw' alg (Environment.banditSeq
      (obliviousBandit (lbOppLaw ε T') (twoPointNoise (lbGame Δr Δc K 0)))) P') :
    (T' : ℝ) / 6
      ≤ ∑ t ∈ range T', P.real (X t ⁻¹' {1}) + ∑ t ∈ range T', P'.real (X' t ⁻¹' {0}) := by
  have hKL := (klDiv_map_history_lbGame_le hΔr hΔc hK ha hb h h').trans
    (ENNReal.ofReal_le_one.2 hδ)
  have hne := ne_top_of_le_ne_top ENNReal.one_ne_top hKL
  have hBH := mul_exp_neg_klDiv_map_history_div_two_le_sum (h.measurable_history T')
    (h'.measurable_history T') (measurableSet_singleton 1) hne
  have hcompl : ({1}ᶜ : Set (Fin 2)) = {0} := by
    ext x
    fin_cases x <;> simp
  rw [hcompl] at hBH
  have hle : (klDiv (P.map (history (fun _ _ ↦ ()) X Rw T'))
      (P'.map (history (fun _ _ ↦ ()) X' Rw' T'))).toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).2 hKL
  have hexp : 1 / 3 ≤ exp (-(klDiv (P.map (history (fun _ _ ↦ ()) X Rw T'))
      (P'.map (history (fun _ _ ↦ ()) X' Rw' T'))).toReal) := by
    calc (1 : ℝ) / 3 ≤ exp (-1) := by
          rw [exp_neg, one_div]
          exact inv_anti₀ (exp_pos 1) exp_one_lt_three.le
      _ ≤ _ := exp_le_exp.2 (by linarith)
  have hT'0 : (0 : ℝ) ≤ T' := Nat.cast_nonneg _
  nlinarith

end TwoRuns

/-! ### The lower bound for given parameters -/

/-- **The lower bound for given parameters** `K`, `ε`, `T' ≤ T` with `T' δ² ≤ 1`,
`δ = ε Δc - K ε + Δr`: for every uninformed learner, in one of the two games `lbGame Δr Δc K b`
against the adversary of the lower bound, the PSMR after `T` rounds is at least
`T' ((Δr - K ε) / 12 - (11 / 12) ε Δc)`. The game depends on the learner: it is `lbGame Δr Δc K 1`
if the learner plays its bad row `1` in at least `T' / 12` of the first `T'` rounds in expectation
in every run, and `lbGame Δr Δc K 0` otherwise, by the Bretagnolle–Huber step. -/
lemma exists_psmr_ge_of_le_one (hΔr : Δr ∈ Set.Ioc 0 1) (hΔc : Δc ∈ Set.Ioc 0 1)
    (hK : K - Δr ∈ Set.Icc (-1) 1) (hKε : K * ε ≤ Δr) (ha : |ε * Δc| ≤ 1 / 2)
    (hb : |K * ε - Δr| ≤ 1 / 2) (hδ : T' * ((ε : ℝ) * Δc - K * ε + Δr) ^ 2 ≤ 1) (hT' : T' ≤ T)
    (alg : Algorithm Unit (Fin 2) ℝ) :
    ∃ (u : Fin 2 → Fin 2 → ℝ) (x₀ y₀ : Fin 2), (∀ x y, u x y ∈ Set.Icc (-1) 1) ∧
      IsStrictPSNE u x₀ y₀ ∧ rowGapMin u x₀ y₀ = Δr ∧ colGapMin u x₀ y₀ = Δc ∧
      ∃ (opp : Player (Fin 2) (Fin 2)) (R : RewardKernel (Fin 2) (Fin 2))
        (_ : ∀ n, IsMarkovKernel (R n)),
        RewardKernel.HasMean R u ∧ RewardKernel.RewardsIn R (Set.Icc (-1) 1) ∧
        ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
          (X : ℕ → Ω → Fin 2) (Y : ℕ → Ω → Fin 2) (Rw : ℕ → Ω → ℝ),
          IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω))
            (Player.ofUninformed alg) (gameEnv opp R) P →
          T' * ((Δr - K * ε) / 12 - 11 / 12 * (ε * Δc)) ≤ psmr u X Y P T := by
  have hfinal (N : ℝ) (hN : T' / 12 ≤ N) :
      T' * ((Δr - K * ε) / 12 - 11 / 12 * (ε * Δc))
        ≤ (Δr - K * ε + ε * Δc) * N - T' * (ε * Δc) := by
    have hεΔc : 0 ≤ (ε : ℝ) * Δc := mul_nonneg ε.2.1 hΔc.1.le
    nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ Δr - K * ε + ε * Δc by linarith)]
  by_cases hA : ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → Fin 2) (Y : ℕ → Ω → Fin 2) (Rw : ℕ → Ω → ℝ),
      IsAlgEnvSeq (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, Rw t ω)) (Player.ofUninformed alg)
        (gameEnv (Player.oblivious (lbOppLaw ε T'))
          (stationaryReward (twoPointNoise (lbGame Δr Δc K 1)))) P →
      (T' : ℝ) / 12 ≤ ∑ t ∈ range T', P.real (X t ⁻¹' {1})
  · refine ⟨lbGame Δr Δc K 1, 0, 0, lbGame_mem_Icc hΔr hΔc hK 1,
      isStrictPSNE_lbGame hΔr.1 hΔc.1 (by decide), rowGapMin_lbGame (by decide),
      colGapMin_lbGame (by decide), Player.oblivious (lbOppLaw ε T'),
      stationaryReward (twoPointNoise (lbGame Δr Δc K 1)), inferInstance,
      hasMean_stationaryReward_twoPointNoise (lbGame_mem_Icc hΔr hΔc hK 1),
      rewardsIn_stationaryReward_twoPointNoise _, ?_⟩
    intro Ω mΩ P _ X Y Rw h
    exact (hfinal _ (hA P X Y Rw h)).trans
      (psmr_lbGame_ge (x₀ := 0) h hΔr.1 hΔc.1 (by decide) hT')
  · push Not at hA
    obtain ⟨Ω₁, mΩ₁, P₁, hP₁, X₁, Y₁, Rw₁, h₁, hlt⟩ := hA
    refine ⟨lbGame Δr Δc K 0, 1, 0, lbGame_mem_Icc hΔr hΔc hK 0,
      isStrictPSNE_lbGame hΔr.1 hΔc.1 (by decide), rowGapMin_lbGame (by decide),
      colGapMin_lbGame (by decide), Player.oblivious (lbOppLaw ε T'),
      stationaryReward (twoPointNoise (lbGame Δr Δc K 0)), inferInstance,
      hasMean_stationaryReward_twoPointNoise (lbGame_mem_Icc hΔr hΔc hK 0),
      rewardsIn_stationaryReward_twoPointNoise _, ?_⟩
    intro Ω mΩ P _ X Y Rw h
    have hsum := div_six_le_sum_lbGame hΔr hΔc hK ha hb hδ h₁.isAlgEnvSeq_banditSeq_oblivious
      h.isAlgEnvSeq_banditSeq_oblivious
    exact (hfinal _ (by linarith)).trans
      (psmr_lbGame_ge (x₀ := 1) h hΔr.1 hΔc.1 (by decide) hT')

end Ito2026Adversarial
