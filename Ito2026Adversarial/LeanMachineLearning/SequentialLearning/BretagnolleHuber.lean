/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.InformationTheory.KullbackLeibler.BretagnolleHuber
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# The Bretagnolle–Huber inequality for the actions of sequential algorithms

For two sequences of rounds `(O, A, Y)` under `P` and `(O', A', Y')` under `P'` (for instance two
runs of an algorithm against two environments), the Bretagnolle–Huber inequality applied to the
laws of the histories of the first `M` rounds bounds from below the probability that the actions
of a round `t < M` differ in the two sequences: for a measurable set `s` of actions,
`P(A t ∈ s) + P'(A' t ∉ s) ≥ exp(-KL) / 2`, where `KL` is the divergence between the laws of the
two histories. Summed over the rounds, this is the step of bandit lower bounds that turns a bound
on the divergence (from the divergence decomposition) into a bound on the expected numbers of
rounds in which the actions are in `s`.

## Main statements

* `exp_neg_klDiv_map_history_div_two_le`: the inequality for one round.
* `mul_exp_neg_klDiv_map_history_div_two_le_sum`: the inequality summed over the rounds `t < M`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real
open scoped ENNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨} {M : ℕ} {s : Set 𝓐}

/-- **Bretagnolle–Huber inequality for the action of a round.** If the laws of the histories of
the first `M` rounds of two sequences of rounds are at finite divergence `KL`, then for a round
`t < M` and a measurable set `s` of actions, `exp(-KL) / 2 ≤ P(A t ∈ s) + P'(A' t ∉ s)`. -/
lemma exp_neg_klDiv_map_history_div_two_le (hH : Measurable (history O A Y M))
    (hH' : Measurable (history O' A' Y' M)) {t : ℕ} (ht : t < M) (hs : MeasurableSet s)
    (h : klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) ≠ ∞) :
    exp (-(klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M))).toReal) / 2
      ≤ P.real (A t ⁻¹' s) + P'.real (A' t ⁻¹' sᶜ) := by
  have hE : MeasurableSet {h : Hist 𝓞 𝓐 𝓨 M | (h ⟨t, ht⟩).action ∈ s} :=
    (Round.measurable_action.comp (measurable_pi_apply _)) hs
  have h_bh := bretagnolle_huber hE h
  rwa [map_measureReal_apply hH hE, map_measureReal_apply hH' hE.compl] at h_bh

/-- **Bretagnolle–Huber inequality for the actions**, summed over the rounds: if the laws of the
histories of the first `M` rounds of two sequences of rounds are at finite divergence `KL`, then
for a measurable set `s` of actions, the expected number of rounds `t < M` with `A t ∈ s` plus the
expected number of rounds `t < M` with `A' t ∉ s` is at least `M exp(-KL) / 2`. -/
lemma mul_exp_neg_klDiv_map_history_div_two_le_sum (hH : Measurable (history O A Y M))
    (hH' : Measurable (history O' A' Y' M)) (hs : MeasurableSet s)
    (h : klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) ≠ ∞) :
    M * (exp (-(klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M))).toReal) / 2)
      ≤ ∑ t ∈ range M, P.real (A t ⁻¹' s) + ∑ t ∈ range M, P'.real (A' t ⁻¹' sᶜ) := by
  rw [← sum_add_distrib]
  refine le_of_eq_of_le (by simp) (sum_le_sum fun t ht ↦
    exp_neg_klDiv_map_history_div_two_le hH hH' (mem_range.1 ht) hs h)

end Learning
