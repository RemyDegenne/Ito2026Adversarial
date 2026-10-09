/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition

/-!
# The divergence decomposition for non-stationary bandits

Complements to LML's `LeanMachineLearning.SequentialLearning.DivergenceDecomposition`, which
proves the chain rule for the history of a fixed number of rounds
(`IsAlgEnvSeq.klDiv_map_history_stepKernel`) and the divergence decomposition for two stationary
environments. This file is the section `NonstationaryBandit` of the LMLPapers file
`LMLPapers.LeanMachineLearning.SequentialLearning.DivergenceDecomposition` (the rest of that file,
on stopped histories, is not needed here).

For a single algorithm run against two non-stationary bandits `Environment.banditSeq ν` and
`Environment.banditSeq ν'`, the step kernels of round `t` share the observation kernel and the
policy and differ only in the reward kernels `ν t` and `ν' t`, so the divergence between the laws
of the histories of the first `M` rounds is `∑_{t < M} E[KL(ν t (X t) ‖ ν' t (X t))]`.

## Main statements

* `stepKernel_banditSeq`, `IsAlgEnvSeq.klDiv_map_history_compProd_banditSeq`,
  `IsAlgEnvSeq.klDiv_map_history_banditSeq`, `IsAlgEnvSeq.klDiv_map_history_banditSeq_eq_sum`:
  the divergence decomposition for a fixed number of rounds against two non-stationary bandits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}

section NonstationaryBandit

variable {ν ν' : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)] [∀ n, IsMarkovKernel (ν' n)]

/-- The step kernel of round `n` of an algorithm against the non-stationary bandit
`Environment.banditSeq ν`: a trivial observation, the policy, then the reward kernel `ν n`. -/
lemma stepKernel_banditSeq (alg : Algorithm Unit 𝓐 𝓨) (n : ℕ) :
    stepKernel alg (Environment.banditSeq ν) n
      = Kernel.const _ (Measure.dirac ()) ⊗ₖ (alg.policy n ⊗ₖ (ν n).prodMkLeft _) := by
  rw [stepKernel_def, obs_banditSeq, feedback_banditSeq]

/-- **Divergence decomposition for non-stationary bandits**, in composition-product form: the
divergence between the laws of the histories of the first `M` rounds of an algorithm against the
non-stationary bandits `ν` and `ν'` is `∑_{t < M} KL(P_{X t} ⊗ ν t ‖ P_{X t} ⊗ ν' t)`, where
`P_{X t}` is the law of the action of round `t` against `ν`. -/
lemma IsAlgEnvSeq.klDiv_map_history_compProd_banditSeq {alg : Algorithm Unit 𝓐 𝓨}
    {O : ℕ → Ω → Unit} {O' : ℕ → Ω' → Unit}
    (h : IsAlgEnvSeq O X Y alg (Environment.banditSeq ν) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.banditSeq ν') P') (M : ℕ) :
    klDiv (P.map (history O X Y M)) (P'.map (history O' X' Y' M)) =
      ∑ t ∈ range M, klDiv (P.map (X t) ⊗ₘ ν t) (P.map (X t) ⊗ₘ ν' t) := by
  rw [h.klDiv_map_history_stepKernel h']
  refine sum_congr rfl fun t _ ↦ ?_
  have h_obs := (h.hasCondDistrib_obs t).map_eq
  rw [obs_banditSeq] at h_obs
  rw [stepKernel_banditSeq, stepKernel_banditSeq,
    klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd, ← h_obs,
    ← (h.hasCondDistrib_action t).hasLaw_comp.map_eq]

/-- **Divergence decomposition for non-stationary bandits**: the divergence between the laws of
the histories of the first `M` rounds of an algorithm against the non-stationary bandits `ν` and
`ν'` is `∑_{t < M} E[KL(ν t (X t) ‖ ν' t (X t))]`, the expectation being along the first
sequence. -/
lemma IsAlgEnvSeq.klDiv_map_history_banditSeq [MeasurableSpace.CountablyGenerated 𝓨]
    {alg : Algorithm Unit 𝓐 𝓨} {O : ℕ → Ω → Unit} {O' : ℕ → Ω' → Unit}
    (h : IsAlgEnvSeq O X Y alg (Environment.banditSeq ν) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.banditSeq ν') P') (M : ℕ) :
    klDiv (P.map (history O X Y M)) (P'.map (history O' X' Y' M)) =
      ∑ t ∈ range M, ∫⁻ ω, klDiv (ν t (X t ω)) (ν' t (X t ω)) ∂P := by
  rw [h.klDiv_map_history_compProd_banditSeq h']
  refine sum_congr rfl fun t _ ↦ ?_
  rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel (ν t) (ν' t)) (h.measurable_action t)]

/-- **Divergence decomposition for non-stationary bandits with finitely many arms**: the
divergence between the laws of the histories of the first `M` rounds of an algorithm against the
non-stationary bandits `ν` and `ν'` is `∑_{t < M} ∑_a P(X t = a) KL(ν t a ‖ ν' t a)`. -/
lemma IsAlgEnvSeq.klDiv_map_history_banditSeq_eq_sum [Fintype 𝓐] [MeasurableSingletonClass 𝓐]
    [MeasurableSpace.CountablyGenerated 𝓨] {alg : Algorithm Unit 𝓐 𝓨} {O : ℕ → Ω → Unit}
    {O' : ℕ → Ω' → Unit}
    (h : IsAlgEnvSeq O X Y alg (Environment.banditSeq ν) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.banditSeq ν') P') (M : ℕ) :
    klDiv (P.map (history O X Y M)) (P'.map (history O' X' Y' M)) =
      ∑ t ∈ range M, ∑ a, P {ω | X t ω = a} * klDiv (ν t a) (ν' t a) := by
  rw [h.klDiv_map_history_compProd_banditSeq h']
  refine sum_congr rfl fun t _ ↦ ?_
  rw [klDiv_compProd_right_eq_lintegral, lintegral_fintype]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Measure.map_apply (h.measurable_action t) (measurableSet_singleton a), mul_comm]
  rfl

end NonstationaryBandit

end Learning
