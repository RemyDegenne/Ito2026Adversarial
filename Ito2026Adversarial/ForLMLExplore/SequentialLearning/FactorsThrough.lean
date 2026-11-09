/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Comap
public import LeanMachineLearning.SequentialLearning.Deterministic

/-!
# Algorithms factoring through a statistic

LML's `Algorithm.comap alg F hF` transports `alg` along the maps `F n` of the pair (history,
current observation). This file adds the predicate that names the property such a transport has.

## Main definitions

* `Algorithm.FactorsThrough alg T`: the policy of `alg` reads the history and the current
  observation only through the statistic `T n`. This is the natural predicate for stating that
  algorithms factor through a given statistic (the observed part of the feedback, a state, ...).

## Main statements

* `Algorithm.factorsThrough_comap`: `Algorithm.comap alg F hF` factors through `F`.
* `Algorithm.FactorsThrough.comap`: transport of the predicate along `Algorithm.comap`.
* `Algorithm.FactorsThrough.of_comp`: an algorithm factoring through a coarser statistic factors
  through a finer one.
* `factorsThrough_deterministic`: a deterministic algorithm playing a function of `T` factors
  through `T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓞' 𝓐 𝓨 𝓨' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓞' : MeasurableSpace 𝓞'}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨} {m𝓨' : MeasurableSpace 𝓨'}

/-- The policy of `alg` at each time `n` depends on the history and the current observation only
through the statistic `T n`: it is a kernel applied to `T n p`. -/
def Algorithm.FactorsThrough {𝓑 : ℕ → Type*} [∀ n, MeasurableSpace (𝓑 n)] (alg : Algorithm 𝓞 𝓐 𝓨)
    (T : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓑 n) : Prop :=
  ∀ n, ∃ κ : Kernel (𝓑 n) 𝓐, ∀ p, alg.policy n p = κ (T n p)

/-- Every algorithm factors through the identity (the full history and the observation). -/
lemma Algorithm.factorsThrough_id (alg : Algorithm 𝓞 𝓐 𝓨) :
    alg.FactorsThrough fun n (p : Hist 𝓞 𝓐 𝓨 n × 𝓞) ↦ p :=
  fun n ↦ ⟨alg.policy n, fun _ ↦ rfl⟩

/-- `alg.comap F hF` factors through `F`. -/
lemma Algorithm.factorsThrough_comap (alg : Algorithm 𝓞 𝓐 𝓨)
    (F : (n : ℕ) → Hist 𝓞' 𝓐 𝓨' n × 𝓞' → Hist 𝓞 𝓐 𝓨 n × 𝓞) (hF : ∀ n, Measurable (F n)) :
    (alg.comap F hF).FactorsThrough F :=
  fun n ↦ ⟨alg.policy n, fun h ↦ by simp [Kernel.comap_apply]⟩

/-- If `alg` factors through `T`, then its transport `alg.comap F hF` factors through `T n ∘ F n`.
-/
lemma Algorithm.FactorsThrough.comap {𝓑 : ℕ → Type*} [∀ n, MeasurableSpace (𝓑 n)]
    {alg : Algorithm 𝓞 𝓐 𝓨} {T : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓑 n} (h : alg.FactorsThrough T)
    (F : (n : ℕ) → Hist 𝓞' 𝓐 𝓨' n × 𝓞' → Hist 𝓞 𝓐 𝓨 n × 𝓞) (hF : ∀ n, Measurable (F n)) :
    (alg.comap F hF).FactorsThrough fun n p ↦ T n (F n p) := fun n ↦ by
  obtain ⟨κ, hκ⟩ := h n
  exact ⟨κ, fun p ↦ by rw [Algorithm.policy_comap, Kernel.comap_apply, hκ]⟩

/-- An algorithm factoring through a coarser statistic `T' n = g n ∘ T n` factors through
`T`. -/
lemma Algorithm.FactorsThrough.of_comp {𝓑 𝓑' : ℕ → Type*} [∀ n, MeasurableSpace (𝓑 n)]
    [∀ n, MeasurableSpace (𝓑' n)] {alg : Algorithm 𝓞 𝓐 𝓨}
    {T : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓑 n} {T' : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓑' n}
    (h : alg.FactorsThrough T') (g : (n : ℕ) → 𝓑 n → 𝓑' n) (hg : ∀ n, Measurable (g n))
    (hT : ∀ n x, T' n x = g n (T n x)) : alg.FactorsThrough T := fun n ↦ by
  obtain ⟨κ, hκ⟩ := h n
  exact ⟨κ.comap (g n) (hg n), fun x ↦ by rw [hκ, Kernel.comap_apply, hT]⟩

/-- The deterministic algorithm playing `f n (T n p)` at round `n` factors through `T`. -/
lemma factorsThrough_deterministic {𝓑 : ℕ → Type*} [∀ n, MeasurableSpace (𝓑 n)]
    {T : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → 𝓑 n} {f : (n : ℕ) → 𝓑 n → 𝓐}
    (hf : ∀ n, Measurable (f n)) (h_next : ∀ n, Measurable fun p ↦ f n (T n p)) :
    (Algorithm.deterministic (fun n p ↦ f n (T n p)) h_next).FactorsThrough T :=
  fun n ↦ ⟨Kernel.deterministic (f n) (hf n), fun _ ↦ rfl⟩

end Learning
