/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of `ite`, `decide` and of evaluation on a countable domain

`Measurable.ite` needs the measurability of the set defined by the condition, which `fun_prop`
does not prove by itself: with `Measurable.ite` tagged `@[fun_prop]` (done here), goals such as
`Measurable fun x ↦ if k x = c then f x else g x` or `… if k₁ x ≤ k₂ x then …` are closed by
`fun_prop (disch := measurability)`, the discharger proving the measurability of the condition.
The same holds for the `Bool`-valued `decide` of a condition with `measurable_decide`.

## Main statements

* `measurable_decide`: `x ↦ decide (p x)` is measurable if `{x | p x}` is measurable.
* `measurable_eval_prod`: evaluation `(f, b) ↦ f b` is measurable on `(β → γ) × β` when `β` is
  countable with measurable singletons; `Measurable.eval_prod` is its compositional form.
-/

@[expose] public section

attribute [fun_prop] Measurable.ite

variable {α β γ : Type*} [MeasurableSpace α]

/-- The `Bool`-valued indicator `x ↦ decide (p x)` of a measurable set is measurable. -/
@[fun_prop]
lemma measurable_decide {p : α → Prop} [DecidablePred p] (hp : MeasurableSet {a | p a}) :
    Measurable fun x ↦ decide (p x) := by
  refine measurable_to_countable' fun b ↦ ?_
  cases b
  · have : (fun x ↦ decide (p x)) ⁻¹' {false} = {a | p a}ᶜ := by ext; simp
    rw [this]
    exact hp.compl
  · have : (fun x ↦ decide (p x)) ⁻¹' {true} = {a | p a} := by ext; simp
    rw [this]
    exact hp

variable [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]

/-- Evaluation `(f, b) ↦ f b` is measurable when the domain `β` is countable and discrete. -/
lemma measurable_eval_prod : Measurable fun p : (β → γ) × β ↦ p.1 p.2 :=
  measurable_from_prod_countable_left fun b ↦ measurable_pi_apply b

/-- Compositional form of `measurable_eval_prod`: `x ↦ f x (b x)` is measurable if `f` and `b`
are, for a countable discrete domain `β`. -/
lemma Measurable.eval_prod {f : α → β → γ} {b : α → β} (hf : Measurable f) (hb : Measurable b) :
    Measurable fun x ↦ f x (b x) :=
  measurable_eval_prod.comp (hf.prodMk hb)
