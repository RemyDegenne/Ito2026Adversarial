/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.Process.Filtration

/-!
# Ville's inequality for nonnegative extended supermartingales

A process `Z : ℕ → Ω → ℝ≥0∞` adapted to a filtration `𝓕` is a *nonnegative supermartingale in
the lower-integral sense* if `∫⁻_s Z (n + 1) ≤ ∫⁻_s Z n` for every `n` and every `𝓕 n`-measurable
set `s`. For such a process, **Ville's inequality** `c ℙ(∃ n, Z n ≥ c) ≤ 𝔼[Z 0]` holds. No
integrability is needed, which makes this form convenient for mixtures of exponential
supermartingales over an infinite measure (such as the Lebesgue measure in the method of mixtures
for self-normalized bounds), where Tonelli's theorem gives the supermartingale inequality
directly in lower integrals.

The proof is the classical one: with `B N = {Z k < c for all k < N}` (a `𝓕 (N - 1)`-measurable
event), `c ℙ(∃ k < N, Z k ≥ c) + ∫⁻_{B N} Z N ≤ 𝔼[Z 0]` by induction on `N`.

## Main statements

* `MeasureTheory.mul_measure_exists_le_le_lintegral`: `c ℙ(∃ n, c ≤ Z n) ≤ ∫⁻ Z 0`;
* `MeasureTheory.measure_exists_le_le_lintegral_div`: `ℙ(∃ n, c ≤ Z n) ≤ (∫⁻ Z 0) / c`.
## Tags

Ville's inequality, supermartingale, maximal inequality
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ}
  {Z : ℕ → Ω → ℝ≥0∞}

/-- **Ville's inequality** for a nonnegative supermartingale in the lower-integral sense:
if `Z n` is `𝓕 n`-measurable and `∫⁻_s Z (n + 1) ≤ ∫⁻_s Z n` for every `𝓕 n`-measurable `s`, then
`c ℙ(∃ n, c ≤ Z n) ≤ ∫⁻ Z 0` for every `c`. -/
lemma mul_measure_exists_le_le_lintegral (hZ : ∀ n, Measurable[𝓕 n] (Z n))
    (hsuper : ∀ n s, MeasurableSet[𝓕 n] s → ∫⁻ ω in s, Z (n + 1) ω ∂μ ≤ ∫⁻ ω in s, Z n ω ∂μ)
    (c : ℝ≥0∞) :
    c * μ {ω | ∃ n, c ≤ Z n ω} ≤ ∫⁻ ω, Z 0 ω ∂μ := by
  set A : ℕ → Set Ω := fun N ↦ {ω | ∃ k < N, c ≤ Z k ω} with hA
  set B : ℕ → Set Ω := fun N ↦ {ω | ∀ k < N, Z k ω < c} with hB
  have hBm : ∀ N, MeasurableSet[𝓕 N] (B N) := by
    intro N
    have : B N = ⋂ k ∈ Finset.range N, {ω | Z k ω < c} := by ext; simp [hB]
    rw [this]
    refine Finset.measurableSet_biInter _ fun k hk ↦ ?_
    exact measurableSet_lt ((hZ k).mono (𝓕.mono (Finset.mem_range.1 hk).le) le_rfl)
      measurable_const
  have hZm : ∀ n, Measurable (Z n) := fun n ↦ (hZ n).mono (𝓕.le n) le_rfl
  have key : ∀ N, c * μ (A N) + ∫⁻ ω in B N, Z N ω ∂μ ≤ ∫⁻ ω, Z 0 ω ∂μ := by
    intro N
    induction N with
    | zero => simp [hA, hB]
    | succ N ih =>
      have hA_eq : A (N + 1) = A N ∪ (B N ∩ {ω | c ≤ Z N ω}) := by
        ext ω
        simp only [hA, hB, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
        constructor
        · rintro ⟨k, hk, hck⟩
          by_cases h : ∃ j < N, c ≤ Z j ω
          · exact Or.inl h
          · push Not at h
            rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
            · exact absurd hck (not_le.2 (h k hk))
            · exact Or.inr ⟨h, hck⟩
        · rintro (⟨k, hk, hck⟩ | ⟨_, hck⟩)
          · exact ⟨k, hk.trans (Nat.lt_succ_self N), hck⟩
          · exact ⟨N, Nat.lt_succ_self N, hck⟩
      have hB_eq : B (N + 1) = B N ∩ {ω | c ≤ Z N ω}ᶜ := by
        ext ω
        simp only [hB, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
        constructor
        · intro h
          exact ⟨fun k hk ↦ h k (hk.trans (Nat.lt_succ_self N)), h N (Nat.lt_succ_self N)⟩
        · rintro ⟨h, hN⟩ k hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact h k hk
          · exact hN
      have hmeasC : MeasurableSet {ω | c ≤ Z N ω} := measurableSet_le measurable_const (hZm N)
      have hBNm : MeasurableSet (B N) := 𝓕.le N _ (hBm N)
      have hdisj : Disjoint (A N) (B N ∩ {ω | c ≤ Z N ω}) := by
        rw [Set.disjoint_left]
        rintro ω ⟨k, hk, hck⟩ ⟨hω, -⟩
        exact absurd hck (not_le.2 (hω k hk))
      have h1 : c * μ (B N ∩ {ω | c ≤ Z N ω}) ≤ ∫⁻ ω in B N ∩ {ω | c ≤ Z N ω}, Z N ω ∂μ := by
        rw [← setLIntegral_const]
        exact setLIntegral_mono (hZm N) fun ω hω ↦ hω.2
      have hBm' : MeasurableSet[𝓕 N] (B (N + 1)) := by
        rw [hB_eq]
        exact (hBm N).inter (measurableSet_le measurable_const (hZ N)).compl
      have h2 : ∫⁻ ω in B (N + 1), Z (N + 1) ω ∂μ ≤ ∫⁻ ω in B (N + 1), Z N ω ∂μ :=
        hsuper N _ hBm'
      have h3 : ∫⁻ ω in B N, Z N ω ∂μ = ∫⁻ ω in B N ∩ {ω | c ≤ Z N ω}, Z N ω ∂μ +
          ∫⁻ ω in B (N + 1), Z N ω ∂μ := by
        rw [hB_eq, ← lintegral_inter_add_sdiff _ (B N) hmeasC, Set.sdiff_eq]
      calc c * μ (A (N + 1)) + ∫⁻ ω in B (N + 1), Z (N + 1) ω ∂μ
          ≤ c * μ (A N) + c * μ (B N ∩ {ω | c ≤ Z N ω}) + ∫⁻ ω in B (N + 1), Z N ω ∂μ := by
            rw [hA_eq, measure_union hdisj (hBNm.inter hmeasC), mul_add]
            gcongr
        _ ≤ c * μ (A N) + ∫⁻ ω in B N, Z N ω ∂μ := by
            rw [h3, add_assoc]
            gcongr
        _ ≤ ∫⁻ ω, Z 0 ω ∂μ := ih
  have hunion : {ω | ∃ n, c ≤ Z n ω} = ⋃ N, A N := by
    ext ω
    simp only [hA, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨n + 1, n, Nat.lt_succ_self n, hn⟩, fun ⟨_, n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  have hmono : Monotone A := fun N N' hNN' ω ⟨k, hk, hck⟩ ↦ ⟨k, hk.trans_le hNN', hck⟩
  rw [hunion, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun N ↦ le_trans le_self_add (key N)

/-- **Ville's inequality** for a nonnegative supermartingale in the lower-integral sense:
`ℙ(∃ n, c ≤ Z n) ≤ (∫⁻ Z 0) / c` for `c ≠ 0`, `c ≠ ∞`. -/
lemma measure_exists_le_le_lintegral_div (hZ : ∀ n, Measurable[𝓕 n] (Z n))
    (hsuper : ∀ n s, MeasurableSet[𝓕 n] s → ∫⁻ ω in s, Z (n + 1) ω ∂μ ≤ ∫⁻ ω in s, Z n ω ∂μ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    μ {ω | ∃ n, c ≤ Z n ω} ≤ (∫⁻ ω, Z 0 ω ∂μ) / c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc), mul_comm]
  exact mul_measure_exists_le_le_lintegral hZ hsuper c

end MeasureTheory
