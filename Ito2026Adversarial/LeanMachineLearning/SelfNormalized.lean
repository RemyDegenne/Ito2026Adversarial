/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.DesignMatrix
public import Ito2026Adversarial.Mathlib.Analysis.SpecialFunctions.Gaussian.QuadraticForm
public import Ito2026Adversarial.Mathlib.Probability.Martingale.Ville
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# The self-normalized bound for vector-valued martingales

Let `𝓕` be a filtration, `a_n ∈ ℝ^d` a predictable sequence of features (`a_n` is
`𝓕 n`-measurable) and `ε_n` a conditionally `1`-sub-Gaussian noise sequence (`ε_n` is
`𝓕 (n + 1)`-measurable and `E[e^{c ε_n} | 𝓕 n] ≤ e^{c² / 2}` for every `𝓕 n`-measurable `c`,
`IsCondSubgaussianNoise`). Let `S_n = ∑_{s < n} ε_s a_s` and `V_n = λ I + ∑_{s < n} a_s a_sᵀ`
(`regGram λ a n`) for `λ > 0`. **The self-normalized bound** of Abbasi-Yadkori, Pál, Szepesvári
(2011, Theorem 1) states that with probability at least `1 - δ`, for all `n`,
`‖S_n‖²_{V_n⁻¹} ≤ 2 log(1/δ) + log(det V_n / λ^d)`.

The proof is the method of mixtures: for each `θ`, `exp(⟪θ, S_n⟫ - ‖θ‖²_{V_n} / 2)` is a
nonnegative supermartingale; its mixture over `θ` with respect to the Lebesgue measure is
`(2π)^{d/2} (det V_n)^{-1/2} exp(‖S_n‖²_{V_n⁻¹} / 2)`
(`Matrix.PosDef.lintegral_exp_inner_sub_mahalanobisSq`), again a supermartingale by Tonelli's
theorem, and Ville's inequality (`MeasureTheory.measure_exists_le_le_lintegral_div`) concludes.
Working with lower integrals of nonnegative extended processes avoids all integrability
questions.

## Main definitions

* `Learning.IsCondSubgaussianNoise 𝓕 ε P`: the noise `ε` is conditionally `1`-sub-Gaussian with
  respect to `𝓕`, in integrated form.
* `Learning.selfNormMixture λ a ε n`: the Gaussian mixture
  `(λ^d / det V_n)^{1/2} exp(‖S_n‖²_{V_n⁻¹} / 2)`.

## Main statements

* `Learning.setLIntegral_selfNormMixture_succ_le`: the Gaussian mixture is a nonnegative
  supermartingale (with initial value `1`, `Learning.selfNormMixture_zero`);
* `Learning.measure_exists_lt_mahalanobisSq_inv_regGram_le`: the self-normalized bound, as an
  upper bound on the probability of the bad event;
* `Learning.probReal_forall_mahalanobisSq_inv_regGram_le_ge`: the same, as a lower bound on the
  probability of the good event.

## Tags

self-normalized bound, method of mixtures, martingale, linear bandit
-/

@[expose] public section

open MeasureTheory Finset Real Matrix
open scoped ENNReal RealInnerProductSpace

namespace Learning

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℕ mΩ}

/-- The real noise sequence `ε` is *conditionally `1`-sub-Gaussian* with respect to the filtration
`𝓕`, in integrated form: for every `n`, every nonnegative `𝓕 n`-measurable weight `g` and every
`𝓕 n`-measurable coefficient `c`, `∫⁻ g e^{c ε_n} ≤ ∫⁻ g e^{c² / 2}`. This holds as soon as the
conditional law of `ε n` given `𝓕 n` is `1`-sub-Gaussian. -/
def IsCondSubgaussianNoise (𝓕 : Filtration ℕ mΩ) (ε : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ n (g : Ω → ℝ≥0∞) (c : Ω → ℝ), Measurable[𝓕 n] g → Measurable[𝓕 n] c →
    ∫⁻ ω, g ω * ENNReal.ofReal (rexp (c ω * ε n ω)) ∂P ≤
      ∫⁻ ω, g ω * ENNReal.ofReal (rexp (c ω ^ 2 / 2)) ∂P

variable {a : ℕ → Ω → EuclideanSpace ℝ ι} {ε : ℕ → Ω → ℝ}

section Measurability

/-- The regularized Gram matrix `λ I + ∑_{s < n} a_s a_sᵀ` of predictable features is
`𝓕 n`-measurable. -/
lemma measurable_regGram_filtration [Finite ι] [DecidableEq ι] (ha : ∀ n, Measurable[𝓕 n] (a n))
    (lam : ℝ) (n : ℕ) :
    Measurable[𝓕 n] fun ω ↦ regGram lam (a · ω) n := by
  have := Fintype.ofFinite ι
  have hT : Measurable[𝓕 n] fun ω (s : Fin n) ↦ a s ω :=
    @Measurable.of_eval _ _ _ (𝓕 n) _ _ fun s ↦ (ha s).mono (𝓕.mono s.2.le) le_rfl
  have hcont : Continuous fun y : Fin n → EuclideanSpace ℝ ι ↦
      lam • (1 : Matrix ι ι ℝ) + ∑ s, outerSelf (y s) := by fun_prop
  have : (fun ω ↦ regGram lam (a · ω) n) = (fun y : Fin n → EuclideanSpace ℝ ι ↦
      lam • (1 : Matrix ι ι ℝ) + ∑ s, outerSelf (y s)) ∘ fun ω s ↦ a s ω := by
    funext ω
    simp [regGram, gram, Finset.sum_range]
  rw [this]
  exact hcont.measurable.comp hT

/-- The weighted sum `∑_{s < n} ε_s a_s` of predictable features and adapted weights is
`𝓕 n`-measurable. -/
lemma measurable_sum_smul_filtration [Finite ι] (ha : ∀ n, Measurable[𝓕 n] (a n))
    (hε : ∀ n, Measurable[𝓕 (n + 1)] (ε n)) (n : ℕ) :
    Measurable[𝓕 n] fun ω ↦ ∑ s ∈ range n, ε s ω • a s ω := by
  have := Fintype.ofFinite ι
  have hT : Measurable[𝓕 n] fun ω (s : Fin n) ↦ (a s ω, ε s ω) :=
    @Measurable.of_eval _ _ _ (𝓕 n) _ _ fun s ↦
      ((ha s).mono (𝓕.mono s.2.le) le_rfl).prodMk ((hε s).mono (𝓕.mono s.2) le_rfl)
  have hcont : Continuous fun y : Fin n → EuclideanSpace ℝ ι × ℝ ↦ ∑ s, (y s).2 • (y s).1 := by
    fun_prop
  have : (fun ω ↦ ∑ s ∈ range n, ε s ω • a s ω) =
      (fun y : Fin n → EuclideanSpace ℝ ι × ℝ ↦ ∑ s, (y s).2 • (y s).1) ∘
        fun ω s ↦ (a s ω, ε s ω) := by
    funext ω
    simp [Finset.sum_range]
  rw [this]
  exact hcont.measurable.comp hT

end Measurability

variable [Fintype ι] [DecidableEq ι]

/-- The **Gaussian mixture** `(λ^d / det V_n)^{1/2} exp(‖S_n‖²_{V_n⁻¹} / 2)` of the
self-normalized process, with `S_n = ∑_{s < n} ε_s a_s` and `V_n = λ I + ∑_{s < n} a_s a_sᵀ`: the
mixture of the exponential supermartingales `exp(⟪θ, S_n⟫ - ‖θ‖²_{V_n - λ I} / 2)` over
`θ ∼ N(0, λ⁻¹ I)` (`lintegral_exp_inner_sub_mahalanobisSq_regGram`). In dimension one with
`λ = 1` and `a_s ∈ {0, 1}`, it is `(1 + N_n)^{-1/2} exp(S_n² / (2 (1 + N_n)))`. -/
noncomputable def selfNormMixture (lam : ℝ) (a : ℕ → Ω → EuclideanSpace ℝ ι) (ε : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  √(lam ^ Fintype.card ι / (regGram lam (a · ω) n).det) *
    rexp (mahalanobisSq (regGram lam (a · ω) n)⁻¹ (∑ s ∈ range n, ε s ω • a s ω) / 2)

/-- The Gaussian mixture is nonnegative. -/
lemma selfNormMixture_nonneg (lam : ℝ) (a : ℕ → Ω → EuclideanSpace ℝ ι) (ε : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : 0 ≤ selfNormMixture lam a ε n ω :=
  mul_nonneg (Real.sqrt_nonneg _) (exp_pos _).le

/-- The Gaussian mixture has initial value `1`. -/
@[simp]
lemma selfNormMixture_zero {lam : ℝ} (hlam : lam ≠ 0) (a : ℕ → Ω → EuclideanSpace ℝ ι)
    (ε : ℕ → Ω → ℝ) (ω : Ω) : selfNormMixture lam a ε 0 ω = 1 := by
  simp [selfNormMixture, regGram_zero, hlam]

/-- The Gaussian mixture is `𝓕 n`-measurable. -/
lemma measurable_selfNormMixture (ha : ∀ n, Measurable[𝓕 n] (a n))
    (hε : ∀ n, Measurable[𝓕 (n + 1)] (ε n)) (lam : ℝ) (n : ℕ) :
    Measurable[𝓕 n] (selfNormMixture lam a ε n) := by
  have hV := measurable_regGram_filtration ha lam n
  have hS := measurable_sum_smul_filtration ha hε n
  have hF : Measurable fun p : Matrix ι ι ℝ × EuclideanSpace ℝ ι ↦
      √(lam ^ Fintype.card ι / p.1.det) * rexp (mahalanobisSq p.1⁻¹ p.2 / 2) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.div (continuous_id.matrix_det.measurable.comp measurable_fst)).sqrt
    · exact measurable_exp.comp
        ((measurable_fst.matrix_inv.mahalanobisSq measurable_snd).div_const 2)
  exact hF.comp (hV.prodMk hS)

/-- **The method of mixtures.** The mixture over the Lebesgue measure of the exponential processes
`exp(⟪θ, S_n⟫ - ‖θ‖²_{V_n} / 2)` is `(2π/λ)^{d/2}` times the Gaussian mixture
`selfNormMixture`. -/
lemma lintegral_exp_inner_sub_mahalanobisSq_regGram {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (ω : Ω) :
    ∫⁻ θ : EuclideanSpace ℝ ι, ENNReal.ofReal (rexp (⟪θ, ∑ s ∈ range n, ε s ω • a s ω⟫ -
      mahalanobisSq (regGram lam (a · ω) n) θ / 2)) =
      ENNReal.ofReal ((2 * π) ^ (Fintype.card ι / 2 : ℝ) / √(lam ^ Fintype.card ι)) *
        ENNReal.ofReal (selfNormMixture lam a ε n ω) := by
  have hpd := posDef_regGram hlam (a · ω) n
  rw [hpd.lintegral_exp_inner_sub_mahalanobisSq, selfNormMixture,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hD := hpd.det_pos
  have hl : 0 < lam ^ Fintype.card ι := pow_pos hlam _
  rw [Real.sqrt_div' _ hD.le]
  have : 0 < √(lam ^ Fintype.card ι) := Real.sqrt_pos.2 hl
  have : 0 < √(regGram lam (a · ω) n).det := Real.sqrt_pos.2 hD
  field_simp

/-- **The Gaussian mixture is a supermartingale** (in the lower-integral sense): for predictable
features `a`, a conditionally `1`-sub-Gaussian noise `ε` and `λ > 0`,
`∫_s Z_{n+1} ≤ ∫_s Z_n` for every `𝓕 n`-measurable set `s`, where `Z = selfNormMixture λ a ε`.
For each `θ`, `exp(⟪θ, S_n⟫ - ‖θ‖²_{V_n} / 2)` is a supermartingale since
`E[exp(⟪θ, a_n⟫ ε_n - ⟪θ, a_n⟫² / 2) | 𝓕 n] ≤ 1`; their mixture over `θ` is a supermartingale by
Tonelli's theorem, and is a constant multiple of `Z`
(`lintegral_exp_inner_sub_mahalanobisSq_regGram`). -/
lemma setLIntegral_selfNormMixture_succ_le [SFinite P] (ha : ∀ n, Measurable[𝓕 n] (a n))
    (hε : ∀ n, Measurable[𝓕 (n + 1)] (ε n)) (hsub : IsCondSubgaussianNoise 𝓕 ε P) {lam : ℝ}
    (hlam : 0 < lam) (n : ℕ) {s : Set Ω} (hs : MeasurableSet[𝓕 n] s) :
    ∫⁻ ω in s, ENNReal.ofReal (selfNormMixture lam a ε (n + 1) ω) ∂P ≤
      ∫⁻ ω in s, ENNReal.ofReal (selfNormMixture lam a ε n ω) ∂P := by
  -- the exponential supermartingales `W θ`
  set W : EuclideanSpace ℝ ι → ℕ → Ω → ℝ≥0∞ := fun θ n ω ↦
    ENNReal.ofReal (rexp (⟪θ, ∑ s ∈ range n, ε s ω • a s ω⟫ -
      mahalanobisSq (regGram lam (a · ω) n) θ / 2)) with hW
  set F : EuclideanSpace ℝ ι × (Matrix ι ι ℝ × EuclideanSpace ℝ ι) → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal (rexp (⟪p.1, p.2.2⟫ - mahalanobisSq p.2.1 p.1 / 2)) with hF
  have hFm : Measurable F := by
    refine (ENNReal.continuous_ofReal.comp (continuous_exp.comp ?_)).measurable
    exact (continuous_fst.inner (continuous_snd.comp continuous_snd)).sub
      (((continuous_fst.comp continuous_snd).mahalanobisSq continuous_fst).div_const 2)
  have hVS : ∀ m, Measurable[𝓕 m] fun ω ↦
      (regGram lam (a · ω) m, ∑ s ∈ range m, ε s ω • a s ω) := fun m ↦
    (measurable_regGram_filtration ha lam m).prodMk (measurable_sum_smul_filtration ha hε m)
  have hWm : ∀ θ m, Measurable[𝓕 m] (W θ m) := fun θ m ↦ by
    have : W θ m = (fun y ↦ F (θ, y)) ∘ fun ω ↦
        (regGram lam (a · ω) m, ∑ s ∈ range m, ε s ω • a s ω) := rfl
    rw [this]
    exact (hFm.comp (measurable_const.prodMk measurable_id)).comp (hVS m)
  -- one step of `W θ`
  have hW_succ : ∀ θ ω, W θ (n + 1) ω = W θ n ω * ENNReal.ofReal (rexp (⟪θ, a n ω⟫ * ε n ω)) *
      ENNReal.ofReal (rexp (-(⟪θ, a n ω⟫ ^ 2 / 2))) := by
    intro θ ω
    simp only [hW]
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (by positivity), ← exp_add,
      ← exp_add]
    congr 2
    rw [sum_range_succ, inner_add_right, inner_smul_right, regGram_succ, mahalanobisSq_add_left,
      mahalanobisSq_apply (outerSelf _), dotProduct_outerSelf_mulVec]
    ring
  -- `W θ` is a supermartingale in the lower-integral sense
  have hW_super : ∀ θ, ∫⁻ ω in s, W θ (n + 1) ω ∂P ≤ ∫⁻ ω in s, W θ n ω ∂P := by
    intro θ
    set c : Ω → ℝ := fun ω ↦ ⟪θ, a n ω⟫ with hc
    have hcm : Measurable[𝓕 n] c := Measurable.inner measurable_const (ha n)
    set g : Ω → ℝ≥0∞ := s.indicator (fun ω ↦ W θ n ω * ENNReal.ofReal (rexp (-(c ω ^ 2 / 2))))
      with hg
    have hgm : Measurable[𝓕 n] g :=
      ((hWm θ n).mul (ENNReal.measurable_ofReal.comp
        (measurable_exp.comp ((hcm.pow_const 2).div_const 2).neg))).indicator hs
    have h1 : ∫⁻ ω in s, W θ (n + 1) ω ∂P =
        ∫⁻ ω, g ω * ENNReal.ofReal (rexp (c ω * ε n ω)) ∂P := by
      rw [← lintegral_indicator (𝓕.le n _ hs)]
      congr 1
      funext ω
      by_cases hω : ω ∈ s
      · simp only [hg, hω, Set.indicator_of_mem, hW_succ, hc]
        ring
      · simp [hg, hω]
    have h2 : ∫⁻ ω, g ω * ENNReal.ofReal (rexp (c ω ^ 2 / 2)) ∂P = ∫⁻ ω in s, W θ n ω ∂P := by
      rw [← lintegral_indicator (𝓕.le n _ hs)]
      congr 1
      funext ω
      by_cases hω : ω ∈ s
      · simp only [hg, hω, Set.indicator_of_mem]
        rw [mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
        simp
      · simp [hg, hω]
    rw [h1, ← h2]
    exact hsub n g c hgm hcm
  -- the mixture over `θ`, by Tonelli's theorem
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * π) ^ (Fintype.card ι / 2 : ℝ) / √(lam ^ Fintype.card ι))
    with hK
  have hK0 : K ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hmix : ∀ m, ∫⁻ ω in s, ENNReal.ofReal (selfNormMixture lam a ε m ω) ∂P =
      K⁻¹ * ∫⁻ θ, ∫⁻ ω in s, W θ m ω ∂P := by
    intro m
    have hjoint : Measurable (fun p : Ω × EuclideanSpace ℝ ι ↦ W p.2 m p.1) := by
      have : (fun p : Ω × EuclideanSpace ℝ ι ↦ W p.2 m p.1) = F ∘ fun p ↦
          (p.2, (regGram lam (a · p.1) m, ∑ s ∈ range m, ε s p.1 • a s p.1)) := rfl
      rw [this]
      exact hFm.comp (measurable_snd.prodMk (((hVS m).mono (𝓕.le m) le_rfl).comp measurable_fst))
    rw [← lintegral_lintegral_swap hjoint.aemeasurable]
    simp only [hW, lintegral_exp_inner_sub_mahalanobisSq_regGram hlam, ← hK]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      ENNReal.inv_mul_cancel hK0 ENNReal.ofReal_ne_top, one_mul]
  rw [hmix, hmix]
  exact mul_le_mul_of_nonneg_left (lintegral_mono fun θ ↦ hW_super θ) zero_le

/-- **The self-normalized bound** (Abbasi-Yadkori, Pál, Szepesvári 2011, Theorem 1). For
predictable features `a` (`a n` is `𝓕 n`-measurable), a conditionally `1`-sub-Gaussian noise `ε`
(`ε n` is `𝓕 (n + 1)`-measurable), `λ > 0` and `δ > 0`, the probability that for some `n`,
`‖S_n‖²_{V_n⁻¹} > 2 log(1/δ) + log(det V_n / λ^d)` is at most `δ`, where
`S_n = ∑_{s < n} ε_s a_s` and `V_n = λ I + ∑_{s < n} a_s a_sᵀ`. Proof: Ville's inequality for the
Gaussian mixture `selfNormMixture`, a nonnegative supermartingale with initial value `1`. -/
lemma measure_exists_lt_mahalanobisSq_inv_regGram_le [IsProbabilityMeasure P]
    (ha : ∀ n, Measurable[𝓕 n] (a n)) (hε : ∀ n, Measurable[𝓕 (n + 1)] (ε n))
    (hsub : IsCondSubgaussianNoise 𝓕 ε P) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    P {ω | ∃ n, 2 * log (1 / δ) + log ((regGram lam (a · ω) n).det / lam ^ Fintype.card ι) <
      mahalanobisSq (regGram lam (a · ω) n)⁻¹ (∑ s ∈ range n, ε s ω • a s ω)} ≤
      ENNReal.ofReal δ := by
  have hville := measure_exists_le_le_lintegral_div (μ := P)
    (Z := fun n ω ↦ ENNReal.ofReal (selfNormMixture lam a ε n ω))
    (fun n ↦ ENNReal.measurable_ofReal.comp (measurable_selfNormMixture ha hε lam n))
    (fun n s hs ↦ setLIntegral_selfNormMixture_succ_le ha hε hsub hlam n hs)
    (c := ENNReal.ofReal (1 / δ)) (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
  simp only [selfNormMixture_zero hlam.ne', ENNReal.ofReal_one, lintegral_const, measure_univ,
    mul_one] at hville
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (by positivity), one_div_one_div]
    at hville
  refine le_trans (measure_mono ?_) hville
  -- the bad event is contained in the event of Ville's inequality
  rintro ω ⟨n, hn⟩
  refine ⟨n, ENNReal.ofReal_le_ofReal ?_⟩
  set D := (regGram lam (a · ω) n).det with hD
  have hD_pos : 0 < D := (posDef_regGram hlam (a · ω) n).det_pos
  have hlamd : 0 < lam ^ Fintype.card ι := pow_pos hlam _
  have hkey : 1 / δ = √(lam ^ Fintype.card ι / D) *
      rexp (log (1 / δ) + log (D / lam ^ Fintype.card ι) / 2) := by
    have hsq : rexp (log (D / lam ^ Fintype.card ι) / 2) = √(D / lam ^ Fintype.card ι) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      ring_nf
    rw [exp_add, exp_log (by positivity), hsq, ← mul_assoc, mul_comm _ (1 / δ), mul_assoc,
      ← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm D,
      div_self (by positivity), Real.sqrt_one, mul_one]
  rw [hkey, selfNormMixture]
  gcongr
  linarith

/-- **The self-normalized bound** (Abbasi-Yadkori, Pál, Szepesvári 2011, Theorem 1), good-event
form: under the assumptions of `measure_exists_lt_mahalanobisSq_inv_regGram_le`, with probability
at least `1 - δ`, for all `n`, `‖S_n‖²_{V_n⁻¹} ≤ 2 log(1/δ) + log(det V_n / λ^d)`. -/
lemma probReal_forall_mahalanobisSq_inv_regGram_le_ge [IsProbabilityMeasure P]
    (ha : ∀ n, Measurable[𝓕 n] (a n)) (hε : ∀ n, Measurable[𝓕 (n + 1)] (ε n))
    (hsub : IsCondSubgaussianNoise 𝓕 ε P) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∀ n,
      mahalanobisSq (regGram lam (a · ω) n)⁻¹ (∑ s ∈ range n, ε s ω • a s ω) ≤
        2 * log (1 / δ) + log ((regGram lam (a · ω) n).det / lam ^ Fintype.card ι)} := by
  set G := {ω | ∀ n,
    mahalanobisSq (regGram lam (a · ω) n)⁻¹ (∑ s ∈ range n, ε s ω • a s ω) ≤
      2 * log (1 / δ) + log ((regGram lam (a · ω) n).det / lam ^ Fintype.card ι)} with hG
  have hcompl : Gᶜ = {ω | ∃ n, 2 * log (1 / δ) +
      log ((regGram lam (a · ω) n).det / lam ^ Fintype.card ι) <
        mahalanobisSq (regGram lam (a · ω) n)⁻¹ (∑ s ∈ range n, ε s ω • a s ω)} := by
    ext ω
    simp [hG]
  have hbad : P.real Gᶜ ≤ δ := by
    rw [hcompl]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le
      (measure_exists_lt_mahalanobisSq_inv_regGram_le ha hε hsub hlam hδ)
  have h1 : P.real Set.univ ≤ P.real G + P.real Gᶜ := by
    rw [← Set.union_compl_self G]
    exact measureReal_union_le _ _
  rw [probReal_univ] at h1
  linarith

end Learning
