/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.SequentialLearning.Algorithms.Index
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.TsallisINF
public import Ito2026Adversarial.LeanMachineLearning.DesignMatrix
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.Linear.Ridge
public import Ito2026Adversarial.Mathlib.Analysis.InnerProductSpace.Mahalanobis
public import Ito2026Adversarial.Mathlib.Analysis.Matrix.MeasurableSpace
public import Ito2026Adversarial.Mathlib.Probability.Distributions.TwoPoint
public import Ito2026Adversarial.LeanMachineLearning.Game.RepeatedGame
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Deterministic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Setting of Ito, Luo, Maiti, Tsuchiya, Wu (2026): adversarial learning in games with bandit
feedback

A learner plays a zero-sum game `u : 𝒳 → 𝒴 → ℝ` against an adaptive adversary with bandit feedback
(`Learning.RepeatedGame`): *uninformed* learners see only the reward, *informed* learners also
see the adversary's action. The performance measure is the pure-strategy maximin regret
`psmr`.

* **Normal-form games**: `𝒳 = Fin mx`, `𝒴 = Fin my`, `u` is a matrix. `tsallisINFHalf mx` is
  Tsallis-INF with `α = 1/2` and `η_t = 1 / (2 √t)` (uninformed, Theorem 1); `maximinUCB δ`
  (Maximin-UCB, Algorithm 2) is the informed algorithm playing the pure maximin action
  `argmax_x min_y U_t(x, y)` of the upper confidence bounds `ucbIndex δ h x y` built from the
  counts and reward sums of the history. `entryGap u` is the minimal entry gap `Δ_M` of a `2 × 2`
  game (Lemma 10).
* **Bilinear games**: the action sets are finite types `𝒳`, `𝒴` with features
  `φ : 𝒳 → ℝ^{d_x}`, `ψ : 𝒴 → ℝ^{d_y}` (the paper's finite subsets of `ℝ^{d_x}`, `ℝ^{d_y}`) and
  `u x y = ⟪φ x, A ψ y⟫` (`bilinearUtility`, `bilinearGame φ ψ A`); `IsBilinearGame φ ψ A` collects
  the paper's assumptions (features of norm at most `1` spanning the spaces, `‖A‖₂ ≤ 1`).
  `pairFeature x y = vec(x yᵀ)` and `vecMatrix A = vec(A)`, so that `u x y = ⟪vec(x yᵀ), vec(A)⟫`.
  - `tsallisSPM 𝒳 α β₁ βbar p₀ c` is Tsallis-FTRL with stability-penalty matching (Ito et al.
    2024, Algorithm 3), uninformed: the FTRL distribution `p̂_t` for the hybrid regularizer
    `β_t φ_α + βbar φ_{1-α}` (`spmHat`), mixed with the exploration distribution `p₀` with
    coefficient `γ_t = 4 c z_t / β_t` (`spmDist`, `zCoef`), the linear reward estimate
    `g_t(x) = r_t ⟪x_t, S(p_t)⁻¹ x⟫` (`spmEstimate`, `designOf`) and the learning-rate update
    `β_{t+1} = β_t + z_t / (β_t φ_α(p̂_t))` (`spmUpdate`). `tsallisSPMPaper φ c p₀` uses the
    parameters of Theorem 5.
  - `maximinLinUCB φ ψ λ β` (Maximin-LinUCB, Algorithm 4), informed: ridge regression of
    `vec(A)` on the features `vec(x_t y_tᵀ)` with regularization `λ` (`linUpdate`, the library's
    `ridgeUpdate` and `ridgeEstimate`, `Online/Bandit/Linear/Ridge.lean`), optimistic index
    `U_t(x, y) = ⟪a, Â_t⟫ + β_t ‖a‖_{V_{t-1}⁻¹}` (`linIndex`, the library's `ucbIndex`)
    and pure maximin action `argmax_x min_y U_t(x, y)` (`linAction`). `linRadius d λ δ t` is the
    paper's radius `β_t`, `linState φ ψ λ X Y R t` the ridge state `(V_t, b_t)` after `t` rounds
    of a run.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.ZeroSumGame Learning.RepeatedGame
  Matrix Real
open scoped RealInnerProductSpace

namespace Ito2026Adversarial

/-! ### Normal-form games: Tsallis-INF and Maximin-UCB -/

/-- `Δ` is a threshold for the positive pair gaps of the game `u`:
`v* - u x y ∈ (-∞, 0] ∪ [Δ, ∞)` for all `(x, y)` (the parameter `Δ^lin` of the paper). -/
def IsGapThreshold {𝒳 𝒴 : Type*} (u : 𝒳 → 𝒴 → ℝ) (Δ : ℝ) : Prop :=
  ∀ x y, pairGap u x y ≤ 0 ∨ Δ ≤ pairGap u x y

/-- Tsallis-INF with `α = 1/2` and `η_t = 1 / (2 √t)` (Theorem 1), on the arms `Fin mx`. -/
noncomputable def tsallisINFHalf (mx : ℕ) [NeZero mx] : Algorithm Unit (Fin mx) ℝ :=
  Bandits.tsallisINF (1 / (2 : ℕ)) fun n ↦ 1 / ((2 : ℕ) * √(n + 1))

/-- The minimal entry gap `Δ_M = min {|a - b|, |a - c|, |b - d|, |c - d|}` of the `2 × 2` game
`(a b; c d)`. -/
noncomputable def entryGap (u : Fin 2 → Fin 2 → ℝ) : ℝ :=
  min (min |u 0 0 - u 0 1| |u 0 0 - u 1 0|) (min |u 0 1 - u 1 1| |u 1 0 - u 1 1|)

section MaximinUCB

variable {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] [DecidableEq 𝒳] [DecidableEq 𝒴]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

/-- The upper confidence bound `U(x, y)` of Maximin-UCB after the history `h`: `1` if `(x, y)`
was never played, and otherwise the empirical mean plus
`√((4 log(1/δ) + 2 log(1 + N(x, y))) / N(x, y))`. -/
noncomputable def ucbIndex (δ : ℝ) {n : ℕ} (h : Hist Unit 𝒳 (𝒴 × ℝ) n) (x : 𝒳) (y : 𝒴) : ℝ :=
  if histPairCount h x y = 0 then 1 else
    histPairSum h x y / histPairCount h x y
      + √((4 * log (1 / δ) + ((2 : ℕ) : ℝ) * log (1 + histPairCount h x y)) / histPairCount h x y)

/-- The action of Maximin-UCB: the pure maximin action `argmax_x min_y U(x, y)` of the upper
confidence bounds. -/
noncomputable def ucbAction [Nonempty 𝒳] [Nonempty 𝒴] (δ : ℝ) {n : ℕ}
    (h : Hist Unit 𝒳 (𝒴 × ℝ) n) : 𝒳 :=
  argmax fun x ↦ (fun y ↦ ucbIndex δ h x y).min

variable [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒴]

omit [Fintype 𝒳] [Fintype 𝒴] in
@[fun_prop]
lemma measurable_ucbIndex (δ : ℝ) (n : ℕ) (x : 𝒳) (y : 𝒴) :
    Measurable fun h : Hist Unit 𝒳 (𝒴 × ℝ) n ↦ ucbIndex δ h x y := by
  unfold ucbIndex
  fun_prop (disch := measurability)

/-- **Algorithm 2** (Maximin-UCB) with confidence parameter `δ`: an informed deterministic player
which, at each round, plays the pure maximin action `ucbAction` of the upper confidence bounds of
the utilities of all action pairs (an index algorithm with index `x ↦ min_y U(x, y)`). -/
noncomputable def maximinUCB [Nonempty 𝒳] [Nonempty 𝒴] (δ : ℝ) : Player 𝒳 𝒴 :=
  Algorithm.index (fun _ p x ↦ (fun y ↦ ucbIndex δ p.1 x y).min) fun _ ↦ by fun_prop

end MaximinUCB

/-! ### Bilinear games -/

section Bilinear

variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

/-- The bilinear utility `u(x, y) = ⟪x, A y⟫ = xᵀ A y`. -/
noncomputable def bilinearUtility (A : Matrix ιx ιy ℝ) (x : EuclideanSpace ℝ ιx)
    (y : EuclideanSpace ℝ ιy) : ℝ :=
  WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp y)

variable {𝒳 𝒴 : Type*}

/-- The bilinear game with matrix `A` on the finite action sets `𝒳`, `𝒴` with features
`φ : 𝒳 → ℝ^{d_x}`, `ψ : 𝒴 → ℝ^{d_y}`: `u x y = ⟪φ x, A ψ y⟫`. -/
noncomputable def bilinearGame (φ : 𝒳 → EuclideanSpace ℝ ιx) (ψ : 𝒴 → EuclideanSpace ℝ ιy)
    (A : Matrix ιx ιy ℝ) : 𝒳 → 𝒴 → ℝ :=
  fun x y ↦ bilinearUtility A (φ x) (ψ y)

/-- The assumptions of the paper on a bilinear game: the actions have norm at most `1` and span
their spaces, and the matrix has operator norm at most `1` (so that `u x y ∈ [-1, 1]`). -/
structure IsBilinearGame (φ : 𝒳 → EuclideanSpace ℝ ιx) (ψ : 𝒴 → EuclideanSpace ℝ ιy)
    (A : Matrix ιx ιy ℝ) : Prop where
  norm_le_x : ∀ x, ‖φ x‖ ≤ 1
  norm_le_y : ∀ y, ‖ψ y‖ ≤ 1
  span_x : Submodule.span ℝ (Set.range φ) = ⊤
  span_y : Submodule.span ℝ (Set.range ψ) = ⊤
  opNorm_le : ∀ y : EuclideanSpace ℝ ιy,
    ‖(WithLp.toLp 2 (A *ᵥ WithLp.ofLp y) : EuclideanSpace ℝ ιx)‖ ≤ ‖y‖

omit [Fintype ιx] [Fintype ιy] in
/-- The feature `vec(x yᵀ)` of the action pair `(x, y)`, a vector indexed by `ιx × ιy`. -/
noncomputable def pairFeature (x : EuclideanSpace ℝ ιx) (y : EuclideanSpace ℝ ιy) :
    EuclideanSpace ℝ (ιx × ιy) :=
  WithLp.toLp _ fun ij ↦ x ij.1 * y ij.2

omit [Fintype ιx] [Fintype ιy] in
@[fun_prop]
lemma continuous_pairFeature :
    Continuous fun p : EuclideanSpace ℝ ιx × EuclideanSpace ℝ ιy ↦ pairFeature p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ij ↦ ?_)
  exact ((PiLp.continuous_apply 2 _ ij.1).comp continuous_fst).mul
    ((PiLp.continuous_apply 2 _ ij.2).comp continuous_snd)

omit [Fintype ιx] [Fintype ιy] in
/-- The matrix `A` flattened to a vector `vec(A)` indexed by `ιx × ιy`. -/
noncomputable def vecMatrix (A : Matrix ιx ιy ℝ) : EuclideanSpace ℝ (ιx × ιy) :=
  WithLp.toLp _ fun ij ↦ A ij.1 ij.2

/-- The design matrix `S(p) = E_{x ∼ p}[φ x (φ x)ᵀ]` of a distribution `p` on the action set
`𝒳` with features `φ`. -/
noncomputable def designOf [Fintype 𝒳] (φ : 𝒳 → EuclideanSpace ℝ ιx) (p : EuclideanSpace ℝ 𝒳) :
    Matrix ιx ιx ℝ :=
  ∑ x, p x • outerSelf (φ x)

omit [Fintype ιx] in
@[fun_prop]
lemma continuous_designOf [Fintype 𝒳] (φ : 𝒳 → EuclideanSpace ℝ ιx) :
    Continuous (designOf φ) :=
  continuous_finsetSum _ fun x _ ↦ (PiLp.continuous_apply 2 _ x).smul continuous_const

/-- The exploration distribution `p₀` on `𝒳` has variance ratio `c`: `S(p₀)` is positive definite
and `⟪φ x, S(p₀)⁻¹ φ x⟫ ≤ c d_x` for all `x` (`c = 1` is achievable by the Kiefer–Wolfowitz
theorem). The positive definiteness is implicit in the paper; without it the inequality would
hold for `S(p₀)` singular, Lean's inverse of a singular matrix being `0`. -/
def HasVarianceRatio [Fintype 𝒳] [DecidableEq ιx] (φ : 𝒳 → EuclideanSpace ℝ ιx)
    (p₀ : EuclideanSpace ℝ 𝒳) (c : ℝ) : Prop :=
  (designOf φ p₀).PosDef ∧
    ∀ x, WithLp.ofLp (φ x) ⬝ᵥ (designOf φ p₀)⁻¹ *ᵥ WithLp.ofLp (φ x) ≤ c * Fintype.card ιx

end Bilinear

/-! ### Tsallis-FTRL with stability-penalty matching (uninformed, bilinear games) -/

section SPM

variable {ιx : Type*} [Fintype ιx] {𝒳 : Type*} [Fintype 𝒳] [Nonempty 𝒳]

/-- The hybrid regularizer `β φ_α + βbar φ_{1-α}` of Tsallis-FTRL-SPM, with the learning rate `β`
as parameter. -/
noncomputable def hybridEntropy (α βbar β : ℝ) (p : EuclideanSpace ℝ 𝒳) : ℝ :=
  β * tsallisEntropy α p + βbar * tsallisEntropy (1 - α) p

/-- The FTRL distribution `p̂ = argmax_p ⟪p, G⟫ + β φ_α(p) + βbar φ_{1-α}(p)` from the state
`(G, β)`. -/
noncomputable def spmHat (α βbar : ℝ) (s : EuclideanSpace ℝ 𝒳 × ℝ) : simplex 𝒳 :=
  ftrlSimplexParam (hybridEntropy α βbar) (s.2, s.1)

/-- The coefficient `z = d (min {‖p‖_∞, 1 - ‖p‖_∞})^(1 - α) / (1 - α)`. -/
noncomputable def zCoef (α : ℝ) (d : ℕ) (p : EuclideanSpace ℝ 𝒳) : ℝ :=
  d * min (fun x ↦ p x).max (1 - (fun x ↦ p x).max) ^ (1 - α) / (1 - α)

/-- The distribution played by Tsallis-FTRL-SPM from the state `(G, β)`:
`(1 - γ) p̂ + γ p₀` with `γ = 4 c z / β`, for `d = d_x`. -/
noncomputable def spmDist (α βbar : ℝ) (d : ℕ) (p₀ : simplex 𝒳) (c : ℝ)
    (s : EuclideanSpace ℝ 𝒳 × ℝ) : simplex 𝒳 :=
  toSet (simplex 𝒳)
    ((1 - 4 * c * zCoef α d ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳) / s.2) •
        ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳)
      + (4 * c * zCoef α d ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳) / s.2) •
        (p₀ : EuclideanSpace ℝ 𝒳))

omit [Fintype ιx] in
@[fun_prop]
lemma measurable_spmHat (α βbar : ℝ) : Measurable (spmHat (𝒳 := 𝒳) α βbar) :=
  (measurable_ftrlSimplexParam (hybridEntropy α βbar)).comp (measurable_snd.prodMk measurable_fst)

omit [Fintype ιx] in
@[fun_prop]
lemma measurable_zCoef (α : ℝ) (d : ℕ) : Measurable (zCoef (𝒳 := 𝒳) α d) := by
  have hm : Measurable fun p : EuclideanSpace ℝ 𝒳 ↦ (fun x ↦ p x).max :=
    measurable_max.comp (by fun_prop)
  unfold zCoef
  refine Measurable.div ?_ measurable_const
  refine Measurable.mul measurable_const ?_
  refine Measurable.pow_const ?_ (1 - α)
  exact hm.min (measurable_const.sub hm)

omit [Fintype ιx] in
@[fun_prop]
lemma measurable_spmDist (α βbar : ℝ) (d : ℕ) (p₀ : simplex 𝒳) (c : ℝ) :
    Measurable (spmDist α βbar d p₀ c) := by
  have hp : Measurable fun s : EuclideanSpace ℝ 𝒳 × ℝ ↦
      ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳) :=
    measurable_subtype_coe.comp (measurable_spmHat α βbar)
  have hγ : Measurable fun s : EuclideanSpace ℝ 𝒳 × ℝ ↦
      4 * c * zCoef α d ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳) / s.2 :=
    (measurable_const.mul ((measurable_zCoef α d).comp hp)).div measurable_snd
  exact (measurable_toSet measurableSet_simplex).comp
    (((measurable_const.sub hγ).smul hp).add (hγ.smul measurable_const))

variable [DecidableEq ιx] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
  (φ : 𝒳 → EuclideanSpace ℝ ιx)

/-- The reward estimate `g(x) = r ⟪φ x_t, S(p)⁻¹ φ x⟫` of a round played with the distribution
`p` (action `x_t`, reward `r`). -/
noncomputable def spmEstimate (p : simplex 𝒳) (r : Round Unit 𝒳 ℝ) : EuclideanSpace ℝ 𝒳 :=
  WithLp.toLp _ fun x ↦ r.feedback *
    (WithLp.ofLp (φ r.action) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ x))

/-- The state update of Tsallis-FTRL-SPM: `(G, β) ↦ (G + g, β + z / (β φ_α(p̂)))`. -/
noncomputable def spmUpdate (α βbar : ℝ) (p₀ : simplex 𝒳) (c : ℝ)
    (s : EuclideanSpace ℝ 𝒳 × ℝ) (r : Round Unit 𝒳 ℝ) : EuclideanSpace ℝ 𝒳 × ℝ :=
  (s.1 + spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r,
    s.2 + zCoef α (Fintype.card ιx) ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳)
      / (s.2 * tsallisEntropy α ((spmHat α βbar s : simplex 𝒳) : EuclideanSpace ℝ 𝒳)))

omit [Nonempty 𝒳] in
@[fun_prop]
lemma measurable_spmEstimate {X : Type*} [MeasurableSpace X] {p : X → simplex 𝒳}
    {r : X → Round Unit 𝒳 ℝ} (hp : Measurable p) (hr : Measurable r) :
    Measurable fun x ↦ spmEstimate φ (p x) (r x) := by
  unfold spmEstimate
  fun_prop

@[fun_prop]
lemma measurable_spmUpdate {X : Type*} [MeasurableSpace X] (α βbar : ℝ) (p₀ : simplex 𝒳) (c : ℝ)
    {s : X → EuclideanSpace ℝ 𝒳 × ℝ} {r : X → Round Unit 𝒳 ℝ} (hs : Measurable s)
    (hr : Measurable r) : Measurable fun x ↦ spmUpdate φ α βbar p₀ c (s x) (r x) := by
  unfold spmUpdate
  fun_prop

/-- **Algorithm 3** (Tsallis-FTRL with stability-penalty matching, Ito et al. 2024) with
Tsallis parameter `α`, initial learning rate `β₁`, penalty coefficient `βbar`, exploration
distribution `p₀` with variance ratio `c`, as an uninformed algorithm on the action set `𝒳` with
features `φ`: the stateful algorithm with state `(G_n, β_n)` updated by `spmUpdate`, sampling
from `spmDist` of the state. -/
noncomputable def tsallisSPM (α β₁ βbar : ℝ) (p₀ : simplex 𝒳) (c : ℝ) : Algorithm Unit 𝒳 ℝ :=
  Algorithm.stateful (0, β₁) (fun _ ↦ spmUpdate φ α βbar p₀ c) (by fun_prop) fun _ ↦
    (simplexKernel 𝒳).comap (fun q ↦ spmDist α βbar (Fintype.card ιx) p₀ c q.1) (by fun_prop)

/-- The Tsallis parameter `α = 1 - 1 / (4 log m_x)` of Theorem 5. -/
noncomputable def spmAlpha (mx : ℕ) : ℝ := 1 - 1 / (4 * log mx)

/-- The initial learning rate `β₁ = 8 c d_x / (1 - α)` of Theorem 5. -/
noncomputable def spmBeta₁ (c : ℝ) (dx : ℕ) (α : ℝ) : ℝ := 8 * c * dx / (1 - α)

/-- The penalty coefficient `βbar = 32 d_x / ((1 - α)² β₁)` of Theorem 5. -/
noncomputable def spmBetaBar (dx : ℕ) (α β₁ : ℝ) : ℝ := 32 * dx / ((1 - α) ^ 2 * β₁)

/-- Tsallis-FTRL-SPM with the parameters of Theorem 5: `α = 1 - 1 / (4 log m_x)`,
`β₁ = 8 c d_x / (1 - α)`, `βbar = 32 d_x / ((1 - α)² β₁)`, for the exploration distribution `p₀`
with variance ratio `c`. -/
noncomputable def tsallisSPMPaper (c : ℝ) (p₀ : simplex 𝒳) : Algorithm Unit 𝒳 ℝ :=
  tsallisSPM φ (spmAlpha (Fintype.card 𝒳))
    (spmBeta₁ c (Fintype.card ιx) (spmAlpha (Fintype.card 𝒳)))
    (spmBetaBar (Fintype.card ιx) (spmAlpha (Fintype.card 𝒳))
      (spmBeta₁ c (Fintype.card ιx) (spmAlpha (Fintype.card 𝒳)))) p₀ c

end SPM

/-! ### Maximin-LinUCB (informed, bilinear games) -/

section LinUCB

variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy] {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒴] (φ : 𝒳 → EuclideanSpace ℝ ιx) (ψ : 𝒴 → EuclideanSpace ℝ ιy)

/-- The state of the ridge regression of Maximin-LinUCB: the matrix `V` and the vector `b` (the
library's ridge regression state for features indexed by `ιx × ιy`). -/
abbrev LinState (ιx ιy : Type*) := Bandits.Linear.RidgeState (ιx × ιy)

/-- The ridge regression update `(V, b) ↦ (V + a aᵀ, b + r a)` for the feature
`a = vec(φ x (ψ y)ᵀ)` of the round and its reward `r` (the library's `ridgeUpdate`). -/
noncomputable def linUpdate (s : LinState ιx ιy) (r : Round Unit 𝒳 (𝒴 × ℝ)) : LinState ιx ιy :=
  Bandits.Linear.ridgeUpdate s (pairFeature (φ r.action) (ψ r.feedback.1)) r.feedback.2

variable [Countable 𝒳] [MeasurableSingletonClass 𝒳] [Countable 𝒴] [MeasurableSingletonClass 𝒴]

omit [Fintype ιx] [Fintype ιy] in
@[fun_prop]
lemma measurable_linUpdate [Finite ιx] [Finite ιy] {X : Type*} [MeasurableSpace X]
    {s : X → LinState ιx ιy} {r : X → Round Unit 𝒳 (𝒴 × ℝ)} (hs : Measurable s)
    (hr : Measurable r) : Measurable fun x ↦ linUpdate φ ψ (s x) (r x) := by
  have := Fintype.ofFinite ιx
  have := Fintype.ofFinite ιy
  unfold linUpdate
  fun_prop

variable [DecidableEq ιx] [DecidableEq ιy]

/-- The optimistic index `U(x, y) = ⟪vec(x yᵀ), V⁻¹ b⟫ + β ‖vec(x yᵀ)‖_{V⁻¹}` of the pair
`(x, y)` from the ridge state `(V, b)` and the radius `β` (the library's optimistic index
`ucbIndex` of the feature `vec(x yᵀ)`, with the ridge estimate `V⁻¹ b = ridgeEstimate s`). -/
noncomputable def linIndex (β : ℝ) (s : LinState ιx ιy) (x : EuclideanSpace ℝ ιx)
    (y : EuclideanSpace ℝ ιy) : ℝ :=
  Bandits.Linear.ucbIndex β s (pairFeature x y)

@[fun_prop]
lemma measurable_linIndex {X : Type*} [MeasurableSpace X] {β : X → ℝ} {s : X → LinState ιx ιy}
    (hβ : Measurable β) (hs : Measurable s) (x : EuclideanSpace ℝ ιx) (y : EuclideanSpace ℝ ιy) :
    Measurable fun q ↦ linIndex (β q) (s q) x y := by
  unfold linIndex
  fun_prop

variable [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳] [Nonempty 𝒴]

/-- The action of Maximin-LinUCB from the ridge state: the pure maximin action
`argmax_x min_y U(x, y)` of the optimistic indices. -/
noncomputable def linAction (β : ℝ) (s : LinState ιx ιy) : 𝒳 :=
  argmax fun x ↦ (fun y ↦ linIndex β s (φ x) (ψ y)).min

/-- **Algorithm 4** (Maximin-LinUCB) with regularization `λ` and radii `β`: an informed
deterministic player which, at round `n`, plays the pure maximin action `linAction` of the
optimistic indices built from the ridge regression state
`(V_n, b_n) = (λ I + ∑_{s<n} a_s a_sᵀ, ∑_{s<n} r_s a_s)` and the radius `β n` (a stateful index
algorithm). -/
noncomputable def maximinLinUCB (lam : ℝ) (β : ℕ → ℝ) : Player 𝒳 𝒴 :=
  Algorithm.statefulIndex (lam • 1, 0) (fun _ ↦ linUpdate φ ψ) (by fun_prop)
    (fun n s _ x ↦ (fun y ↦ linIndex (β n) s (φ x) (ψ y)).min) (by fun_prop)

/-- The confidence radius `β_t = √(λ d) + √(2 log(1/δ) + d log(1 + t / (d λ)))` of
Maximin-LinUCB, with `d = d_x d_y`. -/
noncomputable def linRadius (d : ℕ) (lam δ : ℝ) (t : ℕ) : ℝ :=
  √(lam * d) + √(((2 : ℕ) : ℝ) * log (1 / δ) + d * log (1 + t / (d * lam)))

/-- The ridge regression state `(V_t, b_t)` after `t` rounds of the run `(X, Y, R)`. -/
noncomputable def linState {Ω : Type*} (lam : ℝ) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → 𝒴)
    (R : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : LinState ιx ιy :=
  stateProcess (fun _ ↦ linUpdate φ ψ) (lam • 1, 0) (fun _ _ ↦ ()) X (fun t ω ↦ (Y t ω, R t ω))
    t ω

end LinUCB

end Ito2026Adversarial
