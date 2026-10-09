/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.FTRLRegret
public import Ito2026Adversarial.Mathlib.Analysis.SpecialFunctions.Pow.Tangent
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# FTRL on the simplex with a hybrid Tsallis regularizer

Follow-the-regularized-leader on the probability simplex of `EuclideanSpace ℝ ι` for the hybrid
regularizer `β φ_α + βbar φ_{1-α}` (`φ_a = tsallisEntropy a`, `0 < α < 1`, `β > 0`,
`βbar ≥ 0`), as in the Tsallis-FTRL algorithm with stability-penalty matching of Ito, Tsuchiya
and Honda (2024). The FTRL objective is `hybridObjective α βbar β G p = ⟪p, G⟫ + β φ_α(p)
+ βbar φ_{1-α}(p)`, maximized over the simplex for the cumulative reward `G`.

## Main statements

* `exists_forall_hybridObjective_le`, `pos_of_forall_hybridObjective_le`,
  `exists_kkt_of_forall_hybridObjective_le`: the objective has a maximizer on the simplex, every
  maximizer has positive coordinates and satisfies the first-order conditions
  `G i + β p i ^ (α - 1) + βbar p i ^ (-α) = λ` (KKT);
* `hybridObjective_eq_sub_bregman`: at a KKT point `p`, the objective at any `r` of the simplex is
  the objective at `p` minus the Bregman divergences of the two Tsallis entropies; hence
  `hybridObjective_le_sub_sq`: quadratic growth around the maximizer;
* `ftrlSimplexParam_hybrid_eq`: the FTRL distribution `ftrlSimplexParam`, defined as the partial
  gradient of the joint value function in `(β, G)`, is the maximizer (Danskin's theorem for the
  joint value function, which is differentiable at every `(β, G)` with `β > 0`).
-/

@[expose] public section

open Finset Filter Asymptotics Set
open scoped RealInnerProductSpace Topology

namespace Learning

variable {ι : Type*} [Fintype ι]

/-! ### Tsallis entropies -/

/-- The Tsallis entropy is continuous for a nonnegative parameter. -/
lemma continuous_tsallisEntropy {a : ℝ} (ha : 0 ≤ a) : Continuous (tsallisEntropy (ι := ι) a) := by
  unfold tsallisEntropy
  refine continuous_const.mul (continuous_finsetSum _ fun i _ ↦ ?_)
  exact ((Real.continuous_rpow_const ha).comp (PiLp.continuous_apply 2 _ i)).sub
    (PiLp.continuous_apply 2 _ i)

/-- The Tsallis entropy of a point of the simplex is nonnegative, for `0 < a ≤ 1`. -/
lemma tsallisEntropy_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {p : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) : 0 ≤ tsallisEntropy a p := by
  unfold tsallisEntropy
  refine mul_nonneg (inv_nonneg.2 ha0.le) (sum_nonneg fun i _ ↦ sub_nonneg.2 ?_)
  calc p i = p i ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ p i ^ a := Real.rpow_le_rpow_of_exponent_ge' (hp.1 i) (le_one_of_mem_simplex hp i)
        ha0.le ha1

/-- The Tsallis entropy vanishes at the vertices of the simplex. -/
lemma tsallisEntropy_single [DecidableEq ι] {a : ℝ} (ha : a ≠ 0) (x : ι) :
    tsallisEntropy a (EuclideanSpace.single x (1 : ℝ)) = 0 := by
  unfold tsallisEntropy
  rw [sum_eq_zero fun i _ ↦ ?_, mul_zero]
  by_cases hi : i = x
  · subst hi
    simp
  · simp [hi, Real.zero_rpow ha]

/-! ### The objective and its coordinates -/

/-- The hybrid Tsallis regularizer `β φ_α + βbar φ_{1-α}`, with the learning rate `β` as
parameter. -/
noncomputable def hybridTsallis (α βbar β : ℝ) (p : EuclideanSpace ℝ ι) : ℝ :=
  β * tsallisEntropy α p + βbar * tsallisEntropy (1 - α) p

/-- The objective `⟪p, G⟫ + β φ_α(p) + βbar φ_{1-α}(p)` of FTRL with the hybrid Tsallis
regularizer, for the cumulative reward `G`. -/
noncomputable def hybridObjective (α βbar β : ℝ) (G p : EuclideanSpace ℝ ι) : ℝ :=
  ⟪p, G⟫ + hybridTsallis α βbar β p

/-- The contribution `g x + β (x ^ α - x) / α + βbar (x ^ (1 - α) - x) / (1 - α)` of a
coordinate `x` with reward `g` to the hybrid objective. -/
noncomputable def hybridCoord (α βbar β g x : ℝ) : ℝ :=
  g * x + β * (α⁻¹ * (x ^ α - x)) + βbar * ((1 - α)⁻¹ * (x ^ (1 - α) - x))

/-- The hybrid objective is the sum of the contributions of the coordinates. -/
lemma hybridObjective_eq_sum (α βbar β : ℝ) (G p : EuclideanSpace ℝ ι) :
    hybridObjective α βbar β G p = ∑ i, hybridCoord α βbar β (G i) (p i) := by
  simp only [hybridObjective, hybridTsallis, hybridCoord, tsallisEntropy, PiLp.inner_apply,
    RCLike.inner_apply,
    conj_trivial, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- The hybrid objective is continuous in `p`, for `0 ≤ α ≤ 1`. -/
lemma continuous_hybridObjective {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (βbar β : ℝ)
    (G : EuclideanSpace ℝ ι) : Continuous (hybridObjective α βbar β G) := by
  unfold hybridObjective hybridTsallis
  exact (continuous_id.inner continuous_const).add
    ((continuous_const.mul (continuous_tsallisEntropy hα0)).add
      (continuous_const.mul (continuous_tsallisEntropy (by linarith))))

/-- The hybrid objective has a maximizer on the simplex. -/
lemma exists_forall_hybridObjective_le [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (βbar β : ℝ) (G : EuclideanSpace ℝ ι) :
    ∃ p ∈ simplex ι, ∀ q ∈ simplex ι,
      hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p := by
  obtain ⟨p, hp, hmax⟩ := isCompact_simplex.exists_isMaxOn ⟨_, uniformVec_mem_simplex⟩
    (continuous_hybridObjective hα0 hα1 βbar β G).continuousOn
  exact ⟨p, hp, fun q hq ↦ hmax hq⟩

/-- The derivative `g + β (x ^ (α - 1) - 1 / α) + βbar (x ^ (-α) - 1 / (1 - α))` of the
contribution of a coordinate. -/
noncomputable def hybridCoordDeriv (α βbar β g x : ℝ) : ℝ :=
  g + β * (x ^ (α - 1) - α⁻¹) + βbar * (x ^ (-α) - (1 - α)⁻¹)

/-- The derivative of the contribution of a coordinate, at a positive point. -/
lemma hasDerivAt_hybridCoord {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (βbar β g : ℝ) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (hybridCoord α βbar β g) (hybridCoordDeriv α βbar β g x) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ α) (α * x ^ (α - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun x : ℝ ↦ x ^ (1 - α)) ((1 - α) * x ^ (1 - α - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h := (((hasDerivAt_id x).const_mul g).add
    (((h1.sub (hasDerivAt_id x)).const_mul α⁻¹).const_mul β)).add
    (((h2.sub (hasDerivAt_id x)).const_mul (1 - α)⁻¹).const_mul βbar)
  convert h using 1
  · funext y
    simp [hybridCoord]
  · have hα : α ≠ 0 := hα0.ne'
    have hα' : 1 - α ≠ 0 := by linarith
    simp only [hybridCoordDeriv, show 1 - α - 1 = -α by ring]
    field_simp

/-! ### Positivity and first-order conditions at a maximizer -/

section KKT

omit [Fintype ι] in
/-- The coordinates of `p + t (e_i - e_j)`. -/
lemma add_smul_single_sub_apply [DecidableEq ι] (p : EuclideanSpace ℝ ι) (t : ℝ) (i j k : ι) :
    (p + t • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1) : EuclideanSpace ℝ ι) k
      = p k + t * ((if k = i then 1 else 0) - if k = j then 1 else 0) := by
  simp [PiLp.single_apply]

/-- Moving mass `t` from the coordinate `j` to the coordinate `i` stays in the simplex for
`-p i ≤ t ≤ p j`. -/
lemma add_smul_single_sub_mem_simplex [DecidableEq ι] {p : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) {i j : ι} (hij : i ≠ j) {t : ℝ} (hti : -p i ≤ t) (htj : t ≤ p j) :
    p + t • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1) ∈ simplex ι := by
  refine ⟨fun k ↦ ?_, ?_⟩
  · rw [add_smul_single_sub_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
      linarith
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
        linarith
      · simp [hki, hkj, hp.1 k]
  · have : ∑ k, (p + t • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1) :
        EuclideanSpace ℝ ι) k = ∑ k, p k + t * (∑ k, (if k = i then (1 : ℝ) else 0)
          - ∑ k, (if k = j then (1 : ℝ) else 0)) := by
      simp only [add_smul_single_sub_apply, sum_add_distrib]
      rw [← sum_sub_distrib, mul_sum]
    rw [this, hp.2]
    simp

/-- The objective after moving mass `t` from the coordinate `j` to the coordinate `i`. -/
lemma hybridObjective_add_smul_single_sub [DecidableEq ι] (α βbar β : ℝ)
    (G p : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j) (t : ℝ) :
    hybridObjective α βbar β G
        (p + t • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1))
      = hybridObjective α βbar β G p
        + (hybridCoord α βbar β (G i) (p i + t) - hybridCoord α βbar β (G i) (p i))
        + (hybridCoord α βbar β (G j) (p j - t) - hybridCoord α βbar β (G j) (p j)) := by
  rw [hybridObjective_eq_sum, hybridObjective_eq_sum, add_assoc, ← sub_eq_iff_eq_add',
    ← sum_sub_distrib, sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simp [hij, hij.symm, sub_eq_add_neg]
  · intro k _ hk
    simp [hk.1, hk.2]

variable {α βbar β : ℝ}

/-- A lower bound on the increase of the contribution of a coordinate when moving it from `x` to
`x - t`, for `0 < t ≤ x / 2`. -/
lemma hybridCoord_sub_ge (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hβbar : 0 ≤ βbar) (g : ℝ)
    {x t : ℝ} (hx : 0 < x) (ht0 : 0 ≤ t) (ht : t ≤ x / 2) :
    -(|g| + β * (x / 2) ^ (α - 1) + βbar * (x / 2) ^ (-α)) * t
      ≤ hybridCoord α βbar β g (x - t) - hybridCoord α βbar β g x := by
  have hxt : x / 2 ≤ x - t := by linarith
  have hxt0 : 0 < x - t := by linarith
  have h1 := Real.rpow_le_rpow_add_mul_sub hα0.le hα1.le hxt0 hx.le
  have h2 := Real.rpow_le_rpow_add_mul_sub (a := 1 - α) (by linarith) (by linarith) hxt0 hx.le
  have h3 : (x - t) ^ (α - 1) ≤ (x / 2) ^ (α - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hxt (by linarith)
  have h4 : (x - t) ^ (1 - α - 1) ≤ (x / 2) ^ (-α) := by
    rw [show 1 - α - 1 = -α by ring]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxt (by linarith)
  have hα1' : 0 < 1 - α := by linarith
  have e1 : β * (α⁻¹ * ((x - t) ^ α - (x - t))) - β * (α⁻¹ * (x ^ α - x))
      ≥ -β * (x - t) ^ (α - 1) * t := by
    have : (x - t) ^ α - x ^ α ≥ -(α * (x - t) ^ (α - 1) * t) := by
      have := h1
      rw [show x - (x - t) = t by ring] at this
      linarith
    have hαinv : 0 < α⁻¹ := inv_pos.2 hα0
    have key : α⁻¹ * ((x - t) ^ α - (x - t)) - α⁻¹ * (x ^ α - x)
        ≥ -(x - t) ^ (α - 1) * t := by
      have e : α⁻¹ * ((x - t) ^ α - (x - t)) - α⁻¹ * (x ^ α - x)
          = α⁻¹ * ((x - t) ^ α - x ^ α) + α⁻¹ * t := by ring
      rw [e]
      have : α⁻¹ * ((x - t) ^ α - x ^ α) ≥ α⁻¹ * (-(α * (x - t) ^ (α - 1) * t)) :=
        mul_le_mul_of_nonneg_left this hαinv.le
      have e2 : α⁻¹ * (-(α * (x - t) ^ (α - 1) * t)) = -(x - t) ^ (α - 1) * t := by
        field_simp
      nlinarith [mul_nonneg hαinv.le ht0]
    nlinarith [mul_le_mul_of_nonneg_left key hβ]
  have e2 : βbar * ((1 - α)⁻¹ * ((x - t) ^ (1 - α) - (x - t)))
      - βbar * ((1 - α)⁻¹ * (x ^ (1 - α) - x)) ≥ -βbar * (x - t) ^ (1 - α - 1) * t := by
    have : (x - t) ^ (1 - α) - x ^ (1 - α) ≥ -((1 - α) * (x - t) ^ (1 - α - 1) * t) := by
      have := h2
      rw [show x - (x - t) = t by ring] at this
      linarith
    have hαinv : 0 < (1 - α)⁻¹ := inv_pos.2 hα1'
    have key : (1 - α)⁻¹ * ((x - t) ^ (1 - α) - (x - t)) - (1 - α)⁻¹ * (x ^ (1 - α) - x)
        ≥ -(x - t) ^ (1 - α - 1) * t := by
      have e : (1 - α)⁻¹ * ((x - t) ^ (1 - α) - (x - t)) - (1 - α)⁻¹ * (x ^ (1 - α) - x)
          = (1 - α)⁻¹ * ((x - t) ^ (1 - α) - x ^ (1 - α)) + (1 - α)⁻¹ * t := by ring
      rw [e]
      have : (1 - α)⁻¹ * ((x - t) ^ (1 - α) - x ^ (1 - α))
          ≥ (1 - α)⁻¹ * (-((1 - α) * (x - t) ^ (1 - α - 1) * t)) :=
        mul_le_mul_of_nonneg_left this hαinv.le
      have e2 : (1 - α)⁻¹ * (-((1 - α) * (x - t) ^ (1 - α - 1) * t))
          = -(x - t) ^ (1 - α - 1) * t := by
        field_simp
      nlinarith [mul_nonneg hαinv.le ht0]
    nlinarith [mul_le_mul_of_nonneg_left key hβbar]
  have hg : -|g| * t ≤ g * (x - t) - g * x := by
    nlinarith [le_abs_self g]
  simp only [hybridCoord]
  nlinarith [mul_le_mul_of_nonneg_right h3 (mul_nonneg hβ ht0),
    mul_le_mul_of_nonneg_right h4 (mul_nonneg hβbar ht0)]

/-- A lower bound on the increase of the contribution of a coordinate when moving it from `0` to
`t ∈ [0, 1]`: `β t ^ α / α - (|g| + β / α + βbar / (1 - α)) t`. -/
lemma hybridCoord_ge_of_zero (hα0 : 0 < α) (hα1 : α < 1) (hβbar : 0 ≤ βbar) (g : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) :
    β * α⁻¹ * t ^ α - (|g| + β * α⁻¹ + βbar * (1 - α)⁻¹) * t
      ≤ hybridCoord α βbar β g t - hybridCoord α βbar β g 0 := by
  have hα1' : 0 < 1 - α := by linarith
  have h0 : hybridCoord α βbar β g 0 = 0 := by
    simp [hybridCoord, Real.zero_rpow hα0.ne', Real.zero_rpow hα1'.ne']
  rw [h0, sub_zero]
  have ht1 : 0 ≤ t ^ (1 - α) := Real.rpow_nonneg ht0 _
  have hg : -|g| * t ≤ g * t := by nlinarith [neg_abs_le g]
  simp only [hybridCoord]
  have : 0 ≤ βbar * ((1 - α)⁻¹ * t ^ (1 - α)) := by positivity
  nlinarith

/-- **Positivity of the maximizer**: every maximizer of the hybrid objective on the simplex has
positive coordinates (the Tsallis entropy has an infinite slope at `0`). -/
lemma pos_of_forall_hybridObjective_le (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p)
    (j : ι) : 0 < p j := by
  classical
  rcases (hp.1 j).lt_or_eq with hj | hj
  · exact hj
  exfalso
  obtain ⟨k, hk⟩ : ∃ k, 0 < p k := by
    by_contra h
    push Not at h
    have : ∑ i, p i ≤ 0 := sum_nonpos fun i _ ↦ h i
    linarith [hp.2]
  have hjk : j ≠ k := by
    rintro rfl
    linarith
  have hα1' : 0 < 1 - α := by linarith
  set C := |G j| + β * α⁻¹ + βbar * (1 - α)⁻¹
    + (|G k| + β * (p k / 2) ^ (α - 1) + βbar * (p k / 2) ^ (-α)) with hC
  have hC0 : 0 < C := by
    have : 0 < β * α⁻¹ := mul_pos hβ (inv_pos.2 hα0)
    have : 0 ≤ (p k / 2) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ (p k / 2) ^ (-α) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ βbar * (1 - α)⁻¹ := mul_nonneg hβbar (inv_nonneg.2 hα1'.le)
    positivity
  set s := (β / (2 * α * C)) ^ (1 - α)⁻¹ with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  set t := min (p k / 2) s with ht
  have ht0 : 0 < t := lt_min (by linarith) hs0
  have ht1 : t ≤ p k / 2 := min_le_left _ _
  have hts : t ^ (1 - α) ≤ β / (2 * α * C) := by
    calc t ^ (1 - α) ≤ s ^ (1 - α) := Real.rpow_le_rpow ht0.le (min_le_right _ _) hα1'.le
      _ = β / (2 * α * C) := Real.rpow_inv_rpow (by positivity) hα1'.ne'
  have htt : t = t ^ (1 - α) * t ^ α := by
    rw [← Real.rpow_add ht0, show 1 - α + α = 1 by ring, Real.rpow_one]
  have hpos : C * t < β * α⁻¹ * t ^ α := by
    have hta : 0 < t ^ α := Real.rpow_pos_of_pos ht0 _
    calc C * t = C * t ^ (1 - α) * t ^ α := by rw [mul_assoc, ← htt]
      _ ≤ C * (β / (2 * α * C)) * t ^ α := by gcongr
      _ = β * α⁻¹ * t ^ α / 2 := by field_simp
      _ < β * α⁻¹ * t ^ α := by
          have : 0 < β * α⁻¹ * t ^ α := by positivity
          linarith
  have hmem := add_smul_single_sub_mem_simplex hp hjk (t := t) (by rw [← hj]; linarith)
    (by linarith)
  have hle := hmax _ hmem
  rw [hybridObjective_add_smul_single_sub α βbar β G p hjk t, hj.symm, zero_add] at hle
  have h1 := hybridCoord_ge_of_zero (β := β) hα0 hα1 hβbar (G j) ht0.le
  have h2 := hybridCoord_sub_ge hα0 hα1 hβ.le hβbar (G k) hk ht0.le ht1
  have : 0 < (hybridCoord α βbar β (G j) t - hybridCoord α βbar β (G j) 0)
      + (hybridCoord α βbar β (G k) (p k - t) - hybridCoord α βbar β (G k) (p k)) := by
    have : C * t = (|G j| + β * α⁻¹ + βbar * (1 - α)⁻¹) * t
        + (|G k| + β * (p k / 2) ^ (α - 1) + βbar * (p k / 2) ^ (-α)) * t := by
      rw [hC]
      ring
    linarith
  linarith

/-- **First-order conditions at a maximizer**: the derivatives of the contributions of two
coordinates of a maximizer are equal. -/
lemma hybridCoordDeriv_eq_of_forall_hybridObjective_le (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p)
    (i j : ι) :
    hybridCoordDeriv α βbar β (G i) (p i) = hybridCoordDeriv α βbar β (G j) (p j) := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hpi := pos_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax i
  have hpj := pos_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax j
  set h : ℝ → ℝ := fun s ↦ hybridCoord α βbar β (G i) (p i + s)
    + hybridCoord α βbar β (G j) (p j - s) with hh
  have hderiv : HasDerivAt h (hybridCoordDeriv α βbar β (G i) (p i)
      - hybridCoordDeriv α βbar β (G j) (p j)) 0 := by
    have h1 : HasDerivAt (fun s ↦ hybridCoord α βbar β (G i) (p i + s))
        (hybridCoordDeriv α βbar β (G i) (p i)) 0 :=
      HasDerivAt.comp_const_add (p i) 0
        (by rw [add_zero]; exact hasDerivAt_hybridCoord hα0 hα1 βbar β (G i) hpi)
    have h2 : HasDerivAt (fun s ↦ hybridCoord α βbar β (G j) (p j - s))
        (-hybridCoordDeriv α βbar β (G j) (p j)) 0 :=
      HasDerivAt.comp_const_sub (p j) 0
        (by rw [sub_zero]; exact hasDerivAt_hybridCoord hα0 hα1 βbar β (G j) hpj)
    rw [sub_eq_add_neg]
    exact h1.add h2
  have hloc : IsLocalMax h 0 := by
    have hδ : 0 < min (p i) (p j) := lt_min hpi hpj
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hs
    have hmem := add_smul_single_sub_mem_simplex hp hij (t := s)
      (by linarith [min_le_left (p i) (p j)]) (by linarith [min_le_right (p i) (p j)])
    have hle := hmax _ hmem
    rw [hybridObjective_add_smul_single_sub α βbar β G p hij s] at hle
    simp only [hh, add_zero, sub_zero]
    linarith
  have := hloc.hasDerivAt_eq_zero hderiv
  linarith

/-- **First-order conditions (KKT) at a maximizer**: there is `λ` with
`G i + β p i ^ (α - 1) + βbar p i ^ (-α) = λ` for all `i`. -/
lemma exists_kkt_of_forall_hybridObjective_le (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p) :
    ∃ l : ℝ, ∀ i, G i + β * p i ^ (α - 1) + βbar * p i ^ (-α) = l := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simpa using hp.2
  refine ⟨G i₀ + β * p i₀ ^ (α - 1) + βbar * p i₀ ^ (-α), fun i ↦ ?_⟩
  have := hybridCoordDeriv_eq_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax i i₀
  simp only [hybridCoordDeriv] at this
  linarith

end KKT

/-! ### Bregman divergences and quadratic growth -/

/-- The Bregman divergence `x ^ a + a x ^ (a - 1) (y - x) - y ^ a` of the convex function
`-x ^ a` between `y` and `x`. -/
noncomputable def powBregman (a y x : ℝ) : ℝ := x ^ a + a * x ^ (a - 1) * (y - x) - y ^ a

/-- The Bregman divergence of `-x ^ a` is nonnegative for `0 ≤ a ≤ 1` (concavity). -/
lemma powBregman_nonneg {a x y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) (hy : 0 ≤ y) :
    0 ≤ powBregman a y x := by
  have := Real.rpow_le_rpow_add_mul_sub ha0 ha1 hx hy
  unfold powBregman
  linarith

/-- The Bregman divergence of `-x ^ a` is at least quadratic on `[0, M]`. -/
lemma sq_le_powBregman {a x y M : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hxM : x ≤ M)
    (hy : 0 ≤ y) (hyM : y ≤ M) :
    a * (1 - a) * M ^ (a - 2) * (y - x) ^ 2 / 2 ≤ powBregman a y x :=
  Real.sq_le_rpow_bregman ha0 ha1 hx hxM hy hyM

variable {α βbar β : ℝ}

/-- The change of the contribution of a coordinate from `x` to `y`, in terms of the Bregman
divergences. -/
lemma hybridCoord_sub_eq (hα0 : 0 < α) (hα1 : α < 1) (g : ℝ) {x : ℝ} (y : ℝ) :
    hybridCoord α βbar β g y - hybridCoord α βbar β g x
      = (g + β * x ^ (α - 1) + βbar * x ^ (-α) - (β * α⁻¹ + βbar * (1 - α)⁻¹)) * (y - x)
        - β * α⁻¹ * powBregman α y x - βbar * (1 - α)⁻¹ * powBregman (1 - α) y x := by
  have hα : α ≠ 0 := hα0.ne'
  have hα' : 1 - α ≠ 0 := by linarith
  simp only [hybridCoord, powBregman, show 1 - α - 1 = -α by ring]
  field_simp
  ring

/-- **Three-point identity**: at a point `p` of the simplex with positive coordinates satisfying
the first-order conditions, the hybrid objective at any `r` of the simplex is the objective at
`p` minus `β / α` times the Bregman divergence of `φ_α` and `βbar / (1 - α)` times that of
`φ_{1-α}`. -/
lemma hybridObjective_eq_sub_bregman (hα0 : 0 < α) (hα1 : α < 1) {G p r : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) {l : ℝ} (hkkt : ∀ i, G i + β * p i ^ (α - 1) + βbar * p i ^ (-α) = l)
    (hr : r ∈ simplex ι) :
    hybridObjective α βbar β G r = hybridObjective α βbar β G p
      - β * α⁻¹ * ∑ i, powBregman α (r i) (p i)
      - βbar * (1 - α)⁻¹ * ∑ i, powBregman (1 - α) (r i) (p i) := by
  rw [hybridObjective_eq_sum, hybridObjective_eq_sum]
  have h : ∑ i, hybridCoord α βbar β (G i) (r i) - ∑ i, hybridCoord α βbar β (G i) (p i)
      = (l - (β * α⁻¹ + βbar * (1 - α)⁻¹)) * (∑ i, r i - ∑ i, p i)
        - β * α⁻¹ * ∑ i, powBregman α (r i) (p i)
        - βbar * (1 - α)⁻¹ * ∑ i, powBregman (1 - α) (r i) (p i) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib,
      ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hybridCoord_sub_eq hα0 hα1, hkkt i]
  rw [hr.2, hp.2, sub_self, mul_zero, zero_sub] at h
  linarith

/-- At a point `p` of the simplex with positive coordinates satisfying the first-order
conditions, the hybrid objective at `r` is at most the objective at `p` minus
`β / α ∑ i, powBregman α (r i) (p i)`. -/
lemma hybridObjective_le_sub_bregman (hα0 : 0 < α) (hα1 : α < 1) (hβbar : 0 ≤ βbar)
    {G p r : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i) {l : ℝ}
    (hkkt : ∀ i, G i + β * p i ^ (α - 1) + βbar * p i ^ (-α) = l) (hr : r ∈ simplex ι) :
    hybridObjective α βbar β G r
      ≤ hybridObjective α βbar β G p - β * α⁻¹ * ∑ i, powBregman α (r i) (p i) := by
  rw [hybridObjective_eq_sub_bregman hα0 hα1 hp hkkt hr]
  have : 0 ≤ βbar * (1 - α)⁻¹ * ∑ i, powBregman (1 - α) (r i) (p i) :=
    mul_nonneg (mul_nonneg hβbar (inv_nonneg.2 (by linarith)))
      (sum_nonneg fun i _ ↦ powBregman_nonneg (by linarith) (by linarith) (hpos i) (hr.1 i))
  linarith

/-- **Quadratic growth** around a point `p` of the simplex with positive coordinates satisfying
the first-order conditions: `obj r ≤ obj p - β (1 - α) / 2 ‖r - p‖²`. -/
lemma hybridObjective_le_sub_sq (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hβbar : 0 ≤ βbar)
    {G p r : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i) {l : ℝ}
    (hkkt : ∀ i, G i + β * p i ^ (α - 1) + βbar * p i ^ (-α) = l) (hr : r ∈ simplex ι) :
    hybridObjective α βbar β G r
      ≤ hybridObjective α βbar β G p - β * (1 - α) / 2 * ‖r - p‖ ^ 2 := by
  refine (hybridObjective_le_sub_bregman hα0 hα1 hβbar hp hpos hkkt hr).trans ?_
  have hsq : β * (1 - α) / 2 * ‖r - p‖ ^ 2
      ≤ β * α⁻¹ * ∑ i, powBregman α (r i) (p i) := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_sum, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    have h := sq_le_powBregman hα0 hα1 (hpos i) (le_one_of_mem_simplex hp i) (hr.1 i)
      (le_one_of_mem_simplex hr i)
    rw [Real.one_rpow, mul_one] at h
    have hα : α ≠ 0 := hα0.ne'
    calc β * (1 - α) / 2 * (r - p) i ^ 2 = β * α⁻¹ * (α * (1 - α) * (r i - p i) ^ 2 / 2) := by
          simp only [PiLp.sub_apply]
          field_simp
      _ ≤ β * α⁻¹ * powBregman α (r i) (p i) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hβ (inv_nonneg.2 hα0.le))
  linarith

/-! ### The maximizer -/

section Maximizer

/-- Quadratic growth around a maximizer of the hybrid objective. -/
lemma hybridObjective_le_sub_sq_of_forall_le (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p)
    {r : EuclideanSpace ℝ ι} (hr : r ∈ simplex ι) :
    hybridObjective α βbar β G r
      ≤ hybridObjective α βbar β G p - β * (1 - α) / 2 * ‖r - p‖ ^ 2 := by
  obtain ⟨l, hl⟩ := exists_kkt_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax
  exact hybridObjective_le_sub_sq hα0 hα1 hβ.le hβbar hp
    (pos_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax) hl hr

/-- The maximizer of the hybrid objective on the simplex is unique. -/
lemma eq_of_forall_hybridObjective_le (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p r : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p)
    (hr : r ∈ simplex ι)
    (hmax' : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G r) :
    r = p := by
  have h1 := hybridObjective_le_sub_sq_of_forall_le hα0 hα1 hβ hβbar hp hmax hr
  have h2 := hmax' p hp
  have hμ : 0 < β * (1 - α) / 2 := by
    have : 0 < 1 - α := by linarith
    positivity
  have : ‖r - p‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖r - p‖ = 0 := by nlinarith [norm_nonneg (r - p)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- The hybrid objective at `(β + b, G + θ)` is the objective at `(β, G)` plus
`b φ_α(q) + ⟪q, θ⟫`. -/
lemma hybridObjective_add (α βbar β b : ℝ) (G θ q : EuclideanSpace ℝ ι) :
    hybridObjective α βbar (β + b) (G + θ) q
      = hybridObjective α βbar β G q + b * tsallisEntropy α q + ⟪q, θ⟫ := by
  simp only [hybridObjective, hybridTsallis, inner_add_right]
  ring

/-- The Tsallis entropy of a point of the simplex is at most `card ι / a`. -/
lemma tsallisEntropy_le_card_div {a : ℝ} (ha0 : 0 < a) {q : EuclideanSpace ℝ ι}
    (hq : q ∈ simplex ι) : tsallisEntropy a q ≤ Fintype.card ι / a := by
  unfold tsallisEntropy
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  calc ∑ i, (q i ^ a - q i) ≤ ∑ _i : ι, (1 : ℝ) := sum_le_sum fun i _ ↦ by
        have := Real.rpow_le_one (hq.1 i) (le_one_of_mem_simplex hq i) ha0.le
        linarith [hq.1 i]
    _ = Fintype.card ι := by simp

/-- **Danskin's theorem for the joint value function**: for `β > 0`, the joint value function
`(β, G) ↦ max_{p ∈ simplex} ⟪p, G⟫ + β φ_α(p) + βbar φ_{1-α}(p)` is differentiable at `(β, G)`,
with derivative `(b, θ) ↦ b φ_α(p) + ⟪p, θ⟫` where `p` is the maximizer. -/
lemma hasFDerivAt_ftrlValueParam_hybrid [Nonempty ι] (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p) :
    HasFDerivAt
      (ftrlValueParam (hybridTsallis (ι := ι) α βbar))
      (tsallisEntropy α p • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ ι)
        + (innerSL ℝ p).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ ι))) (β, G) := by
  set V := ftrlValueParam (hybridTsallis (ι := ι) α βbar) with hV
  set L := tsallisEntropy α p • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ ι)
    + (innerSL ℝ p).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ ι)) with hL
  -- a maximizer at every point
  have hex (z : ℝ × EuclideanSpace ℝ ι) := exists_forall_hybridObjective_le (ι := ι) hα0.le
    hα1.le βbar z.1 z.2
  choose P hP hPmax using hex
  have hVeq (z : ℝ × EuclideanSpace ℝ ι) : V z = hybridObjective α βbar z.1 z.2 (P z) :=
    ftrlValue_eq_of_isMaxOn (hP z) (hPmax z)
  have hV0 : V (β, G) = hybridObjective α βbar β G p := ftrlValue_eq_of_isMaxOn hp hmax
  have hLh (h : ℝ × EuclideanSpace ℝ ι) : L h = h.1 * tsallisEntropy α p + ⟪p, h.2⟫ := by
    simp [hL, mul_comm]
  set μ := β * (1 - α) / 2 with hμ
  have hμ0 : 0 < μ := by
    have : 0 < 1 - α := by linarith
    positivity
  -- the two basic inequalities
  have hbounds (h : ℝ × EuclideanSpace ℝ ι) :
      0 ≤ V ((β, G) + h) - V (β, G) - L h ∧
      V ((β, G) + h) - V (β, G) - L h + μ * ‖P ((β, G) + h) - p‖ ^ 2
        ≤ h.1 * (tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p)
          + ⟪P ((β, G) + h) - p, h.2⟫ := by
    have hz : (β, G) + h = (β + h.1, G + h.2) := rfl
    rw [hz]
    have e1 := hVeq (β + h.1, G + h.2)
    simp only at e1
    have e2 := hybridObjective_add α βbar β h.1 G h.2 (P (β + h.1, G + h.2))
    have e3 := hybridObjective_add α βbar β h.1 G h.2 p
    have hge := hPmax (β + h.1, G + h.2) p hp
    simp only at hge
    have hgrowth := hybridObjective_le_sub_sq_of_forall_le hα0 hα1 hβ hβbar hp hmax
      (hP (β + h.1, G + h.2))
    rw [hLh, hV0, e1, inner_sub_left]
    constructor <;> nlinarith
  -- continuity of the maximizer
  have hK : ∀ q ∈ simplex ι, |tsallisEntropy α q - tsallisEntropy α p| ≤ Fintype.card ι / α := by
    intro q hq
    rw [abs_le]
    have := tsallisEntropy_le_card_div hα0 hq
    have := tsallisEntropy_le_card_div hα0 hp
    have := tsallisEntropy_nonneg hα0 hα1.le hq
    have := tsallisEntropy_nonneg hα0 hα1.le hp
    constructor <;> linarith
  have hsq (h : ℝ × EuclideanSpace ℝ ι) :
      ‖P ((β, G) + h) - p‖ ^ 2 ≤ (Fintype.card ι / α + 2) / μ * ‖h‖ := by
    obtain ⟨h0, h1⟩ := hbounds h
    have hq := hP ((β, G) + h)
    have hnorm : ‖P ((β, G) + h) - p‖ ≤ 2 := (norm_sub_le _ _).trans
      (by linarith [norm_le_one_of_mem_simplex hq, norm_le_one_of_mem_simplex hp])
    have i1 : h.1 * (tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p)
        ≤ ‖h‖ * (Fintype.card ι / α) := by
      calc _ ≤ |h.1 * (tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p)| := le_abs_self _
        _ = ‖h.1‖ * |tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p| := by
            rw [abs_mul, Real.norm_eq_abs]
        _ ≤ ‖h‖ * (Fintype.card ι / α) :=
            mul_le_mul (norm_fst_le h) (hK _ hq) (abs_nonneg _) (norm_nonneg _)
    have i2 : ⟪P ((β, G) + h) - p, h.2⟫ ≤ ‖h‖ * 2 :=
      (real_inner_le_norm _ _).trans (by
        rw [mul_comm]
        exact mul_le_mul (norm_snd_le h) hnorm (norm_nonneg _) (norm_nonneg _))
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ0]
    nlinarith
  have hPtend : Tendsto (fun h : ℝ × EuclideanSpace ℝ ι ↦ P ((β, G) + h)) (𝓝 0) (𝓝 p) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun h : ℝ × EuclideanSpace ℝ ι ↦
        √((Fintype.card ι / α + 2) / μ * ‖h‖)) (𝓝 0) (𝓝 0) := by
      have : Continuous fun h : ℝ × EuclideanSpace ℝ ι ↦
          √((Fintype.card ι / α + 2) / μ * ‖h‖) := by fun_prop
      simpa using this.tendsto 0
    refine squeeze_zero (fun h ↦ norm_nonneg _) (fun h ↦ ?_) hlim
    exact Real.le_sqrt_of_sq_le (hsq h)
  have hεtend : Tendsto (fun h : ℝ × EuclideanSpace ℝ ι ↦
      |tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p| + ‖P ((β, G) + h) - p‖)
      (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ × EuclideanSpace ℝ ι ↦ tsallisEntropy α (P ((β, G) + h)))
        (𝓝 0) (𝓝 (tsallisEntropy α p)) :=
      ((continuous_tsallisEntropy hα0.le).tendsto p).comp hPtend
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 hPtend)
    have h3 : Tendsto (fun h : ℝ × EuclideanSpace ℝ ι ↦
        |tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p|) (𝓝 0) (𝓝 0) := by
      have := (h1.sub_const (tsallisEntropy α p)).abs
      simpa using this
    simpa using h3.add h2
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  filter_upwards [(tendsto_order.1 hεtend).2 c hc] with h hh
  obtain ⟨h0, h1⟩ := hbounds h
  have hq := hP ((β, G) + h)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have i1 : h.1 * (tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p)
      ≤ ‖h‖ * |tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p| := by
    calc _ ≤ |h.1 * (tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p)| := le_abs_self _
      _ = ‖h.1‖ * |tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p| := by
          rw [abs_mul, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_right (norm_fst_le h) (abs_nonneg _)
  have i2 : ⟪P ((β, G) + h) - p, h.2⟫ ≤ ‖h‖ * ‖P ((β, G) + h) - p‖ :=
    (real_inner_le_norm _ _).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_snd_le h) (norm_nonneg _))
  have : 0 ≤ μ * ‖P ((β, G) + h) - p‖ ^ 2 := by positivity
  calc V ((β, G) + h) - V (β, G) - L h
      ≤ ‖h‖ * (|tsallisEntropy α (P ((β, G) + h)) - tsallisEntropy α p|
        + ‖P ((β, G) + h) - p‖) := by nlinarith
    _ ≤ c * ‖h‖ := by
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left hh.le (norm_nonneg _)

/-- **The FTRL distribution of the hybrid regularizer is the maximizer.** For `β > 0`, the FTRL
distribution `ftrlSimplexParam` (the partial gradient in `G` of the joint value function) at
`(β, G)` is the maximizer of the hybrid objective. -/
lemma ftrlSimplexParam_hybrid_eq [Nonempty ι] (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβbar : 0 ≤ βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p) :
    ftrlSimplexParam (hybridTsallis α βbar) (β, G)
      = ⟨p, hp⟩ := by
  unfold ftrlSimplexParam gradientSnd
  rw [(hasFDerivAt_ftrlValueParam_hybrid hα0 hα1 hβ hβbar hp hmax).fderiv]
  have : (tsallisEntropy α p • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ ι)
      + (innerSL ℝ p).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ ι))).comp
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ ι))
      = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) p := by
    ext θ
    simp
  rw [this, LinearIsometryEquiv.symm_apply_apply, toSet_of_mem hp]

/-- For `β > 0`, the FTRL distribution `ftrlSimplexParam` of the hybrid regularizer maximizes the
hybrid objective. -/
lemma forall_hybridObjective_le_ftrlSimplexParam [Nonempty ι] (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβbar : 0 ≤ βbar) (G : EuclideanSpace ℝ ι) :
    ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G
      (ftrlSimplexParam (hybridTsallis α βbar)
        (β, G) : EuclideanSpace ℝ ι) := by
  obtain ⟨p, hp, hmax⟩ := exists_forall_hybridObjective_le (ι := ι) hα0.le hα1.le βbar β G
  rw [ftrlSimplexParam_hybrid_eq hα0 hα1 hβ hβbar hp hmax]
  exact hmax

end Maximizer

/-! ### Stability -/

/-- For `K ≥ 1` and `0 ≤ a ≤ 1`, `K ^ (-a) ≤ 1 - a (1 - 1 / K)` (Bernoulli's inequality). -/
lemma rpow_neg_le_one_sub_mul {K a : ℝ} (hK : 1 ≤ K) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    K ^ (-a) ≤ 1 - a * (1 - 1 / K) := by
  have hK0 : 0 < K := by linarith
  have h := rpow_one_add_le_one_add_mul_self (s := 1 / K - 1)
    (by have : 0 ≤ 1 / K := by positivity
        linarith) ha0 ha1
  rw [add_sub_cancel, Real.div_rpow zero_le_one hK0.le, Real.one_rpow] at h
  calc K ^ (-a) = 1 / K ^ a := by rw [Real.rpow_neg hK0.le, one_div]
    _ ≤ 1 + a * (1 / K - 1) := h
    _ = 1 - a * (1 - 1 / K) := by ring

/-- `2 ^ (α - 1) ≤ 1 - (1 - α) / 2` for `0 ≤ α ≤ 1`. -/
lemma two_rpow_sub_one_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (2 : ℝ) ^ (α - 1) ≤ 1 - (1 - α) / 2 := by
  have := rpow_neg_le_one_sub_mul (K := 2) (a := 1 - α) (by norm_num) (by linarith) (by linarith)
  rw [neg_sub] at this
  linarith

/-- **One-dimensional stability** of the Tsallis entropy: for `β > 0`, `x > 0`, `y ≥ 0` and
`g ≤ (1 - α) β x ^ (α - 1) / 2`,
`g (y - x) - β / α powBregman α y x ≤ 2 x ^ (2 - α) g² / ((1 - α) β)`. -/
lemma mul_sub_sub_powBregman_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {β : ℝ} (hβ : 0 < β)
    {x y g : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hg : g ≤ (1 - α) * β * x ^ (α - 1) / 2) :
    g * (y - x) - β * α⁻¹ * powBregman α y x ≤ 2 * x ^ (2 - α) * g ^ 2 / ((1 - α) * β) := by
  have hα1' : 0 < 1 - α := by linarith
  have h2x : 0 < 2 * x := by linarith
  -- the bound for `y ≤ 2 x`
  have hnear (y : ℝ) (hy : 0 ≤ y) (hy2 : y ≤ 2 * x) :
      g * (y - x) - β * α⁻¹ * powBregman α y x ≤ 2 * x ^ (2 - α) * g ^ 2 / ((1 - α) * β) := by
    have hq := sq_le_powBregman hα0 hα1 hx (by linarith) hy hy2
    set c := β * (1 - α) * (2 * x) ^ (α - 2) with hc
    have hc0 : 0 < c := by positivity
    have hB : c * (y - x) ^ 2 / 2 ≤ β * α⁻¹ * powBregman α y x := by
      have := mul_le_mul_of_nonneg_left hq (mul_nonneg hβ.le (inv_nonneg.2 hα0.le))
      calc c * (y - x) ^ 2 / 2
          = β * α⁻¹ * (α * (1 - α) * (2 * x) ^ (α - 2) * (y - x) ^ 2 / 2) := by
            rw [hc]
            field_simp
        _ ≤ _ := this
    have hamgm : g * (y - x) - c * (y - x) ^ 2 / 2 ≤ g ^ 2 / (2 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (g - c * (y - x))]
    have hpow : (2 * x) ^ (2 - α) ≤ 4 * x ^ (2 - α) := by
      rw [Real.mul_rpow (by norm_num) hx.le]
      gcongr
      calc (2 : ℝ) ^ (2 - α) ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have hinv : (2 * x) ^ (α - 2) * (2 * x) ^ (2 - α) = 1 := by
      rw [← Real.rpow_add h2x, show α - 2 + (2 - α) = 0 by ring, Real.rpow_zero]
    have hfinal : g ^ 2 / (2 * c) ≤ 2 * x ^ (2 - α) * g ^ 2 / ((1 - α) * β) := by
      have e : g ^ 2 / (2 * c) = (2 * x) ^ (2 - α) * g ^ 2 / (2 * ((1 - α) * β)) := by
        rw [hc]
        field_simp
        rw [mul_assoc, hinv, mul_one]
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right hpow (sq_nonneg g)
      nlinarith [mul_pos hα1' hβ]
    linarith
  rcases le_or_gt y (2 * x) with hy2 | hy2
  · exact hnear y hy hy2
  · refine le_trans ?_ (hnear (2 * x) h2x.le le_rfl)
    -- tangent line of `x ^ α` at `2 x`
    have ht := Real.rpow_le_rpow_add_mul_sub hα0.le hα1.le h2x hy
    have hcoef : g - β * x ^ (α - 1) + β * (2 * x) ^ (α - 1) ≤ 0 := by
      have h2 := two_rpow_sub_one_le hα0.le hα1.le
      rw [Real.mul_rpow (by norm_num) hx.le]
      have hxa : 0 < x ^ (α - 1) := Real.rpow_pos_of_pos hx _
      nlinarith [mul_le_mul_of_nonneg_right h2 (mul_nonneg hβ.le hxa.le)]
    have hα : α ≠ 0 := hα0.ne'
    have key : g * (y - x) - β * α⁻¹ * powBregman α y x
        ≤ g * (2 * x - x) - β * α⁻¹ * powBregman α (2 * x) x
          + (g - β * x ^ (α - 1) + β * (2 * x) ^ (α - 1)) * (y - 2 * x) := by
      simp only [powBregman]
      have hb : β * α⁻¹ * (y ^ α) ≤ β * α⁻¹ * ((2 * x) ^ α + α * (2 * x) ^ (α - 1) * (y - 2 * x)) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg hβ.le (inv_nonneg.2 hα0.le))
      have e : β * α⁻¹ * (α * (2 * x) ^ (α - 1) * (y - 2 * x))
          = β * (2 * x) ^ (α - 1) * (y - 2 * x) := by field_simp
      have e' : β * α⁻¹ * (α * x ^ (α - 1) * (y - x)) = β * x ^ (α - 1) * (y - x) := by
        field_simp
      have e'' : β * α⁻¹ * (α * x ^ (α - 1) * (2 * x - x)) = β * x ^ (α - 1) * (2 * x - x) := by
        field_simp
      nlinarith
    nlinarith [mul_nonneg (neg_nonneg.2 hcoef) (by linarith : (0 : ℝ) ≤ y - 2 * x)]

section QStar

variable [Nonempty ι]

/-- `q* = min (‖p‖_∞, 1 - ‖p‖_∞)`: the distance of the distribution `p` to the vertices. -/
noncomputable def qStar (p : EuclideanSpace ℝ ι) : ℝ :=
  min (fun i ↦ p i).max (1 - (fun i ↦ p i).max)

/-- `q*` is measurable. -/
@[fun_prop]
lemma measurable_qStar : Measurable (qStar (ι := ι)) := by
  have hm : Measurable fun p : EuclideanSpace ℝ ι ↦ (fun i ↦ p i).max :=
    measurable_max.comp (by fun_prop)
  exact hm.min (measurable_const.sub hm)

/-- `q* ≤ ‖p‖_∞`. -/
lemma qStar_le_max (p : EuclideanSpace ℝ ι) : qStar p ≤ (fun i ↦ p i).max := min_le_left _ _

/-- `q* ≤ 1 - ‖p‖_∞`. -/
lemma qStar_le_one_sub_max (p : EuclideanSpace ℝ ι) : qStar p ≤ 1 - (fun i ↦ p i).max :=
  min_le_right _ _

/-- `q*` is nonnegative on the simplex. -/
lemma qStar_nonneg {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) : 0 ≤ qStar p := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  refine le_min ?_ ?_
  · rw [← hj]
    exact hp.1 j
  · rw [← hj]
    linarith [le_one_of_mem_simplex hp j]

/-- `q* ≤ 1/2`. -/
lemma qStar_le_half (p : EuclideanSpace ℝ ι) : qStar p ≤ 1 / 2 := by
  unfold qStar
  rcases le_total (fun i ↦ p i).max (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

omit [Nonempty ι] in
/-- Two distinct coordinates of a point of the simplex sum to at most `1`. -/
lemma add_le_one_of_mem_simplex {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {i j : ι}
    (hij : i ≠ j) : p i + p j ≤ 1 := by
  classical
  rw [← hp.2, ← sum_pair hij]
  exact sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ ↦ hp.1 k

/-- A coordinate of `p` which is not a maximal coordinate is at most `q*`. -/
lemma le_qStar_of_ne {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {i j : ι}
    (hj : p j = (fun i ↦ p i).max) (hij : i ≠ j) : p i ≤ qStar p := by
  refine le_min (Function.le_max (fun i ↦ p i) i) ?_
  have := add_le_one_of_mem_simplex hp hij
  rw [← hj]
  linarith

/-- If a coordinate of `p` exceeds `q*`, it is larger than `1/2`. -/
lemma half_lt_of_qStar_lt {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {i : ι}
    (hi : qStar p < p i) : 1 / 2 < p i := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  by_cases hij : i = j
  · subst hij
    by_contra hle
    push Not at hle
    have : qStar p = p i := by
      unfold qStar
      rw [← hj]
      exact min_eq_left (by linarith)
    linarith
  · exact absurd (le_qStar_of_ne hp hj hij) (not_le.2 hi)

/-- If all the coordinates of `p` are at least `ℓ` and there are at least two coordinates, then
`ℓ ≤ q*`. -/
lemma le_qStar_of_forall_le {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) {ℓ : ℝ}
    (hℓ : ∀ i, ℓ ≤ p i) (hcard : 2 ≤ Fintype.card ι) : ℓ ≤ qStar p := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  obtain ⟨k, hk⟩ : ∃ k, k ≠ j := by
    by_contra h
    push Not at h
    have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ by rw [h a, h b]
    omega
  refine le_min ?_ ?_
  · rw [← hj]
    exact hℓ j
  · have := add_le_one_of_mem_simplex hp hk
    rw [← hj]
    linarith [hℓ k]

/-- For every coordinate `x`, `q* ≤ 1 - p x`. -/
lemma qStar_le_one_sub {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (x : ι) :
    qStar p ≤ 1 - p x := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  by_cases hxj : x = j
  · subst hxj
    rw [hj]
    exact qStar_le_one_sub_max p
  · have := add_le_one_of_mem_simplex hp hxj
    have := qStar_le_max p
    rw [← hj] at this
    linarith

/-- `q* > 0` for a point of the simplex with positive coordinates and at least two coordinates. -/
lemma qStar_pos {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i)
    (hcard : 2 ≤ Fintype.card ι) : 0 < qStar p := by
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  obtain ⟨k, hk⟩ : ∃ k, k ≠ j := by
    by_contra h
    push Not at h
    have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ by rw [h a, h b]
    omega
  refine lt_min ?_ ?_
  · rw [← hj]
    exact hpos j
  · have := add_le_one_of_mem_simplex hp hk
    rw [← hj]
    linarith [hpos k]

end QStar

/-- **Stability on the simplex**: if `p` is a point of the simplex with positive coordinates and
`|g i| ≤ (1 - α) β q* ^ (α - 1) / 4` for all `i`, then for every `r` of the simplex,
`⟪r - p, g⟫ - β / α ∑ i, powBregman α (r i) (p i) ≤ 4 / ((1 - α) β) q* ^ (1 - α) ∑ i, p i g i²`.
The maximal coordinate is excluded from the variance term by shifting the estimates. -/
lemma inner_sub_sub_bregman_le [Nonempty ι] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {β : ℝ}
    (hβ : 0 < β) {p r g : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i)
    (hr : r ∈ simplex ι) (hq : 0 < qStar p)
    (hg : ∀ i, |g i| ≤ (1 - α) * β * qStar p ^ (α - 1) / 4) :
    ⟪r - p, g⟫ - β * α⁻¹ * ∑ i, powBregman α (r i) (p i)
      ≤ 4 / ((1 - α) * β) * qStar p ^ (1 - α) * ∑ i, p i * g i ^ 2 := by
  classical
  have hα1' : 0 < 1 - α := by linarith
  have hk : 0 < 4 / ((1 - α) * β) := by positivity
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  have hinner (c : ℝ) : ⟪r - p, g⟫ = ∑ i, (g i - c) * (r i - p i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.sub_apply]
    have : ∑ i, c * (r i - p i) = 0 := by
      rw [← mul_sum, sum_sub_distrib, hr.2, hp.2, sub_self, mul_zero]
    have h2 : ∑ i, (g i - c) * (r i - p i) = ∑ i, g i * (r i - p i) - ∑ i, c * (r i - p i) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [h2, this, sub_zero]
  -- coordinates below `q*`
  have hle_pow (i : ι) (hi : p i ≤ qStar p) : qStar p ^ (α - 1) ≤ p i ^ (α - 1) :=
    Real.rpow_le_rpow_of_nonpos (hpos i) hi (by linarith)
  have hpow2 (i : ι) (hi : p i ≤ qStar p) :
      p i ^ (2 - α) ≤ qStar p ^ (1 - α) * p i := by
    rw [show 2 - α = (1 - α) + 1 by ring, Real.rpow_add (hpos i), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hpos i).le hi hα1'.le) (hpos i).le
  rcases le_or_gt (p j) (1 / 2) with hj2 | hj2
  · -- no shift: all coordinates are below `q* = max p`
    have hqj : qStar p = p j := by
      unfold qStar
      rw [← hj]
      exact min_eq_left (by linarith)
    have hall (i : ι) : p i ≤ qStar p := by
      rw [hqj, hj]
      exact Function.le_max (fun i ↦ p i) i
    rw [hinner 0, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun i _ ↦ ?_
    have h1 := mul_sub_sub_powBregman_le hα0 hα1 hβ (hpos i) (hr.1 i) (g := g i - 0) (by
      have h1 := (le_abs_self (g i)).trans (hg i)
      have h2 := mul_le_mul_of_nonneg_left (hle_pow i (hall i))
        (by positivity : (0 : ℝ) ≤ (1 - α) * β)
      have h3 : 0 ≤ (1 - α) * β * p i ^ (α - 1) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg (hpos i).le _)
      linarith)
    simp only [sub_zero] at h1 ⊢
    calc g i * (r i - p i) - β * α⁻¹ * powBregman α (r i) (p i)
        ≤ 2 * p i ^ (2 - α) * g i ^ 2 / ((1 - α) * β) := h1
      _ ≤ 4 / ((1 - α) * β) * qStar p ^ (1 - α) * (p i * g i ^ 2) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
          nlinarith [hpow2 i (hall i), sq_nonneg (g i), Real.rpow_nonneg (hpos i).le (2 - α)]
  · -- shift by `g j`
    have hqj : qStar p = 1 - p j := by
      unfold qStar
      rw [← hj]
      exact min_eq_right (by linarith)
    rw [hinner (g j), mul_sum, mul_sum, ← sum_sub_distrib]
    have hterm (i : ι) : (g i - g j) * (r i - p i) - β * α⁻¹ * powBregman α (r i) (p i)
        ≤ 4 / ((1 - α) * β) * qStar p ^ (1 - α)
          * (if i = j then 0 else p i * g i ^ 2 + p i * g j ^ 2) := by
      by_cases hij : i = j
      · subst hij
        simp only [sub_self, zero_mul, zero_sub, ite_true, mul_zero, neg_nonpos]
        exact mul_nonneg (mul_nonneg hβ.le (inv_nonneg.2 hα0.le))
          (powBregman_nonneg hα0.le hα1.le (hpos i) (hr.1 i))
      · simp only [hij, ite_false]
        have hi := le_qStar_of_ne hp hj hij
        have h1 := mul_sub_sub_powBregman_le hα0 hα1 hβ (hpos i) (hr.1 i) (g := g i - g j) (by
          have := hg i
          have := hg j
          have := le_abs_self (g i)
          have := neg_abs_le (g j)
          have := hle_pow i hi
          have : 0 ≤ (1 - α) * β := by positivity
          nlinarith)
        calc (g i - g j) * (r i - p i) - β * α⁻¹ * powBregman α (r i) (p i)
            ≤ 2 * p i ^ (2 - α) * (g i - g j) ^ 2 / ((1 - α) * β) := h1
          _ ≤ 4 / ((1 - α) * β) * qStar p ^ (1 - α) * (p i * g i ^ 2 + p i * g j ^ 2) := by
              rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
                div_le_div_iff_of_pos_right (by positivity)]
              have := hpow2 i hi
              have h0 : 0 ≤ p i ^ (2 - α) := Real.rpow_nonneg (hpos i).le _
              have : (g i - g j) ^ 2 ≤ 2 * (g i ^ 2 + g j ^ 2) := by
                nlinarith [sq_nonneg (g i + g j)]
              nlinarith [mul_le_mul_of_nonneg_left this h0, sq_nonneg (g i), sq_nonneg (g j),
                mul_le_mul_of_nonneg_right this (mul_nonneg (Real.rpow_nonneg hq.le (1 - α))
                  (hpos i).le)]
    refine (sum_le_sum fun i _ ↦ hterm i).trans ?_
    rw [← mul_sum, ← mul_sum]
    refine mul_le_mul_of_nonneg_left (a := 4 / ((1 - α) * β) * qStar p ^ (1 - α)) ?_
      (mul_nonneg hk.le (Real.rpow_nonneg hq.le _))
    have hsum : ∑ x ∈ univ.erase j, p x = 1 - p j := by
      rw [← hp.2, ← add_sum_erase univ (fun i ↦ p i) (Finset.mem_univ j)]
      ring
    have hL : ∑ i, (if i = j then (0 : ℝ) else p i * g i ^ 2 + p i * g j ^ 2)
        = ∑ x ∈ univ.erase j, p x * g x ^ 2 + (∑ x ∈ univ.erase j, p x) * g j ^ 2 := by
      rw [← add_sum_erase univ (fun i ↦ if i = j then (0 : ℝ) else p i * g i ^ 2 + p i * g j ^ 2)
        (Finset.mem_univ j), ite_eq_left rfl, zero_add, sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun x hx ↦ by simp [ne_of_mem_erase hx]
    have hR : ∑ i, p i * g i ^ 2 = p j * g j ^ 2 + ∑ x ∈ univ.erase j, p x * g x ^ 2 :=
      (add_sum_erase univ (fun i ↦ p i * g i ^ 2) (Finset.mem_univ j)).symm
    rw [hL, hR, hsum, ← hqj]
    have : qStar p * g j ^ 2 ≤ p j * g j ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith

/-- **Stability of FTRL with the hybrid regularizer**: if `p` maximizes the hybrid objective at
`(β, G)` and `|g i| ≤ (1 - α) β q*(p) ^ (α - 1) / 4` for all `i`, the stability term
`Φ(G + g) - Φ(G) - ⟪p, g⟫` of the value function `Φ` is at most
`4 / ((1 - α) β) q*(p) ^ (1 - α) ∑ i, p i g i²`. -/
lemma ftrlValue_hybrid_add_sub_le [Nonempty ι] {α βbar β : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hβbar : 0 ≤ βbar) {G p g : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι)
    (hmax : ∀ q ∈ simplex ι, hybridObjective α βbar β G q ≤ hybridObjective α βbar β G p)
    (hq : 0 < qStar p) (hg : ∀ i, |g i| ≤ (1 - α) * β * qStar p ^ (α - 1) / 4) :
    ftrlValue (hybridTsallis α βbar β) (G + g)
      - ftrlValue (hybridTsallis α βbar β) G - ⟪p, g⟫
      ≤ 4 / ((1 - α) * β) * qStar p ^ (1 - α) * ∑ i, p i * g i ^ 2 := by
  obtain ⟨r, hr, hrmax⟩ := exists_forall_hybridObjective_le (ι := ι) hα0.le hα1.le βbar β (G + g)
  have hV1 : ftrlValue (hybridTsallis α βbar β) (G + g)
      = hybridObjective α βbar β (G + g) r := ftrlValue_eq_of_isMaxOn hr hrmax
  have hV0 : ftrlValue (hybridTsallis α βbar β) G
      = hybridObjective α βbar β G p := ftrlValue_eq_of_isMaxOn hp hmax
  obtain ⟨l, hl⟩ := exists_kkt_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax
  have hpos := pos_of_forall_hybridObjective_le hα0 hα1 hβ hβbar hp hmax
  have h3 := hybridObjective_le_sub_bregman hα0 hα1 hβbar hp hpos hl hr
  have hadd := hybridObjective_add α βbar β 0 G g r
  rw [add_zero] at hadd
  have hstab := inner_sub_sub_bregman_le hα0 hα1 hβ hp hpos hr hq hg
  rw [inner_sub_left] at hstab
  rw [hV1, hV0, hadd]
  linarith

/-! ### Multiplicative stability -/

/-- **Multiplicative stability of the hybrid FTRL distributions** (Ito, Tsuchiya, Honda 2024,
Lemma 24, with other constants). Let `p` satisfy the first-order conditions at `(β, G)` and `r`
at `(β', G + g)`, with `1/2 ≤ α < 1`, `0 < β ≤ β'`, `|g i| ≤ (1 - α) β q*(p) ^ (α - 1) / 4` for
all `i` and `β' - β ≤ βbar α q*(p) ^ (1 - 2 α) / 8`. Then `r i ≤ 8 p i` for all `i`. -/
lemma le_eight_mul_of_kkt [Nonempty ι] {α βbar β β' : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1)
    (hβ : 0 < β) (hββ' : β ≤ β') (hβbar : 0 ≤ βbar) {G g p r : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i) (hr : r ∈ simplex ι) (hrpos : ∀ i, 0 < r i)
    {l l' : ℝ} (hkp : ∀ i, G i + β * p i ^ (α - 1) + βbar * p i ^ (-α) = l)
    (hkr : ∀ i, G i + g i + β' * r i ^ (α - 1) + βbar * r i ^ (-α) = l')
    (hq : 0 < qStar p) (hg : ∀ i, |g i| ≤ (1 - α) * β * qStar p ^ (α - 1) / 4)
    (hβ' : β' - β ≤ βbar * α * qStar p ^ (1 - 2 * α) / 8) (i : ι) : r i ≤ 8 * p i := by
  have hα0 : 0 < α := by linarith
  have hα1' : 0 < 1 - α := by linarith
  set M := (1 - α) * β * qStar p ^ (α - 1) / 4 with hM
  -- the multiplier does not decrease by more than `M`
  have hll' : l - M ≤ l' := by
    by_contra hlt
    push Not at hlt
    have hlt' (k : ι) : p k < r k := by
      by_contra hle
      push Not at hle
      have h1 : p k ^ (α - 1) ≤ r k ^ (α - 1) :=
        Real.rpow_le_rpow_of_nonpos (hrpos k) hle (by linarith)
      have h2 : p k ^ (-α) ≤ r k ^ (-α) := Real.rpow_le_rpow_of_nonpos (hrpos k) hle (by linarith)
      have h3 : β * r k ^ (α - 1) ≤ β' * r k ^ (α - 1) :=
        mul_le_mul_of_nonneg_right hββ' (Real.rpow_nonneg (hrpos k).le _)
      have := hkp k
      have := hkr k
      have := (neg_abs_le (g k)).trans' (neg_le_neg (hg k))
      nlinarith [mul_le_mul_of_nonneg_left h1 hβ.le, mul_le_mul_of_nonneg_left h2 hβbar]
    have : ∑ k, p k < ∑ k, r k := sum_lt_sum_of_nonempty univ_nonempty fun k _ ↦ hlt' k
    rw [hp.2, hr.2] at this
    exact lt_irrefl _ this
  by_cases hi : p i ≤ qStar p
  · by_contra hlt
    push Not at hlt
    have h8 : 0 < 8 * p i := by linarith [hpos i]
    have hr1 : r i ^ (α - 1) ≤ (8 * p i) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos h8 hlt.le (by linarith)
    have hr2 : r i ^ (-α) ≤ (8 * p i) ^ (-α) := Real.rpow_le_rpow_of_nonpos h8 hlt.le (by linarith)
    have hr1' : r i ^ (α - 1) < (8 * p i) ^ (α - 1) :=
      Real.rpow_lt_rpow_of_neg h8 hlt (by linarith)
    rw [Real.mul_rpow (by norm_num) (hpos i).le] at hr1 hr2 hr1'
    have hpa : 0 < p i ^ (α - 1) := Real.rpow_pos_of_pos (hpos i) _
    have hpb : 0 < p i ^ (-α) := Real.rpow_pos_of_pos (hpos i) _
    -- the numerical factors
    have h81 : (8 : ℝ) ^ (α - 1) ≤ 1 - (1 - α) * (7 / 8) := by
      have := rpow_neg_le_one_sub_mul (K := 8) (a := 1 - α) (by norm_num) hα1'.le (by linarith)
      rw [neg_sub] at this
      linarith
    have h82 : (8 : ℝ) ^ (-α) ≤ 1 - α * (7 / 8) := by
      have := rpow_neg_le_one_sub_mul (K := 8) (a := α) (by norm_num) hα0.le hα1.le
      linarith
    have h8le : (8 : ℝ) ^ (α - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by linarith)
    -- `2 M ≤ (1 - α) β p ^ (α - 1) / 2`
    have hMp : 2 * M ≤ (1 - α) * β * p i ^ (α - 1) / 2 := by
      have := Real.rpow_le_rpow_of_nonpos (hpos i) hi (by linarith : α - 1 ≤ 0)
      rw [hM]
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (1 - α) * β)]
    -- `q* ^ (1 - 2 α) p ^ (α - 1) ≤ p ^ (-α)`
    have hqp : qStar p ^ (1 - 2 * α) * p i ^ (α - 1) ≤ p i ^ (-α) := by
      have e : p i ^ (α - 1) = p i ^ (-α) * p i ^ (2 * α - 1) := by
        rw [← Real.rpow_add (hpos i)]
        ring_nf
      have h1 : p i ^ (2 * α - 1) ≤ qStar p ^ (2 * α - 1) :=
        Real.rpow_le_rpow (hpos i).le hi (by linarith)
      have h2 : qStar p ^ (1 - 2 * α) * qStar p ^ (2 * α - 1) = 1 := by
        rw [← Real.rpow_add hq]
        simp
      rw [e]
      calc qStar p ^ (1 - 2 * α) * (p i ^ (-α) * p i ^ (2 * α - 1))
          = p i ^ (-α) * (qStar p ^ (1 - 2 * α) * p i ^ (2 * α - 1)) := by ring
        _ ≤ p i ^ (-α) * (qStar p ^ (1 - 2 * α) * qStar p ^ (2 * α - 1)) := by gcongr
        _ = p i ^ (-α) := by rw [h2, mul_one]
    have hgi : g i ≤ M := (le_abs_self _).trans (hg i)
    have hk1 := hkp i
    have hk2 := hkr i
    have hdβ : 0 ≤ β' - β := by linarith
    -- the contradiction
    have hA : (β' - β) * ((8 : ℝ) ^ (α - 1) * p i ^ (α - 1)) ≤ βbar * α * p i ^ (-α) / 8 := by
      calc (β' - β) * ((8 : ℝ) ^ (α - 1) * p i ^ (α - 1)) ≤ (β' - β) * p i ^ (α - 1) := by
            gcongr
            nlinarith
        _ ≤ βbar * α * qStar p ^ (1 - 2 * α) / 8 * p i ^ (α - 1) :=
            mul_le_mul_of_nonneg_right hβ' hpa.le
        _ = βbar * α / 8 * (qStar p ^ (1 - 2 * α) * p i ^ (α - 1)) := by ring
        _ ≤ βbar * α / 8 * p i ^ (-α) := by gcongr
        _ = βbar * α * p i ^ (-α) / 8 := by ring
    have hB : βbar * (8 : ℝ) ^ (-α) * p i ^ (-α)
        ≤ βbar * p i ^ (-α) - βbar * α * p i ^ (-α) / 8 := by
      have : βbar * p i ^ (-α) * (8 : ℝ) ^ (-α) ≤ βbar * p i ^ (-α) * (1 - α * (7 / 8)) :=
        mul_le_mul_of_nonneg_left h82 (mul_nonneg hβbar hpb.le)
      nlinarith [mul_nonneg hβbar hpb.le]
    have hC : β * ((8 : ℝ) ^ (α - 1) * p i ^ (α - 1)) ≤ β * p i ^ (α - 1) - 2 * M := by
      have : β * p i ^ (α - 1) * (8 : ℝ) ^ (α - 1) ≤ β * p i ^ (α - 1) * (1 - (1 - α) * (7 / 8)) :=
        mul_le_mul_of_nonneg_left h81 (mul_nonneg hβ.le hpa.le)
      nlinarith [mul_pos hβ hpa]
    have hD : β' * ((8 : ℝ) ^ (α - 1) * p i ^ (α - 1)) ≥ β' * r i ^ (α - 1) :=
      mul_le_mul_of_nonneg_left hr1 (by linarith)
    have hD' : β' * r i ^ (α - 1) < β' * ((8 : ℝ) ^ (α - 1) * p i ^ (α - 1)) :=
      mul_lt_mul_of_pos_left hr1' (by linarith)
    have hE : βbar * r i ^ (-α) ≤ βbar * ((8 : ℝ) ^ (-α) * p i ^ (-α)) :=
      mul_le_mul_of_nonneg_left hr2 hβbar
    nlinarith
  · push Not at hi
    have h1 := half_lt_of_qStar_lt hp hi
    have := le_one_of_mem_simplex hr i
    linarith

/-! ### Bounds on the Tsallis entropy -/

/-- The Tsallis entropy on the simplex is at most `(card ι ^ (1 - a) - 1) / a` (its value at the
uniform distribution), for `0 < a ≤ 1`. -/
lemma tsallisEntropy_le_of_mem_simplex [Nonempty ι] {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    tsallisEntropy a p ≤ ((Fintype.card ι : ℝ) ^ (1 - a) - 1) / a := by
  have hK : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  set u := (Fintype.card ι : ℝ)⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 hK
  have hsum : ∑ i, p i ^ a ≤ (Fintype.card ι : ℝ) ^ (1 - a) := by
    calc ∑ i, p i ^ a ≤ ∑ i, (u ^ a + a * u ^ (a - 1) * (p i - u)) :=
          sum_le_sum fun i _ ↦ Real.rpow_le_rpow_add_mul_sub ha0.le ha1 hu0 (hp.1 i)
      _ = Fintype.card ι * u ^ a + a * u ^ (a - 1) * (∑ i, p i - Fintype.card ι * u) := by
          rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
          simp
      _ = (Fintype.card ι : ℝ) ^ (1 - a) := by
          rw [hp.2, hu, mul_inv_cancel₀ hK.ne', sub_self, mul_zero, add_zero,
            Real.rpow_sub hK, Real.rpow_one, Real.inv_rpow hK.le, div_eq_mul_inv]
  unfold tsallisEntropy
  rw [sum_sub_distrib, hp.2, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 ha0.le)

/-- For `0 ≤ x ≤ 1/2` and `0 ≤ a ≤ 1`: `(1 - a) x ^ a / 2 ≤ x ^ a - x`. -/
lemma mul_rpow_le_rpow_sub {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - a) * x ^ a / 2 ≤ x ^ a - x := by
  rcases hx0.eq_or_lt with rfl | hx0
  · rcases ha0.eq_or_lt with rfl | ha0
    · norm_num
    · simp [Real.zero_rpow ha0.ne']
  have e : x = x ^ a * x ^ (1 - a) := by
    rw [← Real.rpow_add hx0, show a + (1 - a) = 1 by ring, Real.rpow_one]
  have h1 : x ^ (1 - a) ≤ (1 / 2) ^ (1 - a) :=
    Real.rpow_le_rpow hx0.le hx (by linarith)
  have h2 : (1 / 2 : ℝ) ^ (1 - a) ≤ 1 - (1 - a) / 2 := by
    have := two_rpow_sub_one_le ha0 ha1
    rwa [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_sub]
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 _
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hxa.le]

/-- Subadditivity of `x ↦ x ^ a` for `0 ≤ a ≤ 1`, over a finite sum. -/
lemma rpow_sum_le_sum_rpow {κ : Type*} (s : Finset κ) {x : κ → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) : (∑ i ∈ s, x i) ^ a ≤ ∑ i ∈ s, x i ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow ha0.ne']
  | insert k s hk ih =>
    rw [sum_insert hk, sum_insert hk]
    have h0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi ↦ hx i (mem_insert_of_mem hi)
    calc (x k + ∑ i ∈ s, x i) ^ a ≤ x k ^ a + (∑ i ∈ s, x i) ^ a :=
          Real.rpow_add_le_add_rpow (hx k (mem_insert_self k s)) h0 ha0.le ha1
      _ ≤ x k ^ a + ∑ i ∈ s, x i ^ a := by
          gcongr
          exact ih fun i hi ↦ hx i (mem_insert_of_mem hi)

/-- **Lower bound on the Tsallis entropy** (Ito, Tsuchiya, Honda 2024, Eq. (125)):
`(1 - a) q* ^ a / (2 a) ≤ φ_a(p)` on the simplex, for `0 < a ≤ 1`. -/
lemma mul_qStar_rpow_le_tsallisEntropy [Nonempty ι] {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    (1 - a) * qStar p ^ a / (2 * a) ≤ tsallisEntropy a p := by
  classical
  obtain ⟨j, hj⟩ := exists_argmax (fun i ↦ p i)
  have hterm (i : ι) : 0 ≤ p i ^ a - p i := by
    have := Real.rpow_le_rpow_of_exponent_ge' (hp.1 i) (le_one_of_mem_simplex hp i) ha0.le ha1
    rw [Real.rpow_one] at this
    linarith
  unfold tsallisEntropy
  rw [show (1 - a) * qStar p ^ a / (2 * a) = a⁻¹ * ((1 - a) * qStar p ^ a * 2⁻¹) by
    rw [div_eq_mul_inv, mul_inv]
    ring]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  rcases le_or_gt (p j) (1 / 2) with hj2 | hj2
  · have hqj : qStar p = p j := by
      unfold qStar
      rw [← hj]
      exact min_eq_left (by linarith)
    rw [hqj]
    calc (1 - a) * p j ^ a * 2⁻¹ ≤ p j ^ a - p j := by
          have := mul_rpow_le_rpow_sub ha0.le ha1 (hp.1 j) hj2
          linarith
      _ ≤ ∑ i, (p i ^ a - p i) :=
          single_le_sum (f := fun i ↦ p i ^ a - p i) (fun i _ ↦ hterm i) (Finset.mem_univ j)
  · have hqj : qStar p = 1 - p j := by
      unfold qStar
      rw [← hj]
      exact min_eq_right (by linarith)
    have hsum : ∑ i ∈ univ.erase j, p i = 1 - p j := by
      rw [← hp.2, ← add_sum_erase univ (fun i ↦ p i) (Finset.mem_univ j)]
      ring
    have hq2 : qStar p ≤ 1 / 2 := qStar_le_half p
    have hq0 : 0 ≤ qStar p := by rw [hqj]; linarith [le_one_of_mem_simplex hp j]
    calc (1 - a) * qStar p ^ a * 2⁻¹ ≤ qStar p ^ a - qStar p := by
          have := mul_rpow_le_rpow_sub ha0.le ha1 hq0 hq2
          linarith
      _ ≤ ∑ i ∈ univ.erase j, p i ^ a - ∑ i ∈ univ.erase j, p i := by
          rw [hqj, ← hsum]
          gcongr
          exact rpow_sum_le_sum_rpow _ (fun i _ ↦ hp.1 i) ha0 ha1
      _ = ∑ i ∈ univ.erase j, (p i ^ a - p i) := by rw [sum_sub_distrib]
      _ ≤ ∑ i, (p i ^ a - p i) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ hterm i

/-- **Lemma 23 of Ito, Tsuchiya, Honda (2024)**: if `r i ≤ c p i` for all `i` with `c ≥ 1`
(distributions of the simplex, `p` with positive coordinates), then `φ_a(r) ≤ c φ_a(p)` for
`0 < a ≤ 1`. -/
lemma tsallisEntropy_le_mul_of_le_mul {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hc : 1 ≤ c)
    {p r : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i) (hr : r ∈ simplex ι)
    (hrp : ∀ i, r i ≤ c * p i) :
    tsallisEntropy a r ≤ c * tsallisEntropy a p := by
  unfold tsallisEntropy
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  have hterm (i : ι) : r i ^ a - r i
      ≤ (p i ^ a - p i) + a * (c - 1) * (p i ^ a - p i) - (1 - a) * (r i - p i)
        + a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i) := by
    have h1 := Real.rpow_le_rpow_add_mul_sub ha0.le ha1 (hpos i) (hr.1 i)
    have e : p i ^ (a - 1) * p i = p i ^ a := by
      rw [← Real.rpow_add_one (hpos i).ne', sub_add_cancel]
    have e2 : a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i)
        = a * p i ^ (a - 1) * (r i - p i) - a * (c - 1) * p i ^ a - a * (r i - p i)
          + a * (c - 1) * p i := by
      rw [← e]
      ring
    linarith
  have hsum : ∑ i, (r i - p i) = 0 := by rw [sum_sub_distrib, hr.2, hp.2, sub_self]
  have hneg (i : ι) : a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i) ≤ 0 := by
    have h1 : 1 ≤ p i ^ (a - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hpos i) (le_one_of_mem_simplex hp i)
        (by linarith)
    have h2 : (r i - p i) - (c - 1) * p i ≤ 0 := by linarith [hrp i]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha0.le (by linarith)) h2
  have hpos' : 0 ≤ ∑ i, (p i ^ a - p i) := sum_nonneg fun i _ ↦ by
    have := Real.rpow_le_rpow_of_exponent_ge' (hp.1 i) (le_one_of_mem_simplex hp i) ha0.le ha1
    rw [Real.rpow_one] at this
    linarith
  calc ∑ i, (r i ^ a - r i)
      ≤ ∑ i, ((p i ^ a - p i) + a * (c - 1) * (p i ^ a - p i) - (1 - a) * (r i - p i)
        + a * (p i ^ (a - 1) - 1) * ((r i - p i) - (c - 1) * p i)) := sum_le_sum fun i _ ↦ hterm i
    _ ≤ ∑ i, ((p i ^ a - p i) + a * (c - 1) * (p i ^ a - p i) - (1 - a) * (r i - p i)) :=
        sum_le_sum fun i _ ↦ by linarith [hneg i]
    _ = (1 + a * (c - 1)) * ∑ i, (p i ^ a - p i) := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hsum]
        ring
    _ ≤ c * ∑ i, (p i ^ a - p i) := by
        gcongr
        nlinarith

/-- **Power mean inequality** for `x ↦ x ^ a`, `0 < a ≤ 1`:
`∑_{i ∈ s} x i ^ a ≤ #s ^ (1 - a) (∑_{i ∈ s} x i) ^ a`. -/
lemma sum_rpow_le_card_rpow_mul {κ : Type*} (s : Finset κ) {x : κ → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∑ i ∈ s, x i ^ a ≤ (#s : ℝ) ^ (1 - a) * (∑ i ∈ s, x i) ^ a := by
  rcases (sum_nonneg hx).eq_or_lt with h0 | hpos
  · have hx0 : ∀ i ∈ s, x i = 0 := (sum_eq_zero_iff_of_nonneg hx).1 h0.symm
    rw [sum_eq_zero fun i hi ↦ by rw [hx0 i hi, Real.zero_rpow ha0.ne']]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (sum_nonneg hx) _)
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hpos
  have hn : (0 : ℝ) < #s := Nat.cast_pos.2 (card_pos.2 hs)
  have ht0 : 0 < (∑ i ∈ s, x i) / #s := div_pos hpos hn
  calc ∑ i ∈ s, x i ^ a ≤ ∑ i ∈ s, (((∑ i ∈ s, x i) / #s) ^ a
        + a * ((∑ i ∈ s, x i) / #s) ^ (a - 1) * (x i - (∑ i ∈ s, x i) / #s)) :=
        sum_le_sum fun i hi ↦ Real.rpow_le_rpow_add_mul_sub ha0.le ha1 ht0 (hx i hi)
    _ = #s * ((∑ i ∈ s, x i) / #s) ^ a + a * ((∑ i ∈ s, x i) / #s) ^ (a - 1)
          * (∑ i ∈ s, x i - #s * ((∑ i ∈ s, x i) / #s)) := by
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
        simp
    _ = #s * ((∑ i ∈ s, x i) / #s) ^ a := by
        rw [mul_div_cancel₀ _ hn.ne', sub_self, mul_zero, add_zero]
    _ = (#s : ℝ) ^ (1 - a) * (∑ i ∈ s, x i) ^ a := by
        rw [Real.div_rpow hpos.le hn.le, Real.rpow_sub hn, Real.rpow_one]
        field_simp

/-- **Self-bounding bound on the Tsallis entropy** (Ito, Tsuchiya, Honda 2024, Eq. (132)): for
every `x`, `φ_a(p) ≤ card ι ^ (1 - a) (1 - p x) ^ a / a` on the simplex, for `0 < a ≤ 1`. -/
lemma tsallisEntropy_le_card_rpow_mul {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (x : ι) :
    tsallisEntropy a p ≤ (Fintype.card ι : ℝ) ^ (1 - a) * (1 - p x) ^ a / a := by
  classical
  have hsum : ∑ i ∈ univ.erase x, p i = 1 - p x := by
    rw [← hp.2, ← add_sum_erase univ (fun i ↦ p i) (Finset.mem_univ x)]
    ring
  have hx1 : p x ^ a ≤ 1 := Real.rpow_le_one (hp.1 x) (le_one_of_mem_simplex hp x) ha0.le
  have h1 : ∑ i, (p i ^ a - p i) ≤ ∑ i ∈ univ.erase x, p i ^ a := by
    rw [sum_sub_distrib, hp.2, ← add_sum_erase univ (fun i ↦ p i ^ a) (Finset.mem_univ x)]
    linarith
  have h2 := sum_rpow_le_card_rpow_mul (univ.erase x) (fun i _ ↦ hp.1 i) ha0 ha1
  rw [hsum] at h2
  have h3 : ((#(univ.erase x) : ℕ) : ℝ) ^ (1 - a) ≤ (Fintype.card ι : ℝ) ^ (1 - a) := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by linarith)
    exact_mod_cast (card_erase_le).trans (le_of_eq card_univ)
  have h4 : 0 ≤ (1 - p x) ^ a := Real.rpow_nonneg (by linarith [le_one_of_mem_simplex hp x]) _
  unfold tsallisEntropy
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha0.le)
  calc ∑ i, (p i ^ a - p i) ≤ ((#(univ.erase x) : ℕ) : ℝ) ^ (1 - a) * (1 - p x) ^ a := h1.trans h2
    _ ≤ (Fintype.card ι : ℝ) ^ (1 - a) * (1 - p x) ^ a := mul_le_mul_of_nonneg_right h3 h4

/-! ### A lower bound on the coordinates of the maximizer -/

/-- At a point of the simplex satisfying the first-order conditions, with `|G i| ≤ B`,
`0 ≤ β ≤ B` and `βbar > 0`, every coordinate is at least
`(βbar / (2 B + (B + βbar) card ι)) ^ (1 / α)`. -/
lemma rpow_inv_le_of_kkt [Nonempty ι] {α βbar β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hβbar : 0 < βbar) {G p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) (hpos : ∀ i, 0 < p i)
    {l : ℝ} (hkkt : ∀ i, G i + β * p i ^ (α - 1) + βbar * p i ^ (-α) = l) {B : ℝ}
    (hG : ∀ i, |G i| ≤ B) (hβB : β ≤ B) (i : ι) :
    (βbar / (2 * B + (B + βbar) * Fintype.card ι)) ^ α⁻¹ ≤ p i := by
  have hK1 : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  have hK0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hG i)
  obtain ⟨j, hj⟩ : ∃ j, (Fintype.card ι : ℝ)⁻¹ ≤ p j := by
    by_contra h
    push Not at h
    have : ∑ j, p j < ∑ _j : ι, (Fintype.card ι : ℝ)⁻¹ :=
      sum_lt_sum_of_nonempty univ_nonempty fun j _ ↦ h j
    rw [hp.2, sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀ hK0.ne'] at this
    exact lt_irrefl _ this
  have hinv0 : 0 < (Fintype.card ι : ℝ)⁻¹ := inv_pos.2 hK0
  have hj1 : p j ^ (α - 1) ≤ Fintype.card ι := by
    calc p j ^ (α - 1) ≤ ((Fintype.card ι : ℝ)⁻¹) ^ (α - 1) :=
          Real.rpow_le_rpow_of_nonpos hinv0 hj (by linarith)
      _ = (Fintype.card ι : ℝ) ^ (1 - α) := by
          rw [Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le, neg_sub]
      _ ≤ (Fintype.card ι : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
      _ = Fintype.card ι := Real.rpow_one _
  have hj2 : p j ^ (-α) ≤ Fintype.card ι := by
    calc p j ^ (-α) ≤ ((Fintype.card ι : ℝ)⁻¹) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hinv0 hj (by linarith)
      _ = (Fintype.card ι : ℝ) ^ α := by
          rw [Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le, neg_neg]
      _ ≤ (Fintype.card ι : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK1 hα1.le
      _ = Fintype.card ι := Real.rpow_one _
  have hl : l ≤ B + (B + βbar) * Fintype.card ι := by
    rw [← hkkt j]
    have := (le_abs_self (G j)).trans (hG j)
    nlinarith [mul_le_mul hβB hj1 (Real.rpow_nonneg (hpos j).le _) hB0,
      mul_le_mul_of_nonneg_left hj2 hβbar.le]
  have hpi : βbar * p i ^ (-α) ≤ 2 * B + (B + βbar) * Fintype.card ι := by
    have := hkkt i
    have := neg_abs_le (G i)
    have := hG i
    have : 0 ≤ β * p i ^ (α - 1) := mul_nonneg hβ (Real.rpow_nonneg (hpos i).le _)
    linarith
  set A := 2 * B + (B + βbar) * Fintype.card ι with hA
  have hA0 : 0 < A := by positivity
  have hpa : βbar / A ≤ p i ^ α := by
    rw [Real.rpow_neg (hpos i).le] at hpi
    have hpa0 : 0 < p i ^ α := Real.rpow_pos_of_pos (hpos i) _
    rw [div_le_iff₀ hA0]
    have := mul_le_mul_of_nonneg_right hpi hpa0.le
    rwa [mul_assoc, inv_mul_cancel₀ hpa0.ne', mul_one, mul_comm A] at this
  calc (βbar / A) ^ α⁻¹ ≤ (p i ^ α) ^ α⁻¹ :=
        Real.rpow_le_rpow (by positivity) hpa (inv_nonneg.2 hα0.le)
    _ = p i := Real.rpow_rpow_inv (hpos i).le hα0.ne'

end Learning
