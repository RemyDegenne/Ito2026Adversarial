/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.ILMTW2026.Setting
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.HybridTsallis
public import Ito2026Adversarial.LeanMachineLearning.Online.StabilityPenaltyMatching

/-!
# Tsallis-FTRL-SPM along a sequence of rounds

The deterministic part of the analysis of Tsallis-FTRL with stability-penalty matching
(`tsallisSPM`, Ito, Tsuchiya and Honda 2024, Section 4.3): along any sequence of rounds with
rewards in `[-1, 1]`, for admissible parameters (`IsSPMParams`, their Eq. (35)).

## Main definitions

* `IsSPMParams α β₁ βbar c d`: the conditions `1/2 ≤ α < 1`, `β₁ ≥ 8 c d / (1 - α)`,
  `βbar ≥ 32 d / ((1 - α)² β₁)` of Ito, Tsuchiya, Honda (2024) on the parameters;
* `spmState φ α β₁ βbar p₀ c r t`: the state `(G_t, β_t)` of the algorithm after the rounds
  `r 0, …, r (t - 1)`.

## Main statements

* design matrices: `dotProduct_designOf_mulVec`, `sum_mul_dotProduct_inv_mulVec_mul` (the linear
  estimate is unbiased), `sum_mul_sq_dotProduct_inv_mulVec` (its second moment),
  `sum_mul_dotProduct_inv_mulVec_self` (the trace identity `∑ x, p x ‖φ x‖²_{S(p)⁻¹} = d`);
* `abs_spmEstimate_le`: the estimates are bounded by `(1 - α) β_t q*_t ^ (α - 1) / 4`
  (Ito, Tsuchiya, Honda 2024, Eq. (134));
* `spmBeta_succ_sub_le`: `β_{t+1} - β_t ≤ βbar α q*_t ^ (1 - 2 α) / 8` (their Eq. (136));
* `tsallisEntropy_spmHat_succ_le`: `h_{t+1} ≤ 8 h_t` (multiplicative stability);
* `sum_inner_spmEstimate_le`: the pathwise regret bound of FTRL for the estimates, penalty and
  stability terms bounded through stability-penalty matching.
-/

@[expose] public section

open Finset Real Learning Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace Ito2026Adversarial

/-! ### Design matrices -/

section Design

variable {ιx 𝒳 : Type*} [Fintype ιx] [Fintype 𝒳] (φ : 𝒳 → EuclideanSpace ℝ ιx)

omit [Fintype ιx] in
/-- The design matrix is linear in the distribution. -/
lemma designOf_add_smul (a b : ℝ) (p q : EuclideanSpace ℝ 𝒳) :
    designOf φ (a • p + b • q) = a • designOf φ p + b • designOf φ q := by
  simp only [designOf, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_smul, mul_smul,
    sum_add_distrib, smul_sum]

omit [Fintype ιx] in
/-- The design matrix of nonnegative weights is positive semidefinite. -/
lemma posSemidef_designOf [Finite ιx] {p : EuclideanSpace ℝ 𝒳} (hp : ∀ x, 0 ≤ p x) :
    (designOf φ p).PosSemidef :=
  have := Fintype.ofFinite ιx
  Finset.sum_induction _ _ (fun _ _ ha hb ↦ ha.add hb) PosSemidef.zero
    fun x _ ↦ (outerSelf_posSemidef (φ x)).smul (hp x)

/-- `a ⬝ S(p) b = ∑ x, p x ⟪φ x, a⟫ ⟪φ x, b⟫`. -/
lemma dotProduct_designOf_mulVec (p : EuclideanSpace ℝ 𝒳) (a b : ιx → ℝ) :
    a ⬝ᵥ designOf φ p *ᵥ b
      = ∑ x, p x * ((WithLp.ofLp (φ x) ⬝ᵥ a) * (WithLp.ofLp (φ x) ⬝ᵥ b)) := by
  simp only [designOf, sum_mulVec, smul_mulVec, outerSelf, vecMulVec_mulVec, dotProduct_sum,
    dotProduct_smul]
  refine sum_congr rfl fun x _ ↦ ?_
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [dotProduct_comm a]

variable [DecidableEq ιx]

/-- **Unbiasedness of the linear estimate**: for an invertible design matrix,
`∑ x, p x ⟪φ x, w⟫ ⟪φ x, S(p)⁻¹ φ i⟫ = ⟪φ i, w⟫`. -/
lemma sum_mul_dotProduct_inv_mulVec_mul (p : EuclideanSpace ℝ 𝒳)
    (hS : IsUnit (designOf φ p).det) (w : ιx → ℝ) (i : 𝒳) :
    ∑ x, p x * ((WithLp.ofLp (φ x) ⬝ᵥ w)
      * (WithLp.ofLp (φ x) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i)))
      = WithLp.ofLp (φ i) ⬝ᵥ w := by
  rw [← dotProduct_designOf_mulVec, mulVec_mulVec, mul_nonsing_inv _ hS, one_mulVec,
    dotProduct_comm]

/-- **Second moment of the linear estimate**: for an invertible design matrix,
`∑ x, p x ⟪φ x, S(p)⁻¹ φ i⟫² = ⟪φ i, S(p)⁻¹ φ i⟫`. -/
lemma sum_mul_sq_dotProduct_inv_mulVec (p : EuclideanSpace ℝ 𝒳)
    (hS : IsUnit (designOf φ p).det) (i : 𝒳) :
    ∑ x, p x * (WithLp.ofLp (φ x) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i)) ^ 2
      = WithLp.ofLp (φ i) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i) := by
  have := sum_mul_dotProduct_inv_mulVec_mul φ p hS ((designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i)) i
  simpa [sq] using this

/-- **Trace identity**: for an invertible design matrix, `∑ x, p x ⟪φ x, S(p)⁻¹ φ x⟫ = d`. -/
lemma sum_mul_dotProduct_inv_mulVec_self (p : EuclideanSpace ℝ 𝒳)
    (hS : IsUnit (designOf φ p).det) :
    ∑ x, p x * (WithLp.ofLp (φ x) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ x))
      = Fintype.card ιx := by
  simp only [dotProduct_mulVec_eq_trace_mul_outerSelf]
  rw [← trace_one (n := ιx) (R := ℝ), ← nonsing_inv_mul _ hS]
  simp only [designOf, mul_sum, mul_smul_comm, trace_sum, trace_smul, smul_eq_mul]

variable {𝒴 : Type*}

/-- The estimate of a round is its reward times the estimate of the same action with reward
`1`. -/
lemma spmEstimate_eq_smul (p : simplex 𝒳) (r : Round Unit 𝒳 ℝ) :
    spmEstimate φ p r = r.feedback • spmEstimate φ p ((), r.action, 1) := by
  ext i
  simp [spmEstimate]

/-- The coordinates of the estimate with reward `1`. -/
lemma spmEstimate_one_apply (p : simplex 𝒳) (x i : 𝒳) :
    spmEstimate φ p ((), x, 1) i
      = WithLp.ofLp (φ x) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i) := by
  simp [spmEstimate]

/-- **Unbiasedness of the linear estimates**: for a game `u x y = ⟪φ x, w y⟫` and an invertible
design matrix, `∑ x, p x u x y ⟪v, ĝ(x)⟫ = ∑ i, v i u i y`, where `ĝ(x)` is the estimate when `x`
is played with reward `1`. -/
lemma sum_mul_inner_spmEstimate (p : simplex 𝒳) (hS : IsUnit (designOf φ p).det)
    {u : 𝒳 → 𝒴 → ℝ} {w : 𝒴 → ιx → ℝ} (hu : ∀ x y, u x y = WithLp.ofLp (φ x) ⬝ᵥ w y)
    (v : EuclideanSpace ℝ 𝒳) (y : 𝒴) :
    ∑ x, p x * (u x y * ⟪v, spmEstimate φ p ((), x, 1)⟫) = ∑ i, v i * u i y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, spmEstimate_one_apply, hu,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  have := sum_mul_dotProduct_inv_mulVec_mul φ p hS (w y) i
  rw [mul_comm (v i), ← this, sum_mul]
  exact sum_congr rfl fun x _ ↦ by ring

/-- **Second moment of the linear estimates**: for an invertible design matrix,
`∑ x, p x ∑ i, q i ĝ(x) i² = ∑ i, q i ⟪φ i, S(p)⁻¹ φ i⟫`. -/
lemma sum_mul_sum_sq_spmEstimate (p : simplex 𝒳) (hS : IsUnit (designOf φ p).det) (q : 𝒳 → ℝ) :
    ∑ x, p x * ∑ i, q i * spmEstimate φ p ((), x, 1) i ^ 2
      = ∑ i, q i * (WithLp.ofLp (φ i) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i)) := by
  simp only [spmEstimate_one_apply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_mul_sq_dotProduct_inv_mulVec φ p hS i, mul_sum]
  exact sum_congr rfl fun x _ ↦ by ring

/-- If `q i ≤ 2 p i` and the design matrix of `p` is positive definite,
`∑ i, q i ⟪φ i, S(p)⁻¹ φ i⟫ ≤ 2 d` (trace identity). -/
lemma sum_mul_dotProduct_inv_le (p : simplex 𝒳) (hS : (designOf φ p).PosDef) {q : 𝒳 → ℝ}
    (hq : ∀ i, q i ≤ 2 * p i) :
    ∑ i, q i * (WithLp.ofLp (φ i) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i))
      ≤ 2 * Fintype.card ιx := by
  have hdet : IsUnit (designOf φ p).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  rw [← sum_mul_dotProduct_inv_mulVec_self φ p hdet, mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  have h0 : 0 ≤ WithLp.ofLp (φ i) ⬝ᵥ (designOf φ p)⁻¹ *ᵥ WithLp.ofLp (φ i) :=
    hS.inv.posSemidef.dotProduct_mulVec_nonneg _ |>.trans_eq' (by simp)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hq i) h0

end Design

/-! ### Parameters -/

/-- Admissible parameters of Tsallis-FTRL-SPM for the variance ratio `c` and the dimension `d`
(Ito, Tsuchiya, Honda 2024, Eq. (35)): `1/2 ≤ α < 1`, `β₁ ≥ 8 c d / (1 - α)` and
`βbar ≥ 32 d / ((1 - α)² β₁)`, with `c > 0` and `d ≥ 1`. -/
structure IsSPMParams (α β₁ βbar c : ℝ) (d : ℕ) : Prop where
  half_le : 1 / 2 ≤ α
  lt_one : α < 1
  c_pos : 0 < c
  one_le_d : 1 ≤ d
  le_beta₁ : 8 * c * d / (1 - α) ≤ β₁
  le_betaBar : 32 * d / ((1 - α) ^ 2 * β₁) ≤ βbar

namespace IsSPMParams

variable {α β₁ βbar c : ℝ} {d : ℕ} (h : IsSPMParams α β₁ βbar c d)
include h

/-- `α > 0`. -/
lemma alpha_pos : 0 < α := by linarith [h.half_le]

/-- `1 - α > 0`. -/
lemma one_sub_pos : 0 < 1 - α := by linarith [h.lt_one]

/-- `d > 0`. -/
lemma d_pos : (0 : ℝ) < d := by exact_mod_cast h.one_le_d

/-- `β₁ > 0`. -/
lemma beta₁_pos : 0 < β₁ :=
  lt_of_lt_of_le (by have := h.c_pos; have := h.d_pos; have := h.one_sub_pos; positivity)
    h.le_beta₁

/-- `βbar > 0`. -/
lemma betaBar_pos : 0 < βbar :=
  lt_of_lt_of_le (by have := h.d_pos; have := h.one_sub_pos; have := h.beta₁_pos; positivity)
    h.le_betaBar

end IsSPMParams

/-! ### One step of the algorithm -/

section Step

variable {ιx : Type*} [Fintype ιx] {𝒳 : Type*} [Fintype 𝒳] [Nonempty 𝒳]
  (φ : 𝒳 → EuclideanSpace ℝ ιx) {α β₁ βbar c : ℝ} {p₀ : simplex 𝒳}

/-- `spmHat` is the FTRL distribution `ftrlSimplexParam` of the hybrid Tsallis regularizer. -/
lemma spmHat_eq (α βbar : ℝ) (s : EuclideanSpace ℝ 𝒳 × ℝ) :
    spmHat α βbar s = ftrlSimplexParam (hybridTsallis α βbar) (s.2, s.1) := rfl

/-- `zCoef α d p = d q*(p) ^ (1 - α) / (1 - α)`. -/
lemma zCoef_eq (α : ℝ) (d : ℕ) (p : EuclideanSpace ℝ 𝒳) :
    zCoef α d p = d * qStar p ^ (1 - α) / (1 - α) := rfl

/-- For `β > 0`, `spmHat` maximizes the hybrid objective. -/
lemma forall_hybridObjective_le_spmHat (hα0 : 0 < α) (hα1 : α < 1) (hβbar : 0 ≤ βbar)
    {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : 0 < s.2) :
    ∀ q ∈ simplex 𝒳, hybridObjective α βbar s.2 s.1 q
      ≤ hybridObjective α βbar s.2 s.1 (spmHat α βbar s : EuclideanSpace ℝ 𝒳) := by
  rw [spmHat_eq]
  exact forall_hybridObjective_le_ftrlSimplexParam hα0 hα1 hs hβbar s.1

/-- For `β > 0`, `spmHat` has positive coordinates. -/
lemma spmHat_pos (hα0 : 0 < α) (hα1 : α < 1) (hβbar : 0 ≤ βbar)
    {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : 0 < s.2) (i : 𝒳) :
    0 < (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i :=
  pos_of_forall_hybridObjective_le hα0 hα1 hs hβbar (spmHat α βbar s).2
    (forall_hybridObjective_le_spmHat hα0 hα1 hβbar hs) i

/-- For `β > 0`, `spmHat` satisfies the first-order conditions. -/
lemma exists_kkt_spmHat (hα0 : 0 < α) (hα1 : α < 1) (hβbar : 0 ≤ βbar)
    {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : 0 < s.2) :
    ∃ l : ℝ, ∀ i, s.1 i + s.2 * (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i ^ (α - 1)
      + βbar * (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i ^ (-α) = l :=
  exists_kkt_of_forall_hybridObjective_le hα0 hα1 hs hβbar (spmHat α βbar s).2
    (forall_hybridObjective_le_spmHat hα0 hα1 hβbar hs)

variable (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx)) (h𝒳 : 2 ≤ Fintype.card 𝒳)
include hP

/-- `q*` of `spmHat` is positive. -/
lemma qStar_spmHat_pos {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : 0 < s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    0 < qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) :=
  qStar_pos (spmHat α βbar s).2 (spmHat_pos hP.alpha_pos hP.lt_one hP.betaBar_pos.le hs) h𝒳

/-- The exploration coefficient `γ = 4 c z / β` is at most `q* ^ (1 - α) / 2 ≤ 1/2` when
`β ≥ β₁`. -/
lemma gamma_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) :
    4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2
      ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) / 2 := by
  have hβ₁ := hP.beta₁_pos
  have hs0 : 0 < s.2 := hβ₁.trans_le hs
  have h1 := hP.one_sub_pos
  have hc := hP.c_pos
  have hd := hP.d_pos
  have hq0 : 0 ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) :=
    Real.rpow_nonneg (qStar_nonneg (spmHat α βbar s).2) _
  rw [zCoef_eq, div_le_div_iff₀ hs0 two_pos]
  have hb := hP.le_beta₁
  rw [div_le_iff₀ h1] at hb
  calc 4 * c * (↑(Fintype.card ιx) * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α)
        / (1 - α)) * 2
      = qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) * (8 * c * Fintype.card ιx)
        / (1 - α) := by ring
    _ ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) * (β₁ * (1 - α)) / (1 - α) := by
        gcongr
    _ = qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) * β₁ := by field_simp
    _ ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) * s.2 := by gcongr

/-- The exploration coefficient `γ = 4 c z / β` is positive. -/
lemma gamma_pos {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    0 < 4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2 := by
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  have hq := qStar_spmHat_pos hP hs0 h𝒳
  have := hP.c_pos
  have := hP.d_pos
  have := hP.one_sub_pos
  rw [zCoef_eq]
  have : 0 < qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) := Real.rpow_pos_of_pos hq _
  positivity

/-- The distribution played by Tsallis-FTRL-SPM is the mixture `(1 - γ) p̂ + γ p₀`. -/
lemma coe_spmDist {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳)
      = (1 - 4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2) •
          (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
        + (4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2) •
          (p₀ : EuclideanSpace ℝ 𝒳) := by
  have hγ0 := (gamma_pos hP hs h𝒳).le
  have hγ1 := (gamma_le hP hs).trans (by
    have := Real.rpow_le_one (qStar_nonneg (spmHat α βbar s).2)
      ((qStar_le_half _).trans (by norm_num)) hP.one_sub_pos.le
    linarith : qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) / 2 ≤ 1)
  unfold spmDist
  rw [coe_toSet_of_mem]
  exact convex_simplex (spmHat α βbar s).2 p₀.2 (by linarith) hγ0 (by ring)

/-- The coordinates of the played distribution are at least half those of `p̂`. -/
lemma half_le_spmDist {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳)
    (i : 𝒳) :
    (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i / 2
      ≤ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳) i := by
  rw [coe_spmDist hP hs h𝒳]
  have hγ0 := (gamma_pos hP hs h𝒳).le
  have hγ1 := (gamma_le hP hs).trans (by
    have := Real.rpow_le_one (qStar_nonneg (spmHat α βbar s).2)
      ((qStar_le_half _).trans (by norm_num)) hP.one_sub_pos.le
    linarith : qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) / 2 ≤ 1 / 2)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have := (spmHat α βbar s).2.1 i
  have := p₀.2.1 i
  nlinarith

/-- **Penalty-coefficient bound** (Ito, Tsuchiya, Honda 2024, Eq. (136)): the increment of the
learning rate is at most `βbar α q* ^ (1 - 2 α) / 8`. -/
lemma zCoef_div_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
        / (s.2 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳))
      ≤ βbar * α * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - 2 * α) / 8 := by
  set q := qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) with hq
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  have hq0 : 0 < q := qStar_spmHat_pos hP hs0 h𝒳
  have hα0 := hP.alpha_pos
  have h1 := hP.one_sub_pos
  have hd := hP.d_pos
  have hβ₁ := hP.beta₁_pos
  have hh := mul_qStar_rpow_le_tsallisEntropy hα0 hP.lt_one.le (spmHat α βbar s).2
  rw [← hq] at hh
  have hqa : 0 < q ^ α := Real.rpow_pos_of_pos hq0 _
  have hhpos : 0 < (1 - α) * q ^ α / (2 * α) := by positivity
  have hb := hP.le_betaBar
  rw [div_le_iff₀ (by positivity)] at hb
  -- `q ^ (1 - α) / q ^ α = q ^ (1 - 2 α)`
  have hexp : q ^ (1 - α) = q ^ (1 - 2 * α) * q ^ α := by
    rw [← Real.rpow_add hq0]
    ring_nf
  rw [zCoef_eq, ← hq]
  calc ↑(Fintype.card ιx) * q ^ (1 - α) / (1 - α)
        / (s.2 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳))
      ≤ ↑(Fintype.card ιx) * q ^ (1 - α) / (1 - α) / (β₁ * ((1 - α) * q ^ α / (2 * α))) := by
        gcongr
    _ = 2 * α * Fintype.card ιx / ((1 - α) ^ 2 * β₁) * q ^ (1 - 2 * α) := by
        rw [hexp]
        field_simp
    _ ≤ βbar * α * q ^ (1 - 2 * α) / 8 := by
        have hq2 : 0 ≤ q ^ (1 - 2 * α) := Real.rpow_nonneg hq0.le _
        have e : 2 * α * Fintype.card ιx / ((1 - α) ^ 2 * β₁)
            = α / 16 * (32 * Fintype.card ιx / ((1 - α) ^ 2 * β₁)) := by ring
        rw [e]
        have := hP.le_betaBar
        calc α / 16 * (32 * ↑(Fintype.card ιx) / ((1 - α) ^ 2 * β₁)) * q ^ (1 - 2 * α)
            ≤ α / 16 * βbar * q ^ (1 - 2 * α) := by gcongr
          _ ≤ βbar * α * q ^ (1 - 2 * α) / 8 := by nlinarith [mul_nonneg hα0.le hP.betaBar_pos.le]

/-- The design matrix of the played distribution is `(1 - γ) S(p̂) + γ S(p₀)`. -/
lemma designOf_spmDist {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳)
      = (1 - 4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2) •
          designOf φ (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
        + (4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2) •
          designOf φ (p₀ : EuclideanSpace ℝ 𝒳) := by
  rw [coe_spmDist hP hs h𝒳, designOf_add_smul]

/-- `γ S(p₀) ≤ S(p)` in the Loewner order. -/
lemma smul_le_designOf_spmDist {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2)
    (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    (4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2) •
        designOf φ (p₀ : EuclideanSpace ℝ 𝒳)
      ≤ designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳) := by
  rw [designOf_spmDist φ hP hs h𝒳, Matrix.le_iff, add_sub_cancel_right]
  have hγ1 := (gamma_le hP hs).trans (by
    have := Real.rpow_le_one (qStar_nonneg (spmHat α βbar s).2)
      ((qStar_le_half _).trans (by norm_num)) hP.one_sub_pos.le
    linarith : qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α) / 2 ≤ 1)
  exact (posSemidef_designOf φ (spmHat α βbar s).2.1).smul (by linarith)

variable [DecidableEq ιx] (hV : HasVarianceRatio φ p₀ c)
include hV

/-- The design matrix of the played distribution is positive definite. -/
lemma posDef_designOf_spmDist {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2)
    (h𝒳 : 2 ≤ Fintype.card 𝒳) :
    (designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳)).PosDef := by
  have h := smul_le_designOf_spmDist φ (p₀ := p₀) hP hs h𝒳
  rw [Matrix.le_iff] at h
  have := (hV.1.smul (gamma_pos hP hs h𝒳)).add_posSemidef h
  rwa [add_sub_cancel] at this

/-- **Bound on the bilinear forms of the inverse design matrix** (Ito, Tsuchiya, Honda 2024,
Eq. (134)): `|⟪φ a, S(p)⁻¹ φ b⟫| ≤ c d / γ = (1 - α) β q* ^ (α - 1) / 4` for all actions. -/
lemma abs_dotProduct_inv_designOf_spmDist_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2)
    (h𝒳 : 2 ≤ Fintype.card 𝒳) (a b : 𝒳) :
    |WithLp.ofLp (φ a) ⬝ᵥ
        (designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳))⁻¹
          *ᵥ WithLp.ofLp (φ b)|
      ≤ (1 - α) * s.2 * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) / 4 := by
  set S := designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳) with hS
  set γ := 4 * c * zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) / s.2
    with hγ
  set q := qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) with hq
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  have hq0 : 0 < q := qStar_spmHat_pos hP hs0 h𝒳
  have hγ0 : 0 < γ := gamma_pos hP hs h𝒳
  have hSpd : S.PosDef := posDef_designOf_spmDist φ hP hV hs h𝒳
  have hle (x : 𝒳) : WithLp.ofLp (φ x) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (φ x)
      ≤ γ⁻¹ * (c * Fintype.card ιx) := by
    have := hV.1.dotProduct_inv_mulVec_le_of_smul_le hγ0 (smul_le_designOf_spmDist φ hP hs h𝒳)
      (WithLp.ofLp (φ x))
    simp only [star_trivial] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hV.2 x) (inv_nonneg.2 hγ0.le))
  have hval : γ⁻¹ * (c * Fintype.card ιx) = (1 - α) * s.2 * q ^ (α - 1) / 4 := by
    have h1 := hP.one_sub_pos
    have hc := hP.c_pos
    have hd := hP.d_pos
    have hqq : q ^ (1 - α) * q ^ (α - 1) = 1 := by
      rw [← Real.rpow_add hq0]
      simp
    rw [hγ, zCoef_eq, ← hq]
    field_simp
    linear_combination -hqq
  rw [← hval]
  have h := hSpd.inv.star_dotProduct_mulVec_mul_le (WithLp.ofLp (φ a)) (WithLp.ofLp (φ b))
  simp only [star_trivial] at h
  have hK : 0 ≤ γ⁻¹ * (c * Fintype.card ιx) := by
    have := hP.c_pos
    positivity
  refine (Real.abs_le_sqrt (h := ?_)).trans (le_of_eq (Real.sqrt_sq hK))
  rw [sq]
  refine h.trans ?_
  have hb0 : 0 ≤ WithLp.ofLp (φ b) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (φ b) :=
    hSpd.inv.posSemidef.dotProduct_mulVec_nonneg _ |>.trans_eq' (by simp)
  rw [sq]
  exact mul_le_mul (hle a) (hle b) hb0 hK

/-- **Bound on the linear estimates** (Ito, Tsuchiya, Honda 2024, Eq. (134)): for rewards in
`[-1, 1]`, `|g i| ≤ c d / γ = (1 - α) β q* ^ (α - 1) / 4`. -/
lemma abs_spmEstimate_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳)
    {r : Round Unit 𝒳 ℝ} (hr : |r.feedback| ≤ 1) (i : 𝒳) :
    |spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r i|
      ≤ (1 - α) * s.2 * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) / 4 := by
  unfold spmEstimate
  rw [PiLp.toLp_apply, abs_mul]
  calc |r.feedback| * |WithLp.ofLp (φ r.action) ⬝ᵥ
        (designOf φ (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳))⁻¹
          *ᵥ WithLp.ofLp (φ i)|
      ≤ 1 * ((1 - α) * s.2 * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) / 4) :=
        mul_le_mul hr (abs_dotProduct_inv_designOf_spmDist_le φ hP hV hs h𝒳 r.action i)
          (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Multiplicative stability of Tsallis-FTRL-SPM** (Ito, Tsuchiya, Honda 2024, Section 4.3,
through their Lemma 24): for rewards in `[-1, 1]`, the FTRL distribution of the next round is at
most `8` times the current one, coordinatewise. -/
lemma spmHat_spmUpdate_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2)
    (h𝒳 : 2 ≤ Fintype.card 𝒳) {r : Round Unit 𝒳 ℝ} (hr : |r.feedback| ≤ 1) (i : 𝒳) :
    (spmHat α βbar (spmUpdate φ α βbar p₀ c s r) : EuclideanSpace ℝ 𝒳) i
      ≤ 8 * (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i := by
  set s' := spmUpdate φ α βbar p₀ c s r with hs'
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  have hα0 := hP.alpha_pos
  have hα1 := hP.lt_one
  have hβbar := hP.betaBar_pos.le
  have hz := zCoef_div_le hP hs h𝒳
  have hh0 : 0 < tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳) := by
    have := mul_qStar_rpow_le_tsallisEntropy hα0 hα1.le (spmHat α βbar s).2
    have hq := qStar_spmHat_pos hP hs0 h𝒳
    have : 0 < (1 - α) * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ α / (2 * α) := by
      have := hP.one_sub_pos
      have := Real.rpow_pos_of_pos hq α
      positivity
    linarith
  have hzz : 0 ≤ zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
      / (s.2 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳)) := by
    rw [zCoef_eq]
    have := hP.one_sub_pos
    have := Real.rpow_nonneg (qStar_nonneg (spmHat α βbar s).2) (1 - α)
    positivity
  have hs'2 : s'.2 = s.2 + zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
      / (s.2 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳)) := rfl
  have hs'1 : s'.1 = s.1 + spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r := rfl
  have hss' : s.2 ≤ s'.2 := by rw [hs'2]; linarith
  have hs'0 : 0 < s'.2 := hs0.trans_le hss'
  obtain ⟨l, hl⟩ := exists_kkt_spmHat hα0 hα1 hβbar hs0
  obtain ⟨l', hl'⟩ := exists_kkt_spmHat (s := s') hα0 hα1 hβbar hs'0
  refine le_eight_mul_of_kkt hP.half_le hα1 hs0 hss' hβbar (spmHat α βbar s).2
    (spmHat_pos hα0 hα1 hβbar hs0) (spmHat α βbar s').2 (spmHat_pos hα0 hα1 hβbar hs'0) hl
    (g := spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r) (l' := l') (fun j ↦ ?_)
    (qStar_spmHat_pos hP hs0 h𝒳) (fun j ↦ abs_spmEstimate_le φ hP hV hs h𝒳 hr j) ?_ i
  · rw [← hl' j, hs'1, PiLp.add_apply]
  · rw [hs'2]
    linarith

/-- **Multiplicative stability of the penalty coefficients**: `h_{t+1} ≤ 8 h_t`. -/
lemma tsallisEntropy_spmHat_spmUpdate_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2)
    (h𝒳 : 2 ≤ Fintype.card 𝒳) {r : Round Unit 𝒳 ℝ} (hr : |r.feedback| ≤ 1) :
    tsallisEntropy α (spmHat α βbar (spmUpdate φ α βbar p₀ c s r) : EuclideanSpace ℝ 𝒳)
      ≤ 8 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳) :=
  tsallisEntropy_le_mul_of_le_mul hP.alpha_pos hP.lt_one.le (by norm_num) (spmHat α βbar s).2
    (spmHat_pos hP.alpha_pos hP.lt_one hP.betaBar_pos.le (hP.beta₁_pos.trans_le hs))
    (spmHat α βbar _).2 (spmHat_spmUpdate_le φ hP hV hs h𝒳 hr)

/-- **Stability of a round of Tsallis-FTRL-SPM**: for rewards in `[-1, 1]`, the stability term
of the round is at most `4 / ((1 - α) β) q* ^ (1 - α) ∑ i, p̂ i g i²`. -/
lemma stability_spm_le {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (h𝒳 : 2 ≤ Fintype.card 𝒳)
    {r : Round Unit 𝒳 ℝ} (hr : |r.feedback| ≤ 1) :
    ftrlValue (hybridTsallis α βbar s.2)
        (s.1 + spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r)
      - ftrlValue (hybridTsallis α βbar s.2) s.1
      - ⟪(spmHat α βbar s : EuclideanSpace ℝ 𝒳),
          spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r⟫
      ≤ 4 / ((1 - α) * s.2) * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - α)
        * ∑ i, (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i
          * spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c s) r i ^ 2 := by
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  exact ftrlValue_hybrid_add_sub_le hP.alpha_pos hP.lt_one hs0 hP.betaBar_pos.le
    (spmHat α βbar s).2 (forall_hybridObjective_le_spmHat hP.alpha_pos hP.lt_one
      hP.betaBar_pos.le hs0) (qStar_spmHat_pos hP hs0 h𝒳)
    (fun j ↦ abs_spmEstimate_le φ hP hV hs h𝒳 hr j)

end Step

/-! ### Along a sequence of rounds -/

section Path

variable {ιx : Type*} [Fintype ιx] [DecidableEq ιx] {𝒳 : Type*} [Fintype 𝒳] [Nonempty 𝒳]
  (φ : 𝒳 → EuclideanSpace ℝ ιx) (α β₁ βbar : ℝ) (p₀ : simplex 𝒳) (c : ℝ)

/-- The state `(G_t, β_t)` of Tsallis-FTRL-SPM after the rounds `r 0, …, r (t - 1)`. -/
noncomputable def spmState (r : ℕ → Round Unit 𝒳 ℝ) : ℕ → EuclideanSpace ℝ 𝒳 × ℝ
  | 0 => (0, β₁)
  | t + 1 => spmUpdate φ α βbar p₀ c (spmState r t) (r t)

/-- The reward estimate `g_t` of round `t` along the rounds `r`. -/
noncomputable def spmEstimateAt (r : ℕ → Round Unit 𝒳 ℝ) (t : ℕ) : EuclideanSpace ℝ 𝒳 :=
  spmEstimate φ (spmDist α βbar (Fintype.card ιx) p₀ c (spmState φ α β₁ βbar p₀ c r t)) (r t)

/-- The initial state is `(0, β₁)`. -/
@[simp]
lemma spmState_zero (r : ℕ → Round Unit 𝒳 ℝ) : spmState φ α β₁ βbar p₀ c r 0 = (0, β₁) := rfl

/-- The state after round `t` is the update of the state before it. -/
lemma spmState_succ (r : ℕ → Round Unit 𝒳 ℝ) (t : ℕ) :
    spmState φ α β₁ βbar p₀ c r (t + 1)
      = spmUpdate φ α βbar p₀ c (spmState φ α β₁ βbar p₀ c r t) (r t) := rfl

/-- The state of `tsallisSPM` after a history is `spmState` of its rounds. -/
lemma foldHistIdx_eq_spmState (r : ℕ → Round Unit 𝒳 ℝ) (t : ℕ) :
    foldHistIdx (fun _ ↦ spmUpdate φ α βbar p₀ c) (0, β₁) t (fun i ↦ r i)
      = spmState φ α β₁ βbar p₀ c r t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [foldHistIdx_succ, spmState_succ, ← ih]
    rfl

/-- The cumulative reward of the state is the sum of the past estimates. -/
lemma spmState_fst (r : ℕ → Round Unit 𝒳 ℝ) (t : ℕ) :
    (spmState φ α β₁ βbar p₀ c r t).1 = ∑ s ∈ range t, spmEstimateAt φ α β₁ βbar p₀ c r s := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, ← ih]
    rfl

/-- The update of the learning rate. -/
lemma spmState_succ_snd (r : ℕ → Round Unit 𝒳 ℝ) (t : ℕ) :
    (spmState φ α β₁ βbar p₀ c r (t + 1)).2 = (spmState φ α β₁ βbar p₀ c r t).2
      + zCoef α (Fintype.card ιx)
          (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
        / ((spmState φ α β₁ βbar p₀ c r t).2
          * tsallisEntropy α (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) :
            EuclideanSpace ℝ 𝒳)) := rfl

variable {φ α β₁ βbar p₀ c}

/-- The learning rate does not decrease along an update. -/
lemma le_spmUpdate_snd (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) (r : Round Unit 𝒳 ℝ) :
    s.2 ≤ (spmUpdate φ α βbar p₀ c s r).2 := by
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  have hz : 0 ≤ zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳) := by
    rw [zCoef_eq]
    have := hP.one_sub_pos
    have := Real.rpow_nonneg (qStar_nonneg (spmHat α βbar s).2) (1 - α)
    positivity
  have hh := tsallisEntropy_nonneg hP.alpha_pos hP.lt_one.le (spmHat α βbar s).2
  have : 0 ≤ zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
      / (s.2 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳)) := by positivity
  change s.2 ≤ s.2 + zCoef α (Fintype.card ιx) (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
      / (s.2 * tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳))
  linarith

/-- The learning rates are at least `β₁`. -/
lemma le_spmState_snd (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (r : ℕ → Round Unit 𝒳 ℝ) (t : ℕ) : β₁ ≤ (spmState φ α β₁ βbar p₀ c r t).2 := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact ih.trans (le_spmUpdate_snd hP ih (r t))

/-- The learning rate of the state after any history is at least `β₁`. -/
lemma le_foldHistIdx_spmUpdate_snd (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx)) (n : ℕ)
    (h : Hist Unit 𝒳 ℝ n) :
    β₁ ≤ (foldHistIdx (fun _ ↦ spmUpdate φ α βbar p₀ c) (0, β₁) n h).2 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [foldHistIdx_succ]
    exact (ih _).trans (le_spmUpdate_snd hP (ih _) _)

omit [DecidableEq ιx] in
/-- The penalty coefficients `h_t = φ_α(p̂_t)` are positive. -/
lemma tsallisEntropy_spmHat_pos (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (h𝒳 : 2 ≤ Fintype.card 𝒳) {s : EuclideanSpace ℝ 𝒳 × ℝ} (hs : β₁ ≤ s.2) :
    0 < tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳) := by
  have hs0 : 0 < s.2 := hP.beta₁_pos.trans_le hs
  have := mul_qStar_rpow_le_tsallisEntropy hP.alpha_pos hP.lt_one.le (spmHat α βbar s).2
  have hq := qStar_spmHat_pos hP hs0 h𝒳
  have : 0 < (1 - α) * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ α / (2 * α) := by
    have := hP.one_sub_pos
    have := Real.rpow_pos_of_pos hq α
    have := hP.alpha_pos
    positivity
  linarith

/-- **Pathwise regret of Tsallis-FTRL-SPM for the estimates**: along any sequence of rounds with
rewards in `[-1, 1]`, for every action `x`,
`∑_{t < T} ⟪e_x - p̂_t, g_t⟫ ≤ β₁ φ_α(p̂_0) + βbar φ_{1-α}(p̂_0)
+ ∑_{t < T} (8 z_t / β_t + 4 / ((1 - α) β_t) q*_t ^ (1 - α) ∑ i, p̂_t i g_t i²)`
(FTRL decomposition; the penalty `(β_{t+1} - β_t) h_{t+1} ≤ 8 z_t / β_t` by stability-penalty
matching and multiplicative stability, the stability term by `stability_spm_le`). -/
lemma sum_inner_spmEstimateAt_le [DecidableEq 𝒳] (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (hV : HasVarianceRatio φ p₀ c) (h𝒳 : 2 ≤ Fintype.card 𝒳) (r : ℕ → Round Unit 𝒳 ℝ)
    (hr : ∀ t, |(r t).feedback| ≤ 1) (x : 𝒳) (T : ℕ) :
    ∑ t ∈ range T, ⟪EuclideanSpace.single x (1 : ℝ)
        - (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳),
        spmEstimateAt φ α β₁ βbar p₀ c r t⟫
      ≤ β₁ * tsallisEntropy α (spmHat (𝒳 := 𝒳) α βbar (0, β₁) : EuclideanSpace ℝ 𝒳)
        + βbar * tsallisEntropy (1 - α) (spmHat (𝒳 := 𝒳) α βbar (0, β₁) : EuclideanSpace ℝ 𝒳)
        + ∑ t ∈ range T, (8 * (zCoef α (Fintype.card ιx)
            (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
              / (spmState φ α β₁ βbar p₀ c r t).2)
          + 4 / ((1 - α) * (spmState φ α β₁ βbar p₀ c r t).2)
            * qStar (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
              ^ (1 - α)
            * ∑ i, (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳) i
              * spmEstimateAt φ α β₁ βbar p₀ c r t i ^ 2) := by
  classical
  set st := spmState φ α β₁ βbar p₀ c r with hst
  set ph : ℕ → EuclideanSpace ℝ 𝒳 := fun t ↦ (spmHat α βbar (st t) : EuclideanSpace ℝ 𝒳)
    with hph
  set g := spmEstimateAt φ α β₁ βbar p₀ c r with hg
  set z : ℕ → ℝ := fun t ↦ zCoef α (Fintype.card ιx) (ph t) with hz
  set Vt : ℕ → ℝ := fun t ↦ 4 / ((1 - α) * (st t).2) * qStar (ph t) ^ (1 - α)
    * ∑ i, ph t i * g t i ^ 2 with hVt
  have hα0 := hP.alpha_pos
  have hα1 := hP.lt_one
  have hβbar := hP.betaBar_pos
  have hst0 (t : ℕ) : 0 < (st t).2 := hP.beta₁_pos.trans_le (le_spmState_snd hP r t)
  have hz0 (t : ℕ) : 0 ≤ z t := by
    simp only [hz, zCoef_eq]
    have := hP.one_sub_pos
    have := Real.rpow_nonneg (qStar_nonneg (spmHat α βbar (st t)).2) (1 - α)
    positivity
  have hstab (t : ℕ) : ftrlValue (hybridTsallis α βbar (st t).2) (∑ s ∈ range (t + 1), g s)
      - ftrlValue (hybridTsallis α βbar (st t).2) (∑ s ∈ range t, g s) - ⟪ph t, g t⟫ ≤ Vt t := by
    rw [sum_range_succ, ← spmState_fst]
    exact stability_spm_le φ hP hV (le_spmState_snd hP r t) h𝒳 (hr t)
  have hV0 (t : ℕ) : 0 ≤ Vt t := by
    have := hP.one_sub_pos
    have := hst0 t
    have := Real.rpow_nonneg (qStar_nonneg (spmHat α βbar (st t)).2) (1 - α)
    have : 0 ≤ ∑ i, ph t i * g t i ^ 2 :=
      sum_nonneg fun i _ ↦ mul_nonneg ((spmHat α βbar (st t)).2.1 i) (sq_nonneg _)
    simp only [hVt]
    positivity
  have hpen (t : ℕ) : ((st (t + 1)).2 - (st t).2) * tsallisEntropy α (ph (t + 1))
      ≤ 8 * (z t / (st t).2) := by
    have hh0 := tsallisEntropy_spmHat_pos hP h𝒳 (le_spmState_snd (φ := φ) (p₀ := p₀) hP r t)
    have hmul := tsallisEntropy_spmHat_spmUpdate_le φ hP hV
      (le_spmState_snd (φ := φ) (p₀ := p₀) hP r t) h𝒳 (hr t)
    have hincr : (st (t + 1)).2 - (st t).2 = z t / ((st t).2 * tsallisEntropy α (ph t)) := by
      rw [hst, spmState_succ_snd]
      ring
    have hd0 : 0 ≤ (st (t + 1)).2 - (st t).2 := by
      rw [hincr]
      have := hst0 t
      have := hz0 t
      positivity
    calc ((st (t + 1)).2 - (st t).2) * tsallisEntropy α (ph (t + 1))
        ≤ ((st (t + 1)).2 - (st t).2) * (8 * tsallisEntropy α (ph t)) :=
          mul_le_mul_of_nonneg_left hmul hd0
      _ = 8 * (z t / (st t).2) := by
          rw [hincr]
          have h1 : tsallisEntropy α (ph t) ≠ 0 := hh0.ne'
          have h2 : (st t).2 ≠ 0 := (hst0 t).ne'
          field_simp
  have hrest : 0 ≤ β₁ * tsallisEntropy α (spmHat (𝒳 := 𝒳) α βbar (0, β₁) : EuclideanSpace ℝ 𝒳)
      + βbar * tsallisEntropy (1 - α) (spmHat (𝒳 := 𝒳) α βbar (0, β₁) : EuclideanSpace ℝ 𝒳) := by
    have := tsallisEntropy_nonneg hα0 hα1.le (spmHat (𝒳 := 𝒳) α βbar (0, β₁)).2
    have := tsallisEntropy_nonneg hP.one_sub_pos (by linarith) (spmHat (𝒳 := 𝒳) α βbar (0, β₁)).2
    have := hP.beta₁_pos
    positivity
  rcases T with _ | n
  · simp only [range_zero, sum_empty, add_zero]
    exact hrest
  have hmax (t : ℕ) : ∀ q ∈ simplex 𝒳, ⟪q, ∑ s ∈ range t, g s⟫ + hybridTsallis α βbar (st t).2 q
      ≤ ⟪ph t, ∑ s ∈ range t, g s⟫ + hybridTsallis α βbar (st t).2 (ph t) := by
    rw [← spmState_fst]
    exact forall_hybridObjective_le_spmHat hα0 hα1 hβbar.le (hst0 t)
  have h := sum_inner_sub_le_ftrl (fun t ↦ hybridTsallis α βbar (st t).2) g ph
    (fun t ↦ (spmHat α βbar (st t)).2) hmax (single_mem_simplex x) n
  have hsingle (b : ℝ) : hybridTsallis α βbar b (EuclideanSpace.single x (1 : ℝ)) = 0 := by
    simp [hybridTsallis, tsallisEntropy_single hα0.ne', tsallisEntropy_single hP.one_sub_pos.ne']
  have hdiff (t : ℕ) (q : EuclideanSpace ℝ 𝒳) :
      hybridTsallis α βbar (st (t + 1)).2 q - hybridTsallis α βbar (st t).2 q
        = ((st (t + 1)).2 - (st t).2) * tsallisEntropy α q := by
    simp only [hybridTsallis]
    ring
  simp only [hsingle, hdiff, sub_zero] at h
  have hp0 : hybridTsallis α βbar (st 0).2 (ph 0)
      = β₁ * tsallisEntropy α (spmHat (𝒳 := 𝒳) α βbar (0, β₁) : EuclideanSpace ℝ 𝒳)
        + βbar * tsallisEntropy (1 - α) (spmHat (𝒳 := 𝒳) α βbar (0, β₁) : EuclideanSpace ℝ 𝒳) := rfl
  rw [hp0] at h
  refine h.trans ?_
  rw [sum_add_distrib, ← add_assoc]
  refine add_le_add (add_le_add le_rfl ?_) (sum_le_sum fun t _ ↦ hstab t)
  calc ∑ t ∈ range n, ((st (t + 1)).2 - (st t).2) * tsallisEntropy α (ph (t + 1))
      ≤ ∑ t ∈ range n, 8 * (z t / (st t).2) := sum_le_sum fun t _ ↦ hpen t
    _ ≤ ∑ t ∈ range (n + 1), 8 * (z t / (st t).2) := by
        rw [sum_range_succ]
        have := hz0 n
        have := hst0 n
        have : 0 ≤ 8 * (z n / (st n).2) := by positivity
        linarith

/-! ### Coefficient bounds -/

omit [DecidableEq ιx] in
/-- `z = d q* ^ (1 - α) / (1 - α) ≤ d / (1 - α)`. -/
lemma zCoef_le (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx)) {p : EuclideanSpace ℝ 𝒳}
    (hp : p ∈ simplex 𝒳) : zCoef α (Fintype.card ιx) p ≤ Fintype.card ιx / (1 - α) := by
  rw [zCoef_eq]
  have h1 := hP.one_sub_pos
  have hq : qStar p ^ (1 - α) ≤ 1 :=
    Real.rpow_le_one (qStar_nonneg hp) ((qStar_le_half p).trans (by norm_num)) h1.le
  have := hP.d_pos
  rw [div_le_div_iff_of_pos_right h1]
  nlinarith

omit [DecidableEq ιx] in
/-- `z ≥ 0`. -/
lemma zCoef_nonneg (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx)) {p : EuclideanSpace ℝ 𝒳}
    (hp : p ∈ simplex 𝒳) : 0 ≤ zCoef α (Fintype.card ιx) p := by
  rw [zCoef_eq]
  have := hP.one_sub_pos
  have := Real.rpow_nonneg (qStar_nonneg hp) (1 - α)
  positivity

omit [DecidableEq ιx] in
/-- **Self-bounding bound** (Ito, Tsuchiya, Honda 2024, Eqs. (132) and (137)): for every action
`x`, `z h ≤ d m ^ (1 - α) (1 - p x) / (α (1 - α))`, with `h = φ_α(p)`. -/
lemma zCoef_mul_tsallisEntropy_le (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    {p : EuclideanSpace ℝ 𝒳} (hp : p ∈ simplex 𝒳) (x : 𝒳) :
    zCoef α (Fintype.card ιx) p * tsallisEntropy α p
      ≤ Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α) * (1 - p x) / (α * (1 - α)) := by
  have hα0 := hP.alpha_pos
  have h1 := hP.one_sub_pos
  have hd := hP.d_pos
  have hpx : 0 ≤ 1 - p x := by linarith [le_one_of_mem_simplex hp x]
  have hz : zCoef α (Fintype.card ιx) p ≤ Fintype.card ιx * (1 - p x) ^ (1 - α) / (1 - α) := by
    rw [zCoef_eq]
    gcongr
    · exact qStar_nonneg hp
    · exact qStar_le_one_sub hp x
  have hh := tsallisEntropy_le_card_rpow_mul hα0 hP.lt_one.le hp x
  have hh0 := tsallisEntropy_nonneg hα0 hP.lt_one.le hp
  have hprod : (1 - p x) ^ (1 - α) * (1 - p x) ^ α = 1 - p x := by
    rcases hpx.eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow h1.ne', zero_mul]
    · rw [← Real.rpow_add hpos, show 1 - α + α = 1 by ring, Real.rpow_one]
  calc zCoef α (Fintype.card ιx) p * tsallisEntropy α p
      ≤ Fintype.card ιx * (1 - p x) ^ (1 - α) / (1 - α)
        * ((Fintype.card 𝒳 : ℝ) ^ (1 - α) * (1 - p x) ^ α / α) :=
        mul_le_mul hz hh hh0 (by positivity)
    _ = Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α)
          * ((1 - p x) ^ (1 - α) * (1 - p x) ^ α) / (α * (1 - α)) := by
        field_simp
    _ = _ := by rw [hprod]

/-! ### Stability-penalty matching along the rounds -/

omit [DecidableEq ιx] in
/-- The penalty coefficients are at most `H = (m ^ (1 - α) - 1) / α`. -/
lemma tsallisEntropy_spmHat_le (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (s : EuclideanSpace ℝ 𝒳 × ℝ) :
    tsallisEntropy α (spmHat α βbar s : EuclideanSpace ℝ 𝒳)
      ≤ ((Fintype.card 𝒳 : ℝ) ^ (1 - α) - 1) / α :=
  tsallisEntropy_le_of_mem_simplex hP.alpha_pos hP.lt_one.le (spmHat α βbar s).2

/-- **Worst-case SPM bound along rounds** (Ito, Tsuchiya, Honda 2024, Proposition 16):
`∑_{t < T} z_t / β_t ≤ 2 √(2 H T d / (1 - α)) + 2 d / ((1 - α) β₁)` with
`H = (m ^ (1 - α) - 1) / α`. -/
lemma sum_zCoef_div_le_sqrt (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (h𝒳 : 2 ≤ Fintype.card 𝒳) (r : ℕ → Round Unit 𝒳 ℝ) (T : ℕ) :
    ∑ t ∈ range T, zCoef α (Fintype.card ιx)
        (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
        / (spmState φ α β₁ βbar p₀ c r t).2
      ≤ 2 * √(2 * (((Fintype.card 𝒳 : ℝ) ^ (1 - α) - 1) / α)
          * (T * (Fintype.card ιx / (1 - α))))
        + 2 * (Fintype.card ιx / (1 - α)) / β₁ := by
  have h := spm_sum_le_sqrt (b := fun t ↦ (spmState φ α β₁ βbar p₀ c r t).2)
    (z := fun t ↦ zCoef α (Fintype.card ιx)
      (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳))
    (h := fun t ↦ tsallisEntropy α
      (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳))
    hP.beta₁_pos (fun t ↦ zCoef_nonneg hP (spmHat α βbar _).2)
    (fun t ↦ tsallisEntropy_spmHat_pos hP h𝒳 (le_spmState_snd hP r t))
    (fun t ↦ spmState_succ_snd φ α β₁ βbar p₀ c r t) (fun t ↦ tsallisEntropy_spmHat_le hP _)
    (fun t ↦ zCoef_le hP (spmHat α βbar _).2) T
  refine h.trans (add_le_add_left ?_ _)
  have hH0 : 0 ≤ ((Fintype.card 𝒳 : ℝ) ^ (1 - α) - 1) / α :=
    (tsallisEntropy_nonneg hP.alpha_pos hP.lt_one.le (spmHat α βbar (0, β₁)).2).trans
      (tsallisEntropy_spmHat_le hP (0, β₁))
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg zero_le_two hH0))) zero_le_two
  calc ∑ t ∈ range T, zCoef α (Fintype.card ιx)
        (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
      ≤ ∑ _t ∈ range T, (Fintype.card ιx / (1 - α) : ℝ) :=
        sum_le_sum fun t _ ↦ zCoef_le hP (spmHat α βbar _).2
    _ = T * (Fintype.card ιx / (1 - α)) := by simp

/-- **Level SPM bound along rounds** (Ito, Tsuchiya, Honda 2024, Eq. (116)): for every number
of levels `J`, `∑_{t < T} z_t / β_t ≤ 4 √(J ∑_{t < T} h_t z_t) + 2 √(2 H / 2 ^ J T d / (1 - α))
+ 2 d / ((1 - α) β₁)`. -/
lemma sum_zCoef_div_le_levels (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (h𝒳 : 2 ≤ Fintype.card 𝒳) (r : ℕ → Round Unit 𝒳 ℝ) (J T : ℕ) :
    ∑ t ∈ range T, zCoef α (Fintype.card ιx)
        (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
        / (spmState φ α β₁ βbar p₀ c r t).2
      ≤ 4 * √(J * ∑ t ∈ range T, tsallisEntropy α
            (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
          * zCoef α (Fintype.card ιx)
            (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳))
        + 2 * √(2 * ((((Fintype.card 𝒳 : ℝ) ^ (1 - α) - 1) / α) / 2 ^ J)
          * (T * (Fintype.card ιx / (1 - α))))
        + 2 * (Fintype.card ιx / (1 - α)) / β₁ := by
  have h := spm_sum_le_levels (b := fun t ↦ (spmState φ α β₁ βbar p₀ c r t).2)
    (z := fun t ↦ zCoef α (Fintype.card ιx)
      (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳))
    (h := fun t ↦ tsallisEntropy α
      (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳))
    hP.beta₁_pos (fun t ↦ zCoef_nonneg hP (spmHat α βbar _).2)
    (fun t ↦ tsallisEntropy_spmHat_pos hP h𝒳 (le_spmState_snd hP r t))
    (fun t ↦ spmState_succ_snd φ α β₁ βbar p₀ c r t) (fun t ↦ tsallisEntropy_spmHat_le hP _)
    (fun t ↦ zCoef_le hP (spmHat α βbar _).2) J T
  refine h.trans (add_le_add_left (add_le_add_right ?_ _) _)
  have hH0 : 0 ≤ ((Fintype.card 𝒳 : ℝ) ^ (1 - α) - 1) / α :=
    (tsallisEntropy_nonneg hP.alpha_pos hP.lt_one.le (spmHat α βbar (0, β₁)).2).trans
      (tsallisEntropy_spmHat_le hP (0, β₁))
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg zero_le_two (div_nonneg hH0 (pow_nonneg zero_le_two J))))) zero_le_two
  calc ∑ t ∈ range T, zCoef α (Fintype.card ιx)
        (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
      ≤ ∑ _t ∈ range T, (Fintype.card ιx / (1 - α) : ℝ) :=
        sum_le_sum fun t _ ↦ zCoef_le hP (spmHat α βbar _).2
    _ = T * (Fintype.card ιx / (1 - α)) := by simp

/-- **Self-bounding along rounds** (Ito, Tsuchiya, Honda 2024, Eq. (138)): if `Δ ≥ 0` and
`Δ x ≥ Δmin > 0` for `x ≠ x₀`, then
`∑_{t < T} h_t z_t ≤ 2 d m ^ (1 - α) / (α (1 - α) Δmin) ∑_{t < T} ∑ x, p_t x Δ x`, where `p_t` is
the played distribution. -/
lemma sum_tsallisEntropy_mul_zCoef_le (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (h𝒳 : 2 ≤ Fintype.card 𝒳) (r : ℕ → Round Unit 𝒳 ℝ) (T : ℕ) {x₀ : 𝒳} {Δ : 𝒳 → ℝ}
    {Δmin : ℝ} (hΔmin : 0 < Δmin) (hΔ0 : ∀ x, 0 ≤ Δ x) (hΔ : ∀ x, x ≠ x₀ → Δmin ≤ Δ x) :
    ∑ t ∈ range T, tsallisEntropy α
          (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
        * zCoef α (Fintype.card ιx)
          (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
      ≤ 2 * Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α) / (α * (1 - α) * Δmin)
        * ∑ t ∈ range T, ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c
            (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳) x * Δ x := by
  classical
  rw [mul_sum]
  refine sum_le_sum fun t _ ↦ ?_
  set s := spmState φ α β₁ βbar p₀ c r t with hs
  set ph := (spmHat α βbar s : EuclideanSpace ℝ 𝒳) with hph
  have hsβ : β₁ ≤ s.2 := le_spmState_snd hP r t
  have hα0 := hP.alpha_pos
  have h1α := hP.one_sub_pos
  have hd := hP.d_pos
  have hm : 0 ≤ (Fintype.card 𝒳 : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := zCoef_mul_tsallisEntropy_le hP (spmHat α βbar s).2 x₀
  have hsum : 1 - ph x₀ = ∑ x ∈ univ.erase x₀, ph x := by
    rw [← (spmHat α βbar s).2.2, ← add_sum_erase univ (fun i ↦ ph i) (Finset.mem_univ x₀)]
    ring
  have h2 : 1 - ph x₀ ≤ (∑ x, ph x * Δ x) / Δmin := by
    rw [hsum, le_div_iff₀ hΔmin, sum_mul]
    calc ∑ x ∈ univ.erase x₀, ph x * Δmin ≤ ∑ x ∈ univ.erase x₀, ph x * Δ x :=
          sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left (hΔ x (ne_of_mem_erase hx))
            ((spmHat α βbar s).2.1 x)
      _ ≤ ∑ x, ph x * Δ x := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun x _ _ ↦ mul_nonneg ((spmHat α βbar s).2.1 x) (hΔ0 x)
  have h3 : ∑ x, ph x * Δ x ≤ 2 * ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c s :
      EuclideanSpace ℝ 𝒳) x * Δ x := by
    rw [mul_sum]
    refine sum_le_sum fun x _ ↦ ?_
    have := half_le_spmDist hP hsβ h𝒳 (p₀ := p₀) (c := c) x
    nlinarith [hΔ0 x]
  have hK : 0 ≤ Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α) / (α * (1 - α)) := by
    positivity
  calc tsallisEntropy α ph * zCoef α (Fintype.card ιx) ph
      = zCoef α (Fintype.card ιx) ph * tsallisEntropy α ph := mul_comm _ _
    _ ≤ Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α) * (1 - ph x₀) / (α * (1 - α)) := h1
    _ = Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α) / (α * (1 - α)) * (1 - ph x₀) := by
        ring
    _ ≤ Fintype.card ιx * (Fintype.card 𝒳 : ℝ) ^ (1 - α) / (α * (1 - α))
          * ((2 * ∑ x, (spmDist α βbar (Fintype.card ιx) p₀ c s : EuclideanSpace ℝ 𝒳) x * Δ x)
            / Δmin) := by
        gcongr
        exact h2.trans (div_le_div_of_nonneg_right h3 hΔmin.le)
    _ = _ := by
        field_simp

/-! ### Deterministic bounds on the states -/

/-- The lower bound `(βbar / (2 B + (B + βbar) K)) ^ (1 / α)` on the coordinates of the FTRL
distribution when the state is bounded by `B` (`rpow_inv_le_of_kkt`). -/
noncomputable def spmLow (α βbar : ℝ) (K : ℕ) (B : ℝ) : ℝ :=
  (βbar / (2 * B + (B + βbar) * K)) ^ α⁻¹

/-- A deterministic bound on the state `(G_t, β_t)` after `t` rounds with rewards in `[-1, 1]`. -/
noncomputable def spmBound (α β₁ βbar : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => β₁
  | t + 1 => spmBound α β₁ βbar K t
      + spmBound α β₁ βbar K t * spmLow α βbar K (spmBound α β₁ βbar K t) ^ (α - 1)
      + βbar * spmLow α βbar K (spmBound α β₁ βbar K t) ^ (1 - 2 * α)

omit [Fintype ιx] [DecidableEq ιx] [Fintype 𝒳] [Nonempty 𝒳] in
/-- The deterministic bounds on the states are nonnegative. -/
lemma spmBound_nonneg (hβ₁ : 0 ≤ β₁) (hβbar : 0 ≤ βbar) (K : ℕ) (t : ℕ) :
    0 ≤ spmBound α β₁ βbar K t := by
  induction t with
  | zero => exact hβ₁
  | succ t ih =>
    simp only [spmBound]
    have : 0 ≤ spmLow α βbar K (spmBound α β₁ βbar K t) := Real.rpow_nonneg (by positivity) _
    have := Real.rpow_nonneg this (α - 1)
    have := Real.rpow_nonneg this (1 - 2 * α)
    positivity

/-- **Deterministic bounds on the states**: along rounds with rewards in `[-1, 1]`,
`|G_t i| ≤ B_t` and `β_t ≤ B_t`, and the estimates are bounded by `B_{t+1}`. -/
lemma spmState_le_spmBound (hP : IsSPMParams α β₁ βbar c (Fintype.card ιx))
    (hV : HasVarianceRatio φ p₀ c) (h𝒳 : 2 ≤ Fintype.card 𝒳) (r : ℕ → Round Unit 𝒳 ℝ)
    (hr : ∀ t, |(r t).feedback| ≤ 1) (t : ℕ) :
    (∀ i, |(spmState φ α β₁ βbar p₀ c r t).1 i| ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t)
      ∧ (spmState φ α β₁ βbar p₀ c r t).2 ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t
      ∧ (1 - α) * (spmState φ α β₁ βbar p₀ c r t).2
          * qStar (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
            ^ (α - 1) / 4
          ≤ spmBound α β₁ βbar (Fintype.card 𝒳) (t + 1) := by
  have hα0 := hP.alpha_pos
  have hα1 := hP.lt_one
  have hβbar := hP.betaBar_pos
  have hβ₁ := hP.beta₁_pos
  -- the bound on the estimates follows from the bound on the state
  have hest (t : ℕ) (hG : ∀ i, |(spmState φ α β₁ βbar p₀ c r t).1 i|
      ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t)
      (hβ : (spmState φ α β₁ βbar p₀ c r t).2 ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t) :
      (1 - α) * (spmState φ α β₁ βbar p₀ c r t).2
          * qStar (spmHat α βbar (spmState φ α β₁ βbar p₀ c r t) : EuclideanSpace ℝ 𝒳)
            ^ (α - 1) / 4
          ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t
            * spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t) ^ (α - 1)
      ∧ (spmState φ α β₁ βbar p₀ c r (t + 1)).2 - (spmState φ α β₁ βbar p₀ c r t).2
          ≤ βbar * spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t)
            ^ (1 - 2 * α) := by
    set s := spmState φ α β₁ βbar p₀ c r t with hs
    set B := spmBound α β₁ βbar (Fintype.card 𝒳) t with hB
    set ℓ := spmLow α βbar (Fintype.card 𝒳) B with hℓ
    have hsβ := le_spmState_snd (φ := φ) (p₀ := p₀) hP r t
    have hs0 : 0 < s.2 := hβ₁.trans_le hsβ
    obtain ⟨l, hl⟩ := exists_kkt_spmHat hα0 hα1 hβbar.le hs0
    have hlow (i : 𝒳) : ℓ ≤ (spmHat α βbar s : EuclideanSpace ℝ 𝒳) i :=
      rpow_inv_le_of_kkt hα0 hα1 hs0.le hβbar (spmHat α βbar s).2
        (spmHat_pos hα0 hα1 hβbar.le hs0) hl hG hβ i
    have hℓq : ℓ ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) :=
      le_qStar_of_forall_le (spmHat α βbar s).2 hlow h𝒳
    have hB0 : 0 ≤ B := spmBound_nonneg hβ₁.le hβbar.le _ t
    have hℓ0 : 0 < ℓ := Real.rpow_pos_of_pos (by
      have := hβbar
      have : (0 : ℝ) ≤ Fintype.card 𝒳 := Nat.cast_nonneg _
      have : 0 < 2 * B + (B + βbar) * Fintype.card 𝒳 := by
        have : (1 : ℝ) ≤ Fintype.card 𝒳 := Nat.one_le_cast.2 Fintype.card_pos
        nlinarith
      positivity) _
    constructor
    · have h1 : qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) ≤ ℓ ^ (α - 1) :=
        Real.rpow_le_rpow_of_nonpos hℓ0 hℓq (by linarith)
      have h2 : 0 ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) :=
        Real.rpow_nonneg (qStar_nonneg (spmHat α βbar s).2) _
      have h3 : (1 - α) * s.2 / 4 ≤ B := by
        nlinarith [hP.one_sub_pos]
      calc (1 - α) * s.2 * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) / 4
          = (1 - α) * s.2 / 4 * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (α - 1) := by
            ring
        _ ≤ B * ℓ ^ (α - 1) := mul_le_mul h3 h1 h2 hB0
    · rw [spmState_succ_snd, add_sub_cancel_left]
      refine (zCoef_div_le hP hsβ h𝒳).trans ?_
      have h1 : qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - 2 * α) ≤ ℓ ^ (1 - 2 * α) :=
        Real.rpow_le_rpow_of_nonpos hℓ0 hℓq (by linarith [hP.half_le])
      have h2 : 0 ≤ qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - 2 * α) :=
        Real.rpow_nonneg (qStar_nonneg (spmHat α βbar s).2) _
      calc βbar * α * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - 2 * α) / 8
          = βbar * (α / 8) * qStar (spmHat α βbar s : EuclideanSpace ℝ 𝒳) ^ (1 - 2 * α) := by
            ring
        _ ≤ βbar * 1 * ℓ ^ (1 - 2 * α) := by
            gcongr
            linarith
        _ = βbar * ℓ ^ (1 - 2 * α) := by ring
  -- induction on the state
  have hstate (t : ℕ) : (∀ i, |(spmState φ α β₁ βbar p₀ c r t).1 i|
      ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t)
      ∧ (spmState φ α β₁ βbar p₀ c r t).2 ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t := by
    induction t with
    | zero => exact ⟨fun i ↦ by simp [spmBound, hβ₁.le], le_rfl⟩
    | succ t ih =>
      obtain ⟨hg, hβ⟩ := hest t ih.1 ih.2
      have hB0 := spmBound_nonneg (α := α) hβ₁.le hβbar.le (Fintype.card 𝒳) t
      have hℓ0 : 0 ≤ spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t) :=
        Real.rpow_nonneg (by positivity) _
      have hA : 0 ≤ spmBound α β₁ βbar (Fintype.card 𝒳) t
          * spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t) ^ (α - 1) :=
        mul_nonneg hB0 (Real.rpow_nonneg hℓ0 _)
      have hC : 0 ≤ βbar
          * spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t)
            ^ (1 - 2 * α) := mul_nonneg hβbar.le (Real.rpow_nonneg hℓ0 _)
      refine ⟨fun i ↦ ?_, ?_⟩
      · have e : (spmState φ α β₁ βbar p₀ c r (t + 1)).1 i
            = (spmState φ α β₁ βbar p₀ c r t).1 i + spmEstimateAt φ α β₁ βbar p₀ c r t i := by
          rw [spmState_succ]
          rfl
        have hgi : |spmEstimateAt φ α β₁ βbar p₀ c r t i| ≤ _ :=
          (abs_spmEstimate_le φ hP hV (le_spmState_snd (φ := φ) (p₀ := p₀) hP r t)
            h𝒳 (hr t) i).trans hg
        rw [e, spmBound]
        refine (abs_add_le _ _).trans ?_
        linarith [ih.1 i, hgi]
      · rw [spmBound]
        linarith [ih.2]
  obtain ⟨hG, hβ⟩ := hstate t
  refine ⟨hG, hβ, ?_⟩
  have := (hest t hG hβ).1
  have hB0 := spmBound_nonneg (α := α) hβ₁.le hβbar.le (Fintype.card 𝒳) t
  have hℓ0 : 0 ≤ spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t) :=
    Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ βbar * spmLow α βbar (Fintype.card 𝒳) (spmBound α β₁ βbar (Fintype.card 𝒳) t)
      ^ (1 - 2 * α) := mul_nonneg hβbar.le (Real.rpow_nonneg hℓ0 _)
  rw [spmBound]
  linarith

end Path

end Ito2026Adversarial
