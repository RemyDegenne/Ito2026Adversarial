/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.FTRLRegret
public import Ito2026Adversarial.LeanMachineLearning.Online.Bandit.TsallisINF

/-!
# FTRL with the Tsallis-`1/2` entropy

The FTRL objective `q ↦ ⟪q, θ⟫ + φ(q)` on the simplex for the Tsallis entropy with parameter
`1/2`, `φ(q) = 2 ∑ i, (√(q i) - q i)`, and the stability of FTRL with this regularizer (Zimmert,
Seldin 2021; Ito et al. 2025).

The maximizer is explicit: `p i = (ν - θ i)⁻²` for the normalization `ν > max θ` with
`∑ i, (ν - θ i)⁻² = 1`, and the objective satisfies the exact identity
`⟪q, θ⟫ + φ(q) = ⟪p, θ⟫ + φ(p) - ∑ i, (√(q i) - √(p i))² / √(p i)` on the simplex.

## Main statements

* `exists_tsallisHalf_objective_eq`: the maximizer and the identity above;
* `ftrlSimplex_tsallisEntropy_half`: the FTRL distribution `ftrlSimplex (tsallisEntropy (1/2)) θ`
  (defined as a gradient of the value function) is this maximizer;
* `inner_sub_sub_le_tsallisHalf`: the stability bound
  `⟪q - p, g⟫ - η⁻¹ ∑ i, (√(q i) - √(p i))² / √(p i) ≤ 2 η ∑ i, √(p i)³ (c - g i)²`
  for every shift `c` such that `η √(p i) (c - g i) ≥ -1/2` (the shift by a constant does not
  change FTRL on the simplex, which allows to exclude any one arm from the variance term);
* `Bandits.TsallisINF.inner_sub_estimate_sub_le`, `Bandits.TsallisINF.inner_sub_estimate_sub_le'`:
  the stability bound for the importance-weighted estimate of Tsallis-INF, and its crude form;
* `Bandits.TsallisINF.sum_mul_stabilityWeight`: the conditional expectation of the stability
  bound, `∑ j, p j * w(p, j) = ∑ i, √(p i) (1 - p i)`.
-/

@[expose] public section

open Finset Real
open scoped RealInnerProductSpace

namespace Learning

variable {ι : Type*} [Fintype ι]

/-! ### The Tsallis-`1/2` entropy -/

/-- The Tsallis entropy with parameter `1/2` is `2 ∑ i, (√(p i) - p i)`. -/
lemma tsallisEntropy_half (p : EuclideanSpace ℝ ι) :
    tsallisEntropy (1 / 2) p = 2 * ∑ i, (√(p i) - p i) := by
  simp only [tsallisEntropy, Real.sqrt_eq_rpow]
  norm_num

/-- On the simplex, the Tsallis entropy with parameter `1/2` is `2 (∑ i, √(p i) - 1)`. -/
lemma tsallisEntropy_half_of_mem_simplex {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    tsallisEntropy (1 / 2) p = 2 * (∑ i, √(p i) - 1) := by
  rw [tsallisEntropy_half, sum_sub_distrib, hp.2]

/-- The Tsallis entropy of a point of the simplex is nonnegative. -/
lemma tsallisEntropy_half_nonneg {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    0 ≤ tsallisEntropy (1 / 2) p := by
  rw [tsallisEntropy_half]
  refine mul_nonneg zero_le_two (sum_nonneg fun i _ ↦ sub_nonneg.2 ?_)
  have h0 := hp.1 i
  have h1 := le_one_of_mem_simplex hp i
  calc p i = √(p i) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ √(p i) := by
      rw [sq]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 h1)

/-- The Tsallis entropy vanishes at the vertices of the simplex. -/
lemma tsallisEntropy_half_single [DecidableEq ι] (x : ι) :
    tsallisEntropy (1 / 2) (EuclideanSpace.single x (1 : ℝ)) = 0 := by
  rw [tsallisEntropy_half_of_mem_simplex (single_mem_simplex x)]
  simp only [PiLp.single_apply]
  rw [sum_eq_single x (fun i _ hi ↦ by simp [hi]) (by simp)]
  simp

/-- The Tsallis entropy of `p` is at most `2 ∑_{i ≠ x} √(p i)`, for every `x`. -/
lemma tsallisEntropy_half_le_sum_erase [DecidableEq ι] {p : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) (x : ι) :
    tsallisEntropy (1 / 2) p ≤ 2 * ∑ i ∈ univ.erase x, √(p i) := by
  rw [tsallisEntropy_half_of_mem_simplex hp, ← add_sum_erase _ _ (mem_univ x)]
  have : √(p x) ≤ 1 := Real.sqrt_le_one.2 (le_one_of_mem_simplex hp x)
  linarith

/-- `∑ i, √(p i) ≤ √|ι|` on the simplex (Cauchy–Schwarz). -/
lemma sum_sqrt_le_sqrt_card {p : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι) :
    ∑ i, √(p i) ≤ √(Fintype.card ι) := by
  have h := sum_mul_sq_le_sq_mul_sq univ (fun _ ↦ (1 : ℝ)) fun i ↦ √(p i)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  have h1 : ∑ i, √(p i) ^ 2 = 1 := by
    rw [← hp.2]
    exact sum_congr rfl fun i _ ↦ Real.sq_sqrt (hp.1 i)
  rw [h1, mul_one] at h
  exact Real.le_sqrt_of_sq_le h

/-! ### The maximizer of the FTRL objective -/

/-- The normalization of the maximizer: for every `θ` there is `ν > max θ` with
`∑ i, (ν - θ i)⁻² = 1`. -/
lemma exists_tsallisHalf_normalizer [Nonempty ι] (θ : ι → ℝ) :
    ∃ ν : ℝ, (∀ i, θ i < ν) ∧ ∑ i, ((ν - θ i) ^ 2)⁻¹ = 1 := by
  obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ θ univ_nonempty
  have hle (i : ι) : θ i ≤ θ i₀ := hi₀ i (mem_univ i)
  set m : ℝ := (Fintype.card ι : ℝ)
  have hm : 1 ≤ m := Nat.one_le_cast.2 Fintype.card_pos
  have hsm : 1 ≤ √m := Real.one_le_sqrt.2 hm
  have hcont : ContinuousOn (fun ν ↦ ∑ i, ((ν - θ i) ^ 2)⁻¹)
      (Set.Icc (θ i₀ + 1) (θ i₀ + √m)) := by
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    refine ((continuousOn_id.sub continuousOn_const).pow 2).inv₀ fun ν hν ↦ ?_
    have : 0 < ν - θ i := by linarith [hν.1, hle i]
    exact pow_ne_zero 2 this.ne'
  have h1 : 1 ≤ ∑ i, ((θ i₀ + 1 - θ i) ^ 2)⁻¹ := by
    calc (1 : ℝ) = ((θ i₀ + 1 - θ i₀) ^ 2)⁻¹ := by ring_nf
      _ ≤ ∑ i, ((θ i₀ + 1 - θ i) ^ 2)⁻¹ :=
        single_le_sum (f := fun i ↦ ((θ i₀ + 1 - θ i) ^ 2)⁻¹) (fun i _ ↦ by positivity)
          (mem_univ i₀)
  have h2 : ∑ i, ((θ i₀ + √m - θ i) ^ 2)⁻¹ ≤ 1 := by
    calc ∑ i, ((θ i₀ + √m - θ i) ^ 2)⁻¹ ≤ ∑ _i : ι, m⁻¹ := sum_le_sum fun i _ ↦ by
          have h3 : √m ≤ θ i₀ + √m - θ i := by linarith [hle i]
          have h4 : m ≤ (θ i₀ + √m - θ i) ^ 2 := by
            nlinarith [Real.sq_sqrt (show 0 ≤ m by linarith), Real.sqrt_nonneg m]
          exact inv_anti₀ (by linarith) h4
      _ = 1 := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (by linarith)
  obtain ⟨ν, hν, hfν⟩ := intermediate_value_Icc' (by linarith) hcont ⟨h2, h1⟩
  exact ⟨ν, fun i ↦ by linarith [hle i, hν.1], hfν⟩

/-- The one-dimensional identity behind `tsallisHalf_objective_eq`. -/
private lemma tsallisHalf_objective_aux (a s ν : ℝ) (ha : 0 < a) :
    s ^ 2 * (ν - a⁻¹) + 2 * (s - s ^ 2) - (a ^ 2 * (ν - a⁻¹) + 2 * (a - a ^ 2))
      + (s - a) ^ 2 / a = (ν - 2) * (s ^ 2 - a ^ 2) := by
  field_simp
  ring

/-- **The FTRL objective of the Tsallis-`1/2` entropy.** If `p` is a point of the simplex with
positive coordinates and `θ i = ν - 1 / √(p i)` for some `ν`, then for every `q` of the simplex,
`⟪q, θ⟫ + φ(q) = ⟪p, θ⟫ + φ(p) - ∑ i, (√(q i) - √(p i))² / √(p i)`. In particular `p` maximizes
the objective. -/
lemma tsallisHalf_objective_eq {θ p q : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hp0 : ∀ i, 0 < p i) {ν : ℝ} (hθ : ∀ i, θ i = ν - (√(p i))⁻¹) (hq : q ∈ simplex ι) :
    ⟪q, θ⟫ + tsallisEntropy (1 / 2) q
      = ⟪p, θ⟫ + tsallisEntropy (1 / 2) p - ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i) := by
  have key (i : ι) : q i * θ i + 2 * (√(q i) - q i) - (p i * θ i + 2 * (√(p i) - p i))
      + (√(q i) - √(p i)) ^ 2 / √(p i) = (ν - 2) * (q i - p i) := by
    have h := tsallisHalf_objective_aux (√(p i)) (√(q i)) ν (Real.sqrt_pos.2 (hp0 i))
    rw [Real.sq_sqrt (hq.1 i), Real.sq_sqrt (hp0 i).le] at h
    rw [hθ i, ← h]
  have hsum : ∑ i, (ν - 2) * (q i - p i) = 0 := by
    rw [← mul_sum, sum_sub_distrib, hq.2, hp.2, sub_self, mul_zero]
  have hkey : ∑ i, (q i * θ i + 2 * (√(q i) - q i) - (p i * θ i + 2 * (√(p i) - p i))
      + (√(q i) - √(p i)) ^ 2 / √(p i)) = 0 := by
    rw [sum_congr rfl fun i _ ↦ key i, hsum]
  simp only [tsallisEntropy_half, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hkey ⊢
  simp only [mul_comm (θ _)]
  linarith

/-- The objective gap `∑ i, (√(q i) - √(p i))² / √(p i)` is at least `‖q - p‖² / 4`. -/
lemma sq_norm_sub_div_four_le {p q : EuclideanSpace ℝ ι} (hp : p ∈ simplex ι)
    (hp0 : ∀ i, 0 < p i) (hq : q ∈ simplex ι) :
    ‖q - p‖ ^ 2 / 4 ≤ ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun i _ ↦ sq_nonneg _), sum_div]
  refine sum_le_sum fun i _ ↦ ?_
  have hpi : 0 < √(p i) := Real.sqrt_pos.2 (hp0 i)
  have hp1 : √(p i) ≤ 1 := Real.sqrt_le_one.2 (le_one_of_mem_simplex hp i)
  have hq1 : √(q i) ≤ 1 := Real.sqrt_le_one.2 (le_one_of_mem_simplex hq i)
  have hq0 : 0 ≤ √(q i) := Real.sqrt_nonneg _
  have hsq : ‖(q - p) i‖ ^ 2 = (√(q i) - √(p i)) ^ 2 * (√(q i) + √(p i)) ^ 2 := by
    rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, ← mul_pow]
    congr 1
    linear_combination -Real.sq_sqrt (hq.1 i) + Real.sq_sqrt (hp0 i).le
  rw [hsq, le_div_iff₀ hpi]
  have h4 : (√(q i) + √(p i)) ^ 2 ≤ 4 := by nlinarith
  nlinarith [sq_nonneg (√(q i) - √(p i)), mul_nonneg (sq_nonneg (√(q i) - √(p i)))
    (sub_nonneg.2 h4), mul_nonneg (sq_nonneg (√(q i) - √(p i))) (sub_nonneg.2 hp1)]

/-- **The maximizer of the Tsallis-`1/2` FTRL objective.** For every `θ` there is a point `p` of
the simplex with positive coordinates such that, for every `q` of the simplex,
`⟪q, θ⟫ + φ(q) = ⟪p, θ⟫ + φ(p) - ∑ i, (√(q i) - √(p i))² / √(p i)`. -/
lemma exists_tsallisHalf_objective_eq [Nonempty ι] (θ : EuclideanSpace ℝ ι) :
    ∃ p ∈ simplex ι, (∀ i, 0 < p i) ∧ ∀ q ∈ simplex ι,
      ⟪q, θ⟫ + tsallisEntropy (1 / 2) q
        = ⟪p, θ⟫ + tsallisEntropy (1 / 2) p - ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i) := by
  obtain ⟨ν, hν, hsum⟩ := exists_tsallisHalf_normalizer fun i ↦ θ i
  set p : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ((ν - θ i) ^ 2)⁻¹ with hp_def
  have hp0 (i : ι) : 0 < p i := by
    have : 0 < ν - θ i := sub_pos.2 (hν i)
    simp only [hp_def]
    positivity
  have hp : p ∈ simplex ι := ⟨fun i ↦ (hp0 i).le, hsum⟩
  have hθ (i : ι) : θ i = ν - (√(p i))⁻¹ := by
    have : 0 < ν - θ i := sub_pos.2 (hν i)
    simp only [hp_def, Real.sqrt_inv, Real.sqrt_sq this.le, inv_inv]
    ring
  exact ⟨p, hp, hp0, fun q hq ↦ tsallisHalf_objective_eq hp hp0 hθ hq⟩

/-- **The FTRL distribution of the Tsallis-`1/2` entropy.** The FTRL distribution
`ftrlSimplex (tsallisEntropy (1/2)) θ` has positive coordinates and, for every `q` of the
simplex, `⟪q, θ⟫ + φ(q) = ⟪p, θ⟫ + φ(p) - ∑ i, (√(q i) - √(p i))² / √(p i)`, where `p` is the
FTRL distribution. -/
lemma ftrlSimplex_tsallisEntropy_half [Nonempty ι] (θ : EuclideanSpace ℝ ι) :
    (∀ i, 0 < ftrlSimplex (tsallisEntropy (1 / 2)) θ i) ∧ ∀ q ∈ simplex ι,
      ⟪q, θ⟫ + tsallisEntropy (1 / 2) q
        = ⟪(ftrlSimplex (tsallisEntropy (1 / 2)) θ : EuclideanSpace ℝ ι), θ⟫
          + tsallisEntropy (1 / 2) (ftrlSimplex (tsallisEntropy (1 / 2)) θ : EuclideanSpace ℝ ι)
          - ∑ i, (√(q i) - √(ftrlSimplex (tsallisEntropy (1 / 2)) θ i)) ^ 2
            / √(ftrlSimplex (tsallisEntropy (1 / 2)) θ i) := by
  choose P hP hP0 hPeq using fun θ : EuclideanSpace ℝ ι ↦ exists_tsallisHalf_objective_eq θ
  have hgrowth (θ : EuclideanSpace ℝ ι) : ∀ q ∈ simplex ι,
      ⟪q, θ⟫ + tsallisEntropy (1 / 2) q + 1 / 4 * ‖q - P θ‖ ^ 2
        ≤ ⟪P θ, θ⟫ + tsallisEntropy (1 / 2) (P θ) := fun q hq ↦ by
    have h1 := hPeq θ q hq
    have h2 := sq_norm_sub_div_four_le (hP θ) (hP0 θ) hq
    linarith
  rw [ftrlSimplex_eq (by norm_num) hP hgrowth θ]
  exact ⟨hP0 θ, hPeq θ⟩

/-- The FTRL distribution of the Tsallis-`1/2` entropy for the cumulative reward `G` and the
learning rate `η > 0` maximizes `q ↦ ⟪q, G⟫ + η⁻¹ φ(q)` over the simplex. -/
lemma isMaxOn_ftrlSimplex_tsallisEntropy_half [Nonempty ι] {η : ℝ} (hη : 0 < η)
    (G : EuclideanSpace ℝ ι) (q : EuclideanSpace ℝ ι) (hq : q ∈ simplex ι) :
    ⟪q, G⟫ + η⁻¹ * tsallisEntropy (1 / 2) q
      ≤ ⟪(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) : EuclideanSpace ℝ ι), G⟫
        + η⁻¹ * tsallisEntropy (1 / 2)
          (ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) : EuclideanSpace ℝ ι) := by
  have h := (ftrlSimplex_tsallisEntropy_half (η • G)).2 q hq
  have hD : 0 ≤ ∑ i, (√(q i) - √(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) i)) ^ 2
      / √(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) i) :=
    sum_nonneg fun i _ ↦ div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  rw [inner_smul_right, inner_smul_right] at h
  have hη' : 0 < η⁻¹ := inv_pos.2 hη
  have : η * ⟪q, G⟫ + tsallisEntropy (1 / 2) q ≤
      η * ⟪(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) : EuclideanSpace ℝ ι), G⟫
        + tsallisEntropy (1 / 2)
          (ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) : EuclideanSpace ℝ ι) := by linarith
  have := mul_le_mul_of_nonneg_left this hη'.le
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul,
    one_mul] at this
  exact this

/-- **Stability term of FTRL with the Tsallis-`1/2` entropy.** For the FTRL distributions
`p = P(η G)` and `p' = P(η (G + g))` with the regularizer `η⁻¹ φ`, the stability term of a round
with reward `g` is `⟪p' - p, g⟫ - η⁻¹ ∑ i, (√(p' i) - √(p i))² / √(p i)`. -/
lemma ftrlValue_add_sub_tsallisHalf [Nonempty ι] {η : ℝ} (hη : 0 < η)
    (G g : EuclideanSpace ℝ ι) :
    ftrlValue (η⁻¹ • tsallisEntropy (1 / 2)) (G + g)
        - ftrlValue (η⁻¹ • tsallisEntropy (1 / 2)) G
        - ⟪(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) : EuclideanSpace ℝ ι), g⟫
      = ⟪(ftrlSimplex (tsallisEntropy (1 / 2)) (η • (G + g)) : EuclideanSpace ℝ ι)
          - ftrlSimplex (tsallisEntropy (1 / 2)) (η • G), g⟫
        - η⁻¹ * ∑ i, (√(ftrlSimplex (tsallisEntropy (1 / 2)) (η • (G + g)) i)
            - √(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) i)) ^ 2
          / √(ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) i) := by
  set p : EuclideanSpace ℝ ι :=
    ((ftrlSimplex (tsallisEntropy (1 / 2)) (η • G) : simplex ι) : EuclideanSpace ℝ ι)
  set p' : EuclideanSpace ℝ ι :=
    ((ftrlSimplex (tsallisEntropy (1 / 2)) (η • (G + g)) : simplex ι) : EuclideanSpace ℝ ι)
  have hp : p ∈ simplex ι := (ftrlSimplex _ _).2
  have hp' : p' ∈ simplex ι := (ftrlSimplex _ _).2
  have hV : ftrlValue (η⁻¹ • tsallisEntropy (1 / 2)) G
      = ⟪p, G⟫ + η⁻¹ * tsallisEntropy (1 / 2) p :=
    ftrlValue_eq_of_isMaxOn hp (isMaxOn_ftrlSimplex_tsallisEntropy_half hη G)
  have hW : ftrlValue (η⁻¹ • tsallisEntropy (1 / 2)) (G + g)
      = ⟪p', G + g⟫ + η⁻¹ * tsallisEntropy (1 / 2) p' :=
    ftrlValue_eq_of_isMaxOn hp' (isMaxOn_ftrlSimplex_tsallisEntropy_half hη (G + g))
  have h := (ftrlSimplex_tsallisEntropy_half (η • G)).2 p' hp'
  rw [inner_smul_right, inner_smul_right] at h
  rw [hV, hW, inner_add_right, inner_sub_left]
  have hη' : η⁻¹ * η = 1 := inv_mul_cancel₀ hη.ne'
  have h' := congrArg (fun z ↦ η⁻¹ * z) h
  simp only [mul_add, mul_sub, ← mul_assoc, hη', one_mul] at h'
  linarith

/-! ### Stability -/

/-- The one-dimensional stability inequality:
`(a² - s²) ℓ - (s - a)² / (η a) ≤ 2 η a³ ℓ²` for `a, η > 0` and `η a ℓ ≥ -1/2`. -/
lemma sq_sub_sq_mul_sub_le {η a s ℓ : ℝ} (hη : 0 < η) (ha : 0 < a) (hℓ : -(1 / 2) ≤ η * a * ℓ) :
    (a ^ 2 - s ^ 2) * ℓ - (s - a) ^ 2 / (η * a) ≤ 2 * η * a ^ 3 * ℓ ^ 2 := by
  have hηa : 0 < η * a := mul_pos hη ha
  have key : ((a ^ 2 - s ^ 2) * ℓ - 2 * η * a ^ 3 * ℓ ^ 2) * (η * a) ≤ (s - a) ^ 2 := by
    nlinarith [sq_nonneg (2 * η * a ^ 2 * ℓ + (s - a)),
      mul_nonneg (sq_nonneg (s - a)) (show 0 ≤ 1 / 2 + η * a * ℓ by linarith)]
  have : (a ^ 2 - s ^ 2) * ℓ - 2 * η * a ^ 3 * ℓ ^ 2 ≤ (s - a) ^ 2 / (η * a) := by
    rwa [le_div_iff₀ hηa]
  linarith

/-- **Stability of the Tsallis-`1/2` entropy.** For `p` in the simplex with positive coordinates,
`q` in the simplex, a reward vector `g` and a shift `c` with `η √(p i) (c - g i) ≥ -1/2` for all
`i`, `⟪q - p, g⟫ - η⁻¹ ∑ i, (√(q i) - √(p i))² / √(p i) ≤ 2 η ∑ i, √(p i)³ (c - g i)²`. -/
lemma inner_sub_sub_le_tsallisHalf {η c : ℝ} (hη : 0 < η) {p q g : EuclideanSpace ℝ ι}
    (hp : p ∈ simplex ι) (hp0 : ∀ i, 0 < p i) (hq : q ∈ simplex ι)
    (hc : ∀ i, -(1 / 2) ≤ η * √(p i) * (c - g i)) :
    ⟪q - p, g⟫ - η⁻¹ * ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i)
      ≤ 2 * η * ∑ i, √(p i) ^ 3 * (c - g i) ^ 2 := by
  have h1 : ⟪q - p, g⟫ = ∑ i, (p i - q i) * (c - g i) := by
    have hc0 : ∑ i, (p i - q i) * c = 0 := by
      rw [← sum_mul, sum_sub_distrib, hp.2, hq.2, sub_self, zero_mul]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.sub_apply]
    rw [← add_zero (∑ i, g i * (q i - p i)), ← hc0, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [h1, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun i _ ↦ ?_
  have ha : 0 < √(p i) := Real.sqrt_pos.2 (hp0 i)
  have h := sq_sub_sq_mul_sub_le (s := √(q i)) hη ha (hc i)
  rw [Real.sq_sqrt (hp0 i).le, Real.sq_sqrt (hq.1 i)] at h
  have h2 : η⁻¹ * ((√(q i) - √(p i)) ^ 2 / √(p i)) = (√(q i) - √(p i)) ^ 2 / (η * √(p i)) := by
    field_simp
  rw [h2]
  linarith

/-- The objective gap `∑ i, (√(q i) - √(p i))² / √(p i)` is nonnegative. -/
lemma sum_sq_sqrt_sub_div_nonneg (p q : EuclideanSpace ℝ ι) :
    0 ≤ ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i) :=
  sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

end Learning

/-! ### The importance-weighted estimate of Tsallis-INF -/

namespace Bandits.TsallisINF

open Learning

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight `w(p, j) = ∑ i, √(p i)³ (if i = j then (1 / p j - 1)² else 1)` of the stability
bound of a round in which the arm `j` is played with the distribution `p` is nonnegative. -/
lemma stabilityWeight_nonneg (p : ι → ℝ) (j : ι) :
    0 ≤ ∑ i, √(p i) ^ 3 * (if i = j then (1 / p j - 1) ^ 2 else 1) :=
  sum_nonneg fun i _ ↦ mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (by split_ifs <;> positivity)

/-- The importance-weighted estimate, coordinatewise:
`g i = 1 - 𝟙{x_t = i} (1 - r) / p x_t`. -/
lemma estimate_apply_eq (p : simplex ι) (r : Round Unit ι ℝ) (i : ι) :
    estimate p r i = 1 - if r.action = i then (1 - r.feedback) / p r.action else 0 := by
  rw [estimate_apply, importanceWeighted]

/-- The gain of the distribution `p` under its importance-weighted estimate is the reward. -/
lemma inner_estimate (p : simplex ι) (r : Round Unit ι ℝ) (hp : p r.action ≠ 0) :
    ⟪(p : EuclideanSpace ℝ ι), estimate p r⟫ = r.feedback := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, estimate_apply_eq, sub_mul,
    one_mul, sum_sub_distrib, ite_mul, zero_mul]
  rw [sum_ite_eq univ r.action, ite_eq_left (mem_univ _)]
  have h1 : ∑ i, (p : EuclideanSpace ℝ ι) i = 1 := p.2.2
  change ∑ i, p i = 1 at h1
  change ∑ i, p i - (1 - r.feedback) / p r.action * p r.action = r.feedback
  rw [h1, div_mul_cancel₀ _ hp]
  ring

/-- The gain of a vertex `x` under the importance-weighted estimate. -/
lemma inner_single_estimate (p : simplex ι) (r : Round Unit ι ℝ) (x : ι) :
    ⟪EuclideanSpace.single x (1 : ℝ), estimate p r⟫ = estimate p r x := by
  rw [EuclideanSpace.inner_single_left]
  simp

/-- **Stability for the importance-weighted estimate.** If `η ≤ 1/4` and the reward of the round
is in `[-1, 1]`, the stability term of a round of FTRL with the Tsallis-`1/2` entropy and the
importance-weighted estimate `g` of Tsallis-INF is at most `8 η w(p, j)`, where `j` is the arm
played and `w(p, j) = ∑ i, √(p i)³ (if i = j then (1 / p j - 1)² else 1)` (the estimate is
shifted by the reward `r`, which excludes the played arm's variance). -/
lemma inner_sub_estimate_sub_le {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (p : simplex ι)
    (hp0 : ∀ i, 0 < p i) {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (r : Round Unit ι ℝ)
    (hr : r.feedback ∈ Set.Icc (-1) 1) :
    ⟪q - p, estimate p r⟫ - η⁻¹ * ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i)
      ≤ 8 * η * ∑ i, √(p i) ^ 3 * (if i = r.action then (1 / p r.action - 1) ^ 2 else 1) := by
  have hdiff (i : ι) : r.feedback - estimate p r i
      = (1 - r.feedback) * (if i = r.action then 1 / p r.action - 1 else -1) := by
    rw [estimate_apply_eq]
    by_cases hi : i = r.action
    · subst hi
      simp only [ite_true]
      field_simp
      ring
    · simp only [Ne.symm hi, ite_false, hi]
      ring
  have hpj : 1 / p r.action - 1 ≥ 0 := by
    rw [ge_iff_le, sub_nonneg, le_div_iff₀ (hp0 _), one_mul]
    exact simplex.le_one p _
  have hc (i : ι) : -(1 / 2) ≤ η * √(p i) * (r.feedback - estimate p r i) := by
    rw [hdiff]
    have hsq : √(p i) ≤ 1 := Real.sqrt_le_one.2 (simplex.le_one p i)
    have hs0 : 0 ≤ √(p i) := Real.sqrt_nonneg _
    by_cases hi : i = r.action
    · subst hi
      simp only [ite_true]
      have : 0 ≤ 1 - r.feedback := by linarith [hr.2]
      have := mul_nonneg (mul_nonneg hη.le hs0) (mul_nonneg this hpj)
      linarith
    · simp only [hi, ite_false]
      have h2 : 1 - r.feedback ≤ 2 := by linarith [hr.1]
      have h3 : 0 ≤ 1 - r.feedback := by linarith [hr.2]
      have : η * √(p i) * (1 - r.feedback) ≤ 1 / 4 * 1 * 2 :=
        mul_le_mul (mul_le_mul hη4 hsq hs0 (by norm_num)) h2 h3 (by norm_num)
      linarith
  refine (inner_sub_sub_le_tsallisHalf hη p.2 hp0 hq hc).trans ?_
  have hterm (i : ι) : √(p i) ^ 3 * (r.feedback - estimate p r i) ^ 2
      ≤ 4 * (√(p i) ^ 3 * (if i = r.action then (1 / p r.action - 1) ^ 2 else 1)) := by
    have hsq : (r.feedback - estimate p r i) ^ 2
        ≤ 4 * (if i = r.action then (1 / p r.action - 1) ^ 2 else 1) := by
      rw [hdiff, mul_pow]
      have h4 : (1 - r.feedback) ^ 2 ≤ 4 := by nlinarith [hr.1, hr.2]
      split_ifs
      · exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      · simpa using h4
    calc √(p i) ^ 3 * (r.feedback - estimate p r i) ^ 2
        ≤ √(p i) ^ 3 * (4 * (if i = r.action then (1 / p r.action - 1) ^ 2 else 1)) :=
          mul_le_mul_of_nonneg_left hsq (pow_nonneg (Real.sqrt_nonneg _) _)
      _ = _ := by ring
  calc 2 * η * ∑ i, √(p i) ^ 3 * (r.feedback - estimate p r i) ^ 2
      ≤ 2 * η * ∑ i, 4 * (√(p i) ^ 3 * (if i = r.action then (1 / p r.action - 1) ^ 2 else 1)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun i _ ↦ hterm i) (by positivity)
    _ = _ := by rw [← mul_sum]; ring

/-- **Crude stability for the importance-weighted estimate.** For any learning rate, the
stability term of a round of FTRL with the Tsallis-`1/2` entropy and the importance-weighted
estimate is at most `1 - r ≤ 2`. -/
lemma inner_sub_estimate_sub_le' {η : ℝ} (hη : 0 < η) (p : simplex ι)
    (hp0 : ∀ i, 0 < p i) {q : EuclideanSpace ℝ ι} (hq : q ∈ simplex ι) (r : Round Unit ι ℝ)
    (hr : r.feedback ∈ Set.Icc (-1) 1) :
    ⟪q - p, estimate p r⟫ - η⁻¹ * ∑ i, (√(q i) - √(p i)) ^ 2 / √(p i) ≤ 2 := by
  have hD := mul_nonneg (inv_pos.2 hη).le (sum_sq_sqrt_sub_div_nonneg (p : EuclideanSpace ℝ ι) q)
  have h1 : ⟪q, estimate p r⟫ = 1 - q r.action * (1 - r.feedback) / p r.action := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, estimate_apply_eq, sub_mul,
      one_mul, sum_sub_distrib, ite_mul, zero_mul]
    rw [sum_ite_eq univ r.action, ite_eq_left (mem_univ _), hq.2]
    ring
  have h2 := inner_estimate p r (hp0 _).ne'
  have h3 : 0 ≤ q r.action * (1 - r.feedback) / p r.action :=
    div_nonneg (mul_nonneg (hq.1 _) (by linarith [hr.2])) (hp0 _).le
  rw [inner_sub_left, h1, h2]
  linarith [hr.1]

/-- The conditional expectation of the stability weight when the arm is drawn from `p`:
`∑ j, p j w(p, j) = ∑ i, √(p i) (1 - p i)`. -/
lemma sum_mul_stabilityWeight (p : simplex ι) (hp0 : ∀ i, 0 < p i) :
    ∑ j, p j * ∑ i, √(p i) ^ 3 * (if i = j then (1 / p j - 1) ^ 2 else 1)
      = ∑ i, √(p i) * (1 - p i) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  have hsum : ∑ j, p j * (√(p i) ^ 3 * (if i = j then (1 / p j - 1) ^ 2 else 1))
      = √(p i) ^ 3 * (p i * (1 / p i - 1) ^ 2 + (1 - p i)) := by
    have h1 : ∑ j ∈ univ.erase i, p j = 1 - p i := by
      rw [← simplex.sum_eq_one p, ← add_sum_erase _ _ (mem_univ i)]
      ring
    rw [← add_sum_erase _ _ (mem_univ i), ite_eq_left rfl, ← h1, mul_add, mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl fun j hj ↦ ?_
      rw [ite_eq_right (Ne.symm (ne_of_mem_erase hj))]
      ring
  rw [hsum]
  have hpi : 0 < p i := hp0 i
  have h3 : √(p i) ^ 3 = p i * √(p i) := by
    rw [pow_succ, Real.sq_sqrt hpi.le, mul_comm]
  rw [h3]
  field_simp
  ring

/-- `∑ i, √(p i) (1 - p i) ≤ 2 ∑_{i ≠ x} √(p i)` on the simplex, for every `x`. -/
lemma sum_sqrt_mul_one_sub_le (p : simplex ι) (x : ι) :
    ∑ i, √(p i) * (1 - p i) ≤ 2 * ∑ i ∈ univ.erase x, √(p i) := by
  rw [← add_sum_erase _ _ (mem_univ x)]
  have h1 : 1 - p x = ∑ i ∈ univ.erase x, p i := by
    rw [← simplex.sum_eq_one p, ← add_sum_erase _ _ (mem_univ x)]
    ring
  have h2 : √(p x) * (1 - p x) ≤ ∑ i ∈ univ.erase x, √(p i) := by
    have hx : √(p x) ≤ 1 := Real.sqrt_le_one.2 (simplex.le_one p x)
    have hx' : 0 ≤ 1 - p x := by linarith [simplex.le_one p x]
    calc √(p x) * (1 - p x) ≤ 1 * (1 - p x) :=
          mul_le_mul_of_nonneg_right hx hx'
      _ = ∑ i ∈ univ.erase x, p i := by rw [one_mul, h1]
      _ ≤ ∑ i ∈ univ.erase x, √(p i) := sum_le_sum fun i _ ↦ by
          have h0 := simplex.nonneg p i
          have h1 := simplex.le_one p i
          calc p i = √(p i) ^ 2 := (Real.sq_sqrt h0).symm
            _ ≤ √(p i) := by
              rw [sq]
              exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 h1)
  have h3 : ∑ i ∈ univ.erase x, √(p i) * (1 - p i) ≤ ∑ i ∈ univ.erase x, √(p i) :=
    sum_le_sum fun i _ ↦ mul_le_of_le_one_right (Real.sqrt_nonneg _)
      (by linarith [simplex.nonneg p i])
  linarith

end Bandits.TsallisINF
