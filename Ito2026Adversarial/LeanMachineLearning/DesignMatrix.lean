/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Ito2026Adversarial.Mathlib.Analysis.Convex.CompactHull
public import Ito2026Adversarial.Mathlib.Analysis.CStarAlgebra.Matrix
public import Ito2026Adversarial.Mathlib.Analysis.InnerProductSpace.Mahalanobis
public import Ito2026Adversarial.Mathlib.Analysis.Matrix.Order
public import Ito2026Adversarial.Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Instances.Matrix

/-!
# Design matrices

For points `x` of a Euclidean space `EuclideanSpace ℝ ι`:

* `outerSelf x = x xᵀ` is the rank-one design matrix of `x`;
* `gram x t = ∑_{s < t} x_s x_sᵀ` is the Gram (design) matrix of the first `t` points of a
  sequence `x`, and `regGram λ x t = λ I + gram x t` its regularized version (the matrices `V_t`
  of least squares and ridge regression, linear bandits, and `A_t` of online Newton step);
* `designSet 𝒳 = conv {x xᵀ : x ∈ 𝒳}` is the set of *design matrices* `A(λ) = ∑ λ_x x xᵀ` of
  the finitely supported probability distributions `λ` on the set `𝒳` (the *designs* on `𝒳`, in
  the sense of optimal experimental design).

## Main results

On `outerSelf`: positive semidefiniteness, trace (`trace_outerSelf`), continuity, action as a
linear map (`x xᵀ θ = ⟪x, θ⟫ x`, `toEuclideanCLM_outerSelf_apply`), quadratic form
(`uᵀ (x xᵀ) u = ⟪u, x⟫²`, `dotProduct_outerSelf_mulVec`), behaviour under linear maps
(`(M x)(M x)ᵀ = M (x xᵀ) Mᵀ`, `outerSelf_toEuclideanCLM`) and the matrix determinant lemma for
`(1 - t) A + t x xᵀ` (`det_smul_add_smul_outerSelf`).

On `designSet`: every design matrix is positive semidefinite (`posSemidef_of_mem_designSet`) and
has trace at most `R ^ 2` when `𝒳` is contained in the ball of radius `R`
(`trace_le_of_mem_designSet`); `designSet 𝒳` is convex (`convex_designSet`) and compact when `𝒳`
is compact (`isCompact_designSet`); empirical designs `T⁻¹ ∑ₜ xₜ xₜᵀ` are design matrices
(`inv_smul_sum_outerSelf_mem_designSet`); if `𝒳` spans the space, there is a positive definite
design matrix (`exists_posDef_mem_designSet`); the design set of the image of `𝒳` by a matrix `M`
is the image of `designSet 𝒳` by `A ↦ M A Mᵀ` (`designSet_image_toEuclideanCLM`).

On the Gram matrix `A = ∑_t x_t x_tᵀ` of finitely many points (least squares): the points span the
space when `A` is positive definite (`span_range_eq_top_of_posDef`),
`∑_t ⟪z, A⁻¹ x_t⟫² = zᵀ A⁻¹ z` (`sum_inner_toEuclideanCLM_inv_sum_outerSelf_sq`) and
`⟪z, θ⟫ = ∑_t ⟪z, A⁻¹ x_t⟫ ⟪x_t, θ⟫` for invertible `A`
(`inner_eq_sum_inner_toEuclideanCLM_inv_mul`: least squares is exact on noiseless observations).
-/

@[expose] public section

open Matrix Real
open scoped RealInnerProductSpace

namespace Learning

variable {ι : Type*}

/-- The design matrix `x xᵀ` of a point `x`. -/
def outerSelf (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x)

lemma outerSelf_eq_vecMulVec (x : EuclideanSpace ℝ ι) :
    outerSelf x = Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x) := rfl

/-- `outerSelf` is continuous. -/
@[fun_prop]
lemma continuous_outerSelf : Continuous (outerSelf (ι := ι)) :=
  Continuous.matrix_vecMulVec (PiLp.continuous_ofLp _ _) (PiLp.continuous_ofLp _ _)

/-- The design matrix `x xᵀ` is positive semidefinite. -/
lemma outerSelf_posSemidef [Finite ι] (x : EuclideanSpace ℝ ι) : (outerSelf x).PosSemidef := by
  have := Fintype.ofFinite ι
  simpa [outerSelf] using Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp x)

lemma posSemidef_sum_outerSelf [Finite ι] {κ : Type*} (s : Finset κ)
    (x : κ → EuclideanSpace ℝ ι) :
    (∑ t ∈ s, outerSelf (x t)).PosSemidef := by
  have := Fintype.ofFinite ι
  exact Finset.sum_induction _ _ (fun _ _ ha hb ↦ ha.add hb) Matrix.PosSemidef.zero
    fun t _ ↦ outerSelf_posSemidef (x t)

lemma transpose_sum_outerSelf {T : ℕ} (x : Fin T → EuclideanSpace ℝ ι) :
    (∑ t, outerSelf (x t))ᵀ = ∑ t, outerSelf (x t) := by
  simp [Matrix.transpose_sum, outerSelf_eq_vecMulVec, Matrix.transpose_vecMulVec]

/-! ### Gram matrices of sequences -/

/-- The Gram (design) matrix `V_t = ∑_{s < t} x_s x_sᵀ` of the first `t` points of the sequence
`x`. -/
noncomputable def gram (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) : Matrix ι ι ℝ :=
  ∑ s ∈ Finset.range t, outerSelf (x s)

@[simp]
lemma gram_zero (x : ℕ → EuclideanSpace ℝ ι) : gram x 0 = 0 := by simp [gram]

lemma gram_succ (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) :
    gram x (t + 1) = gram x t + outerSelf (x t) := by
  simp [gram, Finset.sum_range_succ]

/-- The Gram matrix of a sequence is positive semidefinite. -/
lemma posSemidef_gram [Finite ι] (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) : (gram x t).PosSemidef :=
  posSemidef_sum_outerSelf _ _

lemma transpose_gram (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) : (gram x t)ᵀ = gram x t := by
  simp [gram, Matrix.transpose_sum, outerSelf_eq_vecMulVec, Matrix.transpose_vecMulVec]

section RegGram

variable [DecidableEq ι]

/-- The regularized Gram matrix `λ I + ∑_{s < t} x_s x_sᵀ` of the first `t` points of the
sequence `x` (ridge regression, linear bandits, online Newton step). -/
noncomputable def regGram (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) : Matrix ι ι ℝ :=
  lam • 1 + gram x t

@[simp]
lemma regGram_zero (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) : regGram lam x 0 = lam • 1 := by
  simp [regGram]

lemma regGram_succ (lam : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) :
    regGram lam x (t + 1) = regGram lam x t + outerSelf (x t) := by
  simp [regGram, gram_succ, add_assoc]

/-- For `λ > 0` the regularized Gram matrix is positive definite. -/
lemma posDef_regGram [Finite ι] {lam : ℝ} (hlam : 0 < lam) (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ) :
    (regGram lam x t).PosDef :=
  ((PosDef.one).smul hlam).add_posSemidef (posSemidef_gram x t)

end RegGram

variable [Fintype ι]

/-- The trace of `x xᵀ` is `‖x‖ ^ 2`. -/
lemma trace_outerSelf (x : EuclideanSpace ℝ ι) : (outerSelf x).trace = ‖x‖ ^ 2 := by
  rw [outerSelf, Matrix.trace_vecMulVec, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- `xᵀ M x = tr (M x xᵀ)`. -/
lemma dotProduct_mulVec_eq_trace_mul_outerSelf (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    WithLp.ofLp x ⬝ᵥ M *ᵥ WithLp.ofLp x = (M * outerSelf x).trace := by
  rw [outerSelf, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- `uᵀ (y yᵀ) u = ⟪u, y⟫ ^ 2`. -/
lemma dotProduct_outerSelf_mulVec (u y : EuclideanSpace ℝ ι) :
    WithLp.ofLp u ⬝ᵥ outerSelf y *ᵥ WithLp.ofLp u = ⟪u, y⟫ ^ 2 := by
  rw [outerSelf, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul, sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm (WithLp.ofLp u)]

variable [DecidableEq ι]

/-- `(M x) (M x)ᵀ = M (x xᵀ) Mᵀ`. -/
lemma outerSelf_toEuclideanCLM (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    outerSelf (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) = M * outerSelf x * Mᵀ := by
  rw [outerSelf, outerSelf, Matrix.ofLp_toEuclideanCLM, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- `(N x)(N x)ᵀ = N (x xᵀ) Nᵀ` for a rectangular matrix `N`. -/
lemma outerSelf_toEuclideanLin {κ : Type*} (N : Matrix κ ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    outerSelf (Matrix.toEuclideanLin N x) = N * outerSelf x * Nᵀ := by
  rw [outerSelf, outerSelf, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rfl

/-- The action of `x xᵀ` on `θ` is `⟪x, θ⟫ • x`. -/
lemma toEuclideanCLM_outerSelf_apply (x θ : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (outerSelf x) θ = ⟪x, θ⟫ • x := by
  apply WithLp.ofLp_injective
  ext i
  simp [Matrix.ofLp_toEuclideanCLM, outerSelf_eq_vecMulVec, Matrix.vecMulVec_mulVec,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma toEuclideanCLM_sum_outerSelf_apply {T : ℕ} (x : Fin T → EuclideanSpace ℝ ι)
    (θ : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ t, outerSelf (x t)) θ = ∑ t, ⟪x t, θ⟫ • x t := by
  simp [map_sum, toEuclideanCLM_outerSelf_apply]

/-- The determinant of the mixture `(1 - t) A + t x xᵀ` of an invertible matrix `A` with a
rank-one matrix, by the matrix determinant lemma. -/
lemma det_smul_add_smul_outerSelf {A : Matrix ι ι ℝ} (hA : IsUnit A.det) {t : ℝ} (ht : t ≠ 1)
    (x : EuclideanSpace ℝ ι) :
    ((1 - t) • A + t • outerSelf x).det =
      (1 - t) ^ Fintype.card ι * A.det *
        (1 + t / (1 - t) * (WithLp.ofLp x ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp x)) := by
  have hs : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hsA : IsUnit ((1 - t) • A).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hs)).mul hA
  have h_inv : ((1 - t) • A)⁻¹ = (1 - t)⁻¹ • A⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.nonsing_inv_mul A hA, inv_mul_cancel₀ hs, one_smul]
  rw [outerSelf, ← Matrix.smul_vecMulVec, Matrix.det_add_vecMulVec hsA, Matrix.det_smul, h_inv,
    Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, div_eq_mul_inv]
  ring

section designSet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of design matrices of `𝒳`: the convex hull of `{x xᵀ : x ∈ 𝒳}`, that is the set of
matrices `∑ λ_x x xᵀ` for `λ` a finitely supported probability distribution on `𝒳`. -/
def designSet (𝒳 : Set (EuclideanSpace ℝ ι)) : Set (Matrix ι ι ℝ) :=
  convexHull ℝ (outerSelf '' 𝒳)

end designSet

variable {ι : Type*} {𝒳 : Set (EuclideanSpace ℝ ι)} {x : EuclideanSpace ℝ ι} {A : Matrix ι ι ℝ}
  {R : ℝ}

/-- The design matrix `x xᵀ` of a point `x ∈ 𝒳` belongs to `designSet 𝒳`. -/
lemma outerSelf_mem_designSet (hx : x ∈ 𝒳) : outerSelf x ∈ designSet 𝒳 :=
  subset_convexHull ℝ _ (Set.mem_image_of_mem _ hx)

/-- The set of design matrices is convex. -/
lemma convex_designSet : Convex ℝ (designSet 𝒳) := convex_convexHull ℝ _

/-- The empirical design `T⁻¹ ∑ₜ xₜ xₜᵀ` of a sequence of `T ≥ 1` actions is a design matrix. -/
lemma inv_smul_sum_outerSelf_mem_designSet {T : ℕ} (hT : 0 < T) {x : Fin T → EuclideanSpace ℝ ι}
    (hx : ∀ t, x t ∈ 𝒳) :
    (T : ℝ)⁻¹ • ∑ t, outerSelf (x t) ∈ designSet 𝒳 := by
  rw [Finset.smul_sum]
  refine convex_designSet.sum_mem (fun _ _ ↦ by positivity) ?_
    fun t _ ↦ outerSelf_mem_designSet (hx t)
  simp [Finset.sum_const, hT.ne']

/-- The uniform average of the design matrices of a nonempty finite subset of `𝒳` is a design
matrix. -/
lemma inv_card_smul_sum_outerSelf_mem_designSet {t : Finset (EuclideanSpace ℝ ι)}
    (hne : t.Nonempty) (ht : ↑t ⊆ 𝒳) :
    (t.card : ℝ)⁻¹ • ∑ v ∈ t, outerSelf v ∈ designSet 𝒳 := by
  rw [Finset.smul_sum]
  refine convex_designSet.sum_mem (fun _ _ ↦ by positivity) ?_
    fun v hv ↦ outerSelf_mem_designSet (ht hv)
  simp [Finset.sum_const, hne.card_pos.ne']

variable [Fintype ι]

omit [Fintype ι] in
/-- Every design matrix is positive semidefinite. -/
lemma posSemidef_of_mem_designSet [Finite ι] (hA : A ∈ designSet 𝒳) : A.PosSemidef :=
  convexHull_min (by rintro _ ⟨x, -, rfl⟩; exact outerSelf_posSemidef x)
    (Matrix.convex_posSemidef (𝕜 := ℝ)) hA

/-- If `𝒳` is contained in the ball of radius `R`, every design matrix has trace at most
`R ^ 2`. -/
lemma trace_le_of_mem_designSet (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hA : A ∈ designSet 𝒳) :
    A.trace ≤ R ^ 2 := by
  refine convexHull_min ?_ (convex_halfSpace_le (Matrix.traceLinearMap ι ℝ ℝ).isLinear _) hA
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_ofPred_eq, Matrix.traceLinearMap_apply, trace_outerSelf]
  exact pow_le_pow_left₀ (norm_nonneg _) (hR x hx) 2

omit [Fintype ι] in
/-- The set of design matrices of a compact action set is compact. -/
lemma isCompact_designSet [Finite ι] (h𝒳 : IsCompact 𝒳) : IsCompact (designSet 𝒳) := by
  have := Fintype.ofFinite ι
  exact (h𝒳.image continuous_outerSelf).convexHull

omit [Fintype ι] in
/-- If `𝒳` spans the space, there is a positive definite design matrix: the uniform average of
the `v vᵀ` over a basis `b ⊆ 𝒳`. -/
lemma exists_posDef_mem_designSet [Finite ι] [Nonempty ι] (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    ∃ A ∈ designSet 𝒳, A.PosDef := by
  have := Fintype.ofFinite ι
  obtain ⟨b, hb𝒳, hbspan, hbli⟩ := exists_linearIndependent ℝ 𝒳
  have hbfin : b.Finite := hbli.set_finite_of_isNoetherian
  have hbne : b.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [Submodule.span_empty, hspan] at hbspan
    exact bot_ne_top hbspan
  set t := hbfin.toFinset with ht
  have htne : t.Nonempty := by simpa [ht] using hbne
  have ht𝒳 : ↑t ⊆ 𝒳 := by simpa [ht] using hb𝒳
  refine ⟨_, inv_card_smul_sum_outerSelf_mem_designSet htne ht𝒳, ?_⟩
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨(posSemidef_of_mem_designSet (inv_card_smul_sum_outerSelf_mem_designSet htne ht𝒳)).1,
    fun y hy ↦ ?_⟩
  have h : star y ⬝ᵥ ((t.card : ℝ)⁻¹ • ∑ v ∈ t, outerSelf v) *ᵥ y =
      (t.card : ℝ)⁻¹ * ∑ v ∈ t, (WithLp.ofLp v ⬝ᵥ y) ^ 2 := by
    rw [star_trivial, Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
      smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [outerSelf, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      dotProduct_comm y, sq]
  rw [h]
  refine mul_pos (by positivity) (Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ?_)
  by_contra! hcontra
  have hzero : ∀ v ∈ b, ⟪v, WithLp.toLp 2 y⟫ = 0 := fun v hv ↦ by
    have := hcontra v (by simpa [ht] using hv)
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp, dotProduct_comm]
    exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm this (sq_nonneg _))
  have horth : Submodule.span ℝ {WithLp.toLp 2 y} ⟂ Submodule.span ℝ b :=
    Submodule.isOrtho_span.2 fun u hu v hv ↦ by
      rw [Set.mem_singleton_iff] at hu
      rw [hu, real_inner_comm]
      exact hzero v hv
  rw [hbspan, hspan, Submodule.isOrtho_top_right, Submodule.span_singleton_eq_bot,
    WithLp.toLp_eq_zero] at horth
  exact hy horth

variable [DecidableEq ι]

/-- The design set of the image of `𝒳` by the linear map of matrix `M` is the image of
`designSet 𝒳` by `A ↦ M A Mᵀ`. -/
lemma designSet_image_toEuclideanCLM (M : Matrix ι ι ℝ) :
    designSet (Matrix.toEuclideanCLM (𝕜 := ℝ) M '' 𝒳) =
      (fun A ↦ M * A * Mᵀ) '' designSet 𝒳 := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
    (LinearMap.mulRight ℝ Mᵀ).comp (LinearMap.mulLeft ℝ M)
  have hL : (fun A ↦ M * A * Mᵀ) = ⇑L := rfl
  rw [hL, designSet, designSet, L.image_convexHull, Set.image_image, Set.image_image]
  congr 2 with x
  rw [outerSelf_toEuclideanCLM]
  rfl

/-! ### Gram matrices of finitely many points: least squares -/

section LeastSquares

variable {T : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- If `A = ∑_t x_t x_tᵀ` is positive definite, the `x_t` span the space. -/
lemma span_range_eq_top_of_posDef [Finite ι] (x : Fin T → EuclideanSpace ℝ ι)
    (hA : (∑ s, outerSelf (x s)).PosDef) :
    Submodule.span ℝ (Set.range x) = ⊤ := by
  have := Fintype.ofFinite ι
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  have h0 : ∀ t, ⟪v, x t⟫ = 0 := fun t ↦ by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self t)) hv
  have hpos := hA.mahalanobisSq_pos hv0
  rw [mahalanobisSq_apply, sum_mulVec, dotProduct_sum] at hpos
  simp [dotProduct_outerSelf_mulVec, h0] at hpos

/-- For `A = ∑_t x_t x_tᵀ`, `∑_t ⟪z, A⁻¹ x_t⟫² = zᵀ A⁻¹ z` (both sides vanish if `A` is not
invertible, `A⁻¹` being `0`). -/
lemma sum_inner_toEuclideanCLM_inv_sum_outerSelf_sq (x : Fin T → EuclideanSpace ℝ ι)
    (z : EuclideanSpace ℝ ι) :
    ∑ t, ⟪z, toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫ ^ 2
      = mahalanobisSq (∑ s, outerSelf (x s))⁻¹ z := by
  set A := ∑ s, outerSelf (x s) with hA
  have hherm : (A⁻¹).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_nonsing_inv, hA,
      transpose_sum_outerSelf]
  set w := toEuclideanCLM (𝕜 := ℝ) A⁻¹ z with hw
  have h1 (t : Fin T) : ⟪z, toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x t)⟫ ^ 2
      = WithLp.ofLp w ⬝ᵥ outerSelf (x t) *ᵥ WithLp.ofLp w := by
    have hs : ⟪w, x t⟫ = ⟪z, toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x t)⟫ :=
      (isSymmetric_toEuclideanLin_iff.2 hherm) z (x t)
    rw [← hs, dotProduct_outerSelf_mulVec]
  simp_rw [h1]
  rw [← dotProduct_sum, ← sum_mulVec, ← hA, hw, ofLp_toEuclideanCLM, mulVec_mulVec]
  by_cases hdet : IsUnit A.det
  · rw [mul_nonsing_inv A hdet, one_mulVec, dotProduct_comm, mahalanobisSq_apply]
  · rw [nonsing_inv_apply_not_isUnit A hdet]
    simp [mahalanobisSq_apply]

/-- For an invertible `A = ∑_t x_t x_tᵀ`, `⟪z, θ⟫ = ∑_t ⟪z, A⁻¹ x_t⟫ ⟪x_t, θ⟫`: the
least-squares estimator is exact on noiseless observations. -/
lemma inner_eq_sum_inner_toEuclideanCLM_inv_mul (x : Fin T → EuclideanSpace ℝ ι)
    (hA : IsUnit (∑ s, outerSelf (x s)).det) (z θ : EuclideanSpace ℝ ι) :
    ⟪z, θ⟫ = ∑ t, ⟪z, toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫ * ⟪x t, θ⟫ := by
  have h : θ = toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹
      (toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s)) θ) := by
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec, nonsing_inv_mul _ hA,
      one_mulVec]
  conv_lhs => rw [h]
  rw [toEuclideanCLM_sum_outerSelf_apply, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_smul, real_inner_smul_right, mul_comm]

end LeastSquares

end Learning
