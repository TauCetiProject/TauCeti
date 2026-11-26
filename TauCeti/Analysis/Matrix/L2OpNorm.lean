/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
public import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
import TauCeti.Analysis.Matrix.Frobenius

/-!
# The `ℓ²` operator norm as a normed real algebra

Mathlib's scoped `ℓ²` operator norm (`Matrix.Norms.L2Operator`) makes `Matrix n n 𝕜` a normed
`𝕜`-algebra, for `𝕜 = ℝ` or `ℂ` (any `RCLike` field). Results about continuous functional
calculi and the exponential stated over `ℝ` additionally need a normed `ℝ`-algebra structure on
`Matrix n n 𝕜`. This file provides it, extending the existing `ℝ`-algebra structure on matrices
rather than restricting scalars, so that no algebra diamond arises.

## Main definitions

* `Matrix.l2OpNormedAlgebraReal`: `Matrix n n 𝕜` with the `ℓ²` operator norm, as a normed
  `ℝ`-algebra.

## Main results

* `Matrix.opNorm_toEuclideanLin`: the operator-norm unitarily invariant seminorm of
  `A.toEuclideanLin` equals the scoped `ℓ²` operator norm of `A`.
* `Matrix.norm_apply_le_l2_opNorm`: an entrywise bound, including rectangular matrices.
* `Matrix.l2_opNorm_one_le`: an identity bound that also applies to empty matrices.
* `Matrix.norm_trace_le_card_mul_l2_opNorm` and `Matrix.norm_normalized_trace_le_l2_opNorm`:
  trace and normalized trace bounds.
* `Matrix.l2_opNorm_mul_conjTranspose_self`: the operator norm of `A * Aᴴ` is `‖A‖ * ‖A‖`.
* `Matrix.l2_opNorm_diagonal_le` and `Matrix.l2_opNorm_pow_le`: bounds for diagonal matrices and
  for powers, also for empty index types.
* `Matrix.l2_opNorm_submatrix_le`: restricting rows and columns along injective maps does not
  increase the operator norm.
* `Matrix.l2_opNorm_fromBlocks_zero₁₁_zero₂₂_le`: a block matrix with zero diagonal blocks has
  operator norm at most the sum of the norms of its off-diagonal blocks.
* `Matrix.eventually_l2_opNorm_le_of_forall_pow`: along a filter, growth bounds on the norms of
  the powers of Hermitian matrices bound their norms.
* `Matrix.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq`: a Frobenius bound by the operator norm, and
  `Matrix.sum_norm_sq_le_l2_opNorm_sq`: a bound on the squared norm of each row.
* `Matrix.l2_opNorm_sub_diagonal_diag_le`: zeroing the diagonal of a square matrix at most doubles
  its `ℓ²` operator norm.
* `Matrix.l2_opNorm_map_ofReal`: a real, possibly rectangular, matrix has the same `ℓ²` operator
  norm as a complex matrix.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

/-- The operator-norm unitarily invariant seminorm of `A.toEuclideanLin` equals the scoped `ℓ²`
operator norm of `A`. -/
theorem opNorm_toEuclideanLin {m : Type*} [Fintype m] (A : Matrix m n 𝕜) :
    TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜
        (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin =
      ‖A‖ := by
  rw [TauCeti.UnitarilyInvariantSeminorm.opNorm_apply, Matrix.l2_opNorm_def,
    LinearEquiv.trans_apply]

/-- Every entry is bounded by the Euclidean operator norm. -/
theorem norm_apply_le_l2_opNorm {m : Type*} [Fintype m] (A : Matrix m n 𝕜)
    (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace 𝕜 n := PiLp.single 2 j 1
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  let v : EuclideanSpace 𝕜 m := (EuclideanSpace.equiv m 𝕜).symm (A *ᵥ e)
  have h := PiLp.norm_apply_le v i
  have hi : v.ofLp i = A i j := by
    simp [v, e, Matrix.mulVec_single]
  rw [hi] at h
  exact h.trans (by simpa [v, he] using A.l2_opNorm_mulVec e)

/-- A diagonal matrix whose entries have norm at most `r ≥ 0` has operator norm at most `r`. -/
theorem l2_opNorm_diagonal_le {v : n → 𝕜} {r : ℝ} (hr : 0 ≤ r) (hv : ∀ i, ‖v i‖ ≤ r) :
    ‖diagonal v‖ ≤ r := by
  rw [l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hr).2 hv

/-- The norm of the identity is at most one, also when the index type is empty. -/
theorem l2_opNorm_one_le : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one]
  exact l2_opNorm_diagonal_le zero_le_one fun _ => by simp

/-- The norm of a power is at most the power of the norm, also for the zeroth power and empty
index types. -/
theorem l2_opNorm_pow_le (M : Matrix n n 𝕜) (k : ℕ) : ‖M ^ k‖ ≤ ‖M‖ ^ k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simpa using l2_opNorm_one_le
  · exact norm_pow_le' M hk

/-- The trace is bounded by the dimension times the Euclidean operator norm. -/
theorem norm_trace_le_card_mul_l2_opNorm (M : Matrix n n 𝕜) :
    ‖M.trace‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  have h := ContinuousLinearMap.norm_traceCLM_le
    (Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) M)
  simpa only [TauCeti.traceCLM_apply, trace_toEuclideanCLM, finrank_euclideanSpace,
    l2_opNorm_toEuclideanCLM] using h

/-- The Euclidean operator norm of `A * Aᴴ` is `‖A‖ * ‖A‖`, for a possibly rectangular `A`.
Mathlib's `Matrix.l2_opNorm_conjTranspose_mul_self` is the form for `Aᴴ * A`. -/
theorem l2_opNorm_mul_conjTranspose_self {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n 𝕜) : ‖A * Aᴴ‖ = ‖A‖ * ‖A‖ := by
  simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] using
    l2_opNorm_conjTranspose_mul_self Aᴴ

/-- Selecting the rows of the identity along an injective map gives a matrix of `ℓ²` operator norm
at most one: its rows are orthonormal. -/
private theorem l2_opNorm_one_submatrix_id_le {m : Type*} [Fintype m]
    {e : m → n} (he : Function.Injective e) : ‖(1 : Matrix n n 𝕜).submatrix e id‖ ≤ 1 := by
  classical
  have h1 : (1 : Matrix n n 𝕜).submatrix e id * ((1 : Matrix n n 𝕜).submatrix e id)ᴴ = 1 := by
    rw [conjTranspose_submatrix, conjTranspose_one,
      ← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one, submatrix_one _ he]
  have h := l2_opNorm_mul_conjTranspose_self ((1 : Matrix n n 𝕜).submatrix e id)
  rw [h1] at h
  nlinarith [l2_opNorm_one_le (n := m) (𝕜 := 𝕜), norm_nonneg ((1 : Matrix n n 𝕜).submatrix e id)]

/-- Restricting the rows and columns of a matrix along injective maps does not increase its `ℓ²`
operator norm. In particular every block of a block matrix has norm at most that of the whole
matrix. -/
theorem l2_opNorm_submatrix_le {l m o : Type*} [Fintype l] [Fintype m] [Fintype o]
    [DecidableEq o] (A : Matrix m n 𝕜) {e : l → m} {f : o → n} (he : Function.Injective e)
    (hf : Function.Injective f) : ‖A.submatrix e f‖ ≤ ‖A‖ := by
  classical
  -- The restriction is `A` between a row selection and the adjoint of a column selection.
  have hA : A.submatrix e f =
      (1 : Matrix m m 𝕜).submatrix e id * A * ((1 : Matrix n n 𝕜).submatrix f id)ᴴ := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  rw [hA]
  calc _ ≤ ‖(1 : Matrix m m 𝕜).submatrix e id‖ * ‖A‖ *
        ‖((1 : Matrix n n 𝕜).submatrix f id)ᴴ‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by
      rw [l2_opNorm_conjTranspose]
      gcongr
      exacts [l2_opNorm_one_submatrix_id_le he, l2_opNorm_one_submatrix_id_le hf]
    _ = ‖A‖ := by ring

/-- A square block matrix with zero diagonal blocks has operator norm at most the sum of the
norms of its off-diagonal blocks: it is the sum of the two blocks, each placed by partial
isometries. -/
theorem l2_opNorm_fromBlocks_zero₁₁_zero₂₂_le {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m n 𝕜) (C : Matrix n m 𝕜) : ‖fromBlocks 0 B C 0‖ ≤ ‖B‖ + ‖C‖ := by
  set E₁ : Matrix m (m ⊕ n) 𝕜 := (1 : Matrix (m ⊕ n) (m ⊕ n) 𝕜).submatrix Sum.inl id
  set E₂ : Matrix n (m ⊕ n) 𝕜 := (1 : Matrix (m ⊕ n) (m ⊕ n) 𝕜).submatrix Sum.inr id
  have hE₁ : ‖E₁‖ ≤ 1 :=
    (l2_opNorm_submatrix_le _ Sum.inl_injective Function.injective_id).trans l2_opNorm_one_le
  have hE₂ : ‖E₂‖ ≤ 1 :=
    (l2_opNorm_submatrix_le _ Sum.inr_injective Function.injective_id).trans l2_opNorm_one_le
  have hsplit : fromBlocks 0 B C 0 = E₁ᴴ * B * E₂ + E₂ᴴ * C * E₁ := by
    ext (x | x) (y | y) <;> simp [E₁, E₂, Matrix.mul_apply, Matrix.one_apply]
  rw [hsplit]
  calc _ ≤ ‖E₁ᴴ * B * E₂‖ + ‖E₂ᴴ * C * E₁‖ := norm_add_le _ _
    _ ≤ ‖E₁ᴴ‖ * ‖B‖ * ‖E₂‖ + ‖E₂ᴴ‖ * ‖C‖ * ‖E₁‖ := by
      gcongr <;> exact (l2_opNorm_mul _ _).trans (by gcongr; exact l2_opNorm_mul _ _)
    _ ≤ 1 * ‖B‖ * 1 + 1 * ‖C‖ * 1 := by
      rw [l2_opNorm_conjTranspose, l2_opNorm_conjTranspose]
      gcongr
    _ = ‖B‖ + ‖C‖ := by ring

/-- **Norms from powers.** If Hermitian matrices satisfy `‖M ^ k‖ ≤ C * (k + 1) ^ d * s ^ k + δ`
eventually along a filter, for every `k` and `δ > 0`, then `‖M‖ ≤ t` eventually for every `t > s`,
since `‖M ^ (2 ^ m)‖ = ‖M‖ ^ (2 ^ m)` and polynomial factors are negligible against
`(t / s) ^ k`. -/
theorem eventually_l2_opNorm_le_of_forall_pow {ι : Type*} {F : Filter ι} {m : ι → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {M : (i : ι) → Matrix (m i) (m i) 𝕜}
    (hM : ∀ i, (M i).IsHermitian) {C s t : ℝ} {d : ℕ} (hs : 0 < s) (hst : s < t)
    (h : ∀ k : ℕ, ∀ δ > 0, ∀ᶠ i in F, ‖M i ^ k‖ ≤ C * ((k : ℝ) + 1) ^ d * s ^ k + δ) :
    ∀ᶠ i in F, ‖M i‖ ≤ t := by
  -- Enlarging `C` to `max C 0` keeps the hypothesis.
  obtain ⟨C, hC, h⟩ : ∃ C' ≥ 0, ∀ k : ℕ, ∀ δ > 0,
      ∀ᶠ i in F, ‖M i ^ k‖ ≤ C' * ((k : ℝ) + 1) ^ d * s ^ k + δ :=
    ⟨max C 0, le_max_right _ _, fun k δ hδ ↦ (h k δ hδ).mono fun i hi ↦
      hi.trans (by gcongr; exact le_max_left _ _)⟩
  have hq : 1 < t / s := (one_lt_div hs).2 hst
  -- Polynomial factors are negligible against `(t / s) ^ k`.
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt d hq).const_mul (C * 2 ^ d + 1)
  rw [mul_zero] at hlim
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds one_pos))
  set k := 2 ^ (N + 1)
  have hk₁ : 1 ≤ k := Nat.one_le_two_pow
  have hkN : N ≤ k := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right two_pos (by omega))
  have hkey : (C * ((k : ℝ) + 1) ^ d + 1) * s ^ k ≤ t ^ k := by
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk₁
    have hpoly : C * ((k : ℝ) + 1) ^ d + 1 ≤ (C * 2 ^ d + 1) * (k : ℝ) ^ d := by
      have h2k : ((k : ℝ) + 1) ^ d ≤ 2 ^ d * (k : ℝ) ^ d := by
        rw [← mul_pow]; gcongr; linarith
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ d := one_le_pow₀ hk
      nlinarith
    have hratio := hN k hkN
    rw [mul_div_assoc', div_lt_one (by positivity), div_pow] at hratio
    rw [lt_div_iff₀ (by positivity)] at hratio
    nlinarith [pow_pos hs k]
  filter_upwards [h k (s ^ k) (by positivity)] with i hi
  have hpow : ‖M i‖ ^ k = ‖M i ^ k‖ := ((hM i).isSelfAdjoint.norm_pow_two_pow (N + 1)).symm
  refine le_of_pow_le_pow_left₀ (n := k) (pow_ne_zero (N + 1) two_ne_zero) (hs.trans hst).le ?_
  rw [hpow]
  linarith

/-- The squared Frobenius norm of a rectangular matrix is at most its number of rows times
its squared Euclidean operator norm. Empty row and column types are allowed. -/
theorem sum_sum_norm_sq_le_card_mul_l2_opNorm_sq {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by
  classical
  calc
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = RCLike.re (A * Aᴴ).trace :=
      (re_trace_mul_conjTranspose_self A).symm
    _ ≤ ‖(A * Aᴴ).trace‖ := RCLike.re_le_norm _
    _ ≤ (Fintype.card m : ℝ) * ‖A * Aᴴ‖ := norm_trace_le_card_mul_l2_opNorm _
    _ = (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by rw [l2_opNorm_mul_conjTranspose_self, sq]

/-- The sum of squared entry norms over any set of positions is at most the row count times
the squared Euclidean operator norm. -/
theorem sum_norm_sq_le_card_mul_l2_opNorm_sq {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) (s : Finset (m × n)) :
    ∑ p ∈ s, ‖A p.1 p.2‖ ^ 2 ≤ (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ p ∈ (Finset.univ : Finset m) ×ˢ (Finset.univ : Finset n), ‖A p.1 p.2‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ ↦ by simp) (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_product _ _ _
    _ ≤ _ := A.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq

/-- The squared norm of a row is at most the squared Euclidean operator norm. -/
theorem sum_norm_sq_le_l2_opNorm_sq {m : Type*} [Fintype m] (A : Matrix m n 𝕜) (i : m) :
    ∑ j, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h := (A.submatrix (fun _ : Unit ↦ i) id).sum_sum_norm_sq_le_card_mul_l2_opNorm_sq
  have hA := l2_opNorm_submatrix_le A (e := fun _ : Unit ↦ i) (fun _ _ _ ↦ Subsingleton.elim _ _)
    Function.injective_id
  simp only [submatrix_apply, id_eq, Fintype.univ_unit, Finset.sum_singleton, Fintype.card_unit,
    Nat.cast_one, one_mul] at h
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _) hA 2)

/-- The absolute normalized trace is at most the Euclidean operator norm, including in dimension
zero. -/
theorem norm_normalized_trace_le_l2_opNorm (M : Matrix n n 𝕜) :
    ‖((Fintype.card n : ℕ) : 𝕜)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  by_cases hn : Nonempty n
  · let : Nonempty n := hn
    have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    rw [norm_mul, norm_inv, RCLike.norm_natCast]
    exact (inv_mul_le_iff₀ hcard).2 (norm_trace_le_card_mul_l2_opNorm M)
  · have : IsEmpty n := not_nonempty_iff.mp hn
    simp

open scoped Matrix.Norms.L2Operator in
/-- `Matrix n n 𝕜` with the `ℓ²` operator norm, as a normed `ℝ`-algebra. It extends the existing
`ℝ`-algebra structure rather than restricting scalars, so that no algebra diamond arises. -/
protected noncomputable abbrev l2OpNormedAlgebraReal : NormedAlgebra ℝ (Matrix n n 𝕜) where
  __ := (inferInstance : Algebra ℝ (Matrix n n 𝕜))
  norm_smul_le r A := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r A]
    exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs])

/-- Removing the diagonal of a square matrix increases its `ℓ²` operator norm by at most a factor
of `2`. -/
theorem l2_opNorm_sub_diagonal_diag_le (A : Matrix n n 𝕜) :
    ‖A - diagonal A.diag‖ ≤ 2 * ‖A‖ := by
  have hdiag : ‖(diagonal A.diag : Matrix n n 𝕜)‖ ≤ ‖A‖ := by
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr fun i ↦ A.norm_apply_le_l2_opNorm i i
  linarith [norm_sub_le A (diagonal A.diag)]

section OfReal

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **A real matrix has the same `ℓ²` operator norm over `ℂ`**: its norm as an operator
`ℂⁿ → ℂᵐ` is its norm as an operator `ℝⁿ → ℝᵐ`. -/
@[simp]
theorem l2_opNorm_map_ofReal (S : Matrix m n ℝ) : ‖S.map ((↑) : ℝ → ℂ)‖ = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · rw [l2_opNorm_def (S.map _)]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
    rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', toLpLin_apply]
    -- Split `v = a + i b` with real `a` and `b`: `‖S v‖² = ‖S a‖² + ‖S b‖²`.
    let a : EuclideanSpace ℝ n := WithLp.toLp 2 fun i ↦ (v i).re
    let b : EuclideanSpace ℝ n := WithLp.toLp 2 fun i ↦ (v i).im
    have ha : ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp a) : EuclideanSpace ℝ m)‖ ≤ ‖S‖ * ‖a‖ :=
      l2_opNorm_mulVec S a
    have hb : ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp b) : EuclideanSpace ℝ m)‖ ≤ ‖S‖ * ‖b‖ :=
      l2_opNorm_mulVec S b
    have hv : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, a, b, ← Finset.sum_add_distrib, Real.norm_eq_abs,
        sq_abs, Complex.sq_norm, Complex.normSq_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hSv : ‖(WithLp.toLp 2 (S.map ((↑) : ℝ → ℂ) *ᵥ WithLp.ofLp v) : EuclideanSpace ℂ m)‖ ^ 2 =
        ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp a) : EuclideanSpace ℝ m)‖ ^ 2 +
          ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp b) : EuclideanSpace ℝ m)‖ ^ 2 := by
      have hcoord (i : m) :
          (S.map ((↑) : ℝ → ℂ) *ᵥ WithLp.ofLp v) i = ∑ j, (S i j : ℂ) * v j := by
        simp [mulVec, dotProduct]
      simp only [EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib, Real.norm_eq_abs,
        sq_abs, Complex.sq_norm, Complex.normSq_apply, hcoord]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hre : (∑ j, ((S i j : ℂ) * v j)).re = (S *ᵥ WithLp.ofLp a) i := by
        simp [mulVec, dotProduct, Complex.re_sum, a]
      have him : (∑ j, ((S i j : ℂ) * v j)).im = (S *ᵥ WithLp.ofLp b) i := by
        simp [mulVec, dotProduct, Complex.im_sum, b]
      rw [hre, him]
      ring
    have h0 := norm_nonneg S
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hSv, mul_pow, hv]
    nlinarith [norm_nonneg (WithLp.toLp 2 (S *ᵥ WithLp.ofLp a) : EuclideanSpace ℝ m),
      norm_nonneg (WithLp.toLp 2 (S *ᵥ WithLp.ofLp b) : EuclideanSpace ℝ m),
      mul_nonneg h0 (norm_nonneg a), mul_nonneg h0 (norm_nonneg b)]
  · rw [l2_opNorm_def S]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', toLpLin_apply]
    -- A real vector has the same norm as a complex vector.
    let xc : EuclideanSpace ℂ n := WithLp.toLp 2 fun i ↦ (x i : ℂ)
    have hx : ‖xc‖ = ‖x‖ := by
      simp [EuclideanSpace.norm_eq, xc, Complex.norm_real]
    have hSx : ‖(WithLp.toLp 2 (S.map ((↑) : ℝ → ℂ) *ᵥ WithLp.ofLp xc) : EuclideanSpace ℂ m)‖ =
        ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ m)‖ := by
      simp [EuclideanSpace.norm_eq, xc, mulVec, dotProduct, ← Complex.ofReal_mul,
        ← Complex.ofReal_sum]
    rw [← hSx, ← hx]
    exact l2_opNorm_mulVec _ xc
end OfReal

end Matrix
