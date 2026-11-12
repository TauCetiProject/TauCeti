/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Hadamard's inequality for Gram determinants

Hadamard's inequality bounds the volume spanned by a finite family of vectors by the product of
their lengths. This file proves it in the following forms over an `RCLike` field `𝕜`.

* In coordinates: for an orthonormal basis `b` of `E` indexed by a finite type `ι` and any family
  `v : ι → E`, `‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖`. The Gram–Schmidt orthonormal basis `e` of `v`
  makes the coordinate matrix of `v` triangular, so `e.toBasis.det v = ∏ i, ⟪e i, v i⟫`, and
  `b.toBasis.det e` has norm one.
* For Gram matrices: for any finite family `v` in an inner product space, which need not be
  finite-dimensional, `det (gram 𝕜 v) ≤ ∏ i, ‖v i‖ ^ 2` for the order of `ComplexOrder`. Since
  that order compares only elements with equal imaginary parts, the bound also says that the
  Gram determinant is real. Its nonnegativity is Mathlib's `Matrix.PosSemidef.det_nonneg` applied
  to `Matrix.posSemidef_gram`. A dependent family has Gram determinant zero, and an independent
  family is a basis of its span, where the Gram determinant is the squared norm of a coordinate
  determinant.
* For square matrices: the rows of `A : Matrix ι ι 𝕜`, read in `EuclideanSpace 𝕜 ι`, have Gram
  determinant `‖det A‖ ^ 2`, and `‖det A‖ ≤ ∏ i, ‖A i‖`, the classical Hadamard inequality.
* In logarithmic form: the real part of the Gram determinant is positive exactly for an
  independent family, and then its logarithm is at most `∑ i, 2 log ‖v i‖`.

These bounds control the covolume of a lattice by the lengths of its generators, as in the
Gram/covolume calculation of J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192
(2020), §3.

## Main results

* `OrthonormalBasis.norm_det_le_prod_norm`: Hadamard's inequality for the coordinate determinant
  in an orthonormal basis.
* `OrthonormalBasis.det_gram_eq_norm_det_sq`: the Gram determinant of a family is the squared
  norm of its coordinate determinant in an orthonormal basis.
* `Matrix.ofReal_re_det_gram`, `Matrix.re_det_gram_nonneg`: the Gram determinant is real, with
  nonnegative real part. These specialise `Matrix.IsHermitian.ofReal_re_det` and
  `Matrix.PosSemidef.re_det_nonneg`.
* `Matrix.det_gram_le_prod_norm_sq`, `Matrix.re_det_gram_le_prod_norm_sq`: Hadamard's inequality
  for Gram determinants, in `ComplexOrder` and for the real part.
* `Matrix.re_det_gram_le_pow`: the uniform form, `re (det (gram 𝕜 v)) ≤ D ^ card ι` when every
  `‖v i‖ ^ 2 ≤ D`.
* `Matrix.re_det_gram_pos_iff`, `Matrix.det_gram_pos_iff`: the Gram determinant is positive
  exactly for a linearly independent family.
* `Matrix.log_re_det_gram_le`, `Matrix.log_det_gram_le`: Hadamard's inequality on the logarithmic
  scale, `log (det (gram 𝕜 v)) ≤ ∑ i, 2 log ‖v i‖` for an independent family.
* `Matrix.det_gram_toLp_eq_norm_det_sq`, `Matrix.det_gram_toLp_eq_det_sq`: the Gram determinant of
  the rows of a square matrix is the squared norm of its determinant.
* `Matrix.norm_det_le_prod_norm_toLp`, `Matrix.abs_det_le_prod_norm_toLp`: Hadamard's inequality
  for a square matrix, bounding its determinant by the product of the Euclidean norms of its rows.

## References

* M. Waldschmidt, *Diophantine approximation on linear algebraic groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, proof of Lemma 3.25, p. 101.
-/

public section

open Module Submodule
open scoped InnerProductSpace ComplexOrder

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι]

namespace OrthonormalBasis

/-- Hadamard's inequality in `Fin n`-indexed coordinates, the case where the Gram–Schmidt
orthonormal basis is available directly. -/
private theorem norm_det_le_prod_norm_fin {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (v : Fin n → E) : ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have h : finrank 𝕜 E = Fintype.card (Fin n) := finrank_eq_card_basis b.toBasis
  set e := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  have hdet : b.toBasis.det v = b.toBasis.det e * e.toBasis.det v := by
    simpa using congrFun (congrArg DFunLike.coe (b.toBasis.det.eq_smul_basis_det e.toBasis)) v
  rw [hdet, norm_mul, b.det_to_matrix_orthonormalBasis e, one_mul,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  gcongr with i
  simpa [e.norm_eq_one i] using norm_inner_le_norm (𝕜 := 𝕜) (e i) (v i)

/-- **Hadamard's inequality.** The determinant of a family `v` in the coordinates of an
orthonormal basis has norm at most the product of the norms of the vectors. The family may be
linearly dependent. -/
theorem norm_det_le_prod_norm (b : OrthonormalBasis ι 𝕜 E) (v : ι → E) :
    ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  set σ := Fintype.equivFin ι
  have := norm_det_le_prod_norm_fin (b.reindex σ) (v ∘ σ.symm)
  rw [reindex_toBasis, Module.Basis.det_reindex] at this
  simpa [Function.comp_assoc, Equiv.prod_comp σ.symm fun i ↦ ‖v i‖] using this

/-- The Gram determinant of a family `v` is the squared norm of its determinant in the
coordinates of an orthonormal basis. -/
theorem det_gram_eq_norm_det_sq (b : OrthonormalBasis ι 𝕜 E) (v : ι → E) :
    (Matrix.gram 𝕜 v).det = (‖b.toBasis.det v‖ : 𝕜) ^ 2 := by
  rw [Matrix.gram_eq_conjTranspose_mul b, Matrix.det_mul, Matrix.det_conjTranspose,
    RCLike.star_def, RCLike.conj_mul, Module.Basis.det_apply]
  have hM : b.toBasis.toMatrix v = Matrix.of fun i j ↦ b.repr (v j) i := by
    ext; simp [Module.Basis.toMatrix_apply]
  rw [hM]

end OrthonormalBasis

namespace Matrix

/-- The Gram determinant of a finite family is real: it is the image of its real part. This is
`Matrix.IsHermitian.ofReal_re_det` for Gram matrices, stated without hypotheses so that `simp`
can use it. -/
@[simp]
theorem ofReal_re_det_gram (v : ι → E) :
    ((RCLike.re (gram 𝕜 v).det : ℝ) : 𝕜) = (gram 𝕜 v).det :=
  (posSemidef_gram 𝕜 v).isHermitian.ofReal_re_det

/-- The real part of the Gram determinant of a finite family is nonnegative. This is
`Matrix.PosSemidef.re_det_nonneg` for Gram matrices. -/
theorem re_det_gram_nonneg (v : ι → E) : 0 ≤ RCLike.re (gram 𝕜 v).det :=
  (posSemidef_gram 𝕜 v).re_det_nonneg

/-- **Hadamard's inequality for Gram determinants.** In any inner product space, the Gram
determinant of a finite family is at most the product of the squared norms of its vectors. The
order is that of `ComplexOrder`, so this also says that the Gram determinant is real; together
with `Matrix.PosSemidef.det_nonneg` it lies between `0` and `∏ i, ‖v i‖ ^ 2`. -/
theorem det_gram_le_prod_norm_sq (v : ι → E) :
    (gram 𝕜 v).det ≤ ∏ i, (‖v i‖ : 𝕜) ^ 2 := by
  have hprod : ∏ i, (‖v i‖ : 𝕜) ^ 2 = ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by simp
  rw [hprod]
  by_cases hv : LinearIndependent 𝕜 v
  · -- An independent family is a basis of its span, which has an orthonormal basis indexed by `ι`.
    set W := span 𝕜 (Set.range v)
    have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
    let w : ι → W := fun i ↦ ⟨v i, subset_span (Set.mem_range_self i)⟩
    have hgram : gram 𝕜 w = gram 𝕜 v := by
      ext i j
      simp [w]
    let b : OrthonormalBasis ι 𝕜 W := (stdOrthonormalBasis 𝕜 W).reindex
      ((finCongr (finrank_span_eq_card hv)).trans (Fintype.equivFin ι).symm)
    rw [← hgram, b.det_gram_eq_norm_det_sq w, ← RCLike.ofReal_pow, RCLike.ofReal_le_ofReal,
      Finset.prod_pow]
    gcongr
    simpa [w] using b.norm_det_le_prod_norm w
  · rw [← det_gram_ne_zero_iff_linearIndependent (𝕜 := 𝕜), not_not] at hv
    rw [hv, RCLike.ofReal_nonneg]
    positivity

/-- **Hadamard's inequality for Gram determinants**, for the real part: the real part of the Gram
determinant of a finite family is at most the product of the squared norms of its vectors. -/
theorem re_det_gram_le_prod_norm_sq (v : ι → E) :
    RCLike.re (gram 𝕜 v).det ≤ ∏ i, ‖v i‖ ^ 2 := by
  have h := RCLike.re_le_re (det_gram_le_prod_norm_sq (𝕜 := 𝕜) v)
  simpa only [← RCLike.ofReal_pow, ← RCLike.ofReal_prod, RCLike.ofReal_re] using h

/-- **Hadamard's inequality, uniform form.** If every vector of a finite family has squared norm
at most `D`, the real part of its Gram determinant is at most `D ^ card ι`. -/
theorem re_det_gram_le_pow {v : ι → E} {D : ℝ} (hD : ∀ i, ‖v i‖ ^ 2 ≤ D) :
    RCLike.re (gram 𝕜 v).det ≤ D ^ Fintype.card ι := by
  calc RCLike.re (gram 𝕜 v).det ≤ ∏ i, ‖v i‖ ^ 2 := re_det_gram_le_prod_norm_sq v
    _ ≤ ∏ _i : ι, D := by gcongr with i; exact hD i
    _ = D ^ Fintype.card ι := by simp

/-- The real part of the Gram determinant of a finite family is positive if and only if the family
is linearly independent. -/
theorem re_det_gram_pos_iff {v : ι → E} :
    0 < RCLike.re (gram 𝕜 v).det ↔ LinearIndependent 𝕜 v := by
  rw [← det_gram_ne_zero_iff_linearIndependent, (re_det_gram_nonneg v).lt_iff_ne', ne_eq, ne_eq,
    ← RCLike.ofReal_eq_zero (K := 𝕜), ofReal_re_det_gram]

/-- The Gram determinant of a finite family in a real inner product space is positive if and only
if the family is linearly independent. -/
theorem det_gram_pos_iff {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {v : ι → F} :
    0 < (gram ℝ v).det ↔ LinearIndependent ℝ v := by
  simpa using re_det_gram_pos_iff (𝕜 := ℝ) (v := v)

/-- **Hadamard's inequality for Gram determinants, logarithmic form.** For a linearly independent
finite family, the logarithm of the real part of its Gram determinant, which is positive, is at
most `∑ i, 2 log ‖v i‖`. -/
theorem log_re_det_gram_le {v : ι → E} (hv : LinearIndependent 𝕜 v) :
    Real.log (RCLike.re (gram 𝕜 v).det) ≤ ∑ i, 2 * Real.log ‖v i‖ := by
  have h2 : ∀ i, 2 * Real.log ‖v i‖ = Real.log (‖v i‖ ^ 2) := fun i ↦ by simp [Real.log_pow]
  simp_rw [h2]
  rw [← Real.log_prod fun i _ ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv.ne_zero i))]
  exact Real.log_le_log (re_det_gram_pos_iff.mpr hv) (re_det_gram_le_prod_norm_sq v)

/-- **Hadamard's inequality for Gram determinants, real logarithmic form.** For a linearly
independent finite family in a real inner product space, the logarithm of its Gram determinant,
which is positive, is at most `∑ i, 2 log ‖v i‖`. -/
theorem log_det_gram_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {v : ι → F}
    (hv : LinearIndependent ℝ v) : Real.log (gram ℝ v).det ≤ ∑ i, 2 * Real.log ‖v i‖ := by
  simpa using log_re_det_gram_le hv

/-- The determinant, in the standard orthonormal basis of `EuclideanSpace 𝕜 ι`, of the rows of a
square matrix `A` is `A.det`. -/
theorem basisFun_toBasis_det_toLp (A : Matrix ι ι 𝕜) :
    (EuclideanSpace.basisFun ι 𝕜).toBasis.det (fun i ↦ WithLp.toLp 2 (A i)) = A.det := by
  rw [Module.Basis.det_apply, ← Matrix.det_transpose]
  -- The transposed coordinate matrix has entries `(basisFun ι 𝕜).repr (toLp 2 (A i)) j = A i j`.
  refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
  simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- The Gram determinant of the rows of a square matrix `A`, read in `EuclideanSpace 𝕜 ι`, is
`‖A.det‖ ^ 2`. -/
theorem det_gram_toLp_eq_norm_det_sq (A : Matrix ι ι 𝕜) :
    (gram 𝕜 fun i ↦ WithLp.toLp 2 (A i)).det = (‖A.det‖ : 𝕜) ^ 2 := by
  rw [(EuclideanSpace.basisFun ι 𝕜).det_gram_eq_norm_det_sq,
    basisFun_toBasis_det_toLp]

/-- The Gram determinant of the rows of a real square matrix `A`, read in `EuclideanSpace ℝ ι`,
is `A.det ^ 2`. -/
theorem det_gram_toLp_eq_det_sq (A : Matrix ι ι ℝ) :
    (gram ℝ fun i ↦ WithLp.toLp 2 (A i)).det = A.det ^ 2 := by
  simp [det_gram_toLp_eq_norm_det_sq]

/-- **Hadamard's inequality for a square matrix.** The determinant of `A` has norm at most the
product of the Euclidean norms of its rows. -/
theorem norm_det_le_prod_norm_toLp (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ i, ‖WithLp.toLp 2 (A i)‖ := by
  simpa only [basisFun_toBasis_det_toLp] using
    (EuclideanSpace.basisFun ι 𝕜).norm_det_le_prod_norm fun i ↦ WithLp.toLp 2 (A i)

/-- **Hadamard's inequality for a real square matrix.** The absolute value of the determinant of
`A` is at most the product of the Euclidean norms of its rows. -/
theorem abs_det_le_prod_norm_toLp (A : Matrix ι ι ℝ) :
    |A.det| ≤ ∏ i, ‖WithLp.toLp 2 (A i)‖ :=
  norm_det_le_prod_norm_toLp A

end Matrix
