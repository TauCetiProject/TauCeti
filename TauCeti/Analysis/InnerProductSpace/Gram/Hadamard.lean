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
their lengths. This file proves it in two forms over an `RCLike` field `𝕜`.

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

end Matrix
