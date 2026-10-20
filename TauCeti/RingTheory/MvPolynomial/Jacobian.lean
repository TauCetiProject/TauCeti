/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Jacobian matrices of polynomial families at a point

For a family of polynomials `p : ι → MvPolynomial σ R` and a point `v : σ → R`, the matrix
`TauCeti.jacobiMatrixAt p v` has `(i, j)` entry `∂(p i)/∂X_j` evaluated at `v`; as a linear map
it is `(jacobiMatrixAt p v).mulVecLin : (σ → R) →ₗ[R] ι → R`. When every `p i` is homogeneous
and `v ≠ 0`, this is the cone Jacobian `J_p(v)` of the projective zero locus of `p`, whose rank
at the points of that locus governs its smoothness. Full rank means that
`(jacobiMatrixAt p v).mulVec` is surjective; over a field this says that the rank is the number
of equations, by Mathlib's `Matrix.mulVec_surjective_iff_rank_eq_card`.

This file proves the basic properties of this rank on the cone over the zero locus. Euler's
identity puts the radial direction `v` in the kernel at a zero, so the rank is less than the
number of variables, and full rank forces fewer equations than variables. Rescaling the point
multiplies each row by a power of the scalar, so the rank depends only on the projective point.
In the standard affine chart where coordinate `i` is one, the Jacobian of the dehomogenized
equations is the cone Jacobian with column `i` deleted. At a zero, Euler's identity writes that
column in terms of the others, so the chart Jacobian at the coordinate ratios has the same image
and rank as the cone Jacobian at the homogeneous coordinates. In particular full rank can be
tested in any standard chart containing the point, and the answer is independent of the chart.

## Main results

* `TauCeti.jacobiMatrixAt_mulVec_self`: Euler's identity `J_p(v) v = (d_i p_i(v))_i`.
* `TauCeti.jacobiMatrixAt_smul`: `J_p(t • v) = diag(t ^ (d_i - 1)) J_p(v)`.
* `TauCeti.rank_jacobiMatrixAt_eq_of_mk_eq_mk`: the rank depends only on the projective point.
* `TauCeti.jacobiMatrixAt_dehomogenize`: the chart Jacobian is a submatrix of the cone Jacobian.
* `TauCeti.range_mulVecLin_jacobiMatrixAt_dehomogenize`,
  `TauCeti.rank_jacobiMatrixAt_dehomogenize_div`: at a zero, the chart Jacobian and the cone
  Jacobian have the same image and the same rank.
* `TauCeti.rank_jacobiMatrixAt_lt_card`,
  `TauCeti.card_lt_card_of_mulVec_surjective_jacobiMatrixAt`: at a nonzero zero, the rank is less
  than the number of variables, so full rank needs fewer equations than variables.

## References

* W. Fulton, *Algebraic Curves*, Chapter 5, Section 1, for the single-equation chart criterion
  that the chart comparison here extends to families.
* J. Harris, *Algebraic Geometry: A First Course*, Lecture 14, for the projective Jacobian
  criterion.
-/

public section

namespace TauCeti

open MvPolynomial Matrix

variable {R σ ι : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The Jacobian matrix of a family of polynomials `p` at a point `v`: its `(i, j)` entry is the
partial derivative of `p i` in the variable `X_j`, evaluated at `v`. For homogeneous `p` and
`v ≠ 0` this is the cone Jacobian of the projective zero locus of `p`. -/
noncomputable def jacobiMatrixAt (p : ι → MvPolynomial σ R) (v : σ → R) : Matrix ι σ R :=
  Matrix.of fun i j ↦ eval v (pderiv j (p i))

@[simp]
theorem jacobiMatrixAt_apply (p : ι → MvPolynomial σ R) (v : σ → R) (i : ι) (j : σ) :
    jacobiMatrixAt p v i j = eval v (pderiv j (p i)) := (rfl)

/-- **Euler's identity** for the Jacobian matrix of a family of homogeneous polynomials: applied
to the point itself, it returns each equation's value scaled by its degree. -/
theorem jacobiMatrixAt_mulVec_self [Fintype σ] {p : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (v : σ → R) :
    jacobiMatrixAt p v *ᵥ v = fun i ↦ d i • eval v (p i) := by
  ext i
  have h := congrArg (eval v) (hp i).sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul] at h
  simpa only [mulVec, dotProduct, jacobiMatrixAt_apply, mul_comm] using h

/-- At a common zero of a family of homogeneous polynomials, the radial direction lies in the
kernel of the Jacobian matrix. -/
theorem jacobiMatrixAt_mulVec_self_eq_zero [Fintype σ] {p : ι → MvPolynomial σ R}
    {d : ι → ℕ} (hp : ∀ i, (p i).IsHomogeneous (d i)) {v : σ → R}
    (hv : ∀ i, eval v (p i) = 0) :
    jacobiMatrixAt p v *ᵥ v = 0 := by
  rw [jacobiMatrixAt_mulVec_self hp]
  ext i
  simp [hv]

/-- Rescaling the point multiplies the row of a homogeneous equation of degree `d` by the
`(d - 1)`-st power of the scalar. -/
theorem jacobiMatrixAt_smul_apply {p : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (t : R) (v : σ → R) (i : ι) (j : σ) :
    jacobiMatrixAt p (t • v) i j = t ^ (d i - 1) * jacobiMatrixAt p v i j := by
  simp only [jacobiMatrixAt_apply, ((hp i).pderiv).eval_smul, smul_eq_mul]

/-- Rescaling the point multiplies the Jacobian matrix of a family of homogeneous equations on
the left by the diagonal matrix of the powers `t ^ (d i - 1)`. -/
theorem jacobiMatrixAt_smul [Fintype ι] [DecidableEq ι] {p : ι → MvPolynomial σ R}
    {d : ι → ℕ} (hp : ∀ i, (p i).IsHomogeneous (d i)) (t : R) (v : σ → R) :
    jacobiMatrixAt p (t • v) = diagonal (fun i ↦ t ^ (d i - 1)) * jacobiMatrixAt p v := by
  ext i j
  rw [diagonal_mul, jacobiMatrixAt_smul_apply hp]

/-- In the standard affine chart where coordinate `i` is one, the Jacobian matrix of the
dehomogenized equations is the Jacobian matrix of the homogeneous equations with column `i`
deleted. -/
theorem jacobiMatrixAt_dehomogenize {n : ℕ} (i : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (n + 1)) R) (a : Fin n → R) :
    jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) a =
      (jacobiMatrixAt p (i.insertNth 1 a)).submatrix id i.succAbove := by
  ext k j
  simp

end CommSemiring

section CommRing

variable [CommRing R]

/-- Rescaling the point by a unit does not change the rank of the Jacobian matrix of a family of
homogeneous equations. -/
theorem rank_jacobiMatrixAt_smul [Finite ι] [Fintype σ] {p : ι → MvPolynomial σ R}
    {d : ι → ℕ} (hp : ∀ i, (p i).IsHomogeneous (d i)) {t : R} (ht : IsUnit t) (v : σ → R) :
    (jacobiMatrixAt p (t • v)).rank = (jacobiMatrixAt p v).rank := by
  classical
  cases nonempty_fintype ι
  rw [jacobiMatrixAt_smul hp, rank_mul_eq_right_of_isUnit_det _ _ ?_]
  rw [det_diagonal]
  exact IsUnit.prod_univ_iff.mpr fun i ↦ ht.pow _

/-- At a zero in the standard affine chart where coordinate `i` is one, Euler's identity
expresses column `i` of the Jacobian matrix of homogeneous equations through the other columns,
weighted by the affine coordinates. -/
theorem col_jacobiMatrixAt_insertNth {n : ℕ} (i : Fin (n + 1))
    {p : ι → MvPolynomial (Fin (n + 1)) R} {d : ι → ℕ} (hp : ∀ k, (p k).IsHomogeneous (d k))
    {a : Fin n → R} (ha : ∀ k, eval a (dehomogenize i (p k)) = 0) :
    (jacobiMatrixAt p (i.insertNth 1 a)).col i =
      -∑ j, a j • (jacobiMatrixAt p (i.insertNth 1 a)).col (i.succAbove j) := by
  ext k
  rw [col_apply, jacobiMatrixAt_apply, eval_pderiv_eq_neg_sum_dehomogenize i (hp k) a (ha k)]
  simp

/-- At a zero in the standard affine chart where coordinate `i` is one, the Jacobian matrix of
the dehomogenized equations has the same image as the Jacobian matrix of the homogeneous
equations. -/
theorem range_mulVecLin_jacobiMatrixAt_dehomogenize {n : ℕ} (i : Fin (n + 1))
    {p : ι → MvPolynomial (Fin (n + 1)) R} {d : ι → ℕ} (hp : ∀ k, (p k).IsHomogeneous (d k))
    {a : Fin n → R} (ha : ∀ k, eval a (dehomogenize i (p k)) = 0) :
    LinearMap.range (jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) a).mulVecLin =
      LinearMap.range (jacobiMatrixAt p (i.insertNth 1 a)).mulVecLin := by
  set J := jacobiMatrixAt p (i.insertNth 1 a)
  rw [range_mulVecLin, range_mulVecLin, jacobiMatrixAt_dehomogenize]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨j, rfl⟩
    exact ⟨i.succAbove j, (col_submatrix J id i.succAbove j).symm⟩
  · rintro _ ⟨l, rfl⟩
    have hmem : ∀ j, J.col (i.succAbove j) ∈
        Submodule.span R (Set.range (J.submatrix id i.succAbove).col) := fun j ↦
      Submodule.subset_span ⟨j, col_submatrix J id i.succAbove j⟩
    refine Fin.succAboveCases i ?_ hmem l
    rw [col_jacobiMatrixAt_insertNth i hp ha]
    exact neg_mem (Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hmem j))

/-- At a zero in the standard affine chart where coordinate `i` is one, the Jacobian matrix of
the dehomogenized equations has the same rank as the Jacobian matrix of the homogeneous
equations. -/
theorem rank_jacobiMatrixAt_dehomogenize {n : ℕ} (i : Fin (n + 1))
    {p : ι → MvPolynomial (Fin (n + 1)) R} {d : ι → ℕ} (hp : ∀ k, (p k).IsHomogeneous (d k))
    {a : Fin n → R} (ha : ∀ k, eval a (dehomogenize i (p k)) = 0) :
    (jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) a).rank =
      (jacobiMatrixAt p (i.insertNth 1 a)).rank := by
  rw [rank, rank, range_mulVecLin_jacobiMatrixAt_dehomogenize i hp ha]

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The rank of the Jacobian matrix of a family of homogeneous equations at a nonzero point
depends only on the projective point it represents. -/
theorem rank_jacobiMatrixAt_eq_of_mk_eq_mk [Finite ι] [Fintype σ] {p : ι → MvPolynomial σ K}
    {d : ι → ℕ} (hp : ∀ i, (p i).IsHomogeneous (d i)) {v w : σ → K} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) :
    (jacobiMatrixAt p v).rank = (jacobiMatrixAt p w).rank := by
  obtain ⟨t, rfl⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp h
  exact rank_jacobiMatrixAt_smul hp (isUnit_iff_ne_zero.mpr (left_ne_zero_of_smul hv)) w

/-- **The Jacobian criterion in a ratio chart**: at a common zero `b` of a family of homogeneous
equations with `b i ≠ 0`, the Jacobian matrix of the dehomogenized equations at the coordinate
ratios `b (i.succAbove j) / b i` has the same rank as the Jacobian matrix of the homogeneous
equations at `b`. -/
theorem rank_jacobiMatrixAt_dehomogenize_div [Finite ι] {n : ℕ} (i : Fin (n + 1))
    {p : ι → MvPolynomial (Fin (n + 1)) K} {d : ι → ℕ} (hp : ∀ k, (p k).IsHomogeneous (d k))
    {b : Fin (n + 1) → K} (hi : b i ≠ 0) (hb : ∀ k, eval b (p k) = 0) :
    (jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) fun j ↦ b (i.succAbove j) / b i).rank =
      (jacobiMatrixAt p b).rank := by
  rw [rank_jacobiMatrixAt_dehomogenize i hp fun k ↦ by
      rw [eval_dehomogenize_div i (hp k) b hi, hb, mul_zero],
    Fin.insertNth_one_div_eq_inv_smul i b hi,
    rank_jacobiMatrixAt_smul hp (isUnit_iff_ne_zero.mpr (inv_ne_zero hi))]

/-- At a nonzero common zero of a family of homogeneous equations, the rank of the Jacobian
matrix is less than the number of variables, since the radial direction lies in its kernel. -/
theorem rank_jacobiMatrixAt_lt_card [Fintype σ] {p : ι → MvPolynomial σ K} {d : ι → ℕ}
    (hp : ∀ i, (p i).IsHomogeneous (d i)) {v : σ → K} (hv : v ≠ 0)
    (hpv : ∀ i, eval v (p i) = 0) :
    (jacobiMatrixAt p v).rank < Fintype.card σ := by
  have hker : 0 < Module.finrank K (LinearMap.ker (jacobiMatrixAt p v).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, jacobiMatrixAt_mulVec_self_eq_zero hp hpv⟩, fun h ↦ hv (congrArg Subtype.val h)⟩
  have h := LinearMap.finrank_range_add_finrank_ker (jacobiMatrixAt p v).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [rank]
  omega

/-- At a nonzero common zero of a family of homogeneous equations where the Jacobian matrix has
full rank, there are fewer equations than variables. -/
theorem card_lt_card_of_mulVec_surjective_jacobiMatrixAt [Fintype ι] [Fintype σ]
    {p : ι → MvPolynomial σ K} {d : ι → ℕ} (hp : ∀ i, (p i).IsHomogeneous (d i)) {v : σ → K}
    (hv : v ≠ 0) (hpv : ∀ i, eval v (p i) = 0) (hJ : (jacobiMatrixAt p v).mulVec.Surjective) :
    Fintype.card ι < Fintype.card σ :=
  mulVec_surjective_iff_rank_eq_card.mp hJ ▸ rank_jacobiMatrixAt_lt_card hp hv hpv

end Field

end TauCeti
