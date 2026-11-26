/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The half-determinant of `A + Aᵀ` in odd size

For a square matrix `A` of odd size `l`, the determinant of the symmetric matrix `A + Aᵀ` is
divisible by `2`, universally: read as a polynomial in the entries of `A` over `ℤ`, it is `2` times
a unique integer polynomial. Indeed modulo `2` the matrix `A + Aᵀ` is symmetric with zero diagonal,
and in characteristic two such a matrix of odd size has determinant zero: in the permutation
expansion the terms of `σ` and `σ⁻¹` agree and cancel in pairs, while an involution of a set of odd
size has a fixed point, which contributes a diagonal entry. The *half-determinant* `halfDet A` is
the value of the quotient polynomial at the entries of `A`, so `2 * halfDet A = det (A + Aᵀ)` over
every commutative ring, even where `2` is a zero divisor.

This is the matrix input of the half-discriminant `disc'(q)` of a quadratic form of odd rank: in a
basis, `q(x) = xᵀ A x` for an upper triangular `A`, and the Gram matrix of the polar form is
`A + Aᵀ`. The identities below are proved in the polynomial ring over `ℤ`, where `2` cancels, and
specialized: `halfDet` commutes with ring homomorphisms, `halfDet (Pᵀ A P) = det P ^ 2 * halfDet A`,
`halfDet` is unchanged by adding `Z - Zᵀ` (which does not change the quadratic form `xᵀ A x`) and by
reindexing, and for a block-diagonal matrix with an even block `A` and any block `D` it is
`det (A + Aᵀ) * halfDet D`.

## Main definitions

* `Matrix.halfDetPoly ι`: the integer polynomial `det (X + Xᵀ) / 2` in the entries of the generic
  matrix `X`, for `ι` of odd cardinality.
* `Matrix.halfDet A`: its value at the entries of `A`.

## Main results

* `Matrix.det_eq_zero_of_isSymm_of_diag_eq_zero`: in characteristic two, a symmetric matrix of odd
  size with zero diagonal has determinant zero.
* `Matrix.two_mul_halfDet`: `2 * halfDet A = det (A + Aᵀ)`; in even size `halfDet` is `0`
  (`Matrix.halfDet_of_not_odd`).
* `Matrix.map_halfDet`: `halfDet` commutes with ring homomorphisms.
* `Matrix.halfDet_transpose_mul_mul`: `halfDet (Pᵀ * A * P) = det P ^ 2 * halfDet A`.
* `Matrix.halfDet_add_sub_transpose`: `halfDet (A + (Z - Zᵀ)) = halfDet A`.
* `Matrix.halfDet_submatrix_equiv_self`: `halfDet` is invariant under reindexing.
* `Matrix.halfDet_fromBlocks_zero₁₂_zero₂₁`:
  `halfDet (fromBlocks A 0 0 D) = det (A + Aᵀ) * halfDet D` for `A` of even size.
* `Matrix.halfDet_unique`, `Matrix.halfDet_fin_three`: the formulas in sizes one and three.

## References

* B. Conrad, *Reductive group schemes*, Appendix C.1 (the half-discriminant, (C.1.3)).
* M.-A. Knus, *Quadratic and Hermitian forms over rings*, Chapter IV, §3.
-/

public section

open MvPolynomial

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- In characteristic two, a symmetric matrix of odd size with zero diagonal has determinant zero.
-/
theorem det_eq_zero_of_isSymm_of_diag_eq_zero {R : Type*} [CommRing R] [CharP R 2]
    (hι : Odd (Fintype.card ι)) {M : Matrix ι ι R} (hM : M.IsSymm) (hd : ∀ i, M i i = 0) :
    M.det = 0 := by
  rw [det_apply]
  refine Finset.sum_involution (fun σ _ => σ⁻¹) (fun σ _ => ?_) (fun σ _ hσ hinv => ?_)
    (fun _ _ => Finset.mem_univ _) (fun σ _ => inv_inv σ)
  · have h : ∏ i, M (σ⁻¹ i) i = ∏ i, M (σ i) i := by
      rw [← Equiv.prod_comp σ]
      exact Finset.prod_congr rfl fun i _ => by simp [hM.apply]
    rw [Equiv.Perm.sign_inv, h, CharTwo.add_self_eq_zero]
  · obtain ⟨i, hi⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
      (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hι)) (by
        rw [pow_one, sq]
        exact mul_eq_one_iff_eq_inv.mpr hinv.symm)
    exact hσ (by rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hd]), smul_zero])

/-- The determinant of `X + Xᵀ`, for the generic matrix `X` over `ℤ` of odd size, is divisible by
`2`. -/
theorem two_dvd_det_mvPolynomialX_add_transpose (hι : Odd (Fintype.card ι)) :
    (2 : MvPolynomial (ι × ι) ℤ) ∣ (mvPolynomialX ι ι ℤ + (mvPolynomialX ι ι ℤ)ᵀ).det := by
  have h2 : (2 : MvPolynomial (ι × ι) ℤ) = C 2 := (map_ofNat C 2).symm
  rw [h2, C_dvd_iff_map_hom_eq_zero (Int.castRingHom (ZMod 2)) 2
    (fun r => by simpa using ZMod.intCast_zmod_eq_zero_iff_dvd r 2), RingHom.map_det]
  refine det_eq_zero_of_isSymm_of_diag_eq_zero hι ?_ fun i => ?_
  · exact (isSymm_add_transpose_self _).map _
  · simp [RingHom.mapMatrix_apply, ← two_mul, CharTwo.two_eq_zero]

variable (ι) in
/-- The polynomial `det (X + Xᵀ) / 2` in the entries of the generic matrix `X` over `ℤ`, for `ι` of
odd cardinality; it is `0` for `ι` of even cardinality. -/
noncomputable def halfDetPoly : MvPolynomial (ι × ι) ℤ :=
  if h : Odd (Fintype.card ι) then (two_dvd_det_mvPolynomialX_add_transpose h).choose else 0

/-- The defining property of `Matrix.halfDetPoly`: `det (X + Xᵀ) = 2 * halfDetPoly ι`. -/
theorem det_mvPolynomialX_add_transpose_eq (hι : Odd (Fintype.card ι)) :
    (mvPolynomialX ι ι ℤ + (mvPolynomialX ι ι ℤ)ᵀ).det = 2 * halfDetPoly ι := by
  rw [halfDetPoly, dite_eq_left hι]
  exact (two_dvd_det_mvPolynomialX_add_transpose hι).choose_spec

/-- The half-determinant of a square matrix `A` of odd size: the value at the entries of `A` of the
integer polynomial `det (X + Xᵀ) / 2`, so that `2 * halfDet A = det (A + Aᵀ)`
(`Matrix.two_mul_halfDet`). It is `0` in even size. -/
noncomputable def halfDet {R : Type*} [CommRing R] (A : Matrix ι ι R) : R :=
  eval₂ (Int.castRingHom R) (fun p => A p.1 p.2) (halfDetPoly ι)

/-- `halfDet A` is the value of `Matrix.halfDetPoly` at the entries of `A`. -/
theorem halfDet_def {R : Type*} [CommRing R] (A : Matrix ι ι R) :
    A.halfDet = eval₂ (Int.castRingHom R) (fun p => A p.1 p.2) (halfDetPoly ι) :=
  (rfl)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `halfDet` commutes with ring homomorphisms. -/
theorem map_halfDet (f : R →+* S) (A : Matrix ι ι R) : f A.halfDet = (A.map f).halfDet := by
  rw [halfDet, halfDet, eval₂_comp_left, RingHom.ext_int (f.comp (Int.castRingHom R))
    (Int.castRingHom S)]
  simp only [Function.comp_def, map_apply]

/-- In even size, `halfDet` is `0` by convention. -/
theorem halfDet_of_not_odd (hι : ¬Odd (Fintype.card ι)) (A : Matrix ι ι R) : A.halfDet = 0 := by
  simp [halfDet, halfDetPoly, hι]

/-- `2 * halfDet A = det (A + Aᵀ)` for `A` of odd size. -/
theorem two_mul_halfDet (hι : Odd (Fintype.card ι)) (A : Matrix ι ι R) :
    2 * A.halfDet = (A + Aᵀ).det := by
  have h := congrArg (eval₂Hom (Int.castRingHom R) fun p : ι × ι => A p.1 p.2)
    (det_mvPolynomialX_add_transpose_eq hι)
  rw [RingHom.map_det, RingHom.map_mul, map_ofNat] at h
  rw [halfDet, ← coe_eval₂Hom, ← h]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

/-- In the polynomial ring over `ℤ`, `2` cancels. -/
private theorem eq_of_two_mul_eq {σ : Type*} {a b : MvPolynomial σ ℤ} (h : 2 * a = 2 * b) :
    a = b :=
  mul_left_cancel₀ two_ne_zero h

/-- The generic matrix with entries the variables `X (inl (i, j))`. -/
private noncomputable def genericLeft (ι κ : Type*) :
    Matrix ι ι (MvPolynomial ((ι × ι) ⊕ (κ × κ)) ℤ) :=
  of fun i j => X (Sum.inl (i, j))

/-- The generic matrix with entries the variables `X (inr (i, j))`. -/
private noncomputable def genericRight (ι κ : Type*) :
    Matrix κ κ (MvPolynomial ((ι × ι) ⊕ (κ × κ)) ℤ) :=
  of fun i j => X (Sum.inr (i, j))

/-- The evaluation at the entries of two matrices. -/
private noncomputable def evalPair (A : Matrix ι ι R) (B : Matrix κ κ R) :
    MvPolynomial ((ι × ι) ⊕ (κ × κ)) ℤ →+* R :=
  eval₂Hom (Int.castRingHom R) (Sum.elim (fun p => A p.1 p.2) (fun p => B p.1 p.2))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem genericLeft_apply (i j : ι) : genericLeft ι κ i j = X (Sum.inl (i, j)) := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem genericLeft_map (A : Matrix ι ι R) (B : Matrix κ κ R) :
    (genericLeft ι κ).map (evalPair A B) = A := by
  ext; simp [genericLeft, evalPair]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem genericRight_map (A : Matrix ι ι R) (B : Matrix κ κ R) :
    (genericRight ι κ).map (evalPair A B) = B := by
  ext; simp [genericRight, evalPair]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem evalPair_X_inl (A : Matrix ι ι R) (B : Matrix κ κ R) (p : ι × ι) :
    evalPair A B (X (Sum.inl p)) = A p.1 p.2 := by
  simp [evalPair]

attribute [local simp] genericLeft_map genericRight_map evalPair_X_inl

/-- `halfDet (Pᵀ * A * P) = det P ^ 2 * halfDet A`. -/
theorem halfDet_transpose_mul_mul (A P : Matrix ι ι R) :
    (Pᵀ * A * P).halfDet = P.det ^ 2 * A.halfDet := by
  by_cases hι : Odd (Fintype.card ι)
  · have key : ((genericRight ι ι)ᵀ * genericLeft ι ι * genericRight ι ι).halfDet =
        (genericRight ι ι).det ^ 2 * (genericLeft ι ι).halfDet := by
      refine eq_of_two_mul_eq ?_
      rw [two_mul_halfDet hι, mul_left_comm, two_mul_halfDet hι, transpose_mul, transpose_mul,
        transpose_transpose, ← Matrix.mul_assoc (genericRight ι ι)ᵀ, ← Matrix.add_mul,
        ← Matrix.mul_add, det_mul, det_mul, det_transpose]
      ring
    simpa [map_halfDet, RingHom.map_det, transpose_map] using congrArg (evalPair A P) key
  · rw [halfDet_of_not_odd hι, halfDet_of_not_odd hι, mul_zero]

/-- The half-determinant of the zero matrix is `0`. -/
@[simp]
theorem halfDet_zero : (0 : Matrix ι ι R).halfDet = 0 := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact halfDet_of_not_odd (by simp) _
  · simpa using halfDet_transpose_mul_mul (0 : Matrix ι ι R) 0

/-- Adding `Z - Zᵀ`, which does not change the quadratic form `x ↦ xᵀ A x`, does not change
`halfDet`. -/
theorem halfDet_add_sub_transpose (A Z : Matrix ι ι R) :
    (A + (Z - Zᵀ)).halfDet = A.halfDet := by
  by_cases hι : Odd (Fintype.card ι)
  · have key : (genericLeft ι ι + (genericRight ι ι - (genericRight ι ι)ᵀ)).halfDet =
        (genericLeft ι ι).halfDet := by
      refine eq_of_two_mul_eq ?_
      rw [two_mul_halfDet hι, two_mul_halfDet hι]
      congr 1
      rw [transpose_add, transpose_sub, transpose_transpose]
      abel
    simpa [map_halfDet, Matrix.map_add, Matrix.map_sub, transpose_map] using
      congrArg (evalPair A Z) key
  · rw [halfDet_of_not_odd hι, halfDet_of_not_odd hι]

/-- `halfDet` is invariant under reindexing. -/
@[simp]
theorem halfDet_submatrix_equiv_self (e : κ ≃ ι) (A : Matrix ι ι R) :
    (A.submatrix e e).halfDet = A.halfDet := by
  by_cases hι : Odd (Fintype.card ι)
  · have hκ : Odd (Fintype.card κ) := Fintype.card_congr e ▸ hι
    have key : ((genericLeft ι ι).submatrix e e).halfDet = (genericLeft ι ι).halfDet := by
      refine eq_of_two_mul_eq ?_
      rw [two_mul_halfDet hι, two_mul_halfDet hκ, transpose_submatrix]
      exact det_submatrix_equiv_self e (genericLeft ι ι + (genericLeft ι ι)ᵀ)
    simpa [map_halfDet, ← submatrix_map] using congrArg (evalPair A A) key
  · have hκ : ¬Odd (Fintype.card κ) := Fintype.card_congr e ▸ hι
    rw [halfDet_of_not_odd hι, halfDet_of_not_odd hκ]

/-- For `A` of even size, the half-determinant of the block-diagonal matrix `fromBlocks A 0 0 D` is
`det (A + Aᵀ) * halfDet D`. -/
theorem halfDet_fromBlocks_zero₁₂_zero₂₁ (hι : Even (Fintype.card ι)) (A : Matrix ι ι R)
    (D : Matrix κ κ R) :
    (fromBlocks A 0 0 D).halfDet = (A + Aᵀ).det * D.halfDet := by
  by_cases hκ : Odd (Fintype.card κ)
  · have hικ : Odd (Fintype.card (ι ⊕ κ)) := by
      rw [Fintype.card_sum]
      exact hι.add_odd hκ
    have key : (fromBlocks (genericLeft ι κ) 0 0 (genericRight ι κ)).halfDet =
        (genericLeft ι κ + (genericLeft ι κ)ᵀ).det * (genericRight ι κ).halfDet := by
      refine eq_of_two_mul_eq ?_
      rw [two_mul_halfDet hικ, mul_left_comm, two_mul_halfDet hκ, fromBlocks_transpose,
        fromBlocks_add]
      simp only [transpose_zero, add_zero]
      exact det_fromBlocks_zero₂₁ _ _ _
    simpa [map_halfDet, RingHom.map_det, fromBlocks_map, Matrix.map_add, transpose_map] using
      congrArg (evalPair A D) key
  · have hικ : ¬Odd (Fintype.card (ι ⊕ κ)) := by
      rw [Fintype.card_sum, Nat.not_odd_iff_even]
      exact hι.add (Nat.not_odd_iff_even.mp hκ)
    rw [halfDet_of_not_odd hικ, halfDet_of_not_odd hκ, mul_zero]

/-- In size one, `halfDet A` is the single entry of `A`. -/
@[simp]
theorem halfDet_unique [Unique ι] (A : Matrix ι ι R) : A.halfDet = A default default := by
  have hι : Odd (Fintype.card ι) := by simp
  have key : (genericLeft ι ι).halfDet = X (Sum.inl (default, default)) := by
    refine eq_of_two_mul_eq ?_
    rw [two_mul_halfDet hι, det_unique]
    simp [genericLeft_apply, two_mul]
  simpa [map_halfDet] using congrArg (evalPair A A) key

/-- In size three, with `a, b, c` the diagonal entries of `A` and `d, e, f` the entries
`(0, 1)`, `(0, 2)`, `(1, 2)` of `A + Aᵀ`, `halfDet A = 4abc + def - af² - be² - cd²`. -/
theorem halfDet_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    A.halfDet = 4 * A 0 0 * A 1 1 * A 2 2 + (A 0 1 + A 1 0) * (A 0 2 + A 2 0) * (A 1 2 + A 2 1)
      - A 0 0 * (A 1 2 + A 2 1) ^ 2 - A 1 1 * (A 0 2 + A 2 0) ^ 2
      - A 2 2 * (A 0 1 + A 1 0) ^ 2 := by
  have hι : Odd (Fintype.card (Fin 3)) := by decide
  set G := genericLeft (Fin 3) (Fin 3)
  have key : G.halfDet = 4 * G 0 0 * G 1 1 * G 2 2 + (G 0 1 + G 1 0) * (G 0 2 + G 2 0) *
      (G 1 2 + G 2 1) - G 0 0 * (G 1 2 + G 2 1) ^ 2 - G 1 1 * (G 0 2 + G 2 0) ^ 2
      - G 2 2 * (G 0 1 + G 1 0) ^ 2 := by
    refine eq_of_two_mul_eq ?_
    rw [two_mul_halfDet hι]
    simp only [det_fin_three, Matrix.add_apply, Matrix.transpose_apply]
    ring
  simpa [map_halfDet, G, genericLeft_apply, map_ofNat] using congrArg (evalPair A A) key

end Matrix
