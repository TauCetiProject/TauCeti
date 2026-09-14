/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis

/-!
# Change of generators in a quaternion algebra

This file proves the quaternion-symbol square-rescaling relation by changing the standard
generators. `TauCeti.QuaternionAlgebra.rescaleJEquiv` identifies `ℍ[R,a,c²b]` with `ℍ[R,a,b]`
by sending `j` to `c j`, for a unit `c`. Its first-parameter counterpart
`TauCeti.QuaternionAlgebra.rescaleIEquiv` is obtained from it using Mathlib's
`QuaternionAlgebra.swapEquiv`.

Both equivalences are defined through `QuaternionAlgebra.Basis.liftHom`, Mathlib's universal
property for quaternion algebras.  The formulas on `i`, `j`, and `k` are exposed as simplification
lemmas, so later proofs can use these equivalences without unfolding their construction.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, §2.11.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

private def rescaleJBasis (a b : R) (c : Rˣ) :
    _root_.QuaternionAlgebra.Basis ℍ[R,a,b] a 0 ((c : R) ^ 2 * b) where
  i := (_root_.QuaternionAlgebra.Basis.self R).i
  j := (c : R) • (_root_.QuaternionAlgebra.Basis.self R).j
  k := (c : R) • (_root_.QuaternionAlgebra.Basis.self R).k
  i_mul_i := by ext <;> simp
  j_mul_j := by
    ext <;> simp [pow_two]
    ring
  i_mul_j := by simp
  j_mul_i := by simp

private def rescaleJInvBasis (a b : R) (c : Rˣ) :
    _root_.QuaternionAlgebra.Basis ℍ[R,a,(c : R) ^ 2 * b] a 0 b where
  i := (_root_.QuaternionAlgebra.Basis.self R).i
  j := ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).j
  k := ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).k
  i_mul_i := by ext <;> simp
  j_mul_j := by
    ext <;> simp [pow_two, mul_assoc, mul_comm]
  i_mul_j := by simp
  j_mul_i := by simp

private def rescaleJHom (a b : R) (c : Rˣ) :
    ℍ[R,a,(c : R) ^ 2 * b] →ₐ[R] ℍ[R,a,b] :=
  (rescaleJBasis a b c).liftHom

private def rescaleJInvHom (a b : R) (c : Rˣ) :
    ℍ[R,a,b] →ₐ[R] ℍ[R,a,(c : R) ^ 2 * b] :=
  (rescaleJInvBasis a b c).liftHom

/-- **Square rescaling of the second quaternion parameter.** If `c` is a unit, rescaling the
standard generators `j` and `k` by `c` gives an `R`-algebra equivalence
`ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]`. -/
def rescaleJEquiv (a b : R) (c : Rˣ) : ℍ[R,a,(c : R) ^ 2 * b] ≃ₐ[R] ℍ[R,a,b] :=
  AlgEquiv.ofAlgHom (rescaleJHom a b c) (rescaleJInvHom a b c)
    (by
      apply _root_.QuaternionAlgebra.hom_ext <;>
        simp [rescaleJHom, rescaleJInvHom, rescaleJBasis, rescaleJInvBasis,
          _root_.QuaternionAlgebra.Basis.lift])
    (by
      apply _root_.QuaternionAlgebra.hom_ext <;>
        simp [rescaleJHom, rescaleJInvHom, rescaleJBasis, rescaleJInvBasis,
          _root_.QuaternionAlgebra.Basis.lift])

@[simp]
theorem rescaleJEquiv_apply_i (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c (_root_.QuaternionAlgebra.Basis.self R).i =
      (_root_.QuaternionAlgebra.Basis.self R).i := by
  simp [rescaleJEquiv, rescaleJHom, rescaleJBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_apply_j (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c (_root_.QuaternionAlgebra.Basis.self R).j =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).j := by
  simp [rescaleJEquiv, rescaleJHom, rescaleJBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c (_root_.QuaternionAlgebra.Basis.self R).k =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul, rescaleJEquiv_apply_i,
    rescaleJEquiv_apply_j]
  simp

@[simp]
theorem rescaleJEquiv_symm_apply_i (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm (_root_.QuaternionAlgebra.Basis.self R).i =
      (_root_.QuaternionAlgebra.Basis.self R).i := by
  simp [rescaleJEquiv, rescaleJInvHom, rescaleJInvBasis,
    _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_symm_apply_j (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm (_root_.QuaternionAlgebra.Basis.self R).j =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).j := by
  simp [rescaleJEquiv, rescaleJInvHom, rescaleJInvBasis,
    _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_symm_apply_k (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm (_root_.QuaternionAlgebra.Basis.self R).k =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul, rescaleJEquiv_symm_apply_i,
    rescaleJEquiv_symm_apply_j]
  simp

/-- **Square rescaling of the first quaternion parameter.** This is the first-parameter version
of `TauCeti.QuaternionAlgebra.rescaleJEquiv`, obtained by exchanging `i` and `j` before and after
rescaling. -/
def rescaleIEquiv (a b : R) (c : Rˣ) : ℍ[R,(c : R) ^ 2 * a,b] ≃ₐ[R] ℍ[R,a,b] :=
  (_root_.QuaternionAlgebra.swapEquiv ((c : R) ^ 2 * a) b).trans <|
    (rescaleJEquiv b a c).trans
      (_root_.QuaternionAlgebra.swapEquiv b a)

@[simp]
theorem rescaleIEquiv_apply_i (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c (_root_.QuaternionAlgebra.Basis.self R).i =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).i := by
  ext <;> simp [rescaleIEquiv, rescaleJEquiv, rescaleJHom, rescaleJBasis,
    _root_.QuaternionAlgebra.Basis.lift, _root_.QuaternionAlgebra.swapEquiv]

@[simp]
theorem rescaleIEquiv_apply_j (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c (_root_.QuaternionAlgebra.Basis.self R).j =
      (_root_.QuaternionAlgebra.Basis.self R).j := by
  ext <;> simp [rescaleIEquiv, rescaleJEquiv, rescaleJHom, rescaleJBasis,
    _root_.QuaternionAlgebra.Basis.lift, _root_.QuaternionAlgebra.swapEquiv]

@[simp]
theorem rescaleIEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c (_root_.QuaternionAlgebra.Basis.self R).k =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul, rescaleIEquiv_apply_i,
    rescaleIEquiv_apply_j]
  simp

@[simp]
theorem rescaleIEquiv_symm_apply_i (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm (_root_.QuaternionAlgebra.Basis.self R).i =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).i := by
  ext <;> simp [rescaleIEquiv, rescaleJEquiv, rescaleJInvHom, rescaleJInvBasis,
    _root_.QuaternionAlgebra.Basis.lift, _root_.QuaternionAlgebra.swapEquiv]

@[simp]
theorem rescaleIEquiv_symm_apply_j (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm (_root_.QuaternionAlgebra.Basis.self R).j =
      (_root_.QuaternionAlgebra.Basis.self R).j := by
  ext <;> simp [rescaleIEquiv, rescaleJEquiv, rescaleJInvHom, rescaleJInvBasis,
    _root_.QuaternionAlgebra.Basis.lift, _root_.QuaternionAlgebra.swapEquiv]

@[simp]
theorem rescaleIEquiv_symm_apply_k (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm (_root_.QuaternionAlgebra.Basis.self R).k =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul, rescaleIEquiv_symm_apply_i,
    rescaleIEquiv_symm_apply_j]
  simp

end QuaternionAlgebra

end TauCeti
