/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.QuaternionBasis

/-!
# Change of generators in a quaternion algebra

This file proves the quaternion-symbol rescaling relations by changing the standard
generators. `TauCeti.QuaternionAlgebra.rescaleJEquiv` identifies `ℍ[R,a,c²b]` with `ℍ[R,a,b]`
by sending `j` to `c j`, for a unit `c`. Its first-parameter counterpart
`TauCeti.QuaternionAlgebra.rescaleIEquiv` is obtained from it using Mathlib's
`QuaternionAlgebra.swapEquiv`, whose formulas on the standard generators are recorded here as
well.

More generally, `TauCeti.QuaternionAlgebra.normMulEquiv` identifies `ℍ[R,a,N(z) b]` with
`ℍ[R,a,b]` for a unit `z = x + y √a` of `QuadraticAlgebra R a 0`, by sending `j` to `(x + y i) j`.

All three equivalences are defined through `QuaternionAlgebra.Basis.liftHom`, Mathlib's universal
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
    rescaleJEquiv a b c ⟨0, 1, 0, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).i := by
  simp [rescaleJEquiv, rescaleJHom, rescaleJBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_apply_j (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c ⟨0, 0, 1, 0⟩ =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).j := by
  simp [rescaleJEquiv, rescaleJHom, rescaleJBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c ⟨0, 0, 0, 1⟩ =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.k_self]
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul]
  simp only [_root_.QuaternionAlgebra.Basis.i_self,
    _root_.QuaternionAlgebra.Basis.j_self, rescaleJEquiv_apply_i, rescaleJEquiv_apply_j]
  simp

@[simp]
theorem rescaleJEquiv_symm_apply_i (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm ⟨0, 1, 0, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).i := by
  simp [rescaleJEquiv, rescaleJInvHom, rescaleJInvBasis,
    _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_symm_apply_j (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm ⟨0, 0, 1, 0⟩ =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).j := by
  simp [rescaleJEquiv, rescaleJInvHom, rescaleJInvBasis,
    _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem rescaleJEquiv_symm_apply_k (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm ⟨0, 0, 0, 1⟩ =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.k_self]
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul]
  simp only [_root_.QuaternionAlgebra.Basis.i_self,
    _root_.QuaternionAlgebra.Basis.j_self, rescaleJEquiv_symm_apply_i,
    rescaleJEquiv_symm_apply_j]
  simp

/-- Mathlib's `QuaternionAlgebra.swapEquiv` sends `i` to `j`. -/
@[simp]
theorem swapEquiv_apply_i (a b : R) :
    _root_.QuaternionAlgebra.swapEquiv a b ⟨0, 1, 0, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).j := by
  ext <;> simp

/-- Mathlib's `QuaternionAlgebra.swapEquiv` sends `j` to `i`. -/
@[simp]
theorem swapEquiv_apply_j (a b : R) :
    _root_.QuaternionAlgebra.swapEquiv a b ⟨0, 0, 1, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).i := by
  ext <;> simp

/-- The inverse of Mathlib's `QuaternionAlgebra.swapEquiv` sends `i` to `j`. -/
@[simp]
theorem swapEquiv_symm_apply_i (a b : R) :
    (_root_.QuaternionAlgebra.swapEquiv a b).symm ⟨0, 1, 0, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).j := by
  ext <;> simp

/-- The inverse of Mathlib's `QuaternionAlgebra.swapEquiv` sends `j` to `i`. -/
@[simp]
theorem swapEquiv_symm_apply_j (a b : R) :
    (_root_.QuaternionAlgebra.swapEquiv a b).symm ⟨0, 0, 1, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).i := by
  ext <;> simp

/-- **Square rescaling of the first quaternion parameter.** This is the first-parameter version
of `TauCeti.QuaternionAlgebra.rescaleJEquiv`, obtained by exchanging `i` and `j` before and after
rescaling. -/
def rescaleIEquiv (a b : R) (c : Rˣ) : ℍ[R,(c : R) ^ 2 * a,b] ≃ₐ[R] ℍ[R,a,b] :=
  (_root_.QuaternionAlgebra.swapEquiv ((c : R) ^ 2 * a) b).trans <|
    (rescaleJEquiv b a c).trans
      (_root_.QuaternionAlgebra.swapEquiv b a)

@[simp]
theorem rescaleIEquiv_apply_i (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 1, 0, 0⟩ =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).i := by
  simp only [rescaleIEquiv, AlgEquiv.trans_apply, swapEquiv_apply_i,
    _root_.QuaternionAlgebra.Basis.j_self, rescaleJEquiv_apply_j, map_smul,
    swapEquiv_apply_j]

@[simp]
theorem rescaleIEquiv_apply_j (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 0, 1, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).j := by
  simp only [rescaleIEquiv, AlgEquiv.trans_apply, swapEquiv_apply_j,
    _root_.QuaternionAlgebra.Basis.i_self, rescaleJEquiv_apply_i, swapEquiv_apply_i]

@[simp]
theorem rescaleIEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 0, 0, 1⟩ =
      (c : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.k_self]
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul]
  simp only [_root_.QuaternionAlgebra.Basis.i_self,
    _root_.QuaternionAlgebra.Basis.j_self, rescaleIEquiv_apply_i, rescaleIEquiv_apply_j]
  simp

@[simp]
theorem rescaleIEquiv_symm_apply_i (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm ⟨0, 1, 0, 0⟩ =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).i := by
  simp only [rescaleIEquiv, AlgEquiv.symm_trans_apply, swapEquiv_symm_apply_i,
    _root_.QuaternionAlgebra.Basis.j_self, rescaleJEquiv_symm_apply_j, map_smul,
    swapEquiv_symm_apply_j]

@[simp]
theorem rescaleIEquiv_symm_apply_j (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm ⟨0, 0, 1, 0⟩ =
      (_root_.QuaternionAlgebra.Basis.self R).j := by
  simp only [rescaleIEquiv, AlgEquiv.symm_trans_apply, swapEquiv_symm_apply_j,
    _root_.QuaternionAlgebra.Basis.i_self, rescaleJEquiv_symm_apply_i,
    swapEquiv_symm_apply_i]

@[simp]
theorem rescaleIEquiv_symm_apply_k (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm ⟨0, 0, 0, 1⟩ =
      ((c⁻¹ : Rˣ) : R) • (_root_.QuaternionAlgebra.Basis.self R).k := by
  rw [← _root_.QuaternionAlgebra.Basis.k_self]
  rw [← _root_.QuaternionAlgebra.Basis.i_mul_j, map_mul]
  simp only [_root_.QuaternionAlgebra.Basis.i_self,
    _root_.QuaternionAlgebra.Basis.j_self, rescaleIEquiv_symm_apply_i,
    rescaleIEquiv_symm_apply_j]
  simp

section Norm

/-- The basis of `ℍ[R,a,c]` of type `(a, d)` obtained by multiplying `j` and `k` on the left by the
image of `w` under `√a ↦ i`, for `w : R[√a]` with `N(w) c = d`. -/
private def normMulBasis (a c d : R) (w : QuadraticAlgebra R a 0) (h : w.norm * c = d) :
    _root_.QuaternionAlgebra.Basis ℍ[R,a,c] a 0 d where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, w.re, w.im⟩
  k := ⟨0, 0, a * w.im, w.re⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by
    subst h
    ext <;> simp [QuadraticAlgebra.norm_def] <;> ring
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- Multiplying `j` first by `w'` and then by `w` multiplies it by `w' w`, so the two lifts are
mutually inverse when `w' w = 1`. -/
private theorem normMulBasis_liftHom_comp_liftHom {a c d : R} {w w' : QuadraticAlgebra R a 0}
    (h : w.norm * c = d) (h' : w'.norm * d = c) (hw : w' * w = 1) :
    (normMulBasis a c d w h).liftHom.comp (normMulBasis a d c w' h').liftHom = AlgHom.id R _ := by
  have hre := congrArg QuadraticAlgebra.re hw
  have him := congrArg QuadraticAlgebra.im hw
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one] at hre him
  apply _root_.QuaternionAlgebra.hom_ext <;> ext <;>
    simp only [normMulBasis, _root_.QuaternionAlgebra.Basis.i_self,
      _root_.QuaternionAlgebra.Basis.j_self, AlgHom.coe_comp, Function.comp_apply,
      _root_.QuaternionAlgebra.Basis.liftHom_apply, _root_.QuaternionAlgebra.Basis.lift,
      _root_.QuaternionAlgebra.coe_algebraMap, _root_.QuaternionAlgebra.coe_zero,
      _root_.QuaternionAlgebra.smul_mk, _root_.QuaternionAlgebra.mk_add_mk, one_smul,
      zero_smul, zero_add, add_zero, smul_eq_mul, mul_zero, AlgHom.coe_id, id_eq] <;>
    first | linear_combination hre | linear_combination him

variable (a b : R) (z : (QuadraticAlgebra R a 0)ˣ)

private theorem norm_inv_mul_norm_mul :
    (↑z⁻¹ : QuadraticAlgebra R a 0).norm * ((z : QuadraticAlgebra R a 0).norm * b) = b := by
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- **Norm rescaling of the second quaternion parameter.** For a unit `z = x + y √a` of the
quadratic algebra `R[√a] = QuadraticAlgebra R a 0`, sending `j` to `(x + y i) j` gives an
`R`-algebra equivalence `ℍ[R,a,N(z) b] ≃ₐ[R] ℍ[R,a,b]`. The quaternion symbol `(a, b)` therefore
depends on `b` only up to norms of units of `R[√a]`; `TauCeti.QuaternionAlgebra.rescaleJEquiv` is
the analogous statement for a unit scalar `c`, whose norm is `c²`. -/
def normMulEquiv : ℍ[R,a,(z : QuadraticAlgebra R a 0).norm * b] ≃ₐ[R] ℍ[R,a,b] :=
  AlgEquiv.ofAlgHom (normMulBasis a b _ z rfl).liftHom
    (normMulBasis a _ b (↑z⁻¹ : QuadraticAlgebra R a 0) (norm_inv_mul_norm_mul a b z)).liftHom
    (normMulBasis_liftHom_comp_liftHom _ _ z.inv_mul)
    (normMulBasis_liftHom_comp_liftHom _ _ z.mul_inv)

@[simp]
theorem normMulEquiv_apply_i : normMulEquiv a b z ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  simp [normMulEquiv, normMulBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem normMulEquiv_apply_j :
    normMulEquiv a b z ⟨0, 0, 1, 0⟩ =
      ⟨0, 0, (z : QuadraticAlgebra R a 0).re, (z : QuadraticAlgebra R a 0).im⟩ := by
  simp [normMulEquiv, normMulBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem normMulEquiv_apply_k :
    normMulEquiv a b z ⟨0, 0, 0, 1⟩ =
      ⟨0, 0, a * (z : QuadraticAlgebra R a 0).im, (z : QuadraticAlgebra R a 0).re⟩ := by
  simp [normMulEquiv, normMulBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem normMulEquiv_symm_apply_i : (normMulEquiv a b z).symm ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  simp [normMulEquiv, normMulBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem normMulEquiv_symm_apply_j :
    (normMulEquiv a b z).symm ⟨0, 0, 1, 0⟩ =
      ⟨0, 0, (↑z⁻¹ : QuadraticAlgebra R a 0).re, (↑z⁻¹ : QuadraticAlgebra R a 0).im⟩ := by
  simp [normMulEquiv, normMulBasis, _root_.QuaternionAlgebra.Basis.lift]

@[simp]
theorem normMulEquiv_symm_apply_k :
    (normMulEquiv a b z).symm ⟨0, 0, 0, 1⟩ =
      ⟨0, 0, a * (↑z⁻¹ : QuadraticAlgebra R a 0).im, (↑z⁻¹ : QuadraticAlgebra R a 0).re⟩ := by
  simp [normMulEquiv, normMulBasis, _root_.QuaternionAlgebra.Basis.lift]

end Norm

end QuaternionAlgebra

end TauCeti
