/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Algebra.QuaternionBasis
import Mathlib.Tactic.LinearCombination

/-!
# Change of generators in a quaternion algebra

This file proves the quaternion-symbol rescaling relations by changing the standard
generators. `TauCeti.QuaternionAlgebra.rescaleJEquiv` identifies `ℍ[R,a,c²b]` with `ℍ[R,a,b]`
by sending `j` to `c j`, for a unit `c`. Its first-parameter counterpart
`TauCeti.QuaternionAlgebra.rescaleIEquiv` is obtained from it using Mathlib's
`QuaternionAlgebra.swapEquiv`, whose formulas on the standard generators are recorded here as
well.

More generally, `TauCeti.QuaternionAlgebra.normMulEquiv` identifies `ℍ[R,a,b,N(z) c]`
with `ℍ[R,a,b,c]` for a unit `z = x + y ω` of `QuadraticAlgebra R a b`, by sending `j` to
`(x + y i) j`.

Completing the square gives the general change of generators
`TauCeti.QuaternionAlgebra.completeSquareEquiv`, identifying `ℍ[R,a,b,c]` with
`ℍ[R,QuadraticAlgebra.discr a b,0,c]` when `2` is invertible.

These equivalences are defined through `QuaternionAlgebra.Basis.liftHom`, Mathlib's universal
property for quaternion algebras.  The formulas on `i`, `j`, and `k` are exposed as simplification
lemmas, so later proofs can use these equivalences without unfolding their construction.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, §2.11.
-/

public section

open scoped Quaternion

namespace TauCeti

variable {R : Type*} [CommRing R]
section CompleteSquare

variable [Invertible (2 : R)]

private def completeSquareBasis (a b c : R) :
    QuaternionAlgebra.Basis ℍ[R,QuadraticAlgebra.discr a b,0,c] a b c where
  i := ⟨⅟ (2 : R) * b, ⅟ (2 : R), 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, ⅟ (2 : R) * b, ⅟ (2 : R)⟩
  i_mul_i := by
    rw [QuadraticAlgebra.discr_def]
    ext <;> simp [mul_assoc]
    · linear_combination
        (⅟ (2 : R) * b ^ 2 + a * (2 * ⅟ (2 : R) + 1)) *
          (invOf_mul_self (2 : R))
    · linear_combination (⅟ (2 : R) * b) * (invOf_mul_self (2 : R))
  j_mul_j := by
    ext <;> simp
  i_mul_j := by
    ext <;> simp
  j_mul_i := by
    ext <;> simp
    linear_combination b * (invOf_mul_self (2 : R))

private def completeSquareInvBasis (a b c : R) :
    QuaternionAlgebra.Basis ℍ[R,a,b,c] (QuadraticAlgebra.discr a b) 0 c where
  i := ⟨-b, 2, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, -b, 2⟩
  i_mul_i := by
    rw [QuadraticAlgebra.discr_def]
    ext <;> simp <;> ring
  j_mul_j := by
    ext <;> simp
  i_mul_j := by
    ext <;> simp
  j_mul_i := by
    ext <;> simp
    ring

/-- **Completing the square in a quaternion algebra.** The change of generators
`i ↦ ⅟ 2 * (b + i)` identifies `ℍ[R,a,b,c]` with the zero-linear-term presentation
`ℍ[R,QuadraticAlgebra.discr a b,0,c]`. -/
def QuaternionAlgebra.completeSquareEquiv (a b c : R) :
    ℍ[R,a,b,c] ≃ₐ[R] ℍ[R,QuadraticAlgebra.discr a b,0,c] :=
  AlgEquiv.ofAlgHom (completeSquareBasis a b c).liftHom (completeSquareInvBasis a b c).liftHom
    (by ext <;> simp [completeSquareBasis, completeSquareInvBasis, QuaternionAlgebra.Basis.lift])
    (by ext <;> simp [completeSquareBasis, completeSquareInvBasis, QuaternionAlgebra.Basis.lift])

/-- The image of the standard generator `i` under the completing-square equivalence. -/
@[simp]
theorem QuaternionAlgebra.completeSquareEquiv_apply_i (a b c : R) :
    completeSquareEquiv a b c ⟨0, 1, 0, 0⟩ = ⟨⅟ (2 : R) * b, ⅟ (2 : R), 0, 0⟩ := by
  simp [completeSquareEquiv, completeSquareBasis, QuaternionAlgebra.Basis.lift]

/-- The image of the standard generator `j` under the completing-square equivalence. -/
@[simp]
theorem QuaternionAlgebra.completeSquareEquiv_apply_j (a b c : R) :
    completeSquareEquiv a b c ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ := by
  simp [completeSquareEquiv, completeSquareBasis, QuaternionAlgebra.Basis.lift]

/-- The image of the standard generator `k` under the completing-square equivalence. -/
@[simp]
theorem QuaternionAlgebra.completeSquareEquiv_apply_k (a b c : R) :
    completeSquareEquiv a b c ⟨0, 0, 0, 1⟩ = ⟨0, 0, ⅟ (2 : R) * b, ⅟ (2 : R)⟩ := by
  simp [completeSquareEquiv, completeSquareBasis, QuaternionAlgebra.Basis.lift]

/-- The image of the standard generator `i` under the inverse completing-square equivalence. -/
@[simp]
theorem QuaternionAlgebra.completeSquareEquiv_symm_apply_i (a b c : R) :
    (completeSquareEquiv a b c).symm ⟨0, 1, 0, 0⟩ = ⟨-b, 2, 0, 0⟩ := by
  simp [completeSquareEquiv, completeSquareInvBasis, QuaternionAlgebra.Basis.lift]

/-- The image of the standard generator `j` under the inverse completing-square equivalence. -/
@[simp]
theorem QuaternionAlgebra.completeSquareEquiv_symm_apply_j (a b c : R) :
    (completeSquareEquiv a b c).symm ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ := by
  simp [completeSquareEquiv, completeSquareInvBasis, QuaternionAlgebra.Basis.lift]

/-- The image of the standard generator `k` under the inverse completing-square equivalence. -/
@[simp]
theorem QuaternionAlgebra.completeSquareEquiv_symm_apply_k (a b c : R) :
    (completeSquareEquiv a b c).symm ⟨0, 0, 0, 1⟩ = ⟨0, 0, -b, 2⟩ := by
  simp [completeSquareEquiv, completeSquareInvBasis, QuaternionAlgebra.Basis.lift]

end CompleteSquare


section Rescale

private def rescaleJBasis (a b : R) (c : Rˣ) :
    QuaternionAlgebra.Basis ℍ[R,a,b] a 0 ((c : R) ^ 2 * b) where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, c, 0⟩
  k := ⟨0, 0, 0, c⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp; ring
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

private def rescaleJInvBasis (a b : R) (c : Rˣ) :
    QuaternionAlgebra.Basis ℍ[R,a,(c : R) ^ 2 * b] a 0 b where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, ↑c⁻¹, 0⟩
  k := ⟨0, 0, 0, ↑c⁻¹⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp [pow_two, mul_assoc, mul_comm]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- **Square rescaling of the second quaternion parameter.** If `c` is a unit, rescaling the
standard generators `j` and `k` by `c` gives an `R`-algebra equivalence
`ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]`. -/
def QuaternionAlgebra.rescaleJEquiv (a b : R) (c : Rˣ) :
    ℍ[R,a,(c : R) ^ 2 * b] ≃ₐ[R] ℍ[R,a,b] :=
  AlgEquiv.ofAlgHom (rescaleJBasis a b c).liftHom (rescaleJInvBasis a b c).liftHom
    (by ext <;> simp [rescaleJBasis, rescaleJInvBasis, QuaternionAlgebra.Basis.lift])
    (by ext <;> simp [rescaleJBasis, rescaleJInvBasis, QuaternionAlgebra.Basis.lift])

/-- The square-rescaling equivalence `ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]` fixes `i`. -/
@[simp]
theorem QuaternionAlgebra.rescaleJEquiv_apply_i (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  simp [rescaleJEquiv, rescaleJBasis, QuaternionAlgebra.Basis.lift]

/-- The square-rescaling equivalence `ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]` sends `j` to `c j`. -/
@[simp]
theorem QuaternionAlgebra.rescaleJEquiv_apply_j (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c ⟨0, 0, 1, 0⟩ = ⟨0, 0, c, 0⟩ := by
  simp [rescaleJEquiv, rescaleJBasis, QuaternionAlgebra.Basis.lift]

/-- The square-rescaling equivalence `ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]` sends `k` to `c k`. -/
@[simp]
theorem QuaternionAlgebra.rescaleJEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleJEquiv a b c ⟨0, 0, 0, 1⟩ = ⟨0, 0, 0, c⟩ := by
  simp [rescaleJEquiv, rescaleJBasis, QuaternionAlgebra.Basis.lift]

/-- The inverse of the square-rescaling equivalence `ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]` fixes `i`. -/
@[simp]
theorem QuaternionAlgebra.rescaleJEquiv_symm_apply_i (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  simp [rescaleJEquiv, rescaleJInvBasis, QuaternionAlgebra.Basis.lift]

/-- The inverse of the square-rescaling equivalence `ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]` sends `j` to
`c⁻¹ j`. -/
@[simp]
theorem QuaternionAlgebra.rescaleJEquiv_symm_apply_j (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm ⟨0, 0, 1, 0⟩ = ⟨0, 0, ↑c⁻¹, 0⟩ := by
  simp [rescaleJEquiv, rescaleJInvBasis, QuaternionAlgebra.Basis.lift]

/-- The inverse of the square-rescaling equivalence `ℍ[R,a,c²b] ≃ₐ[R] ℍ[R,a,b]` sends `k` to
`c⁻¹ k`. -/
@[simp]
theorem QuaternionAlgebra.rescaleJEquiv_symm_apply_k (a b : R) (c : Rˣ) :
    (rescaleJEquiv a b c).symm ⟨0, 0, 0, 1⟩ = ⟨0, 0, 0, ↑c⁻¹⟩ := by
  simp [rescaleJEquiv, rescaleJInvBasis, QuaternionAlgebra.Basis.lift]

/-- Mathlib's `QuaternionAlgebra.swapEquiv` sends `i` to `j`. -/
@[simp]
theorem QuaternionAlgebra.swapEquiv_apply_i (a b : R) :
    QuaternionAlgebra.swapEquiv a b ⟨0, 1, 0, 0⟩ = ⟨0, 0, 1, 0⟩ := by
  ext <;> simp

/-- Mathlib's `QuaternionAlgebra.swapEquiv` sends `j` to `i`. -/
@[simp]
theorem QuaternionAlgebra.swapEquiv_apply_j (a b : R) :
    QuaternionAlgebra.swapEquiv a b ⟨0, 0, 1, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  ext <;> simp

/-- The inverse of Mathlib's `QuaternionAlgebra.swapEquiv` sends `i` to `j`. -/
@[simp]
theorem QuaternionAlgebra.swapEquiv_symm_apply_i (a b : R) :
    (QuaternionAlgebra.swapEquiv a b).symm ⟨0, 1, 0, 0⟩ = ⟨0, 0, 1, 0⟩ := by
  ext <;> simp

/-- The inverse of Mathlib's `QuaternionAlgebra.swapEquiv` sends `j` to `i`. -/
@[simp]
theorem QuaternionAlgebra.swapEquiv_symm_apply_j (a b : R) :
    (QuaternionAlgebra.swapEquiv a b).symm ⟨0, 0, 1, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  ext <;> simp

/-- **Square rescaling of the first quaternion parameter.** This is the first-parameter version
of `TauCeti.QuaternionAlgebra.rescaleJEquiv`, obtained by exchanging `i` and `j` before and after
rescaling. -/
def QuaternionAlgebra.rescaleIEquiv (a b : R) (c : Rˣ) :
    ℍ[R,(c : R) ^ 2 * a,b] ≃ₐ[R] ℍ[R,a,b] :=
  (QuaternionAlgebra.swapEquiv ((c : R) ^ 2 * a) b).trans <|
    (rescaleJEquiv b a c).trans (QuaternionAlgebra.swapEquiv b a)

/-- The square-rescaling equivalence `ℍ[R,c²a,b] ≃ₐ[R] ℍ[R,a,b]` sends `i` to `c i`. -/
@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_apply_i (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 1, 0, 0⟩ = ⟨0, c, 0, 0⟩ := by
  ext <;> simp [rescaleIEquiv]

/-- The square-rescaling equivalence `ℍ[R,c²a,b] ≃ₐ[R] ℍ[R,a,b]` fixes `j`. -/
@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_apply_j (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ := by
  simp [rescaleIEquiv]

/-- The square-rescaling equivalence `ℍ[R,c²a,b] ≃ₐ[R] ℍ[R,a,b]` sends `k` to `c k`. -/
@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 0, 0, 1⟩ = ⟨0, 0, 0, c⟩ := by
  ext <;> simp [rescaleIEquiv, rescaleJEquiv, rescaleJBasis, QuaternionAlgebra.Basis.lift]

/-- The inverse of the square-rescaling equivalence `ℍ[R,c²a,b] ≃ₐ[R] ℍ[R,a,b]` sends `i` to
`c⁻¹ i`. -/
@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_symm_apply_i (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm ⟨0, 1, 0, 0⟩ = ⟨0, ↑c⁻¹, 0, 0⟩ := by
  ext <;> simp [rescaleIEquiv]

/-- The inverse of the square-rescaling equivalence `ℍ[R,c²a,b] ≃ₐ[R] ℍ[R,a,b]` fixes `j`. -/
@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_symm_apply_j (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ := by
  simp [rescaleIEquiv]

/-- The inverse of the square-rescaling equivalence `ℍ[R,c²a,b] ≃ₐ[R] ℍ[R,a,b]` sends `k` to
`c⁻¹ k`. -/
@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_symm_apply_k (a b : R) (c : Rˣ) :
    (rescaleIEquiv a b c).symm ⟨0, 0, 0, 1⟩ = ⟨0, 0, 0, ↑c⁻¹⟩ := by
  ext <;> simp [rescaleIEquiv, rescaleJEquiv, rescaleJInvBasis, QuaternionAlgebra.Basis.lift]

end Rescale

section Norm

/-- The basis of `ℍ[R,a,b,c]` of type `(a, b, d)` obtained by multiplying `j` and `k` on the left
by the image of `w` under `ω ↦ i`, for `w : QuadraticAlgebra R a b` with `N(w) c = d`. -/
private def normMulBasis (a b c d : R) (w : QuadraticAlgebra R a b) (h : w.norm * c = d) :
    QuaternionAlgebra.Basis ℍ[R,a,b,c] a b d where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, w.re, w.im⟩
  k := ⟨0, 0, a * w.im, w.re + b * w.im⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by
    subst h
    ext <;> simp [QuadraticAlgebra.norm_def] <;> ring
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- The lift of `normMulBasis` in coordinates. -/
private theorem normMulBasis_liftHom_apply {a b c d : R} {w : QuadraticAlgebra R a b}
    (h : w.norm * c = d) (x : ℍ[R,a,b,d]) :
    (normMulBasis a b c d w h).liftHom x =
      ⟨x.re, x.imI, x.imJ * w.re + x.imK * (a * w.im),
        x.imJ * w.im + x.imK * (w.re + b * w.im)⟩ := by
  ext <;> simp [normMulBasis, QuaternionAlgebra.Basis.lift]

/-- Multiplying `j` first by `w'` and then by `w` multiplies it by `w' w`, so the two lifts are
mutually inverse when `w' w = 1`. -/
private theorem normMulBasis_liftHom_comp_liftHom {a b c d : R} {w w' : QuadraticAlgebra R a b}
    (h : w.norm * c = d) (h' : w'.norm * d = c) (hw : w' * w = 1) :
    (normMulBasis a b c d w h).liftHom.comp (normMulBasis a b d c w' h').liftHom =
      AlgHom.id R _ := by
  have hre := congrArg QuadraticAlgebra.re hw
  have him := congrArg QuadraticAlgebra.im hw
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one] at hre him
  ext <;> simp only [AlgHom.comp_apply, AlgHom.id_apply, normMulBasis_liftHom_apply,
      QuaternionAlgebra.Basis.i_self, QuaternionAlgebra.Basis.j_self] <;>
    first | ring1 | linear_combination hre | linear_combination him

variable (a b c : R) (z : (QuadraticAlgebra R a b)ˣ)

private theorem norm_inv_mul_norm_mul :
    (↑z⁻¹ : QuadraticAlgebra R a b).norm * ((z : QuadraticAlgebra R a b).norm * c) = c := by
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- **Norm rescaling of the last quaternion parameter.** For a unit `z = x + y ω` of the
quadratic algebra `QuadraticAlgebra R a b`, where `ω² = a + b ω`, sending `j` to `(x + y i) j`
gives an `R`-algebra equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]`. In particular, the
quaternion symbol `(a, c) = ℍ[R,a,0,c]` depends on `c` only up to norms of units of
`R[√a] = QuadraticAlgebra R a 0`; `TauCeti.QuaternionAlgebra.rescaleJEquiv` is the analogous
statement for a unit scalar, whose norm is its square. -/
def QuaternionAlgebra.normMulEquiv :
    ℍ[R,a,b,(z : QuadraticAlgebra R a b).norm * c] ≃ₐ[R] ℍ[R,a,b,c] :=
  AlgEquiv.ofAlgHom (normMulBasis a b c _ z rfl).liftHom
    (normMulBasis a b _ c (↑z⁻¹ : QuadraticAlgebra R a b) (norm_inv_mul_norm_mul a b c z)).liftHom
    (normMulBasis_liftHom_comp_liftHom _ _ z.inv_mul)
    (normMulBasis_liftHom_comp_liftHom _ _ z.mul_inv)

/-- The norm-rescaling equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]` fixes `i`. -/
@[simp]
theorem QuaternionAlgebra.normMulEquiv_apply_i :
    normMulEquiv a b c z ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  simp [normMulEquiv, normMulBasis_liftHom_apply, -QuaternionAlgebra.Basis.liftHom_apply]

/-- The norm-rescaling equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]` sends `j` to
`(x + y i) j`, where `z = x + y ω`. -/
@[simp]
theorem QuaternionAlgebra.normMulEquiv_apply_j :
    normMulEquiv a b c z ⟨0, 0, 1, 0⟩ =
      ⟨0, 0, (z : QuadraticAlgebra R a b).re, (z : QuadraticAlgebra R a b).im⟩ := by
  simp [normMulEquiv, normMulBasis_liftHom_apply, -QuaternionAlgebra.Basis.liftHom_apply]

/-- The norm-rescaling equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]` sends `k` to
`(x + y i) k`, where `z = x + y ω`. -/
@[simp]
theorem QuaternionAlgebra.normMulEquiv_apply_k :
    normMulEquiv a b c z ⟨0, 0, 0, 1⟩ =
      ⟨0, 0, a * (z : QuadraticAlgebra R a b).im,
        (z : QuadraticAlgebra R a b).re + b * (z : QuadraticAlgebra R a b).im⟩ := by
  simp [normMulEquiv, normMulBasis_liftHom_apply, -QuaternionAlgebra.Basis.liftHom_apply]

/-- The inverse of the norm-rescaling equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]` fixes
`i`. -/
@[simp]
theorem QuaternionAlgebra.normMulEquiv_symm_apply_i :
    (normMulEquiv a b c z).symm ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ := by
  simp [normMulEquiv, normMulBasis_liftHom_apply, -QuaternionAlgebra.Basis.liftHom_apply]

/-- The inverse of the norm-rescaling equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]` sends `j`
to `(x' + y' i) j`, where `z⁻¹ = x' + y' ω`. -/
@[simp]
theorem QuaternionAlgebra.normMulEquiv_symm_apply_j :
    (normMulEquiv a b c z).symm ⟨0, 0, 1, 0⟩ =
      ⟨0, 0, (↑z⁻¹ : QuadraticAlgebra R a b).re, (↑z⁻¹ : QuadraticAlgebra R a b).im⟩ := by
  simp [normMulEquiv, normMulBasis_liftHom_apply, -QuaternionAlgebra.Basis.liftHom_apply]

/-- The inverse of the norm-rescaling equivalence `ℍ[R,a,b,N(z) c] ≃ₐ[R] ℍ[R,a,b,c]` sends `k`
to `(x' + y' i) k`, where `z⁻¹ = x' + y' ω`. -/
@[simp]
theorem QuaternionAlgebra.normMulEquiv_symm_apply_k :
    (normMulEquiv a b c z).symm ⟨0, 0, 0, 1⟩ =
      ⟨0, 0, a * (↑z⁻¹ : QuadraticAlgebra R a b).im,
        (↑z⁻¹ : QuadraticAlgebra R a b).re + b * (↑z⁻¹ : QuadraticAlgebra R a b).im⟩ := by
  simp [normMulEquiv, normMulBasis_liftHom_apply, -QuaternionAlgebra.Basis.liftHom_apply]

end Norm

end TauCeti
