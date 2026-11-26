/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Lift
public import TauCeti.RingTheory.WittVector.Truncated.Basic

/-!
# Truncated Witt vectors as algebra maps out of a polynomial ring

An `R`-algebra map `f` out of the polynomial ring `R[X₀, …, X_{n-1}]` into `A` is the same as the
truncated Witt vector of length `n` over `A` with coordinates `f(X₀), …, f(X_{n-1})`
(`TruncatedWittVector.algHomEquiv`). This is `MvPolynomial.aevalEquiv` read through the
coordinates of `TruncatedWittVector p n A`. The correspondence is natural in the value algebra:
post-composing with `φ : A →ₐ[R] B` changes the coefficients of the Witt vector along `φ`
(`TruncatedWittVector.algHomEquiv_comp`).

So the polynomial ring corepresents the set-valued functor `A ↦ W_n(A)`; transporting the
additive group law of `W_n` (addition, zero and negation) along this bijection gives its
coordinate Hopf algebra.
-/

public section

noncomputable section

open MvPolynomial

namespace TruncatedWittVector

variable (p : ℕ) (n : ℕ) (R : Type*) [CommSemiring R]

section CommSemiring

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- An `R`-algebra map out of the polynomial ring `R[X₀, …, X_{n-1}]` is the same as the
truncated Witt vector of length `n` whose coordinates are its values on the variables. -/
def algHomEquiv : (MvPolynomial (Fin n) R →ₐ[R] A) ≃ TruncatedWittVector p n A :=
  (aevalEquiv (Fin n) R A).symm.trans
    { toFun := mk p
      invFun x i := x.coeff i
      left_inv x := _root_.funext (coeff_mk x)
      right_inv := mk_coeff }

/-- The coordinates of the Witt vector of an algebra map are its values on the variables. -/
@[simp]
theorem coeff_algHomEquiv (f : MvPolynomial (Fin n) R →ₐ[R] A) (i : Fin n) :
    (algHomEquiv p n R f).coeff i = f (X i) :=
  (coeff_mk _ i).trans (aevalEquiv_symm_apply f i)

/-- The algebra map attached to a Witt vector sends the variable `X_i` to the `i`-th
coordinate. -/
@[simp]
theorem algHomEquiv_symm_apply_X (x : TruncatedWittVector p n A) (i : Fin n) :
    (algHomEquiv p n R).symm x (X i) = x.coeff i := by
  rw [← coeff_algHomEquiv, Equiv.apply_symm_apply]

end CommSemiring

variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The Witt vector of an algebra map is natural in the value algebra: post-composing with
`φ : A →ₐ[R] B` changes the coefficients of the Witt vector along `φ`. -/
theorem algHomEquiv_comp [Fact p.Prime] (φ : A →ₐ[R] B)
    (f : MvPolynomial (Fin n) R →ₐ[R] A) :
    algHomEquiv p n R (φ.comp f) = map n φ.toRingHom (algHomEquiv p n R f) := by
  ext i
  simp

end TruncatedWittVector
