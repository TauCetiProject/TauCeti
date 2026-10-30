/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.DualNumber.Polynomial

/-!
# Velocities of polynomial curves through the identity

A polynomial curve in the affine group `Spec H` is an `R[X]`-valued point, that is, an
algebra homomorphism `γ : H →ₐ[R] R[X]`. When the curve passes through the identity at
`t = 0`, meaning that evaluation at zero recovers the counit, its velocity at `t = 0` is the
tangent vector at the identity which sends a coordinate function `h` to the linear coefficient
of the polynomial `γ h`.

A curve lying in a closed subgroup has its velocity in the Lie algebra of that subgroup. This
is the coordinate form of the statement that the derivative at zero of a curve inside a closed
subgroup is tangent to the subgroup. It is the step from polynomial one-parameter subgroups to
tangent vectors, and is used to show that the logarithm of a unipotent point of a closed
subgroup of `GLₙ` lies in its Lie algebra.

## Main declarations

* `TauCeti.Bialgebra.curveVelocity`: the velocity at zero of a polynomial curve through the
  identity.
* `TauCeti.Bialgebra.curveVelocity_apply`, `TauCeti.Bialgebra.algEquivSelf_curveVelocity_apply`:
  the velocity evaluates a coordinate function to the linear coefficient of its pullback.
* `TauCeti.Bialgebra.curveVelocity_mem_lieSubalgebra`: a curve in a closed subgroup has its
  velocity in the subgroup's Lie algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §15.
-/

public section

open Polynomial

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H]

section Velocity

variable [_root_.Bialgebra R H]

/-- The velocity at `t = 0` of a polynomial curve `γ` through the identity: the tangent vector
at the identity sending a coordinate function `h` to the coefficient of `t` in `γ h`. The
hypothesis says that `γ` passes through the identity at `t = 0`.

It is the derivation attached by `derivationToDualNumberEquivLift` to the dual-number point
obtained by substituting `t = ε` into `γ`. -/
noncomputable def curveVelocity (γ : H →ₐ[R] R[X])
    (hγ : (aeval (0 : R)).comp γ = Bialgebra.counitAlgHom R H) :
    Derivation R H (CounitAlgebra R H R) :=
  (derivationToDualNumberEquivLift R H (CounitAlgebra R H R)).symm
    ⟨(aeval DualNumber.eps).comp γ, AlgHom.ext fun h ↦ (DualNumber.fst_aeval_eps (γ h)).trans
      ((coeff_zero_eq_aeval_zero (γ h)).trans (DFunLike.congr_fun hγ h))⟩

/-- The velocity of a polynomial curve evaluates a coordinate function to the coefficient of
`t` in its pullback, read through the identification of the counit coefficient algebra with
`R`. -/
@[simp]
theorem curveVelocity_apply (γ : H →ₐ[R] R[X])
    (hγ : (aeval (0 : R)).comp γ = Bialgebra.counitAlgHom R H) (h : H) :
    curveVelocity γ hγ h = (γ h).coeff 1 :=
  (derivationToDualNumberEquivLift_symm_apply ..).trans (DualNumber.snd_aeval_eps (γ h))

/-- The velocity of a polynomial curve evaluates a coordinate function to the coefficient of
`t` in its pullback.

This is not a `simp` lemma: `CounitAlgebra.algEquivSelf_apply` already rewrites its left-hand
side. -/
theorem algEquivSelf_curveVelocity_apply (γ : H →ₐ[R] R[X])
    (hγ : (aeval (0 : R)).comp γ = Bialgebra.counitAlgHom R H) (h : H) :
    CounitAlgebra.algEquivSelf R H R (curveVelocity γ hγ h) = (γ h).coeff 1 := by
  rw [CounitAlgebra.algEquivSelf_apply, curveVelocity_apply]

end Velocity

/-- A polynomial curve through the identity which lies in the closed subgroup cut out by a
Hopf ideal `I` has its velocity in the Lie algebra of that subgroup. -/
theorem curveVelocity_mem_lieSubalgebra [HopfAlgebra R H] (γ : H →ₐ[R] R[X])
    (hγ : (aeval (0 : R)).comp γ = Bialgebra.counitAlgHom R H) (I : HopfIdeal R H)
    (hI : ∀ x ∈ I, γ x = 0) :
    curveVelocity γ hγ ∈ I.lieSubalgebra (B := R) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff]
  intro x hx
  apply (CounitAlgebra.algEquivSelf R H R).injective
  rw [algEquivSelf_curveVelocity_apply, hI x (HopfIdeal.mem_toIdeal.mp hx), coeff_zero,
    map_zero]

end TauCeti.Bialgebra
