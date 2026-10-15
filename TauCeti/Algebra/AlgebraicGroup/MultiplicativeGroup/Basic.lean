/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# The multiplicative group example

This file records the functor-of-points calculation for the multiplicative group. Mathlib
already equips the Laurent polynomial algebra `R[T;T⁻¹]` with its Hopf algebra structure,
where `T n` is group-like and the antipode sends `T n` to `T (-n)`. We package the resulting
`R`-points of `Spec R[T;T⁻¹]`: for every commutative `R`-algebra `A`, convolution points
`R[T;T⁻¹] →ₐ[R] A` are multiplicatively equivalent to units of `A`.

The evaluation map and its inverse are supplied by `TauCeti.laurentEvalEquiv`, the universal
property of the Laurent polynomial algebra. Over commutative targets this is Mathlib's
`LaurentPolynomial.eval₂`, by `TauCeti.laurentEval_eq_eval₂`.

## Main declarations

* `TauCeti.MultiplicativeGroup.pointsMulEquiv`: the Laurent evaluation equivalence as a
  multiplicative equivalence from the convolution group to `Aˣ`.
* `TauCeti.MultiplicativeGroup.pointsMulEquiv_mapValue`: the points equivalence is natural
  in the value algebra.

## References

The Hopf algebra structure and Laurent polynomial evaluation API are from Mathlib's
`Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` and `Mathlib.Algebra.Polynomial.Laurent`,
building on Amelia Livingston's monoid-algebra Hopf algebra formalization.
-/

public section

open WithConv
open scoped LaurentPolynomial

namespace TauCeti

universe u v w

namespace MultiplicativeGroup

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The functor of points of the multiplicative group is the unit group of the value algebra.

The source is the convolution group of `R`-algebra maps out of `R[T;T⁻¹]`; the target is the
ordinary unit group of `A`. -/
noncomputable def pointsMulEquiv : WithConv (R[T;T⁻¹] →ₐ[R] A) ≃* Aˣ where
  __ := (WithConv.equiv _).trans laurentEvalEquiv.symm
  map_mul' f g := by
    ext
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, WithConv.equiv_apply,
      laurentEvalEquiv_symm_apply, Units.val_mul]
    rw [AlgHom.convMul_apply]
    simp

/-- The multiplicative equivalence sends a convolution point to its value on `T`. -/
@[simp]
theorem pointsMulEquiv_apply (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) f = laurentEvalEquiv.symm f.ofConv :=
  (rfl)

/-- The inverse multiplicative equivalence sends a unit to the corresponding point. -/
@[simp]
theorem pointsMulEquiv_symm_apply (u : Aˣ) :
    (pointsMulEquiv (R := R) (A := A)).symm u = toConv (laurentEval (R := R) u) := by
  simp [pointsMulEquiv]

section Naturality

variable {B : Type w} [CommSemiring B] [Algebra R B]

/-- The `𝔾ₘ` points equivalence is natural in the value algebra. -/
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B)
        (AlgHom.mapValue (H := R[T;T⁻¹]) φ f) =
      Units.map (φ : A →* B) (pointsMulEquiv f) := by
  simp [pointsMulEquiv_apply, AlgHom.mapValue_apply]

/-- Naturality of the inverse `𝔾ₘ` points equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (u : Aˣ) :
    AlgHom.mapValue (H := R[T;T⁻¹]) φ
        ((pointsMulEquiv (R := R) (A := A)).symm u) =
      (pointsMulEquiv (R := R) (A := B)).symm (Units.map (φ : A →* B) u) := by
  simp [pointsMulEquiv_symm_apply, AlgHom.mapValue_apply]

end Naturality


end MultiplicativeGroup

end TauCeti
