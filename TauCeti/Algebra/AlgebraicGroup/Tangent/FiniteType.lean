/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.RingTheory.Ideal.Cotangent.Basic

/-!
# Finiteness of the tangent space of a finite-type affine monoid

The counit of a finitely presented commutative bialgebra has finite cotangent space at the
identity over any commutative base ring. The same holds for a finite-type bialgebra over a
noetherian base. Over a field it is consequently finite-dimensional and projective. This is
the finiteness input for the scalar-extension description of the tangent space and the adjoint
representation.

## Main declarations

* `TauCeti.Bialgebra.instModuleFiniteCotangentSpace`: the specialization to the counit of a
  finite-type commutative bialgebra.
* `TauCeti.Bialgebra.instModuleFiniteCotangentSpaceOfFinitePresentation`: finiteness over
  arbitrary bases for finitely presented bialgebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 14.
-/

public section

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The augmentation cotangent space of a finitely presented affine monoid is finite
over the base, without a noetherian hypothesis. -/
instance instModuleFiniteCotangentSpaceOfFinitePresentation
    [Algebra.FinitePresentation R A] : Module.Finite R (CotangentSpace R A) :=
  TauCeti.AlgHom.finite_cotangent_ker_of_fg (counitAlgHom R A)
    (Algebra.FinitePresentation.ker_fG_of_surjective (counitAlgHom R A)
      (fun r ↦ ⟨algebraMap R A r, (counitAlgHom R A).commutes r⟩))

/-- The cotangent space at the identity of a finite-type commutative bialgebra over a noetherian
base is finite over that base. -/
instance instModuleFiniteCotangentSpace [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Module.Finite R (CotangentSpace R A) := by
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact AlgHom.finite_cotangent_ker (counitAlgHom R A)

end TauCeti.Bialgebra
