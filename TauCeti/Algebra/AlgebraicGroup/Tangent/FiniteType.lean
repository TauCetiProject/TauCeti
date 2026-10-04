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

The counit of a finite-type commutative bialgebra has finite cotangent space at the
identity over any commutative base ring. Over a field it is consequently finite-dimensional
and projective. This is the finiteness input for the scalar-extension description of the
tangent space and the adjoint representation.

## Main declarations

* `TauCeti.Bialgebra.instModuleFiniteCotangentSpace`: the specialization to the counit of a
  finite-type commutative bialgebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 14.
* Mathlib's `Algebra.FinitePresentation.ker_fG_of_surjective` supplies finite generation
  of the augmentation kernel in a polynomial presentation.
-/

public section

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The cotangent space at the identity of a finite-type commutative bialgebra is finite
over any commutative base ring. -/
instance instModuleFiniteCotangentSpace [Algebra.FiniteType R A] :
    Module.Finite R (CotangentSpace R A) := by
  obtain ⟨s, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (inferInstance : Algebra.FiniteType R A))
  let f := counitAlgHom R A
  have hf : Function.Surjective f := fun r ↦ ⟨algebraMap R A r, f.commutes r⟩
  have hfg := (Algebra.FinitePresentation.ker_fG_of_surjective (f.comp g) (hf.comp hg)).map
    g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom] at hfg
  rw [← Ideal.comap_comap,
    Ideal.map_comap_of_surjective (g : MvPolynomial s R →+* A) hg] at hfg
  exact AlgHom.finite_cotangent_ker_of_fg f hfg

end TauCeti.Bialgebra
