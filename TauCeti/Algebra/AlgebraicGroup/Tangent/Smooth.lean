/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.RingTheory.Ideal.Cotangent.Smooth

/-!
# Finite projective cotangent spaces of smooth affine monoids

The cotangent space at the identity of a smooth affine monoid is finite projective over
any commutative base ring. More precisely, finite type supplies finiteness, and
formal smoothness supplies projectivity; the hypotheses are kept separate. No
noetherianity or reducedness is assumed.

For a smooth affine group these instances provide the input to
`Derivation.tangentScalarExtensionEquiv` and `Derivation.adjointComodule`: its Lie algebra
is the dual of the augmentation cotangent space, and its algebra-valued tangent spaces
are scalar extensions of that one module. In particular, the adjoint weight-space API
applies to smooth groups over `ℤ`, such as the special linear group.

## References

* B. Conrad, *Reductive Group Schemes*, §3.1.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The augmentation cotangent space of a formally smooth affine monoid is projective
over the base. No finite-type or noetherian hypothesis is needed. -/
instance instModuleProjectiveCotangentSpaceOfFormallySmooth
    [Algebra.FormallySmooth R A] : Module.Projective R (CotangentSpace R A) :=
  _root_.AlgHom.projective_cotangent_ker_of_formallySmooth (counitAlgHom R A)

end TauCeti.Bialgebra
