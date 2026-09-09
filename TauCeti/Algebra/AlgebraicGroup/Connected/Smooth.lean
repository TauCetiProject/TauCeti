/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.RingTheory.Idempotents.Connected.Etale

/-!
# Smoothness of the identity component

Over an algebraically closed field, the identity-component coordinate algebra is étale
over the ambient finite-type Hopf algebra. Consequently the identity component of a smooth
affine group is smooth. Smoothness of the ambient group is an explicit hypothesis; the
étale inclusion itself also applies to non-smooth group schemes.

In particular this supplies smoothness of the identity component of a reduced center,
once the reduced center has been shown smooth. Together with geometric connectedness,
this allows semisimplicity to trivialize that central subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
* The Stacks Project, Section 10.143, Étale ring maps.
-/

public section

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The identity-component inclusion is étale in coordinate algebras. -/
instance etale_identityComponent (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Algebra.Etale H (identityComponent H) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  -- The bundled Hopf quotient has the ordinary ideal quotient as its coordinate algebra.
  change Algebra.Etale H
    (H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal)
  rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal]
  exact etale_quotient_connectedComponentIdeal (Bialgebra.augmentationPoint k H)

/-- The identity component of a smooth finite-type affine group is smooth. -/
instance smooth_identityComponent (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Algebra.Smooth k H] : Algebra.Smooth k (identityComponent H) :=
  Algebra.Smooth.comp k H (identityComponent H)

end TauCeti.FiniteTypeCommHopfAlgCat
