/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Generic

/-!
# Generic flatness of projective orbit morphisms

For a reduced finite-type affine group over an algebraically closed field, the morphism
onto the projective orbit of a line is flat over a dense open of the orbit scheme.
Its restrictions are already surjective and locally of finite presentation, so this
gives an fppf cover over that open. The flatness statement concerns all scheme points,
rather than only rational points or reduced fibres.

This supplies the initial open set for the translation argument proving faithful
flatness of the whole orbit morphism. The reducedness assumption makes the orbit scheme
reduced, as required by generic flatness; no connectedness or characteristic assumption
is imposed.

The application uses `Scheme.Hom.exists_dense_open_flat` and the locally closed
scheme-theoretic image construction `Comodule.projectiveOrbitScheme`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
* The Stacks Project, Tag 0529, generic flatness.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [_root_.IsReduced H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The morphism onto the projective orbit scheme of a reduced finite-type affine group
is flat over a dense open subset of the orbit scheme. -/
theorem exists_dense_open_flat_toProjectiveOrbit (m : M) (hm : Module.IsUnimodular k m) :
    ∃ U : (projectiveOrbitScheme (H := H) m hm).Opens,
      Dense (U : Set (projectiveOrbitScheme (H := H) m hm)) ∧
        Flat (toProjectiveOrbit (H := H) m hm ∣_ U) := by
  have := Algebra.FiniteType.isNoetherianRing k H
  exact Scheme.Hom.exists_dense_open_flat (toProjectiveOrbit (H := H) m hm)

end TauCeti.Comodule
