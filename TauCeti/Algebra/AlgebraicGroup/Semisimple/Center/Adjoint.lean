/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.RepresentableQuotient
public import TauCeti.Algebra.AlgebraicGroup.Adjoint.Basic
import TauCeti.Algebra.AlgebraicGroup.Isogeny.FiniteCenter

/-!
# The adjoint center quotient in characteristic zero

The represented quotient of a semisimple affine group by its full scheme-theoretic center
is adjoint in characteristic zero. Its semisimplicity and its presentation as the fppf
center quotient are already established in `Semisimple.Center.RepresentableQuotient`.
Here the inverse image of its finite center is a finite normal subgroup of the original
connected group, hence central by Cartier's theorem and finite-normal-subgroup centrality.
Since the quotient kills the entire original center, its own center is trivial.

This gives the adjoint form together with the existing canonical central-isogeny projection;
it does not require a split torus or a choice of root datum.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, adjoint groups and central isogenies.
-/

public section

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The represented quotient of a semisimple affine group by its center is an adjoint
semisimple group in characteristic zero, over an arbitrary ground field. -/
theorem adjointSemisimple_centerQuotient (hH : semisimpleCommHopfAlgProperty k H) :
    adjointSemisimpleCommHopfAlgProperty k
      ⟨hH.reductive.centerQuotient, hH.semisimple_centerQuotient⟩ := by
  let _ : Module.Finite k
      (CommHopfAlgCat.centerCoordinateHopfAlgebra hH.reductive.centerQuotient.obj) :=
    hH.semisimple_centerQuotient.moduleFinite_centerCoordinate
  apply (adjointSemisimpleCommHopfAlgProperty_iff _).mpr
  exact CommHopfAlgCat.IsIsogeny.centerDefiningIdeal_eq_augmentation_of_kernel_eq_center
    hH.isCentralIsogeny_centerQuotientι.isIsogeny hH.geometricallyConnected
    hH.reductive.kernelHopfIdeal_centerQuotientι_eq

end TauCeti.semisimpleCommHopfAlgProperty
