/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Nilpotent

/-!
# Nilpotence of the rational points of a unipotent group

Over an algebraically closed field, a reduced finite-type affine group whose rational points are
all unipotent is a closed subgroup of some upper-unitriangular group `U_n`. Precomposition with
the surjective coordinate map `O(U_n) → H` injects the rational points into those of `U_n`, which
form a nilpotent group, so the rational points of the group are nilpotent.

## Main declarations

* `TauCeti.HopfAlgebra.isNilpotent_points_of_forall_isUnipotentPoint`: the group of rational
  points of a reduced unipotent group over an algebraically closed field is nilpotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.21: a unipotent group is nilpotent.
* A. Borel, *Linear Algebraic Groups*, §4.8.
-/

public section

namespace TauCeti.HopfAlgebra

open WithConv

variable {k H : Type*} [Field k] [CommRing H] [_root_.HopfAlgebra k H]

/-- **The rational points of a unipotent group are nilpotent.** A reduced finite-type affine group
over an algebraically closed field whose rational points are all unipotent has a nilpotent group
of rational points. -/
theorem isNilpotent_points_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    Group.IsNilpotent (WithConv (H →ₐ[k] k)) := by
  obtain ⟨M, n, b, hb, hsurj⟩ :=
    Comodule.exists_coordinateBialgHom_surjective_of_forall_isUnipotentPoint hH
  let f := Comodule.upperUnitriangularCoordinateBialgHom (H := H) b hb
  have hf : Function.Surjective f :=
    Comodule.upperUnitriangularCoordinateBialgHom_surjective_of_coordinateBialgHom_surjective
      b hb hsurj
  have := UpperUnitriangular.isNilpotent_points k (Fin n) k
  let ι : WithConv (H →ₐ[k] k) →*
      WithConv (UpperUnitriangular.coordinateHopfAlgebra k (Fin n) →ₐ[k] k) :=
    BialgHom.mapDomain f
  refine Subgroup.isNilpotent_of_ker_le_center ι ?_
  rw [(MonoidHom.ker_eq_bot_iff ι).mpr (BialgHom.mapDomain_injective_of_surjective f hf)]
  exact bot_le

end TauCeti.HopfAlgebra
