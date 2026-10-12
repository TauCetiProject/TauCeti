/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SubspaceStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.TopSubspace
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.BaseChange

/-!
# Exterior-line detection of closed subgroups

A finite-dimensional regular subcomodule containing generators of a closed subgroup's
ideal realizes that subgroup as a subspace stabilizer. Over every commutative value algebra `A`,
the top-exterior-line criterion in the exterior algebra over `A` of `A ⊗ V`, together with
compatibility of the exterior point action with scalar extension, turns this into the stabilizer
of a line in the finite-dimensional exterior-power comodule `⋀ᵈ V`, where `d` is the dimension of
the defining subspace. This works for nonreduced value algebras and subgroup schemes. The
existence of a stabilizing line, together with its unique subgroup character, is proved in
`TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character`.

## Main statements

* `TauCeti.Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff`: a point
  stabilizes the top exterior line of a subspace exactly when it stabilizes the subspace.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
-/

public section

open scoped TensorProduct
open CategoryTheory

universe u v w

namespace TauCeti.Comodule

variable {k : Type u} [Field k] {H : Type v} [CommSemiring H] [HopfAlgebra k H]
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]

attribute [local instance] exteriorPower

/-- Over a field, a point stabilizes the scalar extension of the top exterior line of a subspace
`W` of a finite-dimensional representation `V` exactly when it stabilizes the scalar extension of
`W`. The line is the image of `⋀ᵈ W` in the representation `⋀ᵈ V`, where `d = dim W`. This holds
over every commutative value algebra, including nonreduced ones. -/
theorem map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff (W : Submodule k V)
    (A : Type*) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    ((LinearMap.range (_root_.exteriorPower.map (Module.finrank k W) W.subtype)).baseChange A).map
        (endOfPoint (⋀[k]^(Module.finrank k W) V) g.ofConv) =
      (LinearMap.range (_root_.exteriorPower.map (Module.finrank k W) W.subtype)).baseChange A ↔
    (W.baseChange A).map (endOfPoint V g.ofConv) = W.baseChange A := by
  rw [map_endOfPoint_baseChange_range_exteriorPowerMap_eq_iff, ← pointsAction_toLinearMap,
    Submodule.map_topExteriorLine_baseChange_eq_iff]

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

attribute [local instance] Comodule.exteriorPower

/-- A finite regular subcomodule containing ideal generators realizes the closed subgroup as
the stabilizer of a line: the image of the top exterior power of the defining subspace in the
corresponding exterior power of the subcomodule. This holds over every value algebra. -/
theorem mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq
    (I : HopfIdeal k H) (V : Subcomodule k H H) [Module.Finite k V]
    (hgen : I.toIdeal ≤ Ideal.span ((V : Set H) ∩ (I : Set H)))
    (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
      ((LinearMap.range (_root_.exteriorPower.map (Module.finrank k (I.definingSubspace V))
          (I.definingSubspace V).subtype)).baseChange A).map
        (Comodule.endOfPoint (⋀[k]^(Module.finrank k (I.definingSubspace V)) V) g.ofConv) =
      (LinearMap.range (_root_.exteriorPower.map (Module.finrank k (I.definingSubspace V))
          (I.definingSubspace V).subtype)).baseChange A := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  rw [Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff]
  exact I.mem_quotientPointsSubgroup_iff_map_definingSubspace_eq V hgen A g

end TauCeti.HopfIdeal
