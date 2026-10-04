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
the defining subspace. This works for nonreduced value algebras and subgroup schemes, and gives
Chevalley's theorem in line form: the closed subgroup is the stabilizer, over every commutative
value algebra, of the line spanned by the top exterior power of the defining subspace in the
rational representation `⋀ᵈ V`.

## Main statements

* `TauCeti.Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff`: a point
  stabilizes the top exterior line of a subspace exactly when it stabilizes the subspace.
* `TauCeti.HopfIdeal.exists_finite_subcomodule_exteriorPower_line_stabilizer`: a closed subgroup
  with finitely generated ideal is the stabilizer of a line in a finite-dimensional
  representation.

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

/-- **Chevalley's theorem**, line form: a closed subgroup with finitely generated defining
ideal, in particular any closed subgroup of a finite-type affine group, is the stabilizer of a
line in a finite-dimensional representation. The representation is an exterior power of a
finite regular subcomodule, and one line works simultaneously over all commutative value
algebras, so the statement detects nonreduced subgroup schemes. -/
theorem exists_finite_subcomodule_exteriorPower_line_stabilizer (I : HopfIdeal k H)
    (hI : I.toIdeal.FG) :
    ∃ (V : Subcomodule k H H) (n : ℕ), Module.Finite k V.toSubmodule ∧
      letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
      ∃ L : Submodule k (⋀[k]^n V), Module.finrank k L = 1 ∧
        ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
          g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
            (L.baseChange A).map (Comodule.endOfPoint (⋀[k]^n V) g.ofConv) = L.baseChange A := by
  obtain ⟨V, hV, hgen⟩ := I.exists_finite_subcomodule_generating hI
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let W := I.definingSubspace V
  refine ⟨V, Module.finrank k W, hV, LinearMap.range (_root_.exteriorPower.map _ W.subtype),
    ?_, fun A g ↦ I.mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq
      V hgen A g⟩
  rw [exteriorPower.finrank_range_map W.injective_subtype, Nat.choose_self]

end TauCeti.HopfIdeal
