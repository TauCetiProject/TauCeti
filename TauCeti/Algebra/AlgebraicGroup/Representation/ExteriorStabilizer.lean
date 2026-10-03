/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SubspaceStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.TopSubspace

/-!
# Exterior-line detection of closed subgroups

A finite-dimensional regular subcomodule containing generators of a closed subgroup's
ideal realizes that subgroup as a subspace stabilizer. Applying the top-exterior-line
criterion identifies its points, over every commutative value algebra `A`, with the
stabilizer of a line in the exterior algebra of the scalar-extended representation.
This works for nonreduced value algebras and subgroup schemes.

The result concerns the exterior algebra over `A` of `A ⊗ V`, not the scalar extension
of a single finite-dimensional exterior comodule. Compatibility of the exterior point action
with scalar extension transports this criterion to a rational line-stabilizer statement.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
-/

public section

open scoped TensorProduct
open CategoryTheory

namespace TauCeti.HopfIdeal

universe u v w

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

/-- A finite regular subcomodule containing ideal generators detects subgroup membership by
stabilization of the top exterior line of its defining subspace, over every value algebra. -/
theorem mem_quotientPointsSubgroup_iff_map_topExteriorLine_eq
    (I : HopfIdeal k H) (V : Subcomodule k H H) [Module.Finite k V]
    (hgen : I.toIdeal ≤ Ideal.span ((V : Set H) ∩ (I : Set H)))
    (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
      ((((I.definingSubspace V).baseChange A).map (ExteriorAlgebra.ι A)) ^
          Module.finrank k (I.definingSubspace V)).map
        (ExteriorAlgebra.map (Comodule.pointsAction V g).toLinearMap).toLinearMap =
      (((I.definingSubspace V).baseChange A).map (ExteriorAlgebra.ι A)) ^
        Module.finrank k (I.definingSubspace V) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  rw [Submodule.map_topExteriorLine_baseChange_eq_iff,
    Comodule.pointsAction_toLinearMap]
  exact I.mem_quotientPointsSubgroup_iff_map_definingSubspace_eq V hgen A g

/-- For every finitely generated subgroup ideal, one finite regular subcomodule gives an
exterior-line stabilizer criterion simultaneously over all commutative value algebras. -/
theorem exists_finite_subcomodule_exterior_stabilizer (I : HopfIdeal k H) (hI : I.toIdeal.FG) :
    ∃ V : Subcomodule k H H, Module.Finite k V.toSubmodule ∧
      letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
      ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
        g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
          ((((I.definingSubspace V).baseChange A).map (ExteriorAlgebra.ι A)) ^
              Module.finrank k (I.definingSubspace V)).map
            (ExteriorAlgebra.map (Comodule.pointsAction V g).toLinearMap).toLinearMap =
          (((I.definingSubspace V).baseChange A).map (ExteriorAlgebra.ι A)) ^
            Module.finrank k (I.definingSubspace V) := by
  obtain ⟨V, hV, hgen⟩ := I.exists_finite_subcomodule_generating hI
  let : Module.Finite k V := hV
  exact ⟨V, hV, fun A g ↦ I.mem_quotientPointsSubgroup_iff_map_topExteriorLine_eq V hgen A g⟩

end TauCeti.HopfIdeal
