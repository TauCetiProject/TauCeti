/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Tangent
public import TauCeti.Algebra.Lie.GeneralLinear.Borel

/-!
# Solvability of the upper triangular tangent Lie algebra

The Lie algebra of the upper triangular general linear group is solvable over every
commutative coefficient ring. The tangent-image criterion identifies its image inside the
ambient general-linear Lie algebra with upper triangular matrices, so root-space containment
can be tested in matrix coordinates. The weight-parabolic tangent equivalence also identifies
the subgroup's own Lie algebra with these matrices. This lets solvability pass to the Lie
algebra of a group embedded in the upper triangular group, as in the Lie--Kolchin theorem.

The identification uses `GeneralLinear.weightParabolicTangentLieEquiv` with the standard
strictly decreasing weights, and solvability is `TauCeti.isSolvable_upperTriangular`.
-/

public section

namespace TauCeti.GeneralLinear.UpperTriangular

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

/-- A tangent vector lies in the upper-triangular subgroup exactly when its matrix is
upper triangular, over any coefficient algebra. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff {n : ℕ}
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) ↔
      tangentMatrix n d ∈ TauCeti.upperTriangular B (Fin n) := by
  rw [definingHopfIdeal, mem_lieSubalgebra_weightParabolicDefiningHopfIdeal_iff,
    TauCeti.mem_upperTriangular_iff]
  simp only [Matrix.BlockTriangular, Function.comp_apply, OrderDual.toDual_lt_toDual,
    weights_lt_weights_iff]

/-- The coefficient-valued tangent Lie algebra of the upper triangular general linear group
is solvable over every commutative coefficient ring. -/
instance isSolvable_tangentLieAlgebra (n : ℕ) :
    LieAlgebra.IsSolvable
      (Derivation R (coordinateHopfAlgebra R n)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) := by
  let e := GeneralLinear.weightParabolicTangentLieEquiv (R := R) (B := B) (weights n)
  let f := (LieSubalgebra.incl _).comp e.toLieHom
  have hmem (d) : f d ∈ TauCeti.upperTriangular B (Fin n) := by
    rw [TauCeti.mem_upperTriangular_iff]
    intro i j hij
    exact (e d).property ((weights_lt_weights_iff n i j).mpr hij)
  let g : _ →ₗ⁅B⁆ TauCeti.upperTriangular B (Fin n) :=
    { f.toLinearMap.codRestrict (TauCeti.upperTriangular B (Fin n)).toSubmodule hmem with
      map_lie' := by
        intros
        apply Subtype.ext
        exact f.map_lie _ _ }
  have hg : Function.Injective g := by
    intro d d' h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun x : TauCeti.upperTriangular B (Fin n) ↦
      (x : Matrix (Fin n) (Fin n) B)) h
  exact Function.Injective.lieAlgebra_isSolvable (R := B) (f := g) hg

end TauCeti.GeneralLinear.UpperTriangular
