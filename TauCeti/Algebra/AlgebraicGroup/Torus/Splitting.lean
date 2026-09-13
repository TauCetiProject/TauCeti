/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import Mathlib.Algebra.AffineMonoid.UniqueSums
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange

/-!
# Recognising a torus from a splitting field

A torus is defined by becoming a finite-rank split torus over an algebraic closure of the base
field. In practice a torus is produced together with a splitting field that is much smaller: a
finite Galois extension over which the coordinate Hopf algebra becomes a group algebra. This file
converts such data into the definition.

Concretely, if `L / k` is algebraic and `L ⊗[k] H` is the coordinate Hopf algebra of a
diagonalizable group whose character group is torsion-free, then `H` is a torus over `k`.

## Main declaration

* `TauCeti.torusCommHopfAlgProperty.of_baseChange_iso_coordinateRing`: a finite-type commutative
  Hopf algebra that becomes a torsion-free diagonalizable coordinate ring over an algebraic
  extension is a torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.17 and Theorem 12.23.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace torusCommHopfAlgProperty

/-- **A finite-type commutative Hopf algebra that becomes a torsion-free diagonalizable
coordinate ring over an algebraic extension is a torus.**

Torsion freeness of the character group `G` distinguishes tori among the groups of multiplicative
type; finite generation then supplies the unique-product property used to prove connectedness and
reducedness. -/
theorem of_baseChange_iso_coordinateRing
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (G : FGCommGrpCat.{u}) [IsMulTorsionFree G]
    (i : FiniteTypeCommHopfAlgCat.baseChange (K := L) H ≅
      DiagonalizableGroup.coordinateRing L G) :
    torusCommHopfAlgProperty k H := by
  let _ : Algebra L (AlgebraicClosure k) :=
    (IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)).toAlgebra
  have : IsScalarTower k L (AlgebraicClosure k) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)).commutes x |>.symm
  let _ : UniqueProds G := inferInstance
  -- Push the given splitting along an embedding of `L` into the algebraic closure of `k`.
  let j : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H :=
    ((DiagonalizableGroup.baseChangeCoordinateRingIso L (AlgebraicClosure k) G).symm ≪≫
      (FiniteTypeCommHopfAlgCat.baseChangeFunctor
        (K := AlgebraicClosure k)).mapIso i.symm) ≪≫
      ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso k (AlgebraicClosure k) H.obj)
  let j' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
    (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso j
  refine (iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced k H).2
    ⟨(multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing k H).2 ⟨G, ⟨j⟩⟩,
      ?_, ?_⟩
  · exact geometricallyConnectedCommHopfAlgProperty.of_baseChange k (AlgebraicClosure k) H.obj
      ((geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso j'
        (DiagonalizableGroup.geometricallyConnected_coordinateRing (AlgebraicClosure k) G))
  · exact geometricallyReducedCommHopfAlgProperty.of_baseChange (AlgebraicClosure k) H.obj
      ((geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso j'
        (DiagonalizableGroup.geometricallyReduced_coordinateRing (AlgebraicClosure k) G))

end torusCommHopfAlgProperty

end TauCeti
