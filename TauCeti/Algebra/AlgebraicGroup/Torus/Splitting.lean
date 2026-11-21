/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

/-!
# Recognising a torus from a splitting field

A torus is defined by becoming a finite-rank split torus over an algebraic closure of the base
field. In practice a torus is produced together with a splitting field that is much smaller: a
finite Galois extension over which the coordinate Hopf algebra becomes a group algebra. This file
converts such data into the definition.

Concretely, if `L / k` is algebraic and `L ⊗[k] H` is a split torus, then `H` is a torus
over `k`.

## Main declaration

* `TauCeti.torusCommHopfAlgProperty.of_baseChange`: a finite-type commutative Hopf algebra that
  becomes a split torus over an algebraic extension is a torus.
* `TauCeti.torusCommHopfAlgProperty.of_baseChange_iso_coordinateRing`: the corresponding
  coordinate-ring criterion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.17 and Theorem 12.23.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace torusCommHopfAlgProperty

/-- **A finite-type commutative Hopf algebra that becomes a split torus over an algebraic
extension is a torus.** -/
theorem of_baseChange
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : splitTorusCommHopfAlgProperty L
      (FiniteTypeCommHopfAlgCat.baseChange (K := L) H)) :
    torusCommHopfAlgProperty k H := by
  let _ : Algebra L (AlgebraicClosure k) :=
    (IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)).toAlgebra
  have : IsScalarTower k L (AlgebraicClosure k) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)).commutes x |>.symm
  -- Push the given splitting along an embedding of `L` into the algebraic closure of `k`.
  rw [torusCommHopfAlgProperty_iff, ← splitTorusCommHopfAlgProperty_iff]
  exact (splitTorusCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := L) k (AlgebraicClosure k) H)
    (hH.baseChange (AlgebraicClosure k))

/-- **A finite-type commutative Hopf algebra that becomes a torsion-free diagonalizable
coordinate ring over an algebraic extension is a torus.**

Torsion freeness of the character group `G` distinguishes tori among the groups of multiplicative
type; finite generation then supplies the split-torus property. -/
theorem of_baseChange_iso_coordinateRing
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (G : FGCommGrpCat.{u}) [IsMulTorsionFree G]
    (i : FiniteTypeCommHopfAlgCat.baseChange (K := L) H ≅
      DiagonalizableGroup.coordinateRing L G) :
    torusCommHopfAlgProperty k H :=
  of_baseChange k L H <|
    (splitTorusCommHopfAlgProperty L).prop_of_iso i.symm
      (splitTorusCommHopfAlgProperty_coordinateRing L G)

end torusCommHopfAlgProperty

end TauCeti
