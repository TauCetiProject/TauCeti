/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Torsion
import TauCeti.Algebra.Group.Equiv.Pow

/-!
# Detecting tori by geometric characters

A group of multiplicative type is a torus exactly when its geometric character group is
torsion-free. The criterion also applies to any chosen diagonalizable presentation over the
algebraic closure. No perfectness assumption on the ground field is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.d.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- In a diagonalizable presentation over the algebraic closure, a group is a torus
exactly when the presenting character group is torsion-free. -/
theorem torus_iff_isMulTorsionFree_of_baseChange_iso_coordinateRing
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    torusCommHopfAlgProperty k H ↔ IsMulTorsionFree G := by
  constructor
  · intro hH
    exact (CommHopfAlgCat.geometricCharacterGroupEquivOfIso k H G i).isMulTorsionFree_iff.mp
      (CommHopfAlgCat.isMulTorsionFree_geometricCharacterGroup H.obj
        (hH.geometricallyReduced k H) (hH.geometricallyConnected k H))
  · intro hG
    obtain ⟨n, ⟨j⟩⟩ := (splitTorusCommHopfAlgProperty_iff _ _).mp
      (splitTorusCommHopfAlgProperty_coordinateRing (AlgebraicClosure k) G)
    exact (torusCommHopfAlgProperty_iff k H).mpr ⟨n, ⟨j ≪≫ i⟩⟩

/-- A group of multiplicative type is a torus exactly when its geometric character group
is torsion-free. This distinguishes tori from both finite étale and infinitesimal factors. -/
theorem multiplicativeTypeCommHopfAlgProperty.torus_iff_isMulTorsionFree_geometricCharacterGroup
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    torusCommHopfAlgProperty k H ↔
      IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup H.obj) := by
  obtain ⟨G, ⟨i⟩⟩ :=
    (multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing k H).mp hH
  exact (torus_iff_isMulTorsionFree_of_baseChange_iso_coordinateRing G i).trans
    (CommHopfAlgCat.geometricCharacterGroupEquivOfIso k H G i).isMulTorsionFree_iff.symm

end TauCeti
