/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

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

/-- The geometric character group of a torus has no nontrivial torsion. -/
theorem torusCommHopfAlgProperty.isMulTorsionFree_geometricCharacterGroup
    (hH : torusCommHopfAlgProperty k H) :
    IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup H.obj) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_characterLattice_addEquiv_of_torus k H hH
  exact Function.Injective.isMulTorsionFree
    (AddEquiv.toMultiplicative e).toMonoidHom (AddEquiv.toMultiplicative e).injective

/-- In a diagonalizable presentation over the algebraic closure, a group is a torus
exactly when the presenting character group is torsion-free. -/
theorem torus_iff_isMulTorsionFree_of_baseChange_iso_coordinateRing
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    torusCommHopfAlgProperty k H ↔ IsMulTorsionFree G := by
  constructor
  · intro hH
    let _ := hH.isMulTorsionFree_geometricCharacterGroup
    let e := CommHopfAlgCat.geometricCharacterGroupEquivOfIso k H G i
    exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective
  · intro hG
    let _ := hG
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
  let e := CommHopfAlgCat.geometricCharacterGroupEquivOfIso k H G i
  rw [torus_iff_isMulTorsionFree_of_baseChange_iso_coordinateRing G i]
  constructor
  · intro hG
    let _ := hG
    exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective
  · intro hG
    let _ := hG
    exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

end TauCeti
