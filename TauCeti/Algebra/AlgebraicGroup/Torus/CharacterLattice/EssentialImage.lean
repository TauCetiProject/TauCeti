/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Functoriality
import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Torus
import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.GeometricCharacter
import TauCeti.RepresentationTheory.GaloisLattice.SeparableActionField

/-!
# Every Galois lattice is the character lattice of a torus

A continuous finite free integral representation of the absolute Galois group factors
through a finite Galois extension. Descending the group algebra along that extension
produces a torus. Its geometric characters recover the given representation, including
the absolute-Galois action. Thus the character-lattice functor is essentially surjective
over every field, including imperfect fields.

The finite extension is `GaloisLatticeCat.separableActionField`; the torus and its
character comparison use the invariant group-algebra constructions of `GaloisDescent`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

variable {k : Type u} [Field k]

/-- Every continuous integral Galois lattice occurs as the geometric character lattice
of a torus. This is the essential-surjectivity half of the classification of tori. -/
noncomputable instance TorusCommHopfAlgCat.characterLatticeFunctor_essSurj :
    (TorusCommHopfAlgCat.characterLatticeFunctor (k := k)).EssSurj where
  mem_essImage M := by
    -- Integral module structures are unique. Normalize the stored structure so the
    -- representation and the group-algebra construction use the same integer action.
    rcases M with ⟨@⟨V, hV1, hV2, r⟩, hM⟩
    have hmod : hV2 = AddCommGroup.toIntModule V := Subsingleton.elim _ _
    subst hV2
    let M : GaloisLatticeCat k := ⟨Rep.of r, hM⟩
    let _ : Module.Free ℤ M.obj := GaloisLatticeCat.instModuleFree k M
    let _ : Module.Finite ℤ M.obj := GaloisLatticeCat.instModuleFinite k M
    let _ : IsAddTorsionFree M.obj := IsAddTorsionFree.of_isTorsionFree ℤ M.obj
    let L := GaloisLatticeCat.separableActionField M
    let ρ : Representation ℤ (L ≃ₐ[k] L) M.obj :=
      GaloisLatticeCat.separableActionFieldRepresentation M
    let T : TorusCommHopfAlgCat k :=
      ⟨GaloisDescent.descendedCoordinateRing (k := k) (L := L) ρ,
        GaloisDescent.torusCommHopfAlgProperty_descendedCoordinateRing (k := k) (L := L) ρ⟩
    let e : CommHopfAlgCat.additiveCharacterGroup T.obj.obj ≃ₗ[ℤ] M.obj :=
      ((GaloisDescent.groupAlgebraInvariantsGeometricCharacterEquiv
        (K := AlgebraicClosure k) ρ).toAdditive.trans
          (AddEquiv.additiveMultiplicative M.obj)).toIntLinearEquiv
    have he (σ : Field.absoluteGaloisGroup k)
        (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
        e (σ • x) = M.obj.ρ σ (e x) := by
      let σ' : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := σ
      have hστ (a : L) :
          σ' (algebraMap L _ a) =
            algebraMap L _ (GaloisLatticeCat.separableActionFieldRestriction M σ a) :=
        (GaloisLatticeCat.separableActionFieldRestriction_apply M σ a).symm
      have h := GaloisDescent.groupAlgebraInvariantsGeometricCharacterEquiv_smul
        (K := AlgebraicClosure k) ρ σ'
        (GaloisLatticeCat.separableActionFieldRestriction M σ) hστ x.toMul
      have h' := congrArg Multiplicative.toAdd h
      -- The additive character representation uses the same action with type tags.
      change e (σ • x) = ρ (GaloisLatticeCat.separableActionFieldRestriction M σ) (e x)
        at h'
      rw [GaloisLatticeCat.separableActionFieldRepresentation_restrict_apply] at h'
      exact h'
    let er : (CommHopfAlgCat.geometricCharacterRepresentation T.obj.obj).ρ.Equiv M.obj.ρ :=
      Representation.Equiv.mk e fun σ ↦ by
        ext x
        exact (congrArg e
          (CommHopfAlgCat.geometricCharacterRepresentation_ρ_apply T.obj.obj σ x)).trans
            (he σ x)
    refine ⟨T, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact eqToIso (TorusCommHopfAlgCat.characterLatticeFunctor_obj_obj T) ≪≫ Rep.mkIso er

end TauCeti
