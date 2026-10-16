/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.Integral
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.RootDatum

/-!
# The integral type-C weight torus in symplectic coordinates

The weight torus of the standard Kostant carrier uses fundamental-weight coordinates.
The standard symplectic diagonal torus uses the classical characters `εᵢ`. The integral
change of coordinates identifies these parametrized tori, and the carrier--symplectic
isomorphism intertwines their embeddings. Thus the comparison preserves the chosen torus
as a group-scheme morphism, including its parameters over rings with nilpotents.

The character change uses `Symplectic.characterEquiv`, and the represented
morphisms use `GeneralLinear.weightCharacterMap` and `Symplectic.diagonalTorus`.
The public ambient comparison `diagonalTorusCoordinateMap_comp_symplecticCharacters`
identifies the coordinate maps on matrix entries, using the public character map. The
scheme comparison then cancels the closed symplectic inclusion.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.SpStd

noncomputable section

variable (n : ℕ)

private def symplecticCharacterEquiv :
    (ULift (Fin (n + 1)) →₀ ℤ) ≃ₗ[ℤ] (Fin (n + 1) →₀ ℤ) :=
  (Symplectic.characterEquiv (n + 1)).symm.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm

private theorem symplecticCharacterEquiv_single (i : Fin (n + 1)) :
    symplecticCharacterEquiv n (Finsupp.single (ULift.up i) 1) =
      Finsupp.equivFunOnFinite.symm (DynkinType.TypeC.weight (n + 1) i) := by
  rw [symplecticCharacterEquiv, LinearEquiv.trans_apply,
    ← Symplectic.characterEquiv_weight, LinearEquiv.symm_apply_apply]
  rfl

private theorem weightCharacterMap_eq_symplecticCharacterEquiv :
    GeneralLinear.weightCharacterMap (fun i : Fin (n + 1) => DynkinType.TypeC.weight (n + 1) i) =
      (AddEquiv.toMultiplicative (symplecticCharacterEquiv n).toAddEquiv).toMonoidHom := by
  apply Multiplicative.monoidHom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  -- The additive and integral-linear wrappers reduce to evaluation of the character map.
  change (GeneralLinear.weightCharacterMap
    (fun i : Fin (n + 1) => DynkinType.TypeC.weight (n + 1) i)
      (Multiplicative.ofAdd (Finsupp.single i 1))).toAdd =
    symplecticCharacterEquiv n (Finsupp.single i 1)
  obtain ⟨i⟩ := i
  rw [GeneralLinear.weightCharacterMap_ofAdd_single, symplecticCharacterEquiv_single]
  rfl

private def symplecticCharacterIso :
    SplitTorus.characterGroup (ULift (Fin (n + 1))) ≅
      SplitTorus.characterGroup (Fin (n + 1)) where
  hom := FGCommGrpCat.ofHom
    (GeneralLinear.weightCharacterMap (fun i : Fin (n + 1) => DynkinType.TypeC.weight (n + 1) i))
  inv := FGCommGrpCat.ofHom
    (AddEquiv.toMultiplicative (symplecticCharacterEquiv n).symm.toAddEquiv).toMonoidHom
  hom_inv_id := by
    apply FGCommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    simp only [FGCommGrpCat.toMonoidHom_comp, FGCommGrpCat.toMonoidHom_ofHom,
      FGCommGrpCat.toMonoidHom_id, MonoidHom.comp_apply, MonoidHom.id_apply,
      weightCharacterMap_eq_symplecticCharacterEquiv, MulEquiv.coe_toMonoidHom]
    apply Multiplicative.toAdd.injective
    exact (symplecticCharacterEquiv n).symm_apply_apply x.toAdd
  inv_hom_id := by
    apply FGCommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    simp only [FGCommGrpCat.toMonoidHom_comp, FGCommGrpCat.toMonoidHom_ofHom,
      FGCommGrpCat.toMonoidHom_id, MonoidHom.comp_apply, MonoidHom.id_apply,
      weightCharacterMap_eq_symplecticCharacterEquiv, MulEquiv.coe_toMonoidHom]
    apply Multiplicative.toAdd.injective
    exact (symplecticCharacterEquiv n).apply_symm_apply x.toAdd

/-- The change from fundamental-weight parameters to classical diagonal parameters on the
rank-`n+1` split torus over any commutative ring. It sends `s` to `i ↦ εᵢ(s)`. -/
def symplecticTorusIso (R : Type) [CommRing R] :
    SplitTorus.groupScheme R (Fin (n + 1)) ≅
      SplitTorus.groupScheme R (ULift (Fin (n + 1))) where
  hom := DiagonalizableGroup.groupSchemeMap R (symplecticCharacterIso n).hom
  inv := DiagonalizableGroup.groupSchemeMap R (symplecticCharacterIso n).inv
  hom_inv_id := by
    rw [← DiagonalizableGroup.groupSchemeMap_comp, Iso.inv_hom_id,
      DiagonalizableGroup.groupSchemeMap_id]
  inv_hom_id := by
    rw [← DiagonalizableGroup.groupSchemeMap_comp, Iso.hom_inv_id,
      DiagonalizableGroup.groupSchemeMap_id]

/-- The torus comparison is the monomial morphism whose characters are the classical
type-C weights written in fundamental-weight coordinates. -/
theorem symplecticTorusIso_hom (R : Type) [CommRing R] :
    (symplecticTorusIso n R).hom =
      DiagonalizableGroup.groupSchemeMap R
        (FGCommGrpCat.ofHom
          (GeneralLinear.weightCharacterMap
            (fun i : Fin (n + 1) => DynkinType.TypeC.weight (n + 1) i))) := (rfl)

/-- On scheme-valued points, the change to classical parameters evaluates the characters
`εᵢ` on the original fundamental-weight parameters. -/
@[simp]
theorem schemePointsMulEquiv_symplecticTorusIso
    {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (Fin (n + 1))).X) (i : Fin (n + 1)) :
    SplitTorus.schemePointsMulEquiv
        (p ≫ (symplecticTorusIso n R).hom.hom.hom) (ULift.up i) =
      torusCharacter (SplitTorus.schemePointsMulEquiv p)
        (DynkinType.TypeC.weight (n + 1) i) := by
  rw [symplecticTorusIso_hom, SplitTorus.schemePointsMulEquiv_eq_freeAbelianCharEquiv,
    DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap, freeAbelianCharEquiv_apply,
    MonoidHom.comp_apply, FGCommGrpCat.toMonoidHom_ofHom,
    GeneralLinear.weightCharacterMap_ofAdd_single]
  have hweight :
      Multiplicative.ofAdd
          (Finsupp.equivFunOnFinite.symm (DynkinType.TypeC.weight (n + 1) i)) =
        SplitTorus.weightCharacter (DynkinType.TypeC.weight (n + 1) i) := by
    apply Multiplicative.toAdd.injective
    ext j
    simp
  rw [hweight, SplitTorus.apply_weightCharacter,
    ← SplitTorus.schemePointsMulEquiv_eq_freeAbelianCharEquiv]

/- Coordinate-map argument adapted from TauCetiProject/TauCeti#15715 (Codex):
https://github.com/TauCetiProject/TauCeti/pull/15715 -/
/-- On ambient matrix coordinates, the classical type-C characters written in fundamental-weight
coordinates recover the carrier weight-torus map. -/
theorem diagonalTorusCoordinateMap_comp_symplecticCharacters :
    Symplectic.coordinateMap ℤ (n + 1) ≫
        Symplectic.diagonalTorusCoordinateMap ≫
        (DiagonalizableGroup.coordinateMap ℤ
          (FGCommGrpCat.ofHom
            (GeneralLinear.weightCharacterMap
              (fun i : Fin (n + 1) => DynkinType.TypeC.weight (n + 1) i)))).hom =
      GeneralLinear.weightTorusCoordinateMap (basisWeight n) := by
  rw [← Category.assoc, Symplectic.coordinateMap_comp_diagonalTorusCoordinateMap]
  apply _root_.CommHopfAlgCat.hom_ext
  apply GeneralLinear.coordinateHopfAlgebra_bialgHom_ext
  intro i j
  rw [CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    GeneralLinear.weightTorusCoordinateMap_X, GeneralLinear.weightTorusCoordinateMap_X]
  split_ifs with hij
  · subst j
    -- The full-subcategory morphism and its bialgebra projection are definitionally equal.
    change FiniteTypeCommHopfAlgCat.toBialgHom
      (DiagonalizableGroup.coordinateMap ℤ
          (FGCommGrpCat.ofHom
            (GeneralLinear.weightCharacterMap
              (fun i : Fin (n + 1) => DynkinType.TypeC.weight (n + 1) i)))) _ = _
    rw [DiagonalizableGroup.toBialgHom_coordinateMap, MonoidAlgebra.mapDomainBialgHom_single]
    congr 1
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd,
        Symplectic.diagonalTorusWeight_inl, basisWeight_apply, weight_inl,
        Finsupp.equivFunOnFinite_symm_coe,
        FGCommGrpCat.toMonoidHom_ofHom]
      exact GeneralLinear.weightCharacterMap_ofAdd_single _ i
    · simp only [finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd,
        Symplectic.diagonalTorusWeight_inr, basisWeight_apply, weight_inr,
        Finsupp.equivFunOnFinite_symm_coe,
        FGCommGrpCat.toMonoidHom_ofHom]
      rw [ofAdd_neg, map_inv,
        GeneralLinear.weightCharacterMap_ofAdd_single, ← ofAdd_neg]
      apply congrArg Multiplicative.ofAdd
      ext j
      simp
  · simp

/-- The integral carrier--symplectic isomorphism identifies the parametrized weight torus
with the standard diagonal torus, after the integral change of torus coordinates. -/
@[reassoc (attr := simp)]
theorem weightTorus_comp_symplecticIso_hom :
    weightTorus n ≫ (symplecticIso n).hom =
      (symplecticTorusIso n ℤ).hom ≫ Symplectic.diagonalTorus := by
  apply (cancel_mono (Symplectic.inclusion ℤ (n + 1))).mp
  rw [Category.assoc, symplecticIso_hom_comp_inclusion, weightTorus_comp_carrierι,
    GeneralLinear.weightTorus_def, symplecticTorusIso_hom,
    DiagonalizableGroup.groupSchemeMap_def, Symplectic.diagonalTorus_def,
    Symplectic.inclusion_def]
  rw [← diagonalTorusCoordinateMap_comp_symplecticCharacters]
  simp [GeneralLinear.hopfIdealInclusion_def, Symplectic.coordinateMap_def,
    CommHopfAlgCat.quotientSpecι_def, op_comp, Functor.map_comp, Category.assoc]

end

end TauCeti.SpStd
