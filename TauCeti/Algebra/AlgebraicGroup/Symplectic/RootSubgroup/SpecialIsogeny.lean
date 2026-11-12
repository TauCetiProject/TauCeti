/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.SpecialIsogeny
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Frobenius

/-!
# Simple root equations for the exceptional isogeny of Sp₄

The exceptional isogeny in characteristic two exchanges the short and long simple root
subgroups. On the short root parameter it applies Frobenius; on the long root parameter it
acts identically. The same formulas hold for the negative simple roots.

This file proves these identities for coordinate Hopf-algebra morphisms and group-scheme
morphisms over `𝔽₂`. In particular they retain the infinitesimal information in the
Frobenius factor and hold on nonreduced value algebras. The simple roots are `e₀ - e₁`
and `2e₁` in the paired diagonal coordinates of the standard symplectic pinning.

The matrix identities are `TauCeti.specialIsogeny_differenceShortRootUnit` and its three
signed counterparts. We evaluate them on the universal additive-group point to obtain
the coordinate identities, and then apply relative spectrum.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.Symplectic

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "U" => AdditiveGroup.coordinateHopfAlgebra 𝔽₂

local instance : CharP (SymmetricAlgebra 𝔽₂ 𝔽₂) 2 :=
  charP_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := 𝔽₂) _) 2

private theorem specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_of_hom
    (a b : GLSymplecticFin.RootSubgroupIndex 2) (f : CommHopfAlgCat.of 𝔽₂ U ⟶
      CommHopfAlgCat.of 𝔽₂ U)
    (h : TauCeti.specialIsogeny (a.hom (Multiplicative.ofAdd (SymmetricAlgebra.ι 𝔽₂ 𝔽₂ 1))) =
      b.hom (Multiplicative.ofAdd (f.hom (SymmetricAlgebra.ι 𝔽₂ 𝔽₂ 1)))) :
    specialIsogenyCoordinateMap ≫ rootSubgroupCoordinateMap a =
      rootSubgroupCoordinateMap b ≫ f := by
  let q : HopfAlgebra.points (H := U) (CommAlgCat.of 𝔽₂ U) := toConv (AlgHom.id 𝔽₂ U)
  have hroot (r : GLSymplecticFin.RootSubgroupIndex 2)
      (p : HopfAlgebra.points (H := U) (CommAlgCat.of 𝔽₂ U)) :
      BialgHom.mapDomain (rootSubgroupCoordinateMap (R := 𝔽₂) r).hom p =
        rootSubgroupPoints r p := by
    have hr := mapPointsFunctor_rootSubgroupCoordinateMap_app r (CommAlgCat.of 𝔽₂ U) p
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hr
    rw [BialgHom.mapDomain_apply]
    exact hr
  have hp : BialgHom.mapDomain specialIsogenyCoordinateMap.hom
        (BialgHom.mapDomain (rootSubgroupCoordinateMap a).hom q) =
      BialgHom.mapDomain (rootSubgroupCoordinateMap b).hom (BialgHom.mapDomain f.hom q) := by
    apply (pointsMulEquiv (R := 𝔽₂) (A := U) 2).injective
    rw [pointsMulEquiv_mapDomain_specialIsogenyCoordinateMap, hroot, hroot,
      pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv q),
      ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv (BialgHom.mapDomain f.hom q))]
    simpa only [AdditiveGroup.toAdd_gaPointsMulEquiv, q, ofConv_toConv,
      AlgHom.id_apply, BialgHom.mapDomain_apply_apply] using h
  apply CommHopfAlgCat.hom_ext
  ext x
  have hx := congrArg (fun p => p.ofConv x) hp
  simpa only [BialgHom.mapDomain_apply_apply, q, ofConv_toConv, AlgHom.id_apply,
    CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using hx

/-- On the positive short simple root, the exceptional comorphism exchanges root length
and applies Frobenius to the parameter. -/
@[reassoc (attr := simp)]
theorem specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_difference :
    specialIsogenyCoordinateMap ≫
        rootSubgroupCoordinateMap (.difference 0 1 (by decide)) =
      rootSubgroupCoordinateMap (.positiveLong 1) ≫
        CommHopfAlgCat.ofHom (AdditiveGroup.frobeniusBialgHom 𝔽₂ 2) := by
  apply specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_of_hom
  simpa only [GLSymplecticFin.RootSubgroupIndex.hom_difference,
    GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
    GLSymplecticFin.differenceShortRootHom_apply,
    GLSymplecticFin.positiveLongRootTransvectionHom_apply, toAdd_ofAdd,
    CommHopfAlgCat.hom_ofHom, AdditiveGroup.frobeniusBialgHom_ι_one] using
    TauCeti.specialIsogeny_differenceShortRootUnit (SymmetricAlgebra.ι 𝔽₂ 𝔽₂ 1)

/-- On the negative short simple root, the exceptional comorphism exchanges root length
and applies Frobenius to the parameter. -/
@[reassoc (attr := simp)]
theorem specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_difference_one_zero :
    specialIsogenyCoordinateMap ≫
        rootSubgroupCoordinateMap (.difference 1 0 (by decide)) =
      rootSubgroupCoordinateMap (.negativeLong 1) ≫
        CommHopfAlgCat.ofHom (AdditiveGroup.frobeniusBialgHom 𝔽₂ 2) := by
  apply specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_of_hom
  simpa only [GLSymplecticFin.RootSubgroupIndex.hom_difference,
    GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
    GLSymplecticFin.differenceShortRootHom_apply,
    GLSymplecticFin.negativeLongRootTransvectionHom_apply, toAdd_ofAdd,
    CommHopfAlgCat.hom_ofHom, AdditiveGroup.frobeniusBialgHom_ι_one] using
    TauCeti.specialIsogeny_differenceShortRootUnit_one_zero (SymmetricAlgebra.ι 𝔽₂ 𝔽₂ 1)

/-- On the positive long simple root, the exceptional comorphism exchanges root length
and preserves the parameter. -/
@[reassoc (attr := simp)]
theorem specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_positiveLong :
    specialIsogenyCoordinateMap ≫ rootSubgroupCoordinateMap (.positiveLong 1) =
      rootSubgroupCoordinateMap (.difference 0 1 (by decide)) := by
  simpa only [CommHopfAlgCat.ofHom_id, Category.comp_id] using
    specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_of_hom
      (.positiveLong 1) (.difference 0 1 (by decide)) (CommHopfAlgCat.ofHom (BialgHom.id 𝔽₂ U)) (by
        simpa only [GLSymplecticFin.RootSubgroupIndex.hom_difference,
          GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
          GLSymplecticFin.differenceShortRootHom_apply,
          GLSymplecticFin.positiveLongRootTransvectionHom_apply, toAdd_ofAdd,
          CommHopfAlgCat.hom_ofHom, BialgHom.id_apply] using
          TauCeti.specialIsogeny_positiveLongRootTransvectionUnit (SymmetricAlgebra.ι 𝔽₂ 𝔽₂ 1))

/-- On the negative long simple root, the exceptional comorphism exchanges root length
and preserves the parameter. -/
@[reassoc (attr := simp)]
theorem specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_negativeLong :
    specialIsogenyCoordinateMap ≫ rootSubgroupCoordinateMap (.negativeLong 1) =
      rootSubgroupCoordinateMap (.difference 1 0 (by decide)) := by
  simpa only [CommHopfAlgCat.ofHom_id, Category.comp_id] using
    specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_of_hom
      (.negativeLong 1) (.difference 1 0 (by decide)) (CommHopfAlgCat.ofHom (BialgHom.id 𝔽₂ U)) (by
        simpa only [GLSymplecticFin.RootSubgroupIndex.hom_difference,
          GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
          GLSymplecticFin.differenceShortRootHom_apply,
          GLSymplecticFin.negativeLongRootTransvectionHom_apply, toAdd_ofAdd,
          CommHopfAlgCat.hom_ofHom, BialgHom.id_apply] using
          TauCeti.specialIsogeny_negativeLongRootTransvectionUnit (SymmetricAlgebra.ι 𝔽₂ 𝔽₂ 1))

/-- The positive short simple root is carried to the positive long simple root,
with relative Frobenius on the additive parameter scheme. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_difference_comp_specialIsogenyHom :
    rootSubgroup (R := 𝔽₂) (.difference 0 1 (by decide)) ≫ specialIsogenyHom =
      AdditiveGroup.frobeniusHom 𝔽₂ 2 ≫ rootSubgroup (.positiveLong 1) := by
  simp only [rootSubgroup_def, specialIsogenyHom_def, AdditiveGroup.frobeniusHom_def,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
    ← Functor.map_comp, ← op_comp,
    specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_difference]

/-- The negative short simple root is carried to the negative long simple root,
with relative Frobenius on the additive parameter scheme. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_difference_one_zero_comp_specialIsogenyHom :
    rootSubgroup (R := 𝔽₂) (.difference 1 0 (by decide)) ≫ specialIsogenyHom =
      AdditiveGroup.frobeniusHom 𝔽₂ 2 ≫ rootSubgroup (.negativeLong 1) := by
  simp only [rootSubgroup_def, specialIsogenyHom_def, AdditiveGroup.frobeniusHom_def,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
    ← Functor.map_comp, ← op_comp,
    specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_difference_one_zero]

/-- The positive long simple root is carried to the positive short simple root,
with the additive parameter scheme unchanged. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_positiveLong_comp_specialIsogenyHom :
    rootSubgroup (R := 𝔽₂) (.positiveLong 1) ≫ specialIsogenyHom =
      rootSubgroup (.difference 0 1 (by decide)) := by
  simp only [rootSubgroup_def, specialIsogenyHom_def, Category.assoc,
    eqToHom_refl, Category.id_comp, Category.comp_id, ← Functor.map_comp, ← op_comp,
    specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_positiveLong]

/-- The negative long simple root is carried to the negative short simple root,
with the additive parameter scheme unchanged. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_negativeLong_comp_specialIsogenyHom :
    rootSubgroup (R := 𝔽₂) (.negativeLong 1) ≫ specialIsogenyHom =
      rootSubgroup (.difference 1 0 (by decide)) := by
  simp only [rootSubgroup_def, specialIsogenyHom_def, Category.assoc,
    eqToHom_refl, Category.id_comp, Category.comp_id, ← Functor.map_comp, ← op_comp,
    specialIsogenyCoordinateMap_comp_rootSubgroupCoordinateMap_negativeLong]

end

end TauCeti.Symplectic
