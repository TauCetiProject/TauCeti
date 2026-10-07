/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Map
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# The local class formation of a finite extension inside that of the base

Let `K` be a nonarchimedean local field and `E/K` a finite extension, embedded in `Kˢ` by
`iota : E →ₐ[K] Kˢ`. The embedding identifies `G_E` with the open subgroup of `G_K` fixing
`iota(E)` (`TauCeti.ClassFieldTheory.localFormationHom`), and the units formation of `E` with the
restriction of that of `K` to this subgroup (`TauCeti.ClassFieldTheory.localFormationRestrict`),
so every finite normal layer of the formation of `E` is isomorphic to a finite normal layer of the
formation of `K` (`TauCeti.ClassFieldTheory.localFormationLayerEquiv`).

This file proves that this isomorphism matches the invariant maps of the two local class
formations (`localClassFormation_inv_localFormationLayerEquiv`): the invariant of a class in the
formation of `E` is the invariant of its image in the formation of `K`. Consequently the Artin map
of a finite normal layer `V ◁ U` of the formation of `E` (the local Artin map of the extension of
the fixed field of `U` cut out by `V`) is the abstract Artin map of the corresponding layer of the
formation of `K` (`artinMap_localFormationLayerEquiv`). Combined with the Artin–Tate
diagram `TauCeti.ClassFieldTheory.ClassFormation.artinMap_groundNorm` inside the formation of `K`,
this is what relates the local Artin map of `E` to that of `K` through the norm `N_{E/K}`. The two
ground-level facts this needs are also here: the isomorphism sends `y ∈ Eˣ` to `iota y`
(`groundEquiv_localFormationLayerEquiv_localGroundEquiv`), and the ground-level norm of the
corresponding restriction inside the formation of `K` is `N_{E/K}`
(`groundNorm_layerRestriction_localFormationMap`).

The comparison is first made for the local invariant `TauCeti.ClassFieldTheory.subgroupInvMap` of
an open subgroup `U ≤ G_E` and its image `U' ≤ G_K`
(`subgroupInvMap_explicitMap2_localFormationHomInv`), and for inflation from a layer to its ground
subgroup (`layerInfl_localFormationLayerEquiv`).

## Main results

* `TauCeti.ClassFieldTheory.subgroupInvMap_explicitMap2_localFormationHomInv`: the local invariant
  of an open subgroup of `G_E` is that of its image in `G_K`.
* `TauCeti.ClassFieldTheory.localClassFormation_inv_localFormationLayerEquiv`: the layer
  isomorphism `localFormationLayerEquiv` matches the invariant maps of the local class formations.
* `TauCeti.ClassFieldTheory.artinMap_localFormationLayerEquiv`: it carries the Artin map of a layer
  of the formation of `E` to the Artin map of the corresponding layer of the formation of `K`.
* `TauCeti.ClassFieldTheory.groundEquiv_localFormationLayerEquiv_localGroundEquiv`: on ground
  levels, `localFormationLayerEquiv` sends `y ∈ Eˣ` to the unit `iota y` of the level of
  `Gal(Kˢ/iota(E))`.
* `TauCeti.ClassFieldTheory.groundNorm_layerRestriction_localFormationMap`: for an open normal
  subgroup `V ≤ Gal(Kˢ/iota(E))` of `G_K`, the ground-level norm of the restriction of `V ◁ G_K` to
  `Gal(Kˢ/iota(E))` is the field norm `N_{E/K}`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1 and 6.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.groupCohomology ContCohomology

/-! ### Inflation from corresponding layers -/

section Embedding

variable (K : Type) [Field K] (E : Type) [Field E] [Algebra K E] [FiniteDimensional K E]
  (iota : E →ₐ[K] SeparableClosure K)

/-- **The units of `Eˢ` as units of `Kˢ` form a compatible pair with `localFormationHomInv`.** -/
@[simp↓]
theorem unitsCoeffMapSymm_localFormationHomInv_smul {U : Subgroup (AbsoluteGaloisGroup E)}
    {U' : Subgroup (AbsoluteGaloisGroup K)} (h : U' ≤ U.map (localFormationHom K E iota))
    (u : U') (y : UnitsCoeff E) :
    unitsCoeffMapSymm K E iota (localFormationHomInv K E iota h u • y) =
      u • unitsCoeffMapSymm K E iota y := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp [localFormationHomInv_apply_coe, Subgroup.smul_def, AlgEquiv.smul_units_def]

omit [FiniteDimensional K E] in
/-- The inverse of the coefficient equivalence of `localFormationRestrict` is the coefficient map
`unitsCoeffMapSymm` of Kummer theory: both send a unit of `Eˢ` to its image in `Kˢ` under the
identification `Eˢ ≃ Kˢ` extending `iota`. -/
@[simp]
theorem localFormationCoeffEquiv_symm_apply (y : UnitsCoeff E) :
    (localFormationCoeffEquiv K E iota).symm y = unitsCoeffMapSymm K E iota y :=
  Additive.toMul.injective (by
    rw [toMul_localFormationCoeffEquiv_symm_apply, toMul_unitsCoeffMapSymm])

-- The cocycle computation parallels `layerCocycle_mapCocycles₂` in
-- `TauCeti.NumberTheory.ClassFieldTheory.Brauer.LayerInvariant`, the conjugation case.
/-- The inflated cocycle of the image of a layer cocycle under a layer isomorphism from a layer
`V ◁ U` over `E` to a layer `V' ◁ U'` over `K`, whose Galois-group map is induced by the embedding
`U' → U` inverse to `G_E → G_K` and whose coefficient map is induced by `(Eˢ)ˣ ≃ (Kˢ)ˣ`, is the
inflated cocycle pulled back along `U' → U` and pushed into `(Kˢ)ˣ`. -/
private theorem layerCocycle_of_localFormation (L : NormalLayer (AbsoluteGaloisGroup E))
    {L' : NormalLayer (AbsoluteGaloisGroup K)}
    (h : L'.ground.toSubgroup ≤ L.ground.toSubgroup.map (localFormationHom K E iota))
    (e : LayerEquiv (unitsFormation E) L (unitsFormation K) L')
    (hgal : ∀ u : L'.ground.toSubgroup,
      e.galEquiv (localFormationHomInv K E iota h u : L.Gal) = (u : L'.Gal))
    (hcoeff : ∀ x : (L.rep (unitsFormation E)).V,
      (unitsCoeffEquivUnitsFormation K).symm (e.coeffEquiv x : (unitsFormation K).toRep.V) =
        unitsCoeffMapSymm K E iota
          ((unitsCoeffEquivUnitsFormation E).symm (x : (unitsFormation E).toRep.V)))
    (c : cocycles₂ (L.rep (unitsFormation E))) (c' : cocycles₂ (L'.rep (unitsFormation K)))
    (hc' : ∀ γ δ : L'.Gal, c' (γ, δ) = e.coeffEquiv (c (e.galEquiv.symm γ, e.galEquiv.symm δ))) :
    layerCocycle L' c' =
      cocyclesMap2 L.ground.toSubgroup (UnitsCoeff E) L'.ground.toSubgroup (UnitsCoeff K)
        (localFormationHomInv K E iota h) (unitsCoeffMapSymm K E iota)
        continuous_of_discreteTopology (unitsCoeffMapSymm_localFormationHomInv_smul K E iota h)
        (layerCocycle L c) := by
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨u, v⟩ := p
  rw [cocyclesMap2_apply, layerCocycle_apply, layerCocycle_apply, hc',
    (MulEquiv.symm_apply_eq _).2 (hgal u).symm, (MulEquiv.symm_apply_eq _).2 (hgal v).symm]
  exact hcoeff _

/-- **Inflation commutes with the layer isomorphism `localFormationLayerEquiv`**: inflating the
image of a class of a layer `V ◁ U` over `E` to the ground subgroup `U'` of the corresponding layer
over `K` is transporting its inflation to `U` along `U' ≃ U` and `(Eˢ)ˣ ≃ (Kˢ)ˣ`. -/
theorem layerInfl_localFormationLayerEquiv (L : NormalLayer (AbsoluteGaloisGroup E))
    (x : L.H (unitsFormation E) 2) :
    layerInfl (L.localFormationMap K E iota)
        (((localFormationLayerEquiv K E iota L).cohomologyIso 2).hom x) =
      explicitMap2 L.ground.toSubgroup (UnitsCoeff E)
        (L.localFormationMap K E iota).ground.toSubgroup (UnitsCoeff K)
        (localFormationHomInv K E iota (L.localFormationMap_ground_toSubgroup K E iota).le)
        (unitsCoeffMapSymm K E iota) continuous_of_discreteTopology
        (unitsCoeffMapSymm_localFormationHomInv_smul K E iota _) (layerInfl L x) := by
  refine layerInfl_eq_explicitMap2_layerInfl L _ _ _
    (fun y => ((localFormationLayerEquiv K E iota L).cohomologyIso 2).hom y) (fun c => ?_) x
  obtain ⟨c', hc, hc'⟩ := (localFormationLayerEquiv K E iota L).exists_cohomologyIso_hom_H2π c
  exact ⟨c', hc, layerCocycle_of_localFormation K E iota L _ _
    (fun u => localFormationLayerEquiv_galEquiv_mk K E iota L _ u
      (localFormationHom_localFormationHomInv K E iota _ u).symm)
    (fun y => (localFormationLayerEquiv_coeffEquiv_apply K E iota L y).trans
      (localFormationCoeffEquiv_symm_apply K E iota _)) c c' hc'⟩

/-- The unit `y ∈ Eˣ`, read in the ground level `((Eˢ)ˣ)^{G_E}` of a layer `V ◁ G_E` and carried to
the corresponding layer over `K`, is the unit `iota y` of the level of `Gal(Kˢ/iota(E))`. -/
theorem groundEquiv_localFormationLayerEquiv_localGroundEquiv
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup E)) (y : Additive Eˣ) :
    (localFormationLayerEquiv K E iota (NormalLayer.ofOpenNormal V)).groundEquiv
        (localGroundEquiv E V y) =
      unitsLevelEquiv iota (fixedField_localFormationMap_ofOpenNormal_ground K E iota V) y := by
  refine Subtype.ext ?_
  rw [LayerEquiv.groundEquiv_apply_coe, unitsLevelEquiv_apply_coe]
  apply (unitsCoeffEquivUnitsFormation K).symm.injective
  rw [localFormationLayerEquiv_coeffEquiv_apply, AddEquiv.symm_apply_apply]
  refine Additive.toMul.injective (Units.ext ?_)
  simp [separableClosureRingEquiv_algebraMap]

/-- For an open normal subgroup `V ≤ Gal(Kˢ/iota(E))` of `G_K`, the norm from the ground level
`Gal(Kˢ/iota(E))` to the ground level `G_K` of the restriction `layerRestriction_localFormationMap`
sends `iota x` to `N_{E/K} x`. -/
theorem groundNorm_layerRestriction_localFormationMap
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hV : V ≤ (galoisSubgroup K E iota).toSubgroup) (x : Additive Eˣ) :
    (layerRestriction_localFormationMap K E iota V hV).groundNorm (unitsFormation K)
        (unitsLevelEquiv iota (fixedField_localFormationMap_ofOpenNormal_ground K E iota _) x) =
      localGroundEquiv K V (Additive.ofMul (Algebra.normUnits K x.toMul)) := by
  refine Subtype.ext ?_
  rw [LayerRestriction.groundNorm_apply_coe, ← Formation.levelNorm_apply_coe _
    (layerRestriction_localFormationMap K E iota V hV).ground_le,
    levelNorm_unitsLevelEquiv iota _ _ (fixedField_ground_ofOpenNormal K V),
    unitsLevelEquiv_apply_coe, localGroundEquiv_apply_coe]

end Embedding

/-! ### The local invariant of an open subgroup of `G_E` -/

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra K E] [ValuativeExtension K E] [FiniteDimensional K E]
  (iota : E →ₐ[K] SeparableClosure K)

/-- Every class in `H²(U, (Eˢ)ˣ)` of an open subgroup `U ≤ G_E` is restricted from `Br E`. -/
private theorem exists_explicitRes2_eq (U : Subgroup (AbsoluteGaloisGroup E)) [U.FiniteIndex]
    (hU : IsOpen (U : Set (AbsoluteGaloisGroup E))) (y : H2 U (UnitsCoeff E)) :
    ∃ z : Br E,
      explicitRes2 (AbsoluteGaloisGroup E) (UnitsCoeff E) U ((unitsRepH2Equiv E).symm z) = y := by
  have hn : ((U.index : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  refine ⟨(invMap E).symm (DivisibleBy.div (subgroupInvMap E U hU y) (U.index : ℤ)), ?_⟩
  refine (subgroupInvMap E U hU).injective ?_
  rw [subgroupInvMap_explicitRes2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ← natCast_zsmul, DivisibleBy.div_cancel _ hn]

/-- **The local invariant of an open subgroup of `G_E` is that of its image in `G_K`**: for an open
subgroup `U ≤ G_E` with image `U'` under the embedding `G_E → G_K`, a class of `H²(U, (Eˢ)ˣ)`
transported to `H²(U', (Kˢ)ˣ)` along `U' ≃ U` and `(Eˢ)ˣ ≃ (Kˢ)ˣ` has the same invariant. For
`U = G_E` this is `subgroupInvMap_explicitMap2`. -/
theorem subgroupInvMap_explicitMap2_localFormationHomInv {U : Subgroup (AbsoluteGaloisGroup E)}
    [U.FiniteIndex] (hU : IsOpen (U : Set (AbsoluteGaloisGroup E)))
    {U' : Subgroup (AbsoluteGaloisGroup K)} [U'.FiniteIndex]
    (hU' : IsOpen (U' : Set (AbsoluteGaloisGroup K)))
    (hUU' : U.map (localFormationHom K E iota) = U') (y : H2 U (UnitsCoeff E)) :
    subgroupInvMap K U' hU'
        (explicitMap2 U (UnitsCoeff E) U' (UnitsCoeff K) (localFormationHomInv K E iota hUU'.ge)
          (unitsCoeffMapSymm K E iota) continuous_of_discreteTopology
          (unitsCoeffMapSymm_localFormationHomInv_smul K E iota hUU'.ge) y) =
      subgroupInvMap E U hU y := by
  subst hUU'
  -- Every class is restricted from `Br E`, and on a restricted class both invariants are
  -- `[G_E : U] • inv_E`.
  obtain ⟨z, rfl⟩ := exists_explicitRes2_eq E U hU y
  have hle : U.map (localFormationHom K E iota) ≤ iota.fieldRange.fixingSubgroup :=
    galoisSubgroup_toSubgroup K E iota ▸ (Subgroup.map_le_range _ U).trans
      (range_localFormationHom K E iota).le
  have hgrp : (ContinuousMonoidHom.subgroupSubtype U).comp
        (localFormationHomInv K E iota (le_refl (U.map (localFormationHom K E iota)))) =
      ((absoluteGaloisGroupEquivFixingSubgroup K E iota).symm :
        ↥iota.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup E).comp
        (ContinuousMonoidHom.subgroupInclusion hle) := by
    ext u x
    simp [localFormationHomInv_apply_coe, galoisSubgroupEquiv_symm_apply,
      absoluteGaloisGroupEquivFixingSubgroup_symm_apply]
  -- Transporting a restricted class is restricting the transported class: both are the pullback
  -- along `U' → G_E` and `(Eˢ)ˣ → (Kˢ)ˣ`.
  have key : (explicitMap2 U (UnitsCoeff E) (U.map (localFormationHom K E iota)) (UnitsCoeff K)
        (localFormationHomInv K E iota (le_refl _)) (unitsCoeffMapSymm K E iota)
        continuous_of_discreteTopology
        (unitsCoeffMapSymm_localFormationHomInv_smul K E iota (le_refl _))).comp
        (explicitMap2 (AbsoluteGaloisGroup E) (UnitsCoeff E) U (UnitsCoeff E)
          (ContinuousMonoidHom.subgroupSubtype U) (AddMonoidHom.id _) continuous_id
          (ContinuousMonoidHom.id_subgroupSubtype_smul _ U)) =
      (explicitMap2 iota.fieldRange.fixingSubgroup (UnitsCoeff K)
        (U.map (localFormationHom K E iota)) (UnitsCoeff K)
        (ContinuousMonoidHom.subgroupInclusion hle) (AddMonoidHom.id _) continuous_id
        (fun _ _ => rfl)).comp
        (explicitMap2 (AbsoluteGaloisGroup E) (UnitsCoeff E) iota.fieldRange.fixingSubgroup
          (UnitsCoeff K) ((absoluteGaloisGroupEquivFixingSubgroup K E iota).symm :
            ↥iota.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup E)
          (unitsCoeffMapSymm K E iota) continuous_of_discreteTopology
          (unitsCoeffMapSymm_smul K E iota)) := by
    rw [← explicitMap2_comp (G := AbsoluteGaloisGroup E) (M := UnitsCoeff E)
      (H := U) (N := UnitsCoeff E) (K := U.map (localFormationHom K E iota))
      (P := UnitsCoeff K)]
    exact (explicitMap2_congr_of_eq _ _ _ _ _ _ _
      ((AddMonoidHom.id _).comp (unitsCoeffMapSymm K E iota)) hgrp
      (AddMonoidHom.ext fun _ => rfl)).trans
      (explicitMap2_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  rw [subgroupInvMap_explicitRes2, AddEquiv.apply_symm_apply, explicitRes2_eq_explicitMap2,
    ← AddMonoidHom.comp_apply, key, AddMonoidHom.comp_apply,
    subgroupInvMap_explicitMap2_subgroupInclusion K _ _
      (isOpen_fixingSubgroup_fieldRange K E iota) hU' hle, subgroupInvMap_explicitMap2,
    ← galoisSubgroup_toSubgroup, ← range_localFormationHom, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ (injective_localFormationHom K E iota),
    Subgroup.relIndex_top_right]

/-! ### The local class formations of `E` and of `K` -/

/-- **The local class formation of `E` is that of `K` on corresponding layers**: the layer
isomorphism `localFormationLayerEquiv` from a finite normal layer of the units formation of `E` to
the corresponding layer of the units formation of `K` matches the invariant maps of the two local
class formations. -/
theorem localClassFormation_inv_localFormationLayerEquiv (L : NormalLayer (AbsoluteGaloisGroup E))
    (x : L.H (unitsFormation E) 2) :
    (localClassFormation K).inv (L.localFormationMap K E iota)
        (((localFormationLayerEquiv K E iota L).cohomologyIso 2).hom x) =
      (localClassFormation E).inv L x := by
  rw [localClassFormation_inv_apply, localClassFormation_inv_apply, layerInv_apply, layerInv_apply,
    layerInfl_localFormationLayerEquiv]
  exact subgroupInvMap_explicitMap2_localFormationHomInv K E iota L.ground.isOpen
    (L.localFormationMap K E iota).ground.isOpen
    (L.localFormationMap_ground_toSubgroup K E iota).symm _

/-- **The Artin map of a layer over `E` is the Artin map of the corresponding layer over `K`**:
for a finite normal layer `V ◁ U` of the units formation of `E`, the Artin symbol of the image of
`a ∈ ((Eˢ)ˣ)^U` in the corresponding layer of the units formation of `K` is the image of the Artin
symbol of `a` under the induced isomorphism of abelianized Galois groups. -/
theorem artinMap_localFormationLayerEquiv (L : NormalLayer (AbsoluteGaloisGroup E))
    (a : (unitsFormation E).level L.ground) :
    (localClassFormation K).artinMap (L.localFormationMap K E iota)
        ((localFormationLayerEquiv K E iota L).groundEquiv a) =
      (localFormationLayerEquiv K E iota L).galEquiv.abelianizationCongr.toAdditive
        ((localClassFormation E).artinMap L a) :=
  ClassFormation.artinMap_layerEquiv _ _ _
    (localClassFormation_inv_localFormationLayerEquiv K E iota L) a

end TauCeti.ClassFieldTheory
