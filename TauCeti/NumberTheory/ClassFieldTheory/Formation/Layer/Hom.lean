/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.CoefficientMap
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Morphisms of finite normal layers between formations

Let `F` be a formation on `G` and `F'` a formation on `G'`, with finite normal layers `V ◁ U` of
`G` and `V' ◁ U'` of `G'`. A **layer morphism** `LayerHom F L F' L'` is an isomorphism of Galois
groups `e : U/V ≃* U'/V'` together with a homomorphism of coefficient modules
`φ : A^V → A'^{V'}`, not necessarily bijective, that intertwines the two Galois actions along `e`.

The motivating example is a place `w` of a finite Galois extension `L/K` of number fields, with
decomposition group `D_w`. Restriction identifies the Galois group of the local extension
`L_w/K_v` with `D_w`, the Galois group of the global extension `L/L^{D_w}`, and the inclusion of
`L_wˣ` into the idele classes `C_L`, as the component at `w`, is equivariant along it; it is not an
isomorphism. The map that an equivariant map of coefficient modules induces on a single layer is
another example (`NormalLayer.repMapLayerHom`), and so is every layer isomorphism
(`LayerEquiv.toLayerHom`).

A layer morphism acts on what a layer carries: on ordinary and Tate cohomology in the coefficient
module (`LayerHom.cohomologyMap`, `LayerHom.tateCohomologyMap`), on Tate cohomology with trivial
integral coefficients, where it is an isomorphism (`LayerHom.trivialTateCohomologyIso`), on the
ground level (`LayerHom.groundMap`) and on the norm quotient (`LayerHom.normQuotientMap`). These
actions commute with the norm, with cup product, and with the low-degree identifications of Tate
cohomology.

If `F` and `F'` carry class formations and the morphism carries the fundamental class of `L` to the
fundamental class of `L'`, which holds as soon as it matches the invariant maps
(`ClassFormation.fundamentalClass_layerHom`), then it carries Tate's isomorphism, the Nakayama map,
Artin reciprocity and the Artin map of `L` to those of `L'` (`ClassFormation.tateIso_layerHom`,
`ClassFormation.nakayamaNegTwo_layerHom`, `ClassFormation.artinEquiv_layerHom`,
`ClassFormation.artinMap_layerHom`): the Artin symbol in `L'` of the image of `a` is the image of
the Artin symbol of `a`. This is the functoriality of the reciprocity map along a morphism of class
formations that preserves invariants. For a place of a number field it reduces the compatibility of
the global Artin map with the local one to the compatibility of the global invariant with the local
invariant.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerHom`: a morphism from a layer of one formation to a layer of
  another.
* `TauCeti.ClassFieldTheory.LayerHom.cohomologyMap`,
  `TauCeti.ClassFieldTheory.LayerHom.tateCohomologyMap`: the induced maps of ordinary and of Tate
  cohomology.
* `TauCeti.ClassFieldTheory.LayerHom.trivialTateCohomologyIso`: the induced isomorphism of Tate
  cohomology with trivial integral coefficients.
* `TauCeti.ClassFieldTheory.LayerHom.groundMap`,
  `TauCeti.ClassFieldTheory.LayerHom.normQuotientMap`: the induced maps of ground levels and of norm
  quotients.
* `TauCeti.ClassFieldTheory.NormalLayer.repMapLayerHom`: the layer morphism induced on one layer by
  an equivariant map of coefficient modules.

## Main statements

* `TauCeti.ClassFieldTheory.LayerHom.norm_coeffMap`: a layer morphism commutes with the norms.
* `TauCeti.ClassFieldTheory.cupClass_layerHom`: cup product with a degree-two class is carried
  along a layer morphism.
* `TauCeti.ClassFieldTheory.ClassFormation.fundamentalClass_layerHom`: a layer morphism matching
  the invariant maps matches the fundamental classes.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_layerHom`: a layer morphism matching the
  fundamental classes carries the Artin symbol of `a` to the Artin symbol of the image of `a`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–6.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep
open _root_.groupCohomology

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [TotallyDisconnectedSpace G']

/-- A **morphism from the layer `L` of the formation `F` to the layer `L'` of the formation `F'`**:
an isomorphism of Galois groups and a homomorphism of coefficient modules that intertwines the
Galois actions along it. -/
@[ext]
structure LayerHom (F : Formation G) (L : NormalLayer G) (F' : Formation G')
    (L' : NormalLayer G') where
  /-- The isomorphism `U/V ≃* U'/V'` of Galois groups. -/
  galEquiv : L.Gal ≃* L'.Gal
  /-- The homomorphism `A^V → A'^{V'}` of coefficient modules. -/
  coeffMap : F.level L.top →ₗ[ℤ] F'.level L'.top
  /-- The coefficient homomorphism intertwines the Galois actions along `galEquiv`. -/
  isIntertwiningMap : (L.rep F).ρ.IsIntertwiningMap
    ((L'.rep F').ρ.comp (galEquiv : L.Gal →* L'.Gal)) coeffMap

namespace LayerHom

variable {F : Formation G} {L : NormalLayer G} {F' : Formation G'} {L' : NormalLayer G'}
  (E : LayerHom F L F' L')

/-- The coefficient homomorphism of a layer morphism intertwines the Galois actions. -/
theorem coeffMap_rep_apply (γ : L.Gal) (x : F.level L.top) :
    E.coeffMap ((L.rep F).ρ γ x) = (L'.rep F').ρ (E.galEquiv γ) (E.coeffMap x) :=
  E.isIntertwiningMap.isIntertwining γ x

include E in
/-- The two layers of a layer morphism have the same degree. -/
theorem degree_eq : L'.degree = L.degree := by
  rw [NormalLayer.degree_eq_natCard_gal, NormalLayer.degree_eq_natCard_gal,
    Nat.card_congr E.galEquiv.toEquiv]

/-! ### Cohomology -/

/-- The map `H^n(U/V, A^V) ⟶ H^n(U'/V', A'^{V'})` of ordinary cohomology induced by a layer
morphism: Mathlib's change-of-group map along the inverse of the isomorphism of Galois groups. -/
def cohomologyMap (n : ℕ) : L.H F n ⟶ L'.H F' n :=
  groupCohomology.map (E.galEquiv.symm : L'.Gal →* L.Gal)
    (Representation.IsIntertwiningMap.ofRes E.isIntertwiningMap) n

/-- The map of ordinary cohomology induced by a layer morphism is Mathlib's `groupCohomology.map`
of the compatible pair. -/
theorem cohomologyMap_def (n : ℕ) :
    E.cohomologyMap n = groupCohomology.map (E.galEquiv.symm : L'.Gal →* L.Gal)
      (Representation.IsIntertwiningMap.ofRes E.isIntertwiningMap) n :=
  (rfl)

/-- The map `H^r(U/V, A^V) ⟶ H^r(U'/V', A'^{V'})` of Tate cohomology induced by a layer morphism,
in every integer degree: the Tate map of its compatible pair. -/
def tateCohomologyMap (r : ℤ) : L.TateH F r ⟶ L'.TateH F' r :=
  TateCohomology.map E.isIntertwiningMap r

/-- The map of Tate cohomology induced by a layer morphism is the Tate map of its compatible
pair. -/
theorem tateCohomologyMap_def (r : ℤ) :
    E.tateCohomologyMap r = TateCohomology.map E.isIntertwiningMap r :=
  (rfl)

/-- **In positive degrees the Tate and ordinary maps agree**, through the identifications
`tateHIsoH` of the two layers. -/
theorem tateCohomologyMap_tateHIsoH_inv (n : ℕ) [NeZero n] (u : L.H F n) :
    E.tateCohomologyMap n ((L.tateHIsoH F n).inv u) =
      (L'.tateHIsoH F' n).inv (E.cohomologyMap n u) := by
  refine (ModuleCat.mono_iff_injective (L'.tateHIsoH F' n).hom).1 inferInstance ?_
  rw [Iso.inv_hom_id_apply, tateCohomologyMap_def, NormalLayer.tateHIsoH_def,
    NormalLayer.tateHIsoH_def]
  -- The Tate map of the pair is, in positive degrees, the change-of-group map of ordinary
  -- cohomology along `galEquiv.symm`, which is how `cohomologyMap` is defined.
  have hm : (TateCohomology.isoGroupCohomology n).hom.app (L'.rep F')
      (TateCohomology.map E.isIntertwiningMap n
        (((TateCohomology.isoGroupCohomology n).app (L.rep F)).inv u)) =
      E.cohomologyMap n ((TateCohomology.isoGroupCohomology n).hom.app (L.rep F)
          (((TateCohomology.isoGroupCohomology n).app (L.rep F)).inv u)) :=
    ConcreteCategory.congr_hom (TateCohomology.map_comp_isoGroupCohomology_hom
      E.isIntertwiningMap n) _
  exact hm.trans <| congrArg _ (((TateCohomology.isoGroupCohomology n).app
    (L.rep F)).inv_hom_id_apply u)

/-- The isomorphism `H^r(U/V, ℤ) ≅ H^r(U'/V', ℤ)` of Tate cohomology with trivial integral
coefficients induced by the isomorphism of Galois groups of a layer morphism. -/
def trivialTateCohomologyIso (r : ℤ) : L.TrivialTateH r ≅ L'.TrivialTateH r :=
  TateCohomology.mapIso (e := E.galEquiv)
    (Rep.isIntertwiningMap_trivial ℤ (E.galEquiv : L.Gal →* L'.Gal)) r

/-- The isomorphism of Tate cohomology with trivial coefficients is the Tate map of the pair formed
by the isomorphism of Galois groups and the identity of `ℤ`. -/
theorem trivialTateCohomologyIso_hom (r : ℤ) :
    (E.trivialTateCohomologyIso r).hom =
      TateCohomology.map (e := E.galEquiv)
        (Rep.isIntertwiningMap_trivial ℤ (E.galEquiv : L.Gal →* L'.Gal)) r :=
  TateCohomology.mapIso_hom _ r

/-- **In degree `-2` the map is the induced isomorphism of abelianized Galois groups**, under the
identifications `H^{-2}(U/V, ℤ) ≃ (U/V)^ab` of the two layers. -/
@[simp]
theorem tateHMinusTwoEquivAbelianization_trivialTateCohomologyIso_apply
    (x : L.TrivialTateH (-2)) :
    L'.tateHMinusTwoEquivAbelianization ((E.trivialTateCohomologyIso (-2)).hom x) =
      E.galEquiv.abelianizationCongr.toAdditive (L.tateHMinusTwoEquivAbelianization x) := by
  rw [trivialTateCohomologyIso_hom, NormalLayer.tateHMinusTwoEquivAbelianization_apply,
    NormalLayer.tateHMinusTwoEquivAbelianization_apply, map_neg, neg_inj]
  exact TateCohomology.HNegTwoAddEquivAbelianization_map _ x

/-! ### The ground level and the norm -/

/-- The map `A^U → A'^{U'}` of ground levels induced by a layer morphism: an element of the ground
level is an invariant of the coefficient module, and its image is the image of that invariant
(`groundMap_apply_coe`). -/
def groundMap : F.level L.ground →ₗ[ℤ] F'.level L'.ground :=
  (L'.groundLevelEquiv F').toLinearMap ∘ₗ TateCohomology.mapInvariants E.isIntertwiningMap ∘ₗ
    (L.groundLevelEquiv F).symm.toLinearMap

-- The `simp` lemma below states its left-hand side through `dsimp% only`; see the implementation
-- notes of `Formation/Basic.lean`.
/-- The map of ground levels is the coefficient homomorphism, applied to the ground level as a
submodule of the top level. -/
@[simp]
theorem groundMap_apply_coe (a : F.level L.ground) :
    (dsimp% only ((E.groundMap a : F'.level L'.ground) : F'.toRep.V)) =
      E.coeffMap (Submodule.inclusion (L.level_ground_le_level_top F) a) := by
  simp only [groundMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    NormalLayer.groundLevelEquiv_apply_coe]
  rw [TateCohomology.mapInvariants_apply_coe]
  exact congrArg (fun y ↦ ((E.coeffMap y : F'.level L'.top) : F'.toRep.V))
    (Subtype.ext (L.groundLevelEquiv_symm_apply_coe F a))

/-- On the invariant attached to a ground-level element, the map of ground levels is the induced
map of invariants. -/
theorem groundMap_groundLevelEquiv (x : (L.rep F).ρ.invariants) :
    E.groundMap (L.groundLevelEquiv F x) =
      L'.groundLevelEquiv F' (TateCohomology.mapInvariants E.isIntertwiningMap x) := by
  simp [groundMap]

/-- **A layer morphism commutes with the norms** `N_{U/V}` and `N_{U'/V'}`. -/
theorem norm_coeffMap (x : F.level L.top) :
    L'.norm F' (E.coeffMap x) = E.groundMap (L.norm F x) := by
  refine Subtype.ext ?_
  rw [groundMap_apply_coe, NormalLayer.norm_apply_coe]
  have hx : Submodule.inclusion (L.level_ground_le_level_top F) (L.norm F x) =
      (L.rep F).ρ.norm x :=
    Subtype.ext (by simp [Representation.norm])
  have hn := LinearMap.congr_fun (Representation.IsIntertwiningMap.comp_norm E.isIntertwiningMap) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hn
  rw [hx, hn]
  simp [Representation.norm]

/-- A layer morphism carries the norm subgroup of `L` into the norm subgroup of `L'`. -/
theorem map_normSubgroup_le :
    (L.normSubgroup F).map E.groundMap ≤ L'.normSubgroup F' := by
  intro y hy
  simp only [Submodule.mem_map, NormalLayer.mem_normSubgroup] at hy ⊢
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hy
  exact ⟨E.coeffMap x, E.norm_coeffMap x⟩

/-- The map `A^U / N_{U/V}(A^V) → A'^{U'} / N_{U'/V'}(A'^{V'})` of norm quotients induced by a
layer morphism. -/
def normQuotientMap : L.NormQuotient F →+ L'.NormQuotient F' :=
  ((L.normSubgroup F).mapQ (L'.normSubgroup F') E.groundMap
    (Submodule.map_le_iff_le_comap.1 E.map_normSubgroup_le)).toAddMonoidHom

-- `dsimp% only` on the left-hand side, as explained in the implementation notes of
-- `Formation/Basic.lean`.
/-- The map of norm quotients sends the class of `a` to the class of its image. -/
@[simp]
theorem normQuotientMap_mk (a : F.level L.ground) :
    (dsimp% only (E.normQuotientMap (Submodule.Quotient.mk a))) =
      Submodule.Quotient.mk (E.groundMap a) := by
  simp [normQuotientMap]

/-- **In degree zero the Tate map is the map of norm quotients**, through the identifications
`tateHZeroEquivNormQuotient` of the two layers. -/
theorem tateHZeroEquivNormQuotient_tateCohomologyMap_apply (x : L.TateH F 0) :
    L'.tateHZeroEquivNormQuotient F' (E.tateCohomologyMap 0 x) =
      E.normQuotientMap (L.tateHZeroEquivNormQuotient F x) := by
  induction x using TateCohomology.H0_induction_on with
  | h y =>
    rw [tateCohomologyMap_def, TauCeti.TateCohomology.H0π_comp_map_apply,
      NormalLayer.tateHZeroEquivNormQuotient_H0π, NormalLayer.tateHZeroEquivNormQuotient_H0π]
    simp only [NormalLayer.normQuotientMk_apply, normQuotientMap_mk]
    exact congrArg _ (E.groundMap_groundLevelEquiv y).symm

/-! ### The character class -/

/-- **The character class `a₀ ∪ δχ` is carried along a layer morphism**: the image of the class
attached to `a` and to the character `χ ∘ e^ab` of `U/V` is the class attached to the image of `a`
and to `χ`. -/
theorem cohomologyMap_artinCharacterCup (a : F.level L.ground)
    (χ : Additive (Abelianization L'.Gal) →+ AddCircle (1 : ℚ)) :
    E.cohomologyMap 2 (L.artinCharacterCup F a
        (χ.comp (E.galEquiv.abelianizationCongr :
          Abelianization L.Gal →* Abelianization L'.Gal).toAdditive)) =
      L'.artinCharacterCup F' (E.groundMap a) χ := by
  obtain ⟨x, rfl⟩ := (L.groundLevelEquiv F).surjective a
  rw [L.artinCharacterCup_groundLevelEquiv_eq_H2π, E.groundMap_groundLevelEquiv,
    L'.artinCharacterCup_groundLevelEquiv_eq_H2π, cohomologyMap_def,
    groupCohomology.H2π_comp_map_apply]
  congr 1
  ext q
  rw [TauCeti.groupCohomology.mapCocycles₂_apply]
  simp only [TauCeti.groupCohomology.characterCarryCocycles₂_apply,
    ContCohomology.characterCarry_comp, map_zsmul, MonoidHom.coe_ofClass,
    abelianizationCongr_of, MulEquiv.apply_symm_apply]
  congr 2
  rw [TateCohomology.mapInvariants_apply_coe]
  -- `ofRes` acts on vectors as the coefficient homomorphism.
  exact LinearMap.congr_fun
    (Representation.IsIntertwiningMap.ofRes_hom_toLinearMap E.isIntertwiningMap) _

end LayerHom

/-- **Cup product with a degree-two class is carried along a layer morphism**: the image of
`x ∪ u` is the cup product of the images of `x` and of `u`, in every degree. -/
@[simp]
theorem cupClass_layerHom {F : Formation G} {L : NormalLayer G} {F' : Formation G'}
    {L' : NormalLayer G'} (E : LayerHom F L F' L') (u : L.H F 2) (r : ℤ)
    (x : L.TrivialTateH r) :
    E.tateCohomologyMap (r + 2) (cupClass F L u r x) =
      cupClass F' L' (E.cohomologyMap 2 u) r ((E.trivialTateCohomologyIso r).hom x) := by
  have hφ := E.isIntertwiningMap
  have h₀ := Rep.isIntertwiningMap_trivial (R := ℤ) ℤ (E.galEquiv : L.Gal →* L'.Gal)
  -- The pair commutes with the left unitors `ℤ ⊗ A^V ≅ A^V`.
  have hl := TateCohomology.tateCohomologyFunctor_map_comp_map (h₀.tensor hφ) hφ
    (λ_ (L.rep F)).hom (λ_ (L'.rep F')).hom (TensorProduct.ext' fun n c ↦ by simp) (r + 2)
  simp only [cupClass_apply, ← E.tateCohomologyMap_tateHIsoH_inv 2,
    LayerHom.trivialTateCohomologyIso_hom, LayerHom.tateCohomologyMap_def]
  rw [← ModuleCat.comp_apply, hl, ModuleCat.comp_apply]
  exact congrArg _ (TateCohomology.map_cup h₀ hφ r 2 (r + 2) _ x _)

/-! ### Equivariant maps of coefficient modules -/

/-- The **layer morphism induced on the layer `L` by an equivariant map `φ : A → A'`** of the
coefficient modules of two formations on `G`: the identity of the Galois group of `L` and the map
`A^V → A'^V` of top levels (`NormalLayer.repMap`). -/
def NormalLayer.repMapLayerHom {F F' : Formation G} (L : NormalLayer G)
    (φ : F.toRep ⟶ F'.toRep) : LayerHom F L F' L where
  galEquiv := MulEquiv.refl L.Gal
  coeffMap := (L.repMap φ).hom.toLinearMap
  isIntertwiningMap := ⟨fun γ x ↦ Rep.hom_comm_apply (L.repMap φ) γ x⟩

/-- The Galois-group isomorphism of `NormalLayer.repMapLayerHom` is the identity. -/
@[simp]
theorem NormalLayer.repMapLayerHom_galEquiv {F F' : Formation G} (L : NormalLayer G)
    (φ : F.toRep ⟶ F'.toRep) : (L.repMapLayerHom φ).galEquiv = MulEquiv.refl L.Gal :=
  (rfl)

/-- The coefficient homomorphism of `NormalLayer.repMapLayerHom` is `NormalLayer.repMap`. -/
@[simp]
theorem NormalLayer.repMapLayerHom_coeffMap {F F' : Formation G} (L : NormalLayer G)
    (φ : F.toRep ⟶ F'.toRep) : (L.repMapLayerHom φ).coeffMap = (L.repMap φ).hom.toLinearMap :=
  (rfl)

/-- The layer morphism induced by an equivariant map acts on ordinary cohomology as
`groupCohomology.functor` applied to `NormalLayer.repMap`. -/
theorem NormalLayer.cohomologyMap_repMapLayerHom {F F' : Formation G} (L : NormalLayer G)
    (φ : F.toRep ⟶ F'.toRep) (n : ℕ) :
    (L.repMapLayerHom φ).cohomologyMap n = (groupCohomology.functor ℤ L.Gal n).map (L.repMap φ) :=
  groupCohomology.map_congr rfl (Representation.IsIntertwiningMap.ofRes_hom_toLinearMap
    (L.repMapLayerHom φ).isIntertwiningMap) n

/-! ### Class formations -/

namespace ClassFormation

variable {F : Formation G} {L : NormalLayer G} {F' : Formation G'} {L' : NormalLayer G'}
  (cf : ClassFormation F) (cf' : ClassFormation F') (E : LayerHom F L F' L')

/-- **A layer morphism matching the invariant maps matches the fundamental classes.** -/
theorem fundamentalClass_layerHom
    (hinv : ∀ x, cf'.inv L' (E.cohomologyMap 2 x) = cf.inv L x) :
    E.cohomologyMap 2 (cf.fundamentalClass L) = cf'.fundamentalClass L' := by
  rw [eq_fundamentalClass_iff, hinv, inv_fundamentalClass, E.degree_eq]

/-- **Tate's isomorphism is carried along a layer morphism matching the fundamental classes**: the
image of `x ∪ u_{U/V}` is the cup product of the image of `x` with `u_{U'/V'}`. -/
theorem tateIso_layerHom
    (hu : E.cohomologyMap 2 (cf.fundamentalClass L) = cf'.fundamentalClass L') (r : ℤ)
    (x : L.TrivialTateH r) :
    E.tateCohomologyMap (r + 2) (cf.tateIso L r x) =
      cf'.tateIso L' r ((E.trivialTateCohomologyIso r).hom x) := by
  simp only [tateIso_apply, cupFundamentalClass_apply, cupClass_layerHom, hu]

/-- **The Nakayama map is carried along a layer morphism matching the fundamental classes.** -/
theorem nakayamaNegTwo_layerHom
    (hu : E.cohomologyMap 2 (cf.fundamentalClass L) = cf'.fundamentalClass L')
    (σ : Additive (Abelianization L.Gal)) :
    cf'.nakayamaNegTwo L' (E.galEquiv.abelianizationCongr.toAdditive σ) =
      E.normQuotientMap (cf.nakayamaNegTwo L σ) := by
  obtain ⟨x, rfl⟩ := L.tateHMinusTwoEquivAbelianization.surjective σ
  rw [nakayamaNegTwo_apply, nakayamaNegTwo_apply, AddEquiv.symm_apply_apply,
    ← E.tateHMinusTwoEquivAbelianization_trivialTateCohomologyIso_apply x,
    AddEquiv.symm_apply_apply, ← tateIso_apply, ← tateIso_apply,
    ← tateIso_layerHom cf cf' E hu (-2) x]
  exact E.tateHZeroEquivNormQuotient_tateCohomologyMap_apply _

/-- **Artin reciprocity is carried along a layer morphism matching the fundamental classes.** -/
theorem artinEquiv_layerHom
    (hu : E.cohomologyMap 2 (cf.fundamentalClass L) = cf'.fundamentalClass L')
    (y : L.NormQuotient F) :
    cf'.artinEquiv L' (E.normQuotientMap y) =
      E.galEquiv.abelianizationCongr.toAdditive (cf.artinEquiv L y) := by
  rw [← nakayamaNegTwo_artinEquiv cf L y, ← nakayamaNegTwo_layerHom cf cf' E hu,
    artinEquiv_nakayamaNegTwo, nakayamaNegTwo_artinEquiv]

/-- **The Artin map is carried along a layer morphism matching the fundamental classes**: the Artin
symbol in `L'` of the image of `a` is the image under `(U/V)^ab ≃ (U'/V')^ab` of the Artin symbol
of `a` in `L`. -/
theorem artinMap_layerHom
    (hu : E.cohomologyMap 2 (cf.fundamentalClass L) = cf'.fundamentalClass L')
    (a : F.level L.ground) :
    cf'.artinMap L' (E.groundMap a) =
      E.galEquiv.abelianizationCongr.toAdditive (cf.artinMap L a) := by
  rw [artinMap_apply, artinMap_apply, ← artinEquiv_layerHom cf cf' E hu]
  simp

end ClassFormation

end TauCeti.ClassFieldTheory
