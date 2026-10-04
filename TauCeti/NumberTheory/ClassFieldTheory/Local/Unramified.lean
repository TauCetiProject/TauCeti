/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.LocalField.Unramified.BaseChange
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Cyclic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Finite unramified local reciprocity

For a finite unramified Galois extension `L/K`, this file normalizes the finite local Artin map
by arithmetic Frobenius.  The character which sends arithmetic Frobenius to `1 / [L : K]` detects
the cyclic Galois group.  The character formula for the Artin map and the explicit cyclic cup
product then identify the Artin symbol of a uniformizer.

## Main definitions

* `TauCeti.ClassFieldTheory.frobeniusCharacter`: the faithful character of the Galois group of an
  unramified extension which sends arithmetic Frobenius to `1 / [L : K]`.

## Main results

* `TauCeti.ClassFieldTheory.localArtinMap_uniformizer`: the finite local Artin map sends every
  uniformizer to arithmetic Frobenius.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §3.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §5.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory MonoidalCategory
open ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L] [IsGalois K L] [IsUnramified K L]

/-- The faithful character of the Galois group of an unramified extension which sends arithmetic
Frobenius to `1 / [L : K]`. -/
def frobeniusCharacter :
    Additive (Abelianization Gal(L/K)) →+ AddCircle (1 : ℚ) := by
  let _ : CommGroup Gal(L/K) := IsCyclic.commGroup
  let e : Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)) :=
    (zmodMulEquivOfGenerator
      (fun σ => by rw [zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top σ)
      (by rw [IsGalois.card_aut_eq_finrank])).symm
  exact (ZMod.toRatAddCircle (Module.finrank K L)).comp
    (MulEquiv.toAdditiveLeft (Abelianization.equivOfComm.symm.trans e)).toAddMonoidHom

/-- The Frobenius character takes arithmetic Frobenius to `1 / [L : K]`. -/
@[simp]
theorem frobeniusCharacter_frobenius :
    frobeniusCharacter K L
        (Additive.ofMul (Abelianization.of (frobeniusAlgEquiv (K := K) (L := L)))) =
      ((1 / Module.finrank K L : ℚ) : AddCircle (1 : ℚ)) := by
  let _ : CommGroup Gal(L/K) := IsCyclic.commGroup
  rw [frobeniusCharacter, AddMonoidHom.comp_apply]
  change (ZMod.toRatAddCircle (Module.finrank K L))
    (Multiplicative.toAdd ((zmodMulEquivOfGenerator
      (fun σ => by rw [zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top σ)
      (by rw [IsGalois.card_aut_eq_finrank])).symm
        (Abelianization.equivOfComm.symm (Abelianization.of
          (frobeniusAlgEquiv (K := K) (L := L)))))) = _
  change (ZMod.toRatAddCircle (Module.finrank K L))
    (Multiplicative.toAdd ((zmodMulEquivOfGenerator
      (fun σ => by rw [zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top σ)
      (by rw [IsGalois.card_aut_eq_finrank])).symm
        (frobeniusAlgEquiv (K := K) (L := L)))) = _
  rw [zmodMulEquivOfGenerator_symm_apply_generator]
  simpa using ZMod.toRatAddCircle_natCast (Module.finrank K L) 1

/-- The Frobenius character detects every element of the abelianized Galois group. -/
theorem injective_frobeniusCharacter : Function.Injective (frobeniusCharacter K L) := by
  let _ : CommGroup Gal(L/K) := IsCyclic.commGroup
  let _ : NeZero (Module.finrank K L) := NeZero.of_pos Module.finrank_pos
  apply Function.Injective.comp (ZMod.toRatAddCircle_injective (Module.finrank K L))
  exact (MulEquiv.toAdditiveLeft
    (Abelianization.equivOfComm.symm.trans
      (zmodMulEquivOfGenerator
        (fun σ => by rw [zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top σ)
        (by rw [IsGalois.card_aut_eq_finrank])).symm)).injective

/-- Arithmetic Frobenius, regarded in the normal layer cut out by an embedding of `L`. -/
private def layerFrobenius (ι : L →ₐ[K] SeparableClosure K) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal :=
  (layerGalEquiv ι).symm (frobeniusAlgEquiv (K := K) (L := L))

/-- Arithmetic Frobenius generates the Galois group of the normal layer. -/
private theorem mem_zpowers_layerFrobenius (ι : L →ₐ[K] SeparableClosure K)
    (σ : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) :
    σ ∈ Subgroup.zpowers (layerFrobenius K L ι) := by
  have hσ : layerGalEquiv ι σ ∈
      Subgroup.zpowers (frobeniusAlgEquiv (K := K) (L := L)) := by
    rw [zpowers_frobeniusAlgEquiv]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := hσ
  refine ⟨n, ?_⟩
  apply (layerGalEquiv ι).injective
  simpa [layerFrobenius] using hn

/-- The order of Frobenius in the normal layer is the degree of the extension. -/
private theorem orderOf_layerFrobenius (ι : L →ₐ[K] SeparableClosure K) :
    orderOf (layerFrobenius K L ι) = Module.finrank K L := by
  rw [layerFrobenius, MulEquiv.orderOf_eq, orderOf_frobeniusAlgEquiv,
    IsUnramified.inertiaDegree_eq_finrank]

/-- The commutative group structure on the cyclic Galois group of an unramified extension. -/
local instance concreteGalCommGroup : CommGroup Gal(L/K) := IsCyclic.commGroup

/-- The commutative group structure on a cyclic layer, with operations inherited from its
Galois group. -/
@[instance_reducible]
private def layerCommGroup (ι : L →ₐ[K] SeparableClosure K) :
    CommGroup (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal := by
  let _ : IsCyclic (NormalLayer.ofOpenNormal
    (fixingOpenNormalSubgroup K L)).Gal := (layerGalEquiv ι).isCyclic.mpr inferInstance
  exact IsCyclic.commGroup

/-! ### Comparison with the Brauer invariant -/

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [IsUnramified K L] in
/-- The concrete coefficient comparison agrees with the embedding of `Lˣ` into the units of the
separable closure. -/
theorem embeddedUnitsEquivInvariants_layerCoefficientEquiv
    (ι : L →ₐ[K] SeparableClosure K)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)) :
    ((embeddedUnitsEquivInvariants K L ι
        (Rep.toAdditive (layerCoefficientEquiv ι x)) :
      FixedPoints.addSubgroup ι.fieldRange.fixingSubgroup (UnitsCoeff K)) : UnitsCoeff K) =
      (unitsCoeffEquivUnitsFormation K).symm
        ((x : (unitsFormation K).level
          (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).top) :
            (unitsFormation K).toRep.V) := by
  rw [embeddedUnitsEquivInvariants_apply]
  apply Additive.toMul.injective
  rw [toMul_coe_embeddedUnitsInvariants]
  exact congrArg Additive.toMul (layerCoefficientEquiv_apply_coe ι x)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [IsUnramified K L] in
/-- The concrete cohomology identification of a finite Galois layer is compatible with inflation
into the Brauer group. -/
theorem relBrInfl_layerCohomologyEquiv (ι : L →ₐ[K] SeparableClosure K)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).H (unitsFormation K) 2) :
    relBrInfl K L ι (layerCohomologyEquiv ι 2 x) =
      brInfl (fixingOpenNormalSubgroup K L) x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    rw [layerCohomologyEquiv_apply, groupCohomology.H2π_comp_map_apply, relBrInfl_H2π]
    symm
    apply brInfl_H2π
    intro g h
    simp only [relBrCocycle_apply]
    rw [_root_.TauCeti.groupCohomology.mapCocycles₂_apply]
    let g' : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).ground :=
      ⟨g, by rw [NormalLayer.ground_ofOpenNormal]; exact OpenSubgroup.mem_top g⟩
    let h' : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).ground :=
      ⟨h, by rw [NormalLayer.ground_ofOpenNormal]; exact OpenSubgroup.mem_top h⟩
    have qg : (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
          (g : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) =
        (g' : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) := by
      apply (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).injective
      rw [MulEquiv.apply_symm_apply, NormalLayer.galOfOpenNormalEquiv_mk]
    have qh : (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
          (h : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) =
        (h' : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) := by
      apply (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).injective
      rw [MulEquiv.apply_symm_apply, NormalLayer.galOfOpenNormalEquiv_mk]
    have hg : (layerGalEquiv ι).symm (ι.restrictNormalHom g) =
        (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
          (g : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) := by
      rw [qg]
      exact (layerGalEquiv ι).symm_apply_eq.2 (layerGalEquiv_mk ι g').symm
    have hh : (layerGalEquiv ι).symm (ι.restrictNormalHom h) =
        (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
          (h : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) := by
      rw [qh]
      exact (layerGalEquiv ι).symm_apply_eq.2 (layerGalEquiv_mk ι h').symm
    rw [layerCoefficientHom_apply]
    have hg' : (layerGalEquiv ι).symm.toMonoidHom
        (ι.restrictNormalHom g, ι.restrictNormalHom h).1 =
        (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
          (g : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) := hg
    have hh' : (layerGalEquiv ι).symm.toMonoidHom
        (ι.restrictNormalHom g, ι.restrictNormalHom h).2 =
        (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
          (h : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) := hh
    have hq :
        ((layerGalEquiv ι).symm.toMonoidHom
            (ι.restrictNormalHom g, ι.restrictNormalHom h).1,
          (layerGalEquiv ι).symm.toMonoidHom
            (ι.restrictNormalHom g, ι.restrictNormalHom h).2) =
        ((NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
            (g : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup),
          (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
            (h : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup)) :=
      Prod.ext hg' hh'
    refine (congrArg (fun z => ((embeddedUnitsEquivInvariants K L ι
      (Rep.toAdditive (layerCoefficientEquiv ι z)) :
        FixedPoints.addSubgroup ι.fieldRange.fixingSubgroup (UnitsCoeff K)) : UnitsCoeff K))
      (congrArg c hq)).trans ?_
    exact embeddedUnitsEquivInvariants_layerCoefficientEquiv K L ι (c _)

private theorem invMap_relBrInfl_unramified_of_equiv
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K E] [IsGalois K E] [IsUnramified K E]
    (e : L ≃ₐ[K] E) (ι : L →ₐ[K] SeparableClosure K)
    (hι : E.val.comp e.toAlgHom = ι)
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) :
    invMap K (relBrInfl K L ι y) = unramifiedInv K L y := by
  let _ : Algebra L E := e.toAlgHom.toRingHom.toAlgebra
  let _ : IsScalarTower K L E := IsScalarTower.of_algHom e.toAlgHom
  have hLE : ValuativeExtension L E := e.toAlgHom.valuativeExtension
  let _ : ValuativeExtension L E := hLE
  rw [← unramifiedInv_map K L E y, ← invMap_relBrInfl E]
  exact congrArg (invMap K) ((relBrInfl_map K L E E.val y).trans
    (congrArg (fun σ => relBrInfl K L σ y) hι)).symm

omit [IsGalois K L] in
private theorem isUnramified_fieldRange (ι : L →ₐ[K] SeparableClosure K)
    [ValuativeRel ι.fieldRange] [TopologicalSpace ι.fieldRange]
    [IsNonarchimedeanLocalField ι.fieldRange]
    [ValuativeExtension K ι.fieldRange] : IsUnramified K ι.fieldRange := by
  let e : L ≃ₐ[K] ι.fieldRange := ι.equivFieldRange
  let _ : Algebra L ι.fieldRange := e.toAlgHom.toRingHom.toAlgebra
  let _ : IsScalarTower K L ι.fieldRange := IsScalarTower.of_algHom e.toAlgHom
  let _ : ValuativeExtension L ι.fieldRange := e.toAlgHom.valuativeExtension
  have hLE : IsUnramified L ι.fieldRange := by
    apply IsUnramified.of_adjoin_range_eq_top (K := K) (L := L) (F := L)
      (M := ι.fieldRange) e
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := e.surjective x
    exact IntermediateField.subset_adjoin L (Set.range (e : L → ι.fieldRange)) ⟨z, rfl⟩
  let _ : IsUnramified L ι.fieldRange := hLE
  exact IsUnramified.trans K L ι.fieldRange

/-- The local invariant of a class inflated from an arbitrary presented unramified extension is
its concrete unramified invariant. -/
theorem invMap_relBrInfl_unramified (ι : L →ₐ[K] SeparableClosure K)
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) :
    invMap K (relBrInfl K L ι y) = unramifiedInv K L y := by
  let E := ι.fieldRange
  let e : L ≃ₐ[K] E := ι.equivFieldRange
  let _ : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let _ : ValuativeRel E := finiteExtensionValuativeRel K E
  let _ : TopologicalSpace E := finiteExtensionNormedFieldTopology K E
  let _ : IsNonarchimedeanLocalField E := finiteExtension_isNonarchimedeanLocalField K E
  let _ : ValuativeExtension K E := finiteExtension_valuativeExtension K E
  let _ : IsGalois K E := IsGalois.of_algEquiv e
  let _ : IsUnramified K E := isUnramified_fieldRange K L ι
  have hι : E.val.comp e.toAlgHom = ι := by
    change ι.fieldRange.val.comp ι.equivFieldRange.toAlgHom = ι
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply]
    exact AlgHom.equivFieldRange_apply_coe ι x
  exact invMap_relBrInfl_unramified_of_equiv K L E e ι hι y

/-! ### The normalization -/

/-- The Frobenius character transported to the Galois group of a normal layer. -/
private def layerFrobeniusCharacter (ι : L →ₐ[K] SeparableClosure K) :
    Additive (Abelianization
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) →+
        AddCircle (1 : ℚ) :=
  (frobeniusCharacter K L).comp
    (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr).toAddMonoidHom

/-- The transported character takes layer Frobenius to the reciprocal of its order. -/
private theorem layerFrobeniusCharacter_frobenius (ι : L →ₐ[K] SeparableClosure K) :
    layerFrobeniusCharacter K L ι
        (Additive.ofMul (Abelianization.of (layerFrobenius K L ι))) =
      ((1 / orderOf (layerFrobenius K L ι) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [layerFrobeniusCharacter, AddMonoidHom.comp_apply]
  change frobeniusCharacter K L
    (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr
      (Additive.ofMul (Abelianization.of (layerFrobenius K L ι)))) = _
  rw [MulEquiv.toAdditive_apply_apply, toMul_ofMul, abelianizationCongr_of,
    orderOf_layerFrobenius, layerFrobenius, MulEquiv.apply_symm_apply,
    frobeniusCharacter_frobenius]

/-- A ground-field unit as an invariant coefficient of the normal layer. -/
private def layerGroundInvariant (a : Kˣ) :=
  ((NormalLayer.ofOpenNormal
    (fixingOpenNormalSubgroup K L)).groundLevelEquiv (unitsFormation K)).symm
      (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
        (Additive.ofMul a))

/-- The periodicity class of a ground-field unit in the normal layer. -/
private def layerPeriodicClass (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).H (unitsFormation K) 2 := by
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  let F := unitsFormation K
  let _ : CommGroup X.Gal := layerCommGroup K L ι
  let A := X.rep F
  let z : LinearMap.ker
      (Rep.applyAsHom A (layerFrobenius K L ι) - (𝟙 A : A ⟶ A)).hom.toLinearMap :=
    ⟨layerGroundInvariant K L a, by
      rw [LinearMap.mem_ker]
      simpa [Rep.sub_hom, sub_eq_zero] using
        (layerGroundInvariant K L a).2 (layerFrobenius K L ι)⟩
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven A (layerFrobenius K L ι)
    (mem_zpowers_layerFrobenius K L ι) 2 even_two z

/-- A ground-field unit as a Frobenius-fixed coefficient of the concrete representation. -/
private def concreteFixedGround (a : Kˣ) : LinearMap.ker
      (Rep.applyAsHom (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)
        (frobeniusAlgEquiv (K := K) (L := L)) - 𝟙 _).hom.toLinearMap := by
  refine ⟨Rep.toAdditive.symm
    (Additive.ofMul (Units.map (algebraMap K L : K →* L) a)), ?_⟩
  rw [LinearMap.mem_ker]
  simp only [Rep.sub_hom, Representation.IntertwiningMap.sub_toLinearMap,
    LinearMap.sub_apply, sub_eq_zero]
  apply Rep.toAdditive.injective
  apply Additive.toMul.injective
  apply Units.ext
  exact AlgEquiv.commutes _ _

/-- The layer coefficient comparison sends the periodicity class to the concrete unramified
class. -/
private theorem layerCohomologyEquiv_layerPeriodicClass
    (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    layerCohomologyEquiv ι 2 (layerPeriodicClass K L ι a) =
      unramifiedClass K L (Additive.ofMul a) := by
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  let F := unitsFormation K
  let _ : CommGroup X.Gal := layerCommGroup K L ι
  let A := X.rep F
  let z : LinearMap.ker
      (Rep.applyAsHom A (layerFrobenius K L ι) - (𝟙 A : A ⟶ A)).hom.toLinearMap :=
    ⟨layerGroundInvariant K L a, by
      rw [LinearMap.mem_ker]
      simpa [Rep.sub_hom, sub_eq_zero] using
        (layerGroundInvariant K L a).2 (layerFrobenius K L ι)⟩
  rw [layerPeriodicClass, layerCohomologyEquiv_apply]
  have hmap := Rep.FiniteCyclicGroup.map_groupCohomologyπEven_two
    (A := Rep.ofMulDistribMulAction Gal(L/K) Lˣ) (B := A)
    (frobeniusAlgEquiv (K := K) (L := L))
    (fun σ => by rw [zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top σ)
    (layerGalEquiv ι).symm (mem_zpowers_layerFrobenius K L ι) 1
    (by simp [layerFrobenius]) (layerCoefficientHom ι) 1
    (by simp only [one_mul]; exact Nat.card_congr (layerGalEquiv ι).toEquiv.symm)
    z (concreteFixedGround K L a) (by
      rw [one_smul, layerCoefficientHom_apply]
      exact congrArg Rep.toAdditive.symm (layerCoefficientEquiv_groundLevel ι a).symm)
  rw [hmap]
  exact (unramifiedClass_apply K L a).symm

/-- The Tate cup of a ground-field unit with the Frobenius connecting class. -/
private def layerCharacterCupTate (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).TateH (unitsFormation K) 2 := by
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  let F := unitsFormation K
  let _ : CommGroup X.Gal := layerCommGroup K L ι
  let A := X.rep F
  exact (tateCohomologyFunctor 2).map (ρ_ A).hom
    (TateCohomology.cup A (Rep.trivial ℤ X.Gal ℤ) 0 2 2 (zero_add 2)
      (TateCohomology.H0π A (layerGroundInvariant K L a))
      (X.characterConnectingClass (layerFrobeniusCharacter K L ι)))

/-- The Frobenius character cup is the inverse comparison image of the layer periodicity
class. -/
private theorem layerCharacterCupTate_eq (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    layerCharacterCupTate K L ι a =
      ((NormalLayer.ofOpenNormal
        (fixingOpenNormalSubgroup K L)).tateHIsoH (unitsFormation K) 2).inv
          (layerPeriodicClass K L ι a) := by
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  let F := unitsFormation K
  let _ : CommGroup X.Gal := layerCommGroup K L ι
  let A := X.rep F
  let x := layerGroundInvariant K L a
  let z : LinearMap.ker
      (Rep.applyAsHom A (layerFrobenius K L ι) - (𝟙 A : A ⟶ A)).hom.toLinearMap :=
    ⟨x, by
      rw [LinearMap.mem_ker]
      simpa [Rep.sub_hom, sub_eq_zero] using x.2 (layerFrobenius K L ι)⟩
  rw [layerCharacterCupTate, layerPeriodicClass, NormalLayer.characterConnectingClass_def,
    NormalLayer.tateHIsoH_def]
  exact TauCeti.TateCohomology.cup_characterConnectingClass_eq_groupCohomologyπEven
    (mem_zpowers_layerFrobenius K L ι) (layerFrobeniusCharacter K L ι)
      (layerFrobeniusCharacter_frobenius K L ι) A x z rfl

/-- The character cup is the periodicity class of the ground-field unit. -/
private theorem layerArtinCharacterCup_eq_layerPeriodicClass
    (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).artinCharacterCup
        (unitsFormation K)
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
          (Additive.ofMul a))
        (layerFrobeniusCharacter K L ι) = layerPeriodicClass K L ι a := by
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  let F := unitsFormation K
  let _ : CommGroup X.Gal := layerCommGroup K L ι
  let x := layerGroundInvariant K L a
  rw [show (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
      (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
      (Additive.ofMul a)) = X.groundLevelEquiv F x from by
        exact (X.groundLevelEquiv F).apply_symm_apply _ |>.symm]
  rw [NormalLayer.artinCharacterCup_apply, NormalLayer.zeroTateClass_groundLevelEquiv]
  rw [← layerCharacterCupTate, layerCharacterCupTate_eq, Iso.inv_hom_id_apply]

/-- The character cup of a ground-field unit maps to its standard unramified class. -/
private theorem layerArtinCharacterCup_eq_unramifiedClass
    (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    layerCohomologyEquiv ι 2
        ((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).artinCharacterCup
          (unitsFormation K)
          (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
            (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
            (Additive.ofMul a))
          (layerFrobeniusCharacter K L ι)) =
      unramifiedClass K L (Additive.ofMul a) := by
  rw [layerArtinCharacterCup_eq_layerPeriodicClass,
    layerCohomologyEquiv_layerPeriodicClass]

/-- The local class-formation invariant of the Frobenius character cup of a uniformizer is the
reciprocal of the unramified degree. -/
private theorem localClassFormation_inv_artinCharacterCup_of_isUniformizer
    (ι : L →ₐ[K] SeparableClosure K) {π : Kˣ} (hπ : IsUniformizer K π) :
    (localClassFormation K).inv
        (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L))
        ((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).artinCharacterCup
          (unitsFormation K)
          (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
            (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
            (Additive.ofMul π))
          (layerFrobeniusCharacter K L ι)) =
      ((1 / Module.finrank K L : ℚ) : AddCircle (1 : ℚ)) := by
  rw [localClassFormation_inv]
  rw [← relBrInfl_layerCohomologyEquiv K L ι]
  rw [invMap_relBrInfl_unramified K L ι]
  rw [layerArtinCharacterCup_eq_unramifiedClass]
  exact unramifiedInv_unramifiedClass_of_isUniformizer hπ

/-- **The unramified normalization of finite local reciprocity**: the local Artin map sends a
uniformizer of `K` to arithmetic Frobenius in `Gal(L/K)ᵃᵇ`. -/
theorem localArtinMap_uniformizer (ι : L →ₐ[K] SeparableClosure K)
    {π : Kˣ} (hπ : IsUniformizer K π) :
    localArtinMap K L ι (Additive.ofMul π) =
      Additive.ofMul (Abelianization.of (frobeniusAlgEquiv (K := K) (L := L))) := by
  apply injective_frobeniusCharacter K L
  rw [frobeniusCharacter_frobenius, localArtinMap_apply, localArtinEquiv_mk]
  change layerFrobeniusCharacter K L ι
      ((localClassFormation K).artinMap
        (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L))
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
          (Additive.ofMul π))) = _
  rw [← (localClassFormation K).character_artinMap]
  exact localClassFormation_inv_artinCharacterCup_of_isUniformizer K L ι hπ

end TauCeti.ClassFieldTheory
