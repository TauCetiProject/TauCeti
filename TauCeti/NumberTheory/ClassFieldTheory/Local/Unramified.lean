/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Cyclic
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.UnitsLayer

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
  rw [frobeniusCharacter, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.toMultiplicativeRight_symm_apply_apply, toMul_ofMul, MulEquiv.trans_apply,
    Abelianization.equivOfComm_symm_apply, Abelianization.lift_apply_of, MonoidHom.id_apply,
    zmodMulEquivOfGenerator_symm_apply_generator]
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

/-! ### The normalization -/

/-- The Frobenius character transported to the Galois group of a normal layer. -/
private def layerFrobeniusCharacter (ι : L →ₐ[K] SeparableClosure K) :
    Additive (Abelianization
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) →+
        AddCircle (1 : ℚ) :=
  (frobeniusCharacter K L).comp
    (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr).toAddMonoidHom

/-- The transported character evaluates the Frobenius character on the concrete Galois group. -/
private theorem layerFrobeniusCharacter_apply (ι : L →ₐ[K] SeparableClosure K)
    (x : Additive (Abelianization
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal)) :
    layerFrobeniusCharacter K L ι x =
      frobeniusCharacter K L (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr x) := by
  rw [layerFrobeniusCharacter, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]

/-- The transported character takes layer Frobenius to the reciprocal of its order. -/
private theorem layerFrobeniusCharacter_frobenius (ι : L →ₐ[K] SeparableClosure K) :
    layerFrobeniusCharacter K L ι
        (Additive.ofMul (Abelianization.of (layerFrobenius K L ι))) =
      ((1 / orderOf (layerFrobenius K L ι) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [layerFrobeniusCharacter_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    abelianizationCongr_of, orderOf_layerFrobenius, layerFrobenius, MulEquiv.apply_symm_apply,
    frobeniusCharacter_frobenius]

/-- A ground-field unit as an invariant coefficient of the normal layer. -/
private def layerGroundInvariant (a : Kˣ) :=
  ((NormalLayer.ofOpenNormal
    (fixingOpenNormalSubgroup K L)).groundLevelEquiv (unitsFormation K)).symm
      (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
        (Additive.ofMul a))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [IsGalois K L] [IsUnramified K L] in
/-- The ground-level identification recovers the unit from its invariant coefficient. -/
private theorem groundLevelEquiv_layerGroundInvariant (a : Kˣ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).groundLevelEquiv (unitsFormation K)
        (layerGroundInvariant K L a) =
      unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L)) (Additive.ofMul a) := by
  rw [layerGroundInvariant, LinearEquiv.apply_symm_apply]

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
  rw [← groundLevelEquiv_layerGroundInvariant, NormalLayer.artinCharacterCup_apply,
    NormalLayer.zeroTateClass_groundLevelEquiv, ← layerCharacterCupTate, layerCharacterCupTate_eq,
    Iso.inv_hom_id_apply]

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
  rw [frobeniusCharacter_frobenius, localArtinMap_apply, localArtinEquiv_mk,
    ← layerFrobeniusCharacter_apply, ← (localClassFormation K).character_artinMap]
  exact localClassFormation_inv_artinCharacterCup_of_isUniformizer K L ι hπ

end TauCeti.ClassFieldTheory
