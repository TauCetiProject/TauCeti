/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.LocalField.Unramified.Coordinate
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Cyclic
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.UnitsLayer
import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# Finite unramified local reciprocity

For a finite unramified Galois extension `L/K`, this file normalizes the finite local Artin map
by arithmetic Frobenius. The character which sends arithmetic Frobenius to `1 / [L : K]` detects
the cyclic Galois group. The character formula for the Artin map and the explicit cyclic cup
product then identify the Artin symbol of a uniformizer. The norm criterion for unramified
extensions extends this calculation to every element: its Artin symbol is the power of Frobenius
given by its normalized valuation.

Passing through all finite unramified extensions proves that the unramified coordinate of the
absolute local Artin symbol is the image of the normalized valuation in `zHat`. Consequently,
lifts of Artin symbols of units lie in inertia, while lifts of uniformizer symbols are arithmetic
Frobenius lifts. Conversely, every element of the image of inertia in `G_K^ab` is the Artin symbol
of a unit. For a uniformizer `ϖ`, the products of the Artin symbols of the compact group `𝒪[K]ˣ`
with the image of `ℤ̂` under `n ↦ Art(ϖ)ⁿ` form a compact set containing the dense image of the
Artin map, hence all of `G_K^ab`; the unramified coordinate recovers `n` from such a product.

## Main definitions

* `TauCeti.ClassFieldTheory.frobeniusCharacter`: the faithful character of the Galois group of an
  unramified extension which sends arithmetic Frobenius to `1 / [L : K]`.

## Main results

* `TauCeti.ClassFieldTheory.localArtinMap_uniformizer`: the finite local Artin map sends every
  uniformizer to arithmetic Frobenius.
* `TauCeti.ClassFieldTheory.localArtinMap_eq_frobenius_pow_valuation`: the finite local Artin map
  is the normalized-valuation power of arithmetic Frobenius.
* `TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap`: the unramified coordinate of the
  absolute local Artin map is normalized valuation.
* `TauCeti.ClassFieldTheory.mem_inertiaSubgroup_of_mk_eq_artinMap`: a lift of the Artin symbol of
  a unit lies in inertia.
* `TauCeti.ClassFieldTheory.isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer`: a lift of the
  Artin symbol of a uniformizer is an arithmetic Frobenius lift.
* `TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero`: the Artin symbols of the units of
  `𝒪[K]` are exactly the image of inertia in `G_K^ab`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §§3–4.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory MonoidalCategory
open _root_.ValuativeRel
open scoped Pointwise

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

/-- **Finite unramified reciprocity is normalized valuation.** For every `x : Kˣ`, its local
Artin symbol in a finite unramified extension is arithmetic Frobenius raised to `v_K(x)`. -/
@[simp]
theorem localArtinMap_eq_frobenius_pow_valuation
    (ι : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    localArtinMap K L ι (Additive.ofMul x) =
      Additive.ofMul (Abelianization.of
        (frobeniusAlgEquiv (K := K) (L := L) ^ (normalizedValuation K x).toAdd)) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  let n := (normalizedValuation K x).toAdd
  let u := x * π ^ (-n)
  have huValuation : normalizedValuation K u = 1 :=
    (normalizedValuation_eq_one_iff u).2 <| (mem_unitFiltration_zero u).1 <|
      mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def π).1 hπ) x
  let f : Kˣ →* Abelianization Gal(L/K) :=
    { toFun := fun a ↦ (localArtinMap K L ι (Additive.ofMul a)).toMul
      map_one' := by simp
      map_mul' := by simp }
  have hfπ : f π = Abelianization.of (frobeniusAlgEquiv (K := K) (L := L)) := by
    simpa [f] using congrArg Additive.toMul (localArtinMap_uniformizer K L ι hπ)
  have hfu : f u = 1 := by
    have hu : localArtinMap K L ι (Additive.ofMul u) = 0 := by
      rw [localArtinMap_eq_zero_iff, mem_normGroup_iff_dvd_normalizedValuation, huValuation,
        toAdd_one]
      exact dvd_zero _
    simpa [f] using congrArg Additive.toMul hu
  have hx : x = π ^ n * u := by
    simp [u, n]
  have hfx : f x = Abelianization.of (frobeniusAlgEquiv (K := K) (L := L) ^ n) := calc
    f x = f (π ^ n * u) := congrArg f hx
    _ = f π ^ n * f u := by rw [map_mul, map_zpow]
    _ = Abelianization.of (frobeniusAlgEquiv (K := K) (L := L)) ^ n := by rw [hfπ, hfu, mul_one]
    _ = Abelianization.of (frobeniusAlgEquiv (K := K) (L := L) ^ n) := by rw [map_zpow]
  apply Additive.toMul.injective
  simpa [f, n] using hfx

/-! ### The absolute unramified coordinate -/

/-- **The unramified coordinate of the absolute local Artin map is normalized valuation.** The
coordinate of `Art_K(x)` is the image of `v_K(x) ∈ ℤ` in the profinite integers. -/
@[simp]
theorem unramifiedCoordinate_artinMap (x : Kˣ) :
    unramifiedCoordinate K (artinMap K x) = zHat.ofInt (normalizedValuation K x) := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure (artinMap K x)
  rw [← hσ]
  rw [← ofAdd_toAdd (normalizedValuation K x), zHat.ofInt_ofAdd]
  apply (unramifiedCoordinate_mk_eq_gen_zpow_iff σ
    (normalizedValuation K x).toAdd).2
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  obtain ⟨f, hf, hy⟩ := mem_maximalUnramifiedExtension_iff.1 y.2
  let L := unramifiedExtension K (AlgebraicClosure K) f
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
  have : IsUnramified K L := isUnramified_unramifiedExtension hf
  let hLsep : L ≤ separableClosure K (AlgebraicClosure K) := le_separableClosure K _ L
  let ι : L →ₐ[K] SeparableClosure K := IntermediateField.inclusion hLsep
  let _ : CommGroup Gal(L/K) := IsCyclic.commGroup
  have hfinite := artinMap_restrict K L ι x σ hσ
  have hformula := localArtinMap_eq_frobenius_pow_valuation K L ι x
  have hab : Abelianization.of
      (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ)) =
      Abelianization.of
        (frobeniusAlgEquiv (K := K) (L := L) ^ (normalizedValuation K x).toAdd) := by
    apply Additive.ofMul.injective
    exact hfinite.symm.trans hformula
  have hres : ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) =
      frobeniusAlgEquiv (K := K) (L := L) ^ (normalizedValuation K x).toAdd :=
    Abelianization.equivOfComm.injective hab
  have heval := DFunLike.congr_fun hres (⟨y, hy⟩ : L)
  have heval' := congrArg (fun z : L ↦ (z : AlgebraicClosure K)) heval
  rw [restrictMaximalUnramifiedHom_coe_apply,
    coe_maximalUnramifiedFrobenius_zpow_apply_of_mem _ hy]
  calc
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ (y : AlgebraicClosure K) =
        ((absoluteGaloisGroupRestrictEquiv K σ) (ι ⟨y, hy⟩) : AlgebraicClosure K) := by
      exact (coe_absoluteGaloisGroupRestrictEquiv_apply (K := K) σ (ι ⟨y, hy⟩)).symm
    _ = ((ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ))
          ⟨y, hy⟩ : L) := by
      exact congrArg (fun z : SeparableClosure K ↦ (z : AlgebraicClosure K))
        (ι.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv K σ)
          (⟨y, hy⟩ : L)).symm
    _ = ((frobeniusAlgEquiv (K := K) (L := L) ^ (normalizedValuation K x).toAdd)
          ⟨y, hy⟩ : L) := heval'

/-- Every lift of the absolute Artin symbol of a valuation-zero unit lies in inertia. -/
theorem mem_inertiaSubgroup_of_mk_eq_artinMap (u : Kˣ)
    (hu : ValuativeRel.valuation K (u : K) = 1) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K u) :
    σ ∈ inertiaSubgroup K := by
  rw [← unramifiedCoordinate_mk_eq_one_iff, hσ, unramifiedCoordinate_artinMap,
    (normalizedValuation_eq_one_iff u).2 hu, map_one]

/-- Every lift of the absolute Artin symbol of a uniformizer is an arithmetic Frobenius lift. -/
theorem isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer {π : Kˣ}
    (hπ : IsUniformizer K π) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K π) :
    IsArithFrobeniusLift K σ := by
  rw [← unramifiedCoordinate_mk_eq_gen_iff, hσ, unramifiedCoordinate_artinMap,
    (isUniformizer_def π).1 hπ, zHat.ofInt_ofAdd]
  simp

/-- **The units of `𝒪[K]` map onto the image of inertia.** The Artin symbols of the elements of
`U(K,0) = 𝒪[K]ˣ` are exactly the classes in `G_K^ab` of the elements of the inertia subgroup,
equivalently (`ker_unramifiedCoordinate`) the classes with trivial unramified coordinate. -/
theorem map_artinMap_unitFiltration_zero :
    (unitFiltration K 0).map (artinMap K) = (inertiaSubgroup K).map (QuotientGroup.mk' _) := by
  rw [← ker_unramifiedCoordinate]
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨u, hu, rfl⟩
    have hv : normalizedValuation K u = 1 := normalizedValuation_coe_unitFiltration_zero K ⟨u, hu⟩
    simp [hv]
  · obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective (K := K) (.ofAdd 1)
    set φ : zHat →ₜ* Field.absoluteGaloisGroupAbelianization K := zHat.lift (artinMap K ϖ)
    have hφ : (unramifiedCoordinate K).comp φ = .id _ :=
      zHat.hom_ext (by simp [φ, hϖ, zHat.ofInt_ofAdd])
    -- `Art(U(K,0)) · φ(ℤ̂)` is compact and contains the dense image of `artinMap K`, since
    -- `x = (x ϖ ^ (-v(x))) · ϖ ^ v(x)`.
    have hS : (artinMap K '' (unitFiltration K 0 : Set Kˣ)) * Set.range φ = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (denseRange_artinMap K).closure_range]
      refine ((((isCompact_unitFiltration (K := K) 0).image (continuous_artinMap K)).mul
        (isCompact_range φ.continuous)).isClosed).closure_subset_iff.2 ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨_, ⟨_, mul_zpow_neg_mem_unitFiltration_zero hϖ x, rfl⟩,
        _, ⟨zHat.ofInt (normalizedValuation K x), rfl⟩, ?_⟩
      simp [φ, map_zpow]
    -- Write `y = Art(u) · φ(z)`; the unramified coordinate of `y` is then `z`, so `z = 1`.
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨z, rfl⟩, rfl⟩ := hS.symm ▸ Set.mem_univ y
    have hv : normalizedValuation K u = 1 := normalizedValuation_coe_unitFiltration_zero K ⟨u, hu⟩
    have hz : z = 1 := by
      have hφz : unramifiedCoordinate K (φ z) = z := DFunLike.congr_fun hφ z
      simpa [hv, hφz] using hy
    exact ⟨u, hu, by simp [hz]⟩

end TauCeti.ClassFieldTheory
