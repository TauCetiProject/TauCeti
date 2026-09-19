/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Bigrading
public import TauCeti.Geometry.Hodge.Mixed.Zero
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Products of mixed Hodge structures

The product of two mixed Hodge structures has componentwise weight and Hodge filtrations.
The product of their Deligne bigradings witnesses purity on the weight-graded pieces.
The two inclusions and projections are mixed Hodge morphisms; their rational maps are the
usual inclusions and projections of vector spaces. Their binary bicone is a bilimit, giving
binary biproducts and, together with the zero object, finite products in the category of
mixed Hodge structures.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}

namespace MixedHodgeStructure

variable (X : MixedHodgeStructure hℚ hℂ) (Y : MixedHodgeStructure h'ℚ h'ℂ)

/-- The product mixed Hodge structure, with componentwise weight and Hodge filtrations. -/
noncomputable def prod : MixedHodgeStructure (IsBaseChange.prodMap ιℚ ι'ℚ hℚ h'ℚ)
    (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ) :=
  ofIsHodgeBigrading
    (X.isHodgeBigrading_deligneSplittingFamily.prod Y.isHodgeBigrading_deligneSplittingFamily)
    (by
      obtain ⟨i, hi⟩ := X.WQ_top
      obtain ⟨j, hj⟩ := Y.WQ_top
      exact ⟨max i j, by
        rw [eq_top_mono (X.WQ_monotone (le_max_left _ _)) hi,
          eq_top_mono (Y.WQ_monotone (le_max_right _ _)) hj, Submodule.prod_top]⟩)
    (by
      obtain ⟨i, hi⟩ := X.WQ_bot
      obtain ⟨j, hj⟩ := Y.WQ_bot
      exact ⟨min i j, by
        rw [eq_bot_mono (X.WQ_monotone (min_le_left _ _)) hi,
          eq_bot_mono (Y.WQ_monotone (min_le_right _ _)) hj, Submodule.prod_bot]⟩)
    (by
      obtain ⟨i, hi⟩ := X.F_top
      obtain ⟨j, hj⟩ := Y.F_top
      exact ⟨min i j, by
        rw [eq_top_mono (X.F_antitone (min_le_left _ _)) hi,
          eq_top_mono (Y.F_antitone (min_le_right _ _)) hj, Submodule.prod_top]⟩)
    (by
      obtain ⟨i, hi⟩ := X.F_bot
      obtain ⟨j, hj⟩ := Y.F_bot
      exact ⟨max i j, by
        rw [eq_bot_mono (X.F_antitone (le_max_left _ _)) hi,
          eq_bot_mono (Y.F_antitone (le_max_right _ _)) hj, Submodule.prod_bot]⟩)

@[simp]
theorem prod_WQ (k : ℤ) : (X.prod Y).WQ k = (X.WQ k).prod (Y.WQ k) := by
  simp [prod]

@[simp]
theorem prod_F (p : ℤ) : (X.prod Y).F p = (X.F p).prod (Y.F p) := by
  simp [prod]

/-- The first projection from the product mixed Hodge structure. -/
noncomputable def fst : Hom (X.prod Y) X where
  toRatLinearMap := LinearMap.fst ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := (prod_WQ X Y _ ▸ hx).1
  map_mem_F _ _ hx := by
    rw [rationalMapToComplex_fst hℚ hℂ h'ℚ h'ℂ]
    exact (prod_F X Y _ ▸ hx).1

/-- The second projection from the product mixed Hodge structure. -/
noncomputable def snd : Hom (X.prod Y) Y where
  toRatLinearMap := LinearMap.snd ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := (prod_WQ X Y _ ▸ hx).2
  map_mem_F _ _ hx := by
    rw [rationalMapToComplex_snd hℚ hℂ h'ℚ h'ℂ]
    exact (prod_F X Y _ ▸ hx).2

/-- The first inclusion into the product mixed Hodge structure. -/
noncomputable def inl : Hom X (X.prod Y) where
  toRatLinearMap := LinearMap.inl ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := by simpa using hx
  map_mem_F _ _ hx := by
    simpa [rationalMapToComplex_inl hℚ hℂ h'ℚ h'ℂ] using hx

/-- The second inclusion into the product mixed Hodge structure. -/
noncomputable def inr : Hom Y (X.prod Y) where
  toRatLinearMap := LinearMap.inr ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := by simpa using hx
  map_mem_F _ _ hx := by
    simpa [rationalMapToComplex_inr hℚ hℂ h'ℚ h'ℂ] using hx

@[simp]
theorem fst_toRatLinearMap : (X.fst Y).toRatLinearMap = LinearMap.fst ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem snd_toRatLinearMap : (X.snd Y).toRatLinearMap = LinearMap.snd ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem inl_toRatLinearMap : (X.inl Y).toRatLinearMap = LinearMap.inl ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem inr_toRatLinearMap : (X.inr Y).toRatLinearMap = LinearMap.inr ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem fst_toLinearMap : (X.fst Y).toLinearMap = LinearMap.fst ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_fst hℚ hℂ h'ℚ h'ℂ]

@[simp]
theorem snd_toLinearMap : (X.snd Y).toLinearMap = LinearMap.snd ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_snd hℚ hℂ h'ℚ h'ℂ]

@[simp]
theorem inl_toLinearMap : (X.inl Y).toLinearMap = LinearMap.inl ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_inl hℚ hℂ h'ℚ h'ℂ]

@[simp]
theorem inr_toLinearMap : (X.inr Y).toLinearMap = LinearMap.inr ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_inr hℚ hℂ h'ℚ h'ℂ]

end MixedHodgeStructure

end TauCeti.Hodge

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

/-- The binary direct-sum bicone, with product carriers and componentwise filtrations. -/
noncomputable def binaryBicone (X Y : MixedHodgeStructureCat.{u}) : BinaryBicone X Y where
  pt := .of (IsBaseChange.prodMap X.toRat Y.toRat X.isBaseChangeRat Y.isBaseChangeRat)
    (IsBaseChange.prodMap X.toComplex Y.toComplex X.isBaseChangeComplex Y.isBaseChangeComplex)
    (X.hs.prod Y.hs)
  fst := X.hs.fst Y.hs
  snd := X.hs.snd Y.hs
  inl := X.hs.inl Y.hs
  inr := X.hs.inr Y.hs
  inl_fst := by apply hom_ext; simp
  inl_snd := by apply hom_ext; simp
  inr_fst := by apply hom_ext; simp
  inr_snd := by apply hom_ext; simp

/-- The direct-sum point has product carriers and componentwise filtrations. -/
@[simp]
theorem binaryBicone_pt (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).pt =
      .of (IsBaseChange.prodMap X.toRat Y.toRat X.isBaseChangeRat Y.isBaseChangeRat)
        (IsBaseChange.prodMap X.toComplex Y.toComplex X.isBaseChangeComplex Y.isBaseChangeComplex)
        (X.hs.prod Y.hs) :=
  (rfl)

/-- The direct-sum `fst` map is the corresponding mixed Hodge morphism. -/
@[simp]
theorem binaryBicone_fst (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).fst = eqToHom (binaryBicone_pt X Y) ≫ X.hs.fst Y.hs := by
  exact (Category.id_comp (obj := MixedHodgeStructureCat.{u})
    (X := (binaryBicone X Y).pt) (Y := X) (X.hs.fst Y.hs)).symm

/-- The direct-sum `snd` map is the corresponding mixed Hodge morphism. -/
@[simp]
theorem binaryBicone_snd (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).snd = eqToHom (binaryBicone_pt X Y) ≫ X.hs.snd Y.hs := by
  exact (Category.id_comp (obj := MixedHodgeStructureCat.{u})
    (X := (binaryBicone X Y).pt) (Y := Y) (X.hs.snd Y.hs)).symm

/-- The direct-sum `inl` map is the corresponding mixed Hodge morphism. -/
@[simp]
theorem binaryBicone_inl (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).inl = X.hs.inl Y.hs ≫ eqToHom (binaryBicone_pt X Y).symm := by
  exact (Category.comp_id (obj := MixedHodgeStructureCat.{u})
    (X := X) (Y := (binaryBicone X Y).pt) (X.hs.inl Y.hs)).symm

/-- The direct-sum `inr` map is the corresponding mixed Hodge morphism. -/
@[simp]
theorem binaryBicone_inr (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).inr = X.hs.inr Y.hs ≫ eqToHom (binaryBicone_pt X Y).symm := by
  exact (Category.comp_id (obj := MixedHodgeStructureCat.{u})
    (X := Y) (Y := (binaryBicone X Y).pt) (X.hs.inr Y.hs)).symm

/-- The componentwise direct sum is both a product and a coproduct. -/
noncomputable def binaryBiconeIsBilimit (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).IsBilimit := by
  apply isBinaryBilimitOfTotal
  let P : MixedHodgeStructureCat.{u} :=
    .of (IsBaseChange.prodMap X.toRat Y.toRat X.isBaseChangeRat Y.isBaseChangeRat)
      (IsBaseChange.prodMap X.toComplex Y.toComplex X.isBaseChangeComplex Y.isBaseChangeComplex)
      (X.hs.prod Y.hs)
  have total : (X.hs.fst Y.hs : P ⟶ X) ≫ X.hs.inl Y.hs +
      (X.hs.snd Y.hs : P ⟶ Y) ≫ X.hs.inr Y.hs = 𝟙 P := by
    apply hom_ext
    rw [MixedHodgeStructure.Hom.add_toRatLinearMap]
    simp only [comp_toRatLinearMap, id_toRatLinearMap,
      MixedHodgeStructure.fst_toRatLinearMap, MixedHodgeStructure.snd_toRatLinearMap,
      MixedHodgeStructure.inl_toRatLinearMap, MixedHodgeStructure.inr_toRatLinearMap]
    exact LinearMap.coprod_inl_inr
  simp only [binaryBicone_fst, binaryBicone_snd, binaryBicone_inl, binaryBicone_inr,
    Category.assoc, ← Preadditive.comp_add]
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, total]
  rw [Category.id_comp, eqToHom_trans]
  exact eqToHom_refl _ _

noncomputable instance hasBinaryBiproducts : HasBinaryBiproducts MixedHodgeStructureCat.{u} where
  has_binary_biproduct X Y :=
    HasBinaryBiproduct.mk ⟨binaryBicone X Y, binaryBiconeIsBilimit X Y⟩

noncomputable instance hasFiniteProducts : HasFiniteProducts MixedHodgeStructureCat.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

end TauCeti.Hodge.MixedHodgeStructureCat
