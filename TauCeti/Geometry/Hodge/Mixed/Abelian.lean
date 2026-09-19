/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.CoimageImage
public import TauCeti.Geometry.Hodge.Mixed.Prod
public import TauCeti.Geometry.Hodge.Mixed.Zero
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The abelian category of mixed Hodge structures

Mixed Hodge structures form an abelian category. Binary direct sums are constructed with
componentwise filtrations and the usual rational inclusions and projections. Together with the
zero object, they provide finite products. The existing kernels, cokernels and invertible
coimage–image comparisons then give the abelian structure by
`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`.

## References

Deligne, *Théorie de Hodge II*, 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/

public section

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

/-- The binary direct-sum bicone, with product carriers and componentwise filtrations. -/
-- The dependent carrier types in the projection formulas require exposure, as for kernels.
@[expose, simps pt fst snd inl inr]
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

/-- The componentwise direct sum is both a product and a coproduct. -/
noncomputable def binaryBiconeIsBilimit (X Y : MixedHodgeStructureCat.{u}) :
    (binaryBicone X Y).IsBilimit := by
  apply isBinaryBilimitOfTotal
  apply hom_ext
  rw [MixedHodgeStructure.Hom.add_toRatLinearMap
    ((binaryBicone X Y).fst ≫ (binaryBicone X Y).inl)
    ((binaryBicone X Y).snd ≫ (binaryBicone X Y).inr)]
  simp only [comp_toRatLinearMap, id_toRatLinearMap]
  simp only [binaryBicone_fst, binaryBicone_snd, binaryBicone_inl, binaryBicone_inr,
    MixedHodgeStructure.fst_toRatLinearMap, MixedHodgeStructure.snd_toRatLinearMap,
    MixedHodgeStructure.inl_toRatLinearMap, MixedHodgeStructure.inr_toRatLinearMap]
  exact LinearMap.coprod_inl_inr

noncomputable instance hasBinaryBiproducts : HasBinaryBiproducts MixedHodgeStructureCat.{u} where
  has_binary_biproduct X Y :=
    HasBinaryBiproduct.mk ⟨binaryBicone X Y, binaryBiconeIsBilimit X Y⟩

noncomputable instance hasFiniteProducts : HasFiniteProducts MixedHodgeStructureCat.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- Mixed Hodge structures, with rational Hodge morphisms, form an abelian category. -/
noncomputable instance abelian : Abelian MixedHodgeStructureCat.{u} :=
  Abelian.ofCoimageImageComparisonIsIso

end TauCeti.Hodge.MixedHodgeStructureCat
