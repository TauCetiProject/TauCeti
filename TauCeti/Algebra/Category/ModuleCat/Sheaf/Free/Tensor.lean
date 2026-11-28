/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed

/-!
# Tensor products with finite free sheaves of modules

For a finite index type `I` and a sheaf of modules `M`, tensoring `M` with the free sheaf
`free I` distributes over the finite biproduct decomposition `free I ≅ ⨁_I unit` because
`tensorLeft M` preserves colimits (being a left adjoint). This gives the canonical isomorphism
`(⨁_I M) ≅ M ⊗ free I` (`SheafOfModules.biproductConstIsoTensorFree`), together with its
compatibility formulas on summand inclusions.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

/-- A finite biproduct of copies of `M` is isomorphic to `M ⊗ free I`. -/
def _root_.SheafOfModules.biproductConstIsoTensorFree
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) (I : Type u) [Finite I] :
    (⨁ fun _ : I ↦ M) ≅ M ⊗ free (R := ringCatSheaf R) I := by
  letI : Fintype I := Fintype.ofFinite I
  have : HasBiproduct (C := _root_.SheafOfModules.{u} (ringCatSheaf R))
      fun _ : I ↦ 𝟙_ (_root_.SheafOfModules.{u} (ringCatSheaf R)) :=
    HasBiproduct.of_hasCoproduct _
  have : PreservesBiproduct
      (fun _ : I ↦ 𝟙_ (_root_.SheafOfModules.{u} (ringCatSheaf R))) (tensorLeft M) :=
    preservesBiproduct_of_preservesCoproduct (tensorLeft M)
  exact (biproduct.mapIso fun _ : I ↦ ρ_ M).symm ≪≫
    ((tensorLeft M).mapBiproduct
      (fun _ : I ↦ 𝟙_ (_root_.SheafOfModules.{u} (ringCatSheaf R)))).symm ≪≫
    whiskerLeftIso M (biproductIsoFree (R := R) I)

/-- `biproductConstIsoTensorFree` sends the `i`-th summand inclusion to `M ◁ ιFree i`, up to the
right unitor of `M`. -/
@[reassoc (attr := simp)]
theorem _root_.SheafOfModules.biproduct_ι_biproductConstIsoTensorFree_hom
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) {I : Type u} [Finite I] (i : I) :
    biproduct.ι (fun _ : I ↦ M) i ≫ (M.biproductConstIsoTensorFree I).hom =
      (ρ_ M).inv ≫ M ◁ ιFree i := by
  let : Fintype I := Fintype.ofFinite I
  have : HasBiproduct (C := _root_.SheafOfModules.{u} (ringCatSheaf R))
      fun _ : I ↦ 𝟙_ (_root_.SheafOfModules.{u} (ringCatSheaf R)) :=
    HasBiproduct.of_hasCoproduct _
  have : PreservesBiproduct
      (fun _ : I ↦ 𝟙_ (_root_.SheafOfModules.{u} (ringCatSheaf R))) (tensorLeft M) :=
    preservesBiproduct_of_preservesCoproduct (tensorLeft M)
  simp only [_root_.SheafOfModules.biproductConstIsoTensorFree, Iso.trans_hom, Iso.symm_hom,
    biproduct.mapIso_inv, biproduct.ι_map_assoc, whiskerLeftIso_hom]
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
  exact congrArg ((ρ_ M).inv ≫ ·)
    ((MonoidalCategory.whiskerLeft_comp M _ _).symm.trans (by simp))

/-- The inverse of `biproductConstIsoTensorFree` sends `M ◁ ιFree i` to the `i`-th summand
inclusion, up to the right unitor of `M`. -/
@[reassoc (attr := simp)]
theorem _root_.SheafOfModules.whiskerLeft_ιFree_biproductConstIsoTensorFree_inv
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) {I : Type u} [Finite I] (i : I) :
    M ◁ ιFree i ≫ (M.biproductConstIsoTensorFree I).inv =
      (ρ_ M).hom ≫ biproduct.ι (fun _ : I ↦ M) i := by
  rw [Iso.comp_inv_eq, Category.assoc,
    _root_.SheafOfModules.biproduct_ι_biproductConstIsoTensorFree_hom, Iso.hom_inv_id_assoc]

end

end TauCeti.SheafOfModules
