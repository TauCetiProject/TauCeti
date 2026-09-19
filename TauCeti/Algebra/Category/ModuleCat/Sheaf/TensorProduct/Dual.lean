/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import TauCeti.CategoryTheory.Monoidal.Rigid.Biproduct

/-!
# Finite free sheaves of modules are self-dual

Let `R` be a sheaf of commutative rings on a small site. In the symmetric monoidal category of
sheaves of `R`-modules, the free sheaf `free I` on a finite type `I` is dualizable, with dual
`free I` itself. Writing `eᵢ = ιFree i` for the basis sections, the evaluation
`free I ⊗ free I ⟶ R` sends `eᵢ ⊗ eⱼ` to `δᵢⱼ`, and the coevaluation `R ⟶ free I ⊗ free I` sends
`1` to `∑ i, eᵢ ⊗ eᵢ`.

The pairing is obtained from `TauCeti.ExactPairing.biproduct`: `free I` is the biproduct of `I`
copies of the unit `R` (`TauCeti.SheafOfModules.biproductIsoFree`), and the unit is canonically
self-dual.
Finite free sheaves are the local models of finite locally free sheaves, so this is the local
input for showing that finite locally free sheaves are dualizable.

## Main declarations

* `TauCeti.SheafOfModules.biproductIsoFree`: the free sheaf on a finite type is the biproduct of
  copies of the unit;
* `TauCeti.SheafOfModules.exactPairingFree`: the exact pairing between `free I` and itself;
* `TauCeti.SheafOfModules.ιFree_tensorHom_ιFree_evaluation`,
  `TauCeti.SheafOfModules.ιFree_tensorHom_ιFree_evaluation_of_ne` and
  `TauCeti.SheafOfModules.coevaluation_free`: its evaluation and coevaluation on basis sections.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

open _root_.SheafOfModules

variable {R : Sheaf J CommRingCat.{u}} (I : Type u) [Finite I]

/-- The free sheaf of modules on a finite type `I` is the biproduct of `I` copies of the unit. -/
def biproductIsoFree :
    ⨁ (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅ free (R := ringCatSheaf R) I :=
  (biproduct.isColimit _).coconePointUniqueUpToIso (isColimitFreeCofan I)

variable {I}

/-- `biproductIsoFree` sends the `i`-th summand to the `i`-th basis section. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biproductIsoFree_hom (i : I) :
    biproduct.ι (fun _ : I ↦ unit (ringCatSheaf R)) i ≫
      (biproductIsoFree (R := R) I).hom = ιFree i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitFreeCofan I) ⟨i⟩

/-- The inverse of `biproductIsoFree` sends the `i`-th basis section to the `i`-th summand. -/
@[reassoc (attr := simp)]
theorem ιFree_biproductIsoFree_inv (i : I) :
    ιFree i ≫ (biproductIsoFree (R := R) I).inv =
      biproduct.ι (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimitFreeCofan I) ⟨i⟩

variable (I) in
/-- The free sheaf of modules on a finite type is self-dual: the evaluation pairs the basis
sections `ιFree i` and `ιFree j` to `δᵢⱼ`, and the coevaluation is `∑ i, ιFree i ⊗ ιFree i`. -/
instance exactPairingFree :
    ExactPairing (free (R := ringCatSheaf R) I) (free (R := ringCatSheaf R) I) :=
  have := Fintype.ofFinite I
  exactPairingCongr (biproductIsoFree I).symm (biproductIsoFree I).symm

/-- The evaluation of `free I` is the evaluation of the biproduct of copies of the unit,
transported along `biproductIsoFree`. -/
private theorem evaluation_free_eq :
    ε_ (free (R := ringCatSheaf R) I) (free I) =
      ((biproductIsoFree I).inv ⊗ₘ (biproductIsoFree I).inv) ≫
        ε_ (⨁ fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) (⨁ fun _ ↦ 𝟙_ _) := by
  -- The evaluation of `exactPairingCongr` whiskers the evaluation of the biproduct pairing by
  -- the two isomorphisms, one on each side.
  rw [tensorHom_def', Category.assoc]
  rfl

/-- The coevaluation of `free I` is the coevaluation of the biproduct of copies of the unit,
transported along `biproductIsoFree`. -/
private theorem coevaluation_free_eq :
    η_ (free (R := ringCatSheaf R) I) (free I) =
      η_ (⨁ fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) (⨁ fun _ ↦ 𝟙_ _) ≫
        ((biproductIsoFree I).hom ⊗ₘ (biproductIsoFree I).hom) := by
  -- The coevaluation of `exactPairingCongr` whiskers the coevaluation of the biproduct pairing
  -- by the inverses of the two isomorphisms.
  rw [tensorHom_def', ← Category.assoc]
  rfl

/-- The evaluation of the free sheaf on a finite type pairs each basis section with itself to
`1`. -/
@[reassoc (attr := simp)]
theorem ιFree_tensorHom_ιFree_evaluation (i : I) :
    (ιFree i ⊗ₘ ιFree i) ≫ ε_ (free (R := ringCatSheaf R) I) (free I) =
      (ρ_ (𝟙_ (SheafOfModules.{u} (ringCatSheaf R)))).hom := by
  rw [evaluation_free_eq, tensorHom_comp_tensorHom_assoc, ιFree_biproductIsoFree_inv,
    ExactPairing.biproduct_ι_tensorHom_biproduct_ι_evaluation, ExactPairing.unit_evaluation]

/-- The evaluation of the free sheaf on a finite type pairs distinct basis sections to `0`. -/
@[reassoc (attr := simp)]
theorem ιFree_tensorHom_ιFree_evaluation_of_ne {i j : I} (h : i ≠ j) :
    (ιFree i ⊗ₘ ιFree j) ≫ ε_ (free (R := ringCatSheaf R) I) (free I) = 0 := by
  rw [evaluation_free_eq, tensorHom_comp_tensorHom_assoc, ιFree_biproductIsoFree_inv,
    ιFree_biproductIsoFree_inv, ExactPairing.biproduct_ι_tensorHom_biproduct_ι_evaluation_of_ne h]

/-- The coevaluation of the free sheaf on a finite type is the sum of the tensor squares of the
basis sections. -/
theorem coevaluation_free [Fintype I] :
    η_ (free (R := ringCatSheaf R) I) (free I) =
      ∑ i, (ρ_ (𝟙_ (SheafOfModules.{u} (ringCatSheaf R)))).inv ≫ (ιFree i ⊗ₘ ιFree i) := by
  rw [coevaluation_free_eq, ExactPairing.biproduct_coevaluation, Preadditive.sum_comp]
  simp only [ExactPairing.unit_coevaluation, Category.assoc, tensorHom_comp_tensorHom]
  simp only [tensorUnit_eq, biproduct_ι_biproductIsoFree_hom]

end SheafOfModules

end

end TauCeti
