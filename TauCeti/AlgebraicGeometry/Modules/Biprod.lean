/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Biprod
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Direct sums of `𝒪ₓ`-modules

The site-level closure properties of direct sums of sheaves of modules
(`TauCeti/Algebra/Category/ModuleCat/Sheaf/Quasicoherent/Biprod.lean`) specialize to a scheme `X`
by taking the sheaf of rings to be the structure sheaf of `X`. Since `X.Modules` carries its own
category and abelian structures, instance search does not find the site-level instances for
`M ⊞ N`, and they are restated here. This file also specializes the zero and finite-product
closure instances for finite presentation. These specializations pre-elaborate the ringed-site
hypotheses to stay within the default typeclass search-size bound.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_biprod`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_biprod` and
  `AlgebraicGeometry.Scheme.Modules.isLocallyFree_biprod`: the direct sum of two quasi-coherent
  (respectively finite type, finitely presented, locally free) `𝒪ₓ`-modules is again so. In
  particular, direct sums of finite locally free `𝒪ₓ`-modules are finite locally free.
* `AlgebraicGeometry.Scheme.Modules.hasFiniteBiproducts`: `𝒪ₓ`-modules have finite biproducts.
* `AlgebraicGeometry.Scheme.Modules.containsZero_isFinitePresentation`,
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderBinaryProducts_isFinitePresentation`,
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderFiniteProducts_isFinitePresentation` and
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_biproduct`: finitely presented sheaves
  contain zero and are closed under binary products, finite products, and finite direct sums.
* `AlgebraicGeometry.Scheme.Modules.biproductIsoFreeTensor`: a finite biproduct of copies of `M`
  indexed by `J ≃ I` is isomorphic to `(free I) ⊗ M`.
-/

public section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TauCeti

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

/-- `𝒪ₓ`-modules have finite biproducts, since they form an abelian category. -/
instance hasFiniteBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  inferInstanceAs (HasFiniteBiproducts (SheafOfModules X.ringCatSheaf))

/-- The direct sum of two quasi-coherent `𝒪ₓ`-modules is quasi-coherent. -/
instance isQuasicoherent_biprod [M.IsQuasicoherent]
    [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_biprod (M := M) (N := N)

/-- The direct sum of two `𝒪ₓ`-modules of finite type is of finite type. -/
instance isFiniteType_biprod [M.IsFiniteType]
    [N.IsFiniteType] : (M ⊞ N).IsFiniteType :=
  SheafOfModules.isFiniteType_biprod (M := M) (N := N)

/-- The direct sum of two finitely presented `𝒪ₓ`-modules is finitely presented. -/
instance isFinitePresentation_biprod
    [M.IsFinitePresentation] [N.IsFinitePresentation] : (M ⊞ N).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_biprod (M := M) (N := N)

/-- The direct sum of two locally free `𝒪ₓ`-modules is locally free. -/
instance isLocallyFree_biprod [M.IsLocallyFree]
    [N.IsLocallyFree] : (M ⊞ N).IsLocallyFree :=
  SheafOfModules.isLocallyFree_biprod (M := M) (N := N)

-- These specializations pre-elaborate the ringed-site hypotheses: synthesizing the site-level
-- instances directly for `X.ringCatSheaf` exceeds the default typeclass search size (128).
/-- The zero module sheaf is finitely presented. -/
instance containsZero_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero :=
  TauCeti.SheafOfModules.containsZero_isFinitePresentation (R := X.ringCatSheaf)

/-- Finitely presented sheaves are closed under binary products, computed as direct sums. -/
instance isClosedUnderBinaryProducts_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderBinaryProducts :=
  TauCeti.SheafOfModules.isClosedUnderBinaryProducts_isFinitePresentation (R := X.ringCatSheaf)

/-- Finitely presented sheaves are closed under finite products. -/
instance isClosedUnderFiniteProducts_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := .mk'

/-- A finite direct sum of finitely presented `𝒪ₓ`-modules is finitely presented. -/
instance isFinitePresentation_biproduct {J : Type*} [Finite J] (F : J → X.Modules)
    [HasBiproduct F] [∀ j, (F j).IsFinitePresentation] :
    (⨁ F).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (biproduct.isoProduct F).symm
    ((SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_product fun _ ↦ inferInstance)

/-- A finite biproduct of copies of an `𝒪ₓ`-module `M`, indexed by a type `J` equivalent to a
finite type `I : Type u`, is isomorphic to `(free I) ⊗ M`. -/
noncomputable def biproductIsoFreeTensor (M : X.Modules) {I : Type u} [Finite I]
    {J : Type*} [Fintype J] (e : J ≃ I) :
    (⨁ fun _ : J ↦ M) ≅
      (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⊗ M :=
  letI : Fintype I := Fintype.ofFinite I
  biproduct.mapIso (fun _ : J ↦ (λ_ M).symm) ≪≫
    ((tensorRight M).mapBiproduct (fun _ : J ↦ 𝟙_ X.Modules)).symm ≪≫
    whiskerRightIso
      (biproduct.whiskerEquiv (f := fun _ : J ↦ 𝟙_ X.Modules)
          (g := fun _ : I ↦ 𝟙_ X.Modules) e (fun _ ↦ Iso.refl _) ≪≫
        TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I) M

/-- `biproductIsoFreeTensor` sends the `j`-th summand `M` to the `(e j)`-th basis summand of
`(free I) ⊗ M` via the inverse left unitor `M ≅ 𝒪ₓ ⊗ M`. -/
@[reassoc (attr := simp)]
lemma biproduct_ι_biproductIsoFreeTensor_hom (M : X.Modules) {I : Type u} [Finite I]
    {J : Type*} [Fintype J] (e : J ≃ I) (j : J) :
    biproduct.ι (fun _ : J ↦ M) j ≫ (biproductIsoFreeTensor M e).hom =
      (λ_ M).inv ≫ (SheafOfModules.ιFree (R := X.ringCatSheaf) (e j) ▷ M) := by
  let _ : Fintype I := Fintype.ofFinite I
  dsimp [biproductIsoFreeTensor]
  rw [biproduct.mapIso_hom, biproduct.ι_map_assoc, Functor.mapBiproduct_inv]
  have h1 : biproduct.ι (fun _ : J ↦ 𝟙_ X.Modules ⊗ M) j ≫
      biproduct.desc (fun j' ↦ (tensorRight M).map (biproduct.ι (fun _ : J ↦ 𝟙_ X.Modules) j')) =
      biproduct.ι (fun _ : J ↦ 𝟙_ X.Modules) j ▷ M :=
    biproduct.ι_desc _ j
  refine (Category.assoc _ _ _).trans ((congrArg (· ≫ _)
    ((Category.assoc _ _ _).trans (congrArg ((λ_ M).inv ≫ ·) h1))).trans ?_)
  refine (Category.assoc _ _ _).trans (congrArg ((λ_ M).inv ≫ ·) ?_)
  have h2 : biproduct.ι (fun _ : J ↦ 𝟙_ X.Modules) j ≫
      (biproduct.whiskerEquiv (f := fun _ : J ↦ 𝟙_ X.Modules)
        (g := fun _ : I ↦ 𝟙_ X.Modules) e (fun _ ↦ Iso.refl _)).hom ≫
        (TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I).hom =
      (SheafOfModules.ιFree (R := X.ringCatSheaf) (e j) :
        𝟙_ X.Modules ⟶ (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ?_).trans
      (TauCeti.SheafOfModules.biproduct_ι_biproductIsoFree_hom (R := X.sheaf) (e j)))
    rw [biproduct.whiskerEquiv_hom, biproduct.ι_desc, Iso.refl_inv, Category.id_comp]
    rfl
  exact ((comp_whiskerRight _ _ M).symm.trans (congrArg (· ▷ M)
    ((Category.assoc _ _ _).trans h2)))

/-- The inverse of `biproductIsoFreeTensor` sends the `i`-th basis summand of `(free I) ⊗ M` to
the `(e.symm i)`-th summand `M` via the left unitor `𝒪ₓ ⊗ M ≅ M`. -/
@[simp, reassoc]
lemma ιFree_whiskerRight_biproductIsoFreeTensor_inv (M : X.Modules) {I : Type u} [Finite I]
    {J : Type*} [Fintype J] (e : J ≃ I) (i : I) :
    (SheafOfModules.ιFree (R := X.ringCatSheaf) i ▷ M) ≫ (biproductIsoFreeTensor M e).inv =
      (λ_ M).hom ≫ biproduct.ι (fun _ : J ↦ M) (e.symm i) := by
  refine (Iso.comp_inv_eq _).2 ?_
  have h := biproduct_ι_biproductIsoFreeTensor_hom M e (e.symm i)
  rw [e.apply_symm_apply] at h
  exact (Category.assoc _ _ _).trans ((congrArg ((λ_ M).hom ≫ ·) h).trans
    (Iso.hom_inv_id_assoc _ _)) |>.symm

/-- The `j`-th biproduct projection of `(biproductIsoFreeTensor M e).inv` extracts the `(e j)`-th
free coordinate tensored with `M`, followed by the left unitor `𝒪ₓ ⊗ M ≅ M`. -/
@[reassoc (attr := simp)]
lemma biproductIsoFreeTensor_inv_biproduct_π (M : X.Modules) {I : Type u} [Finite I]
    {J : Type*} [Fintype J] (e : J ≃ I) (j : J) :
    (biproductIsoFreeTensor M e).inv ≫ biproduct.π (fun _ : J ↦ M) j =
      ((TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I).inv ▷ M) ≫
        (biproduct.π (fun _ : I ↦ 𝟙_ X.Modules) (e j) ▷ M) ≫ (λ_ M).hom := by
  let _ : Fintype I := Fintype.ofFinite I
  dsimp [biproductIsoFreeTensor]
  simp only [Category.assoc, biproduct.mapIso_inv, biproduct.map_π, Functor.mapBiproduct_hom]
  have h1 : biproduct.lift
        (fun j' ↦ (tensorRight M).map (biproduct.π (fun _ : J ↦ 𝟙_ X.Modules) j')) ≫
      biproduct.π (fun _ : J ↦ 𝟙_ X.Modules ⊗ M) j =
      biproduct.π (fun _ : J ↦ 𝟙_ X.Modules) j ▷ M :=
    biproduct.lift_π _ j
  refine (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (λ_ M).hom) h1))).trans ?_
  have h2 : (biproduct.whiskerEquiv (f := fun _ : J ↦ 𝟙_ X.Modules)
        (g := fun _ : I ↦ 𝟙_ X.Modules) e (fun _ ↦ Iso.refl _)).inv ≫
      biproduct.π (fun _ : J ↦ 𝟙_ X.Modules) j =
      biproduct.π (fun _ : I ↦ 𝟙_ X.Modules) (e j) := by
    rw [biproduct.whiskerEquiv_inv_eq_lift, biproduct.lift_π, Iso.refl_hom, Category.comp_id]
  have h3 : ((TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I).inv ≫
      (biproduct.whiskerEquiv (f := fun _ : J ↦ 𝟙_ X.Modules)
        (g := fun _ : I ↦ 𝟙_ X.Modules) e (fun _ ↦ Iso.refl _)).inv) ▷ M ≫
      biproduct.π (fun _ : J ↦ 𝟙_ X.Modules) j ▷ M =
      ((TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I).inv ▷ M) ≫
      (biproduct.π (fun _ : I ↦ 𝟙_ X.Modules) (e j) ▷ M) :=
    (congrArg (· ≫ _) (comp_whiskerRight _ _ M)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        ((comp_whiskerRight _ _ M).symm.trans (congrArg (· ▷ M) h2))))
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (λ_ M).hom) h3) |>.trans
    (Category.assoc _ _ _)

end AlgebraicGeometry.Scheme.Modules
