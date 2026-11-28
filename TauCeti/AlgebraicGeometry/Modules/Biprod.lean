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
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Tensor

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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory BraidedCategory TauCeti

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
  let eConst : (⨁ fun _ : I ↦ M) ≅
      M ⊗ (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) :=
    M.biproductConstIsoTensorFree (R := X.sheaf) I
  biproduct.whiskerEquiv (f := fun _ : J ↦ M) (g := fun _ : I ↦ M) e (fun _ ↦ Iso.refl _) ≪≫
    eConst ≪≫ β_ M (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)

/-- `biproductIsoFreeTensor` sends the `j`-th summand `M` to the `(e j)`-th basis summand of
`(free I) ⊗ M` via the inverse left unitor `M ≅ 𝒪ₓ ⊗ M`. -/
@[reassoc (attr := simp)]
lemma biproduct_ι_biproductIsoFreeTensor_hom (M : X.Modules) {I : Type u} [Finite I]
    {J : Type*} [Fintype J] (e : J ≃ I) (j : J) :
    biproduct.ι (fun _ : J ↦ M) j ≫ (biproductIsoFreeTensor M e).hom =
      (λ_ M).inv ≫ (SheafOfModules.ιFree (R := X.ringCatSheaf) (e j) ▷ M) := by
  have : Fintype I := Fintype.ofFinite I
  let freeX : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
  let ιj : 𝟙_ X.Modules ⟶ freeX := SheafOfModules.ιFree (R := X.ringCatSheaf) (e j)
  let eConst : (⨁ fun _ : I ↦ M) ≅ M ⊗ freeX :=
    M.biproductConstIsoTensorFree (R := X.sheaf) I
  change biproduct.ι (fun _ : J ↦ M) j ≫
      (biproduct.whiskerEquiv (f := fun _ : J ↦ M) (g := fun _ : I ↦ M) e
        (fun _ ↦ Iso.refl _)).hom ≫ eConst.hom ≫ (β_ M freeX).hom =
      (λ_ M).inv ≫ (ιj ▷ M)
  rw [← Category.assoc, biproduct.whiskerEquiv_hom, biproduct.ι_desc, Iso.refl_inv,
    Category.id_comp]
  have h1 : biproduct.ι (fun _ : I ↦ M) (e j) ≫ eConst.hom = (ρ_ M).inv ≫ (M ◁ ιj) :=
    SheafOfModules.biproduct_ι_biproductConstIsoTensorFree_hom M (R := X.sheaf) (e j)
  rw [reassoc_of% h1, braiding_naturality_right]
  simp

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
  classical
  have : Fintype I := Fintype.ofFinite I
  refine (Iso.inv_comp_eq _).2 (biproduct.hom_ext' _ _ fun j' ↦ ?_)
  let freeX : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
  let ιj' : 𝟙_ X.Modules ⟶ freeX := SheafOfModules.ιFree (R := X.ringCatSheaf) (e j')
  let invFree : freeX ⟶ ⨁ fun _ : I ↦ 𝟙_ X.Modules :=
    (TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I).inv
  change biproduct.ι (fun _ : J ↦ M) j' ≫ biproduct.π (fun _ : J ↦ M) j =
    (biproduct.ι (fun _ : J ↦ M) j' ≫ (biproductIsoFreeTensor M e).hom) ≫
      (invFree ▷ M) ≫ (biproduct.π (fun _ : I ↦ 𝟙_ X.Modules) (e j) ▷ M) ≫ (λ_ M).hom
  have h0 : biproduct.ι (fun _ : J ↦ M) j' ≫ (biproductIsoFreeTensor M e).hom =
      (λ_ M).inv ≫ (ιj' ▷ M) :=
    biproduct_ι_biproductIsoFreeTensor_hom M e j'
  have hι : ιj' ≫ invFree = biproduct.ι (fun _ : I ↦ 𝟙_ X.Modules) (e j') :=
    (Iso.comp_inv_eq (TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I)).2
      (TauCeti.SheafOfModules.biproduct_ι_biproductIsoFree_hom (R := X.sheaf) (e j')).symm
  have hιM : (ιj' ▷ M) ≫ (invFree ▷ M) =
      biproduct.ι (fun _ : I ↦ 𝟙_ X.Modules) (e j') ▷ M := by
    rw [← comp_whiskerRight, hι]
  rw [biproduct.ι_π, h0, Category.assoc, reassoc_of% hιM, ← comp_whiskerRight_assoc,
    biproduct.ι_π]
  by_cases hjj' : j' = j
  · subst hjj'
    simp
  · have hij : e j' ≠ e j := fun h ↦ hjj' (e.injective h)
    simp [hjj', hij]

end AlgebraicGeometry.Scheme.Modules
