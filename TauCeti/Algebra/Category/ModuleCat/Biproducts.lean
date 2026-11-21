/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The carrier of a biproduct in `ModuleCat`

Mathlib's `ModuleCat.biproductIsoPi` identifies a finite biproduct in `ModuleCat A` with the
dependent function type `∀ i, P i`. Over a finite index type the external direct sum `⨁ i, P i` is
the same module (`DirectSum.linearEquivFunOnFintype`), so a finite biproduct is also the external
direct sum of the carriers of its summands. This file records that identification, together with
the two lemmas that characterise it: its components are the biproduct projections, and it sends a
biproduct inclusion to the corresponding direct-sum inclusion.

This is the transport along which results about `DirectSum` decompositions of a module — the
Krull-Schmidt theorem among them — can be read as results about biproducts in `ModuleCat A`.

For a binary biproduct, Mathlib's `ModuleCat.biprodIsoProd` identifies `M ⊞ N` with the product
module `M × N`; this file also records that it reads off the two biproduct projections and
carries the biproduct inclusions to `LinearMap.inl` and `LinearMap.inr`, and that the biproduct
`biprod.map f g` of two bijective maps is bijective. A finite biproduct of finitely generated
modules over an arbitrary ring is finitely generated (`ModuleCat.finite_biproduct`).

For a full subcategory `S.FullSubcategory` of `ModuleCat R`, the additive inclusion `S.ι` preserves
finite biproducts, so `(⨁ f).obj` identifies with `∀ j, (f j).obj`
(`CategoryTheory.ObjectProperty.biproductObjIsoPi`), transferring surjections and epimorphisms
between the dependent product and the biproduct in `S.FullSubcategory`.

## Main definitions

* `TauCeti.biproductDirectSumEquiv`: the carrier of a finite biproduct in `ModuleCat A` is the
  external direct sum of the carriers of the summands.
* `CategoryTheory.ObjectProperty.biproductObjIsoPi`: the carrier of a finite biproduct in a full
  subcategory of `ModuleCat R` is the dependent product of the underlying modules.

## Main results

* `TauCeti.component_biproductDirectSumEquiv`: its `i`-th component is the `i`-th biproduct
  projection.
* `TauCeti.biproductDirectSumEquiv_ι`: it carries the `i`-th biproduct inclusion to the `i`-th
  direct-sum inclusion.
* `ModuleCat.biprodIsoProd_hom_apply`: the coordinates of `ModuleCat.biprodIsoProd` are the
  biproduct projections.
* `ModuleCat.inl_comp_biprodIsoProd_hom`, `ModuleCat.inr_comp_biprodIsoProd_hom`: under
  `ModuleCat.biprodIsoProd`, the binary biproduct inclusions are `LinearMap.inl` and
  `LinearMap.inr`.
* `ModuleCat.bijective_biprod_map`: `biprod.map f g` is bijective when `f` and `g` are.
* `ModuleCat.finite_biproduct`: a finite biproduct of finitely generated modules is finitely
  generated.
* `ModuleCat.biprod_inl_fst_apply`, `ModuleCat.biprod_inr_fst_apply`,
  `ModuleCat.biprod_inl_snd_apply`, `ModuleCat.biprod_inr_snd_apply` and
  `ModuleCat.biprod_inl_fst_add_inr_snd_apply`: the binary biproduct projections and inclusions on
  elements.
* `CategoryTheory.ObjectProperty.biproductObjIsoPi_inv_comp_π`,
  `CategoryTheory.ObjectProperty.epi_homMk_biproductObjIsoPi_comp`, and
  `CategoryTheory.ObjectProperty.surjective_biproductObjIsoPi_inv_comp`: projection compatibility
  and epi/surjectivity transfer for finite biproducts in a full subcategory of `ModuleCat R`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits DirectSum

universe u v

variable {A : Type u} [Ring A] {ι : Type} [Fintype ι] (P : ι → ModuleCat.{v} A)

/-- **The carrier of a finite biproduct in `ModuleCat A` is the external direct sum of the carriers
of the summands.** -/
noncomputable def biproductDirectSumEquiv :
    (biproduct P : ModuleCat.{v} A) ≃ₗ[A] ⨁ i, (P i : Type v) :=
  (ModuleCat.biproductIsoPi P).toLinearEquiv.trans
    (DirectSum.linearEquivFunOnFintype A ι fun i ↦ (P i : Type v)).symm

/-- The `i`-th component of `TauCeti.biproductDirectSumEquiv` is the `i`-th biproduct projection. -/
@[simp]
theorem component_biproductDirectSumEquiv (x : (biproduct P : ModuleCat.{v} A)) (i : ι) :
    DirectSum.component A ι (fun i ↦ (P i : Type v)) i (biproductDirectSumEquiv P x) =
      (biproduct.π P i).hom x := by
  -- Read through `ModuleCat.biproductIsoPi`, the `i`-th projection out of the dependent function
  -- type is the `i`-th biproduct projection.
  have key : (ModuleCat.biproductIsoPi P).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, (P j : Type v)) →ₗ[A] (P i : Type v)) =
      biproduct.π P i := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π P i, Iso.hom_inv_id_assoc]
  -- The underlying function of `biproductDirectSumEquiv P x` is `(ModuleCat.biproductIsoPi P).hom`
  -- applied to `x`, because the second factor of the composite is the inverse of
  -- `DirectSum.linearEquivFunOnFintype`.
  have hfun : (DirectSum.linearEquivFunOnFintype A ι fun j ↦ (P j : Type v))
      (biproductDirectSumEquiv P x) = (ModuleCat.biproductIsoPi P).hom.hom x := by
    unfold biproductDirectSumEquiv
    rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Iso.toLinearEquiv_apply]
  rw [← key, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearMap.proj_apply,
    ← hfun, DirectSum.linearEquivFunOnFintype_apply, ← DirectSum.apply_eq_component]

/-- `TauCeti.biproductDirectSumEquiv` carries the `i`-th biproduct inclusion to the `i`-th
direct-sum inclusion. -/
@[simp]
theorem biproductDirectSumEquiv_ι [DecidableEq ι] (i : ι) (y : (P i : Type v)) :
    biproductDirectSumEquiv P ((biproduct.ι P i).hom y) =
      DirectSum.lof A ι (fun i ↦ (P i : Type v)) i y := by
  -- Both sides are determined by their components, which `biproduct.ι_π` computes.
  refine DirectSum.ext_component A fun j ↦ ?_
  rw [component_biproductDirectSumEquiv, DirectSum.component.of, ← ModuleCat.comp_apply,
    biproduct.ι_π]
  rcases eq_or_ne i j with h | h
  · subst h
    simp
  · simp [h]

end TauCeti

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R] (M N : ModuleCat.{v} R)

/-- The identification of the biproduct with the product module has the two biproduct
projections as its coordinates. -/
@[simp]
theorem biprodIsoProd_hom_apply (x : ↑(M ⊞ N)) :
    (biprodIsoProd M N).hom x = ((biprod.fst : M ⊞ N ⟶ M) x, (biprod.snd : M ⊞ N ⟶ N) x) := by
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (biprodIsoProd M N).inv).2 x
  ext <;> simp [← ConcreteCategory.comp_apply]

/-- The first biproduct inclusion followed by the identification of the biproduct with the product
module is the first inclusion `LinearMap.inl` into the product. -/
@[reassoc (attr := simp)]
theorem inl_comp_biprodIsoProd_hom :
    biprod.inl ≫ (biprodIsoProd M N).hom = ofHom (LinearMap.inl R M N) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext <;> ext x <;> simp

/-- The second biproduct inclusion followed by the identification of the biproduct with the
product module is the second inclusion `LinearMap.inr` into the product. -/
@[reassoc (attr := simp)]
theorem inr_comp_biprodIsoProd_hom :
    biprod.inr ≫ (biprodIsoProd M N).hom = ofHom (LinearMap.inr R M N) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext <;> ext x <;> simp

variable {M N} in
/-- The biproduct `biprod.map f g` of two bijective linear maps is bijective. -/
theorem bijective_biprod_map {M' N' : ModuleCat.{v} R} (f : M ⟶ M') (g : N ⟶ N')
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (biprod.map f g) := by
  have := (ConcreteCategory.isIso_iff_bijective f).2 hf
  have := (ConcreteCategory.isIso_iff_bijective g).2 hg
  exact (ConcreteCategory.isIso_iff_bijective _).1 (biprod.mapIso (asIso f) (asIso g)).isIso_hom

variable {M N}

@[simp]
theorem biprod_inl_fst_apply (x : M) :
    (biprod.fst : M ⊞ N ⟶ M) ((biprod.inl : M ⟶ M ⊞ N) x) = x := by
  rw [← ConcreteCategory.comp_apply, biprod.inl_fst, id_apply]

@[simp]
theorem biprod_inr_fst_apply (y : N) :
    (biprod.fst : M ⊞ N ⟶ M) ((biprod.inr : N ⟶ M ⊞ N) y) = 0 := by
  simp [← ConcreteCategory.comp_apply]

@[simp]
theorem biprod_inl_snd_apply (x : M) :
    (biprod.snd : M ⊞ N ⟶ N) ((biprod.inl : M ⟶ M ⊞ N) x) = 0 := by
  simp [← ConcreteCategory.comp_apply]

@[simp]
theorem biprod_inr_snd_apply (y : N) :
    (biprod.snd : M ⊞ N ⟶ N) ((biprod.inr : N ⟶ M ⊞ N) y) = y := by
  rw [← ConcreteCategory.comp_apply, biprod.inr_snd, id_apply]

/-- An element of a binary biproduct is the sum of the inclusions of its two components. -/
theorem biprod_inl_fst_add_inr_snd_apply (x : ↑(M ⊞ N)) :
    (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) x) +
      (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) x) = x := by
  simpa only [hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply, id_apply] using
    ConcreteCategory.congr_hom (biprod.total (X := M) (Y := N)) x

/-- A finite biproduct of finitely generated modules in `ModuleCat R` is finitely generated. -/
theorem finite_biproduct {ι : Type*} [Finite ι] (V : ι → ModuleCat.{v} R)
    [∀ i, Module.Finite R (V i)] :
    Module.Finite R (⨁ V : ModuleCat.{v} R) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact Module.Finite.equiv (((biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _).symm ≪≫
    biproductIsoPi (fun j : Fin m ↦ V (e.symm j)))).symm.toLinearEquiv

end ModuleCat

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R] (S : ObjectProperty (ModuleCat.{v} R))

/-- The underlying module of a finite biproduct in a full subcategory of `ModuleCat R` is the
dependent product of the underlying modules of the summands. -/
noncomputable def biproductObjIsoPi {J : Type} [Finite J] (f : J → S.FullSubcategory)
    [HasBiproduct f] :
    (⨁ f).obj ≅ ModuleCat.of R (∀ j, (f j).obj) :=
  S.ι.mapBiproduct f ≪≫ ModuleCat.biproductIsoPi fun j ↦ (f j).obj

/-- The inverse of `biproductObjIsoPi` followed by the `j`-th biproduct projection is the `j`-th
product projection. -/
@[reassoc (attr := simp)]
theorem biproductObjIsoPi_inv_comp_π {J : Type} [Finite J] (f : J → S.FullSubcategory)
    [HasBiproduct f] (j : J) :
    (S.biproductObjIsoPi f).inv ≫ (biproduct.π f j).hom =
      ModuleCat.ofHom (LinearMap.proj j : (∀ j, (f j).obj) →ₗ[R] (f j).obj) := by
  have h : (S.ι.mapBiproduct f).inv ≫ S.ι.map (biproduct.π f j) = biproduct.π _ j := by
    rw [Iso.inv_comp_eq, Functor.mapBiproduct_hom]
    exact (biproduct.lift_π (fun j ↦ S.ι.map (biproduct.π f j)) j).symm
  simp only [biproductObjIsoPi, Iso.trans_inv, Category.assoc]
  rw [← ι_map, h]
  exact ModuleCat.biproductIsoPi_inv_comp_π (fun j ↦ (f j).obj) j

/-- A surjective linear map from the product `∀ j, (f j).obj` to `X.obj` induces an epimorphism
`(⨁ f) ⟶ X` in `S.FullSubcategory`. -/
theorem epi_homMk_biproductObjIsoPi_comp {J : Type} [Finite J] {f : J → S.FullSubcategory}
    [HasBiproduct f] {X : S.FullSubcategory} {φ : (∀ j, (f j).obj) →ₗ[R] X.obj}
    (hφ : Function.Surjective φ) :
    Epi (ObjectProperty.homMk ((S.biproductObjIsoPi f).hom ≫ ModuleCat.ofHom φ) :
      (⨁ f) ⟶ X) := by
  have : Epi (ModuleCat.ofHom φ : ModuleCat.of R (∀ j, (f j).obj) ⟶ X.obj) :=
    (ModuleCat.epi_iff_surjective _).mpr hφ
  have : Epi (S.ι.map (ObjectProperty.homMk
      ((S.biproductObjIsoPi f).hom ≫ ModuleCat.ofHom φ) : (⨁ f) ⟶ X)) :=
    epi_comp _ _
  exact S.ι.epi_of_epi_map ‹_›

/-- When `S.ι` preserves epimorphisms, an epimorphism `π : (⨁ f) ⟶ X` in `S.FullSubcategory`
yields a surjective linear map `(∀ j, (f j).obj) →ₗ[R] X.obj`. -/
theorem surjective_biproductObjIsoPi_inv_comp [S.ι.PreservesEpimorphisms] {J : Type} [Finite J]
    {f : J → S.FullSubcategory} [HasBiproduct f] {X : S.FullSubcategory} (π : (⨁ f) ⟶ X)
    [Epi π] :
    Function.Surjective ((S.biproductObjIsoPi f).inv ≫ π.hom).hom := by
  have : Epi (S.ι.map π) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).mp (epi_comp (S.biproductObjIsoPi f).inv (S.ι.map π))

end CategoryTheory.ObjectProperty
