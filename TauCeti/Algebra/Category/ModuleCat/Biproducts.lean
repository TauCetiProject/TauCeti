/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
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
modules over an arbitrary ring is finitely generated (`ModuleCat.finite_biproduct`), and so is
each summand of a finitely generated biproduct (`ModuleCat.finite_of_finite_biproduct`).

## Main definitions

* `TauCeti.biproductDirectSumEquiv`: the carrier of a finite biproduct in `ModuleCat A` is the
  external direct sum of the carriers of the summands.

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
* `ModuleCat.biprod_lift_comp_biprodIsoProd_hom`, `ModuleCat.biprodIsoProd_hom_comp_ofHom_coprod`:
  under `ModuleCat.biprodIsoProd`, `biprod.lift f g` and `biprod.desc f g` are the pair map
  `f.hom.prod g.hom` and the sum map `f.hom.coprod g.hom`.
* `ModuleCat.bijective_biprod_map`: `biprod.map f g` is bijective when `f` and `g` are.
* `ModuleCat.finite_biproduct`: a finite biproduct of finitely generated modules is finitely
  generated.
* `ModuleCat.finite_of_finite_biproduct`: the summands of a finitely generated biproduct are
  finitely generated.

* `ModuleCat.biprod_inl_fst_apply`, `ModuleCat.biprod_inr_fst_apply`,
  `ModuleCat.biprod_inl_snd_apply`, `ModuleCat.biprod_inr_snd_apply` and
  `ModuleCat.biprod_inl_fst_add_inr_snd_apply`: the binary biproduct projections and inclusions on
  elements.

* `CategoryTheory.Functor.sum_map_ι_map_π_apply`: for an additive functor `F` to modules, an
  element of `F.obj (⨁ f)` is the sum of the images of its components.
* `CategoryTheory.Functor.finite_obj_biproduct`: such a functor has finitely generated value on a
  finite biproduct of objects with finitely generated values.
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
/-- The map `biprod.lift f g` into a biproduct, followed by the identification of the biproduct
with the product module, is the pair map `f.hom.prod g.hom`. -/
theorem biprod_lift_comp_biprodIsoProd_hom {X : ModuleCat.{v} R} (f : X ⟶ M) (g : X ⟶ N) :
    biprod.lift f g ≫ (biprodIsoProd M N).hom = ofHom (f.hom.prod g.hom) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext <;> ext x <;> simp

variable {M N} in
/-- The identification of the biproduct with the product module, followed by the sum map
`f.hom.coprod g.hom`, is the map `biprod.desc f g` out of the biproduct. -/
theorem biprodIsoProd_hom_comp_ofHom_coprod {Z : ModuleCat.{v} R} (f : M ⟶ Z) (g : N ⟶ Z) :
    (biprodIsoProd M N).hom ≫ ofHom (f.hom.coprod g.hom) = biprod.desc f g := by
  apply biprod.hom_ext' <;> ext x <;> simp

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

/-- A summand of a finitely generated biproduct in `ModuleCat R` is finitely generated: it is the
image of the projection onto it. -/
theorem finite_of_finite_biproduct {ι : Type*} [Finite ι] (V : ι → ModuleCat.{v} R)
    [Module.Finite R (⨁ V : ModuleCat.{v} R)] (i : ι) : Module.Finite R (V i) :=
  Module.Finite.of_surjective (biproduct.π V i).hom fun x ↦
    ⟨(biproduct.ι V i).hom x, by rw [← ConcreteCategory.comp_apply, biproduct.ι_π_self, id_apply]⟩

end ModuleCat

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] {R : Type*} [Ring R] (F : C ⥤ ModuleCat R)
  [F.Additive]

/-- For an additive functor to modules, an element of the value on a finite biproduct is the sum
of the images of its components. -/
theorem sum_map_ι_map_π_apply {ι : Type*} [Fintype ι] (f : ι → C) [HasBiproduct f]
    (v : F.obj (⨁ f)) :
    ∑ j, (F.map (biproduct.ι f j)).hom ((F.map (biproduct.π f j)).hom v) = v := by
  have := congrArg (fun φ ↦ (F.map φ).hom v) (biproduct.total (f := f))
  simp only [F.map_sum, F.map_comp, F.map_id, ModuleCat.hom_sum, ModuleCat.hom_comp,
    ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at this
  exact this

/-- An additive functor to modules has finitely generated value on a finite biproduct of objects
with finitely generated values. -/
instance finite_obj_biproduct {ι : Type*} [Finite ι] (f : ι → C) [HasBiproduct f]
    [∀ j, Module.Finite R (F.obj (f j))] : Module.Finite R (F.obj (⨁ f)) := by
  have := Fintype.ofFinite ι
  refine Module.Finite.of_surjective
    (∑ j, (F.map (biproduct.ι f j)).hom ∘ₗ LinearMap.proj (R := R) j) fun v ↦ ?_
  refine ⟨fun j ↦ (F.map (biproduct.π f j)).hom v, ?_⟩
  simpa using F.sum_map_ι_map_π_apply f v

end CategoryTheory.Functor
