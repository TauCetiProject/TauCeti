/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Biproducts

/-!
# The diagonal action on the fibre of a finite power

Let `ω : C ⥤ ModuleCat R` be an additive functor on a preadditive category with finite
biproducts, let `X : C` and let `ι` be a finite type. This file records how elements of
`ω (⨁ fun _ : ι ↦ X)` interact with the images under `ω` of the biproduct projections and
inclusions, and defines the diagonal action of `Module.End R (ω X)` on `ω (⨁ fun _ : ι ↦ X)`.

## Main definitions and results

* `CategoryTheory.Functor.map_π_map_ι_apply`: the biproduct identity `ιₖ ≫ πⱼ = δₖⱼ` on elements
  of the fibre; the identity `∑ j, πⱼ ≫ ιⱼ = 𝟙` is `CategoryTheory.Functor.sum_map_ι_map_π_apply`
  in `TauCeti.Algebra.Category.ModuleCat.Biproducts`.
* `CategoryTheory.Functor.ext_map_π_apply`: an element of the fibre of a finite biproduct `⨁ F`
  is determined by its images under the projections.
* `CategoryTheory.Functor.powerAlgHom`: the diagonal action of `Module.End R (ω X)` on
  `ω (⨁ fun _ : ι ↦ X)`, characterized by `CategoryTheory.Functor.eq_powerAlgHom_iff`.
-/

public section

namespace CategoryTheory.Functor

open Limits

universe w v u u'

variable {R : Type u'} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasFiniteBiproducts C] (ω : C ⥤ ModuleCat.{w} R) [ω.Additive]
  (X : C) (ι : Type*)

/-- The identity `ιₖ ≫ πⱼ = δₖⱼ` of a finite power of `X`, on elements of the fibre of an
additive functor to modules. -/
theorem map_π_map_ι_apply [DecidableEq ι] [Finite ι] (j k : ι) (x : ω.obj X) :
    (ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom ((ω.map (biproduct.ι (fun _ : ι ↦ X) k)).hom x) =
      if k = j then x else 0 := by
  have h := congrArg (fun φ ↦ (ω.map φ).hom x)
    (biproduct.ι_π (fun _ : ι ↦ X) k j)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  split_ifs with hkj
  · subst hkj
    simp
  · simp

variable {ι} in
/-- An element of the fibre `ω (⨁ F)` of a finite biproduct is determined by its images under
the projections. -/
theorem ext_map_π_apply [Finite ι] {F : ι → C} {v v' : ω.obj (⨁ F)}
    (h : ∀ j, (ω.map (biproduct.π F j)).hom v = (ω.map (biproduct.π F j)).hom v') :
    v = v' := by
  have := Fintype.ofFinite ι
  rw [← sum_map_ι_map_π_apply ω F v, ← sum_map_ι_map_π_apply ω F v']
  simp only [h]

variable [Fintype ι]

/-- The underlying linear map of `powerAlgHom`. -/
private noncomputable def powerEnd (f : Module.End R (ω.obj X)) :
    Module.End R (ω.obj (⨁ fun _ : ι ↦ X)) :=
  ∑ j, (ω.map (biproduct.ι (fun _ : ι ↦ X) j)).hom ∘ₗ f ∘ₗ
    (ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom

private lemma map_π_powerEnd_apply (f : Module.End R (ω.obj X)) (j : ι)
    (v : ω.obj (⨁ fun _ : ι ↦ X)) :
    (ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom (powerEnd ω X ι f v) =
      f ((ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom v) := by
  classical
  simp [powerEnd, map_π_map_ι_apply]

/-- The diagonal action of an endomorphism `f` of `ω X` on `ω (⨁ fun _ : ι ↦ X)`, namely
`∑ j, ω(ιⱼ) ∘ f ∘ ω(πⱼ)`. -/
noncomputable def powerAlgHom :
    Module.End R (ω.obj X) →ₐ[R] Module.End R (ω.obj (⨁ fun _ : ι ↦ X)) where
  toFun := powerEnd ω X ι
  map_one' := LinearMap.ext fun v ↦ ext_map_π_apply ω fun j ↦ by
    simp [map_π_powerEnd_apply]
  map_mul' f g := LinearMap.ext fun v ↦ ext_map_π_apply ω fun j ↦ by
    simp [map_π_powerEnd_apply]
  map_zero' := LinearMap.ext fun v ↦ ext_map_π_apply ω fun j ↦ by
    simp [map_π_powerEnd_apply]
  map_add' f g := LinearMap.ext fun v ↦ ext_map_π_apply ω fun j ↦ by
    simp [map_π_powerEnd_apply]
  commutes' c := LinearMap.ext fun v ↦ ext_map_π_apply ω fun j ↦ by
    simp [map_π_powerEnd_apply, Module.algebraMap_end_apply]

variable {X ι}

/-- The defining formula `∑ j, ω(ιⱼ) ∘ f ∘ ω(πⱼ)` of the diagonal action. -/
theorem powerAlgHom_apply (f : Module.End R (ω.obj X)) (v : ω.obj (⨁ fun _ : ι ↦ X)) :
    ω.powerAlgHom X ι f v = ∑ j, (ω.map (biproduct.ι (fun _ : ι ↦ X) j)).hom
      (f ((ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom v)) := by
  simp [powerAlgHom, powerEnd]

/-- The diagonal action commutes with the projections. -/
@[simp]
theorem map_π_powerAlgHom_apply (f : Module.End R (ω.obj X)) (j : ι)
    (v : ω.obj (⨁ fun _ : ι ↦ X)) :
    (ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom (ω.powerAlgHom X ι f v) =
      f ((ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom v) :=
  map_π_powerEnd_apply ω X ι f j v

/-- The diagonal action commutes with the inclusions. -/
@[simp]
theorem powerAlgHom_map_ι_apply (f : Module.End R (ω.obj X)) (j : ι) (x : ω.obj X) :
    ω.powerAlgHom X ι f ((ω.map (biproduct.ι (fun _ : ι ↦ X) j)).hom x) =
      (ω.map (biproduct.ι (fun _ : ι ↦ X) j)).hom (f x) := by
  classical
  refine ext_map_π_apply ω fun k ↦ ?_
  rw [map_π_powerAlgHom_apply, map_π_map_ι_apply, map_π_map_ι_apply]
  split_ifs <;> simp

/-- The diagonal action of `f` is the unique endomorphism of `ω (⨁ fun _ : ι ↦ X)` intertwining
every projection with `f`. -/
theorem eq_powerAlgHom_iff (f : Module.End R (ω.obj X))
    (φ : Module.End R (ω.obj (⨁ fun _ : ι ↦ X))) :
    φ = ω.powerAlgHom X ι f ↔ ∀ j v, (ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom (φ v) =
      f ((ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom v) := by
  refine ⟨?_, fun h ↦ LinearMap.ext fun v ↦ ext_map_π_apply ω fun j ↦ by simp [h]⟩
  rintro rfl j v
  exact map_π_powerAlgHom_apply ω f j v

end CategoryTheory.Functor
