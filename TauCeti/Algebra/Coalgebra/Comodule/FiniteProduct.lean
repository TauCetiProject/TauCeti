/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.FinitePreadditive
import TauCeti.Algebra.Coalgebra.Comodule.Product

/-!
# Products of finitely generated comodules

This file packages the direct-sum product comodule inside `FGComoduleCat`. The ambient
category `ComoduleCat` already has the product comodule on the cartesian product of the
underlying modules; finite generation is preserved by binary products of modules, so this
construction stays in the full subcategory of finitely generated comodules.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target on the
finite-dimensional comodule representation category: products and biproduct-style maps are
needed before tensor products, duals, and the rigid monoidal category can be built.

## Main declarations

* `TauCeti.FGComoduleCat.prod`: the product of two finitely generated comodules.
* `TauCeti.FGComoduleCat.prodFst`, `prodSnd`, `prodInl`, `prodInr`: the canonical maps.
* `TauCeti.FGComoduleCat.prodLift`, `prodDesc`: maps into and out of the product.

## References

This supplies finite-category packaging for `ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 1 target "Comodules over a coalgebra/Hopf algebra": the finite-dimensional comodule
category should have additive finite products before the rigid monoidal representation
category is developed. The construction reuses the direct-sum comodule from
`TauCeti.Algebra.Coalgebra.Comodule.Product`.
-/

open CategoryTheory

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The product of two finitely generated comodules, carried by the product of the
underlying modules. -/
abbrev prod (M N : FGComoduleCat.{u, v, w} R C) : FGComoduleCat.{u, v, w} R C where
  obj := ComoduleCat.prod R C M.obj N.obj
  property := by
    change Module.Finite R (M × N)
    exact Module.Finite.prod

section Semiring

variable {R C}

/-- The first projection from the product of finitely generated comodules. -/
abbrev prodFst (M N : FGComoduleCat.{u, v, w} R C) : prod R C M N ⟶ M :=
  ObjectProperty.homMk (ComoduleCat.prodFst M.obj N.obj)

/-- The second projection from the product of finitely generated comodules. -/
abbrev prodSnd (M N : FGComoduleCat.{u, v, w} R C) : prod R C M N ⟶ N :=
  ObjectProperty.homMk (ComoduleCat.prodSnd M.obj N.obj)

/-- The morphism into the product of finitely generated comodules induced by two morphisms
with a common source. -/
abbrev prodLift {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodLift f.hom g.hom)

/-- The left inclusion into the product of finitely generated comodules. -/
abbrev prodInl (M N : FGComoduleCat.{u, v, w} R C) : M ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodInl M.obj N.obj)

/-- The right inclusion into the product of finitely generated comodules. -/
abbrev prodInr (M N : FGComoduleCat.{u, v, w} R C) : N ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodInr M.obj N.obj)

/-- The morphism out of the product of finitely generated comodules induced by two morphisms
with a common target. -/
abbrev prodDesc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prod R C M N ⟶ P :=
  ObjectProperty.homMk (ComoduleCat.prodDesc f.hom g.hom)

/-- The ambient comodule underlying the finitely generated product is the ambient product. -/
@[simp]
theorem prod_obj (M N : FGComoduleCat.{u, v, w} R C) :
    (prod R C M N).obj = ComoduleCat.prod R C M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying the first projection is the ambient first
projection. -/
@[simp]
theorem prodFst_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodFst M N).hom = ComoduleCat.prodFst M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying the second projection is the ambient second
projection. -/
@[simp]
theorem prodSnd_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodSnd M N).hom = ComoduleCat.prodSnd M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying a product lift is the ambient product lift. -/
@[simp]
theorem prodLift_hom {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    (prodLift f g).hom = ComoduleCat.prodLift f.hom g.hom :=
  rfl

/-- The ambient comodule morphism underlying the left inclusion is the ambient left
inclusion. -/
@[simp]
theorem prodInl_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodInl M N).hom = ComoduleCat.prodInl M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying the right inclusion is the ambient right
inclusion. -/
@[simp]
theorem prodInr_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodInr M N).hom = ComoduleCat.prodInr M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying a product desc is the ambient product desc. -/
@[simp]
theorem prodDesc_hom {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    (prodDesc f g).hom = ComoduleCat.prodDesc f.hom g.hom :=
  rfl

/-- Evaluating the first projection returns the first component. -/
@[simp]
theorem prodFst_apply (M N : FGComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodFst M N x = x.1 :=
  rfl

/-- Evaluating the second projection returns the second component. -/
@[simp]
theorem prodSnd_apply (M N : FGComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodSnd M N x = x.2 :=
  rfl

/-- Evaluating the product lift gives the pair of evaluations. -/
@[simp]
theorem prodLift_apply {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N)
    (p : P) :
    prodLift f g p = (f p, g p) :=
  rfl

/-- Evaluating the left inclusion gives a pair with zero right component. -/
@[simp]
theorem prodInl_apply (M N : FGComoduleCat.{u, v, w} R C) (m : M) :
    prodInl M N m = (m, 0) :=
  rfl

/-- Evaluating the right inclusion gives a pair with zero left component. -/
@[simp]
theorem prodInr_apply (M N : FGComoduleCat.{u, v, w} R C) (n : N) :
    prodInr M N n = (0, n) :=
  rfl

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Evaluating the product desc adds the evaluations of its two components. -/
@[simp]
theorem prodDesc_apply {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P)
    (x : prod R C M N) :
    prodDesc f g x = f x.1 + g x.2 :=
  rfl

/-- The first projection after a product lift is the first morphism. -/
@[simp]
theorem prodLift_fst {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodLift_hom, prodFst_hom]
  exact
    (ComoduleCat.prodLift_fst (R := R) (C := C) f.hom g.hom)

/-- The second projection after a product lift is the second morphism. -/
@[simp]
theorem prodLift_snd {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodLift_hom, prodSnd_hom]
  exact
    (ComoduleCat.prodLift_snd (R := R) (C := C) f.hom g.hom)

/-- The product desc after the left inclusion is the first morphism. -/
@[simp]
theorem prodInl_desc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prodInl M N ≫ prodDesc f g = f := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodInl_hom, prodDesc_hom]
  exact
    (ComoduleCat.prodInl_desc (R := R) (C := C) f.hom g.hom)

/-- The product desc after the right inclusion is the second morphism. -/
@[simp]
theorem prodInr_desc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prodInr M N ≫ prodDesc f g = g := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodInr_hom, prodDesc_hom]
  exact
    (ComoduleCat.prodInr_desc (R := R) (C := C) f.hom g.hom)

/-- The first projection after the left inclusion is the identity. -/
@[simp]
theorem prodInl_fst (M N : FGComoduleCat.{u, v, w} R C) :
    prodInl M N ≫ prodFst M N = 𝟙 M := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodInl_hom, prodFst_hom,
    ObjectProperty.FullSubcategory.id_hom]
  exact
    (ComoduleCat.prodInl_fst (R := R) (C := C) M.obj N.obj)

/-- The second projection after the left inclusion is zero. -/
@[simp]
theorem prodInl_snd (M N : FGComoduleCat.{u, v, w} R C) :
    prodInl M N ≫ prodSnd M N = 0 := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodInl_hom, prodSnd_hom, hom_zero]
  exact
    (ComoduleCat.prodInl_snd (R := R) (C := C) M.obj N.obj)

/-- The first projection after the right inclusion is zero. -/
@[simp]
theorem prodInr_fst (M N : FGComoduleCat.{u, v, w} R C) :
    prodInr M N ≫ prodFst M N = 0 := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodInr_hom, prodFst_hom, hom_zero]
  exact
    (ComoduleCat.prodInr_fst (R := R) (C := C) M.obj N.obj)

/-- The second projection after the right inclusion is the identity. -/
@[simp]
theorem prodInr_snd (M N : FGComoduleCat.{u, v, w} R C) :
    prodInr M N ≫ prodSnd M N = 𝟙 N := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodInr_hom, prodSnd_hom,
    ObjectProperty.FullSubcategory.id_hom]
  exact
    (ComoduleCat.prodInr_snd (R := R) (C := C) M.obj N.obj)

/-- The two projection-inclusion composites reconstruct the identity of the product. -/
@[simp]
theorem prod_fst_inl_add_snd_inr (M N : FGComoduleCat.{u, v, w} R C) :
    prodFst M N ≫ prodInl M N + prodSnd M N ≫ prodInr M N = 𝟙 (prod R C M N) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, prodFst_hom, prodInl_hom,
    prodSnd_hom, prodInr_hom, hom_add, ObjectProperty.FullSubcategory.id_hom]
  exact
    (ComoduleCat.prod_fst_inl_add_snd_inr (R := R) (C := C) M.obj N.obj)

/-- Morphisms into the product are determined by their projections. -/
@[ext]
theorem prod_hom_ext {P M N : FGComoduleCat.{u, v, w} R C} {f g : P ⟶ prod R C M N}
    (hfst : f ≫ prodFst M N = g ≫ prodFst M N)
    (hsnd : f ≫ prodSnd M N = g ≫ prodSnd M N) : f = g := by
  apply ObjectProperty.hom_ext
  exact ComoduleCat.prod_hom_ext (R := R) (C := C)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodFst_hom] using
      congrArg (fun h => h.hom) hfst)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodSnd_hom] using
      congrArg (fun h => h.hom) hsnd)

/-- Morphisms out of the product are determined by their values on the inclusions. -/
@[ext]
theorem prod_hom_ext' {M N P : FGComoduleCat.{u, v, w} R C} {f g : prod R C M N ⟶ P}
    (hinl : prodInl M N ≫ f = prodInl M N ≫ g)
    (hinr : prodInr M N ≫ f = prodInr M N ≫ g) : f = g := by
  apply ObjectProperty.hom_ext
  exact ComoduleCat.prod_hom_ext' (R := R) (C := C)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodInl_hom] using
      congrArg (fun h => h.hom) hinl)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodInr_hom] using
      congrArg (fun h => h.hom) hinr)

end Ring

end FGComoduleCat

end TauCeti
