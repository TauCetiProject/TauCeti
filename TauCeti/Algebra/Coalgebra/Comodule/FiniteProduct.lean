/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Preadditive.Biproducts
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.FinitePreadditive
import TauCeti.Algebra.Coalgebra.Comodule.Product

/-!
# Products of finitely generated comodules

This file packages the direct-sum product comodule inside `FGComoduleCat`. The ambient
category `ComoduleCat` already has the product comodule on the cartesian product of the
underlying modules; finite generation is preserved by binary products of modules, so this
construction stays in the full subcategory of finitely generated comodules. The same concrete
object is also registered as the categorical binary product in `FGComoduleCat`.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target on the
finite-dimensional comodule representation category: products and biproduct-style maps are
needed before tensor products, duals, and the rigid monoidal category can be built.

## Main declarations

* `TauCeti.FGComoduleCat.prod`: the concrete product of two finitely generated comodules.
* `Limits.prod.fst`, `Limits.prod.snd`, `Limits.prod.inl`, `Limits.prod.inr`: the
  canonical maps.
* `Limits.prod.lift`, `TauCeti.FGComoduleCat.prodDesc`: maps into and out of the product.
* `TauCeti.FGComoduleCat.hasBinaryProduct`: the categorical binary product instance using
  the concrete product object.
* `TauCeti.FGComoduleCat.hasBinaryProducts`, `hasFiniteProducts`: product infrastructure
  induced by the binary product and the existing zero object.
* `TauCeti.FGComoduleCat.hasBinaryBiproduct`: the ring/preadditive biproduct instance induced
  by the binary product.
* `TauCeti.FGComoduleCat.hasBinaryBiproducts`, `hasFiniteBiproducts`: aggregate
  ring/preadditive biproduct infrastructure.

## References

This supplies finite-category packaging for `ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 1 target "Comodules over a coalgebra/Hopf algebra": the finite-dimensional comodule
category should have additive finite products before the rigid monoidal representation
category is developed. The construction reuses the direct-sum comodule from
`TauCeti.Algebra.Coalgebra.Comodule.Product`.
-/

open CategoryTheory CategoryTheory.Limits

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
    -- `ComoduleCat.prod` is carried definitionally by the raw product `M × N`, so the finite
    -- generation obligation is exactly the standard product finiteness instance.
    change Module.Finite R (M × N)
    exact Module.Finite.prod

section Semiring

variable {R C}

private abbrev prodFst (M N : FGComoduleCat.{u, v, w} R C) : prod R C M N ⟶ M :=
  ObjectProperty.homMk (ComoduleCat.prodFst M.obj N.obj)

private abbrev prodSnd (M N : FGComoduleCat.{u, v, w} R C) : prod R C M N ⟶ N :=
  ObjectProperty.homMk (ComoduleCat.prodSnd M.obj N.obj)

private abbrev prodLift {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodLift f.hom g.hom)

private theorem prodFst_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodFst M N).hom = ComoduleCat.prodFst M.obj N.obj :=
  rfl

private theorem prodSnd_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodSnd M N).hom = ComoduleCat.prodSnd M.obj N.obj :=
  rfl

private theorem prodLift_hom {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    (prodLift f g).hom = ComoduleCat.prodLift f.hom g.hom :=
  rfl

private abbrev concreteInl (M N : FGComoduleCat.{u, v, w} R C) : M ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodInl M.obj N.obj)

private abbrev concreteInr (M N : FGComoduleCat.{u, v, w} R C) : N ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodInr M.obj N.obj)

private abbrev concreteDesc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prod R C M N ⟶ P :=
  ObjectProperty.homMk (ComoduleCat.prodDesc f.hom g.hom)

/-- The ambient comodule underlying the finitely generated product is the ambient product. -/
@[simp]
theorem prod_obj (M N : FGComoduleCat.{u, v, w} R C) :
    (prod R C M N).obj = ComoduleCat.prod R C M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying the left inclusion is the ambient left
inclusion. -/
@[simp]
private theorem concreteInl_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (concreteInl M N).hom = ComoduleCat.prodInl M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying the right inclusion is the ambient right
inclusion. -/
@[simp]
private theorem concreteInr_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (concreteInr M N).hom = ComoduleCat.prodInr M.obj N.obj :=
  rfl

/-- The ambient comodule morphism underlying a product desc is the ambient product desc. -/
@[simp]
private theorem concreteDesc_hom {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P)
    (g : N ⟶ P) :
    (concreteDesc f g).hom = ComoduleCat.prodDesc f.hom g.hom :=
  rfl

/-- Evaluating the product desc adds the evaluations of its two components. -/
@[simp]
private theorem concreteDesc_apply {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P)
    (x : prod R C M N) :
    concreteDesc f g x = f x.1 + g x.2 :=
  rfl

/-- Evaluating the left inclusion gives a pair with zero right component. -/
@[simp]
private theorem concreteInl_apply (M N : FGComoduleCat.{u, v, w} R C) (m : M) :
    concreteInl M N m = (m, 0) :=
  rfl

/-- Evaluating the right inclusion gives a pair with zero left component. -/
@[simp]
private theorem concreteInr_apply (M N : FGComoduleCat.{u, v, w} R C) (n : N) :
    concreteInr M N n = (0, n) :=
  rfl

private theorem prodLift_fst {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact
    (ComoduleCat.prodLift_fst (R := R) (C := C) f.hom g.hom)

private theorem prodLift_snd {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact
    (ComoduleCat.prodLift_snd (R := R) (C := C) f.hom g.hom)

private theorem prod_hom_ext {P M N : FGComoduleCat.{u, v, w} R C} {f g : P ⟶ prod R C M N}
    (hfst : f ≫ prodFst M N = g ≫ prodFst M N)
    (hsnd : f ≫ prodSnd M N = g ≫ prodSnd M N) : f = g := by
  apply ObjectProperty.hom_ext
  exact ComoduleCat.prod_hom_ext (R := R) (C := C)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodFst_hom] using
      congrArg (fun h => h.hom) hfst)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodSnd_hom] using
      congrArg (fun h => h.hom) hsnd)

private theorem concreteInl_desc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P)
    (g : N ⟶ P) :
    concreteInl M N ≫ concreteDesc f g = f := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, concreteInl_hom, concreteDesc_hom]
  exact
    (ComoduleCat.prodInl_desc (R := R) (C := C) f.hom g.hom)

private theorem concreteInr_desc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P)
    (g : N ⟶ P) :
    concreteInr M N ≫ concreteDesc f g = g := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, concreteInr_hom, concreteDesc_hom]
  exact
    (ComoduleCat.prodInr_desc (R := R) (C := C) f.hom g.hom)

private theorem concrete_hom_ext' {M N P : FGComoduleCat.{u, v, w} R C}
    {f g : prod R C M N ⟶ P}
    (hinl : concreteInl M N ≫ f = concreteInl M N ≫ g)
    (hinr : concreteInr M N ≫ f = concreteInr M N ≫ g) : f = g := by
  apply ObjectProperty.hom_ext
  exact ComoduleCat.prod_hom_ext' (R := R) (C := C)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, concreteInl_hom] using
      congrArg (fun h => h.hom) hinl)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, concreteInr_hom] using
      congrArg (fun h => h.hom) hinr)

private theorem concreteInl_fst (M N : FGComoduleCat.{u, v, w} R C) :
    concreteInl M N ≫ prodFst M N = 𝟙 M := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, concreteInl_hom, prodFst_hom,
    ObjectProperty.FullSubcategory.id_hom]
  exact
    (ComoduleCat.prodInl_fst (R := R) (C := C) M.obj N.obj)

private theorem concreteInl_snd (M N : FGComoduleCat.{u, v, w} R C) :
    concreteInl M N ≫ prodSnd M N = 0 := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, concreteInl_hom, prodSnd_hom]
  exact
    (ComoduleCat.prodInl_snd (R := R) (C := C) M.obj N.obj)

private theorem concreteInr_fst (M N : FGComoduleCat.{u, v, w} R C) :
    concreteInr M N ≫ prodFst M N = 0 := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, concreteInr_hom, prodFst_hom]
  exact
    (ComoduleCat.prodInr_fst (R := R) (C := C) M.obj N.obj)

private theorem concreteInr_snd (M N : FGComoduleCat.{u, v, w} R C) :
    concreteInr M N ≫ prodSnd M N = 𝟙 N := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, concreteInr_hom, prodSnd_hom,
    ObjectProperty.FullSubcategory.id_hom]
  exact
    (ComoduleCat.prodInr_snd (R := R) (C := C) M.obj N.obj)

private def prodBinaryFan (M N : FGComoduleCat.{u, v, w} R C) : Limits.BinaryFan M N :=
  Limits.BinaryFan.mk (prodFst M N) (prodSnd M N)

private def prodBinaryFanIsLimit (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.IsLimit (prodBinaryFan M N) :=
  Limits.BinaryFan.IsLimit.mk _
    (fun f g => prodLift f g)
    (fun f g => prodLift_fst f g)
    (fun f g => prodLift_snd f g)
    (fun f g _ hfst hsnd =>
      prod_hom_ext
        (hfst.trans (prodLift_fst f g).symm)
        (hsnd.trans (prodLift_snd f g).symm))

private def prodLimitCone (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.LimitCone (Limits.pair M N) :=
  ⟨prodBinaryFan M N, prodBinaryFanIsLimit M N⟩

/-- The concrete product supplies the categorical binary product of finitely generated
comodules. -/
instance hasBinaryProduct (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.HasBinaryProduct M N :=
  Limits.HasLimit.mk ⟨prodBinaryFan M N, prodBinaryFanIsLimit M N⟩

/-- The canonical comparison from the standard categorical product to the concrete finitely
generated product. -/
noncomputable abbrev prodIso (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.limit (Limits.pair M N) ≅ prod R C M N :=
  Limits.limit.isoLimitCone (prodLimitCone M N)

@[reassoc (attr := simp)]
theorem prodIso_hom_fst (M N : FGComoduleCat.{u, v, w} R C) :
    (prodIso M N).hom ≫ prodFst M N = Limits.prod.fst := by
  change (prodIso M N).hom ≫ prodFst M N =
    Limits.limit.π (Limits.pair M N) ⟨Limits.WalkingPair.left⟩
  rw [prodIso]
  exact
    (Limits.limit.isoLimitCone_hom_π (prodLimitCone M N) ⟨Limits.WalkingPair.left⟩)

@[reassoc (attr := simp)]
theorem prodIso_hom_snd (M N : FGComoduleCat.{u, v, w} R C) :
    (prodIso M N).hom ≫ prodSnd M N = Limits.prod.snd := by
  change (prodIso M N).hom ≫ prodSnd M N =
    Limits.limit.π (Limits.pair M N) ⟨Limits.WalkingPair.right⟩
  rw [prodIso]
  exact
    (Limits.limit.isoLimitCone_hom_π (prodLimitCone M N) ⟨Limits.WalkingPair.right⟩)

@[reassoc (attr := simp)]
theorem prodIso_inv_fst (M N : FGComoduleCat.{u, v, w} R C) :
    (prodIso M N).inv ≫ Limits.prod.fst = prodFst M N := by
  change (prodIso M N).inv ≫
    Limits.limit.π (Limits.pair M N) ⟨Limits.WalkingPair.left⟩ = prodFst M N
  rw [prodIso]
  exact
    (Limits.limit.isoLimitCone_inv_π (prodLimitCone M N) ⟨Limits.WalkingPair.left⟩)

@[reassoc (attr := simp)]
theorem prodIso_inv_snd (M N : FGComoduleCat.{u, v, w} R C) :
    (prodIso M N).inv ≫ Limits.prod.snd = prodSnd M N := by
  change (prodIso M N).inv ≫
    Limits.limit.π (Limits.pair M N) ⟨Limits.WalkingPair.right⟩ = prodSnd M N
  rw [prodIso]
  exact
    (Limits.limit.isoLimitCone_inv_π (prodLimitCone M N) ⟨Limits.WalkingPair.right⟩)

/-- The morphism out of the standard product of finitely generated comodules induced by two
morphisms with a common target. -/
noncomputable abbrev prodDesc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P)
    (g : N ⟶ P) : Limits.limit (Limits.pair M N) ⟶ P :=
  (prodIso M N).hom ≫ concreteDesc f g

@[simp]
theorem prod_lift_comp_prodIso_hom {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M)
    (g : P ⟶ N) :
    (Limits.prod.lift f g : P ⟶ Limits.limit (Limits.pair M N)) ≫ (prodIso M N).hom =
      prodLift f g := by
  apply prod_hom_ext
  · rw [Category.assoc, prodIso_hom_fst, Limits.prod.lift_fst, prodLift_fst]
  · rw [Category.assoc, prodIso_hom_snd, Limits.prod.lift_snd, prodLift_snd]

private theorem prod_inl_eq (M N : FGComoduleCat.{u, v, w} R C) :
    (Limits.prod.inl M N : M ⟶ Limits.limit (Limits.pair M N)) =
      concreteInl M N ≫ (prodIso M N).inv := by
  apply Limits.prod.hom_ext
  · simp [Category.assoc, concreteInl_fst]
  · simp [Category.assoc, concreteInl_snd]

private theorem prod_inr_eq (M N : FGComoduleCat.{u, v, w} R C) :
    (Limits.prod.inr M N : N ⟶ Limits.limit (Limits.pair M N)) =
      concreteInr M N ≫ (prodIso M N).inv := by
  apply Limits.prod.hom_ext
  · simp [Category.assoc, concreteInr_fst]
  · simp [Category.assoc, concreteInr_snd]

/-- The product desc after the standard left inclusion is the first morphism. -/
@[simp]
theorem prodInl_desc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    (Limits.prod.inl M N : M ⟶ Limits.limit (Limits.pair M N)) ≫ prodDesc f g = f := by
  simp [prod_inl_eq, prodDesc, Category.assoc, concreteInl_desc]

/-- The product desc after the standard right inclusion is the second morphism. -/
@[simp]
theorem prodInr_desc {M N P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    (Limits.prod.inr M N : N ⟶ Limits.limit (Limits.pair M N)) ≫ prodDesc f g = g := by
  simp [prod_inr_eq, prodDesc, Category.assoc, concreteInr_desc]

/-- Morphisms out of the product are determined by their values on the standard inclusions. -/
@[ext]
theorem prod_hom_ext' {M N P : FGComoduleCat.{u, v, w} R C}
    {f g : Limits.limit (Limits.pair M N) ⟶ P}
    (hinl :
      (Limits.prod.inl M N : M ⟶ Limits.limit (Limits.pair M N)) ≫ f =
        (Limits.prod.inl M N : M ⟶ Limits.limit (Limits.pair M N)) ≫ g)
    (hinr :
      (Limits.prod.inr M N : N ⟶ Limits.limit (Limits.pair M N)) ≫ f =
        (Limits.prod.inr M N : N ⟶ Limits.limit (Limits.pair M N)) ≫ g) : f = g := by
  rw [← Iso.hom_inv_id_assoc (prodIso M N) f, ← Iso.hom_inv_id_assoc (prodIso M N) g]
  congr 1
  apply concrete_hom_ext'
  · simpa [prod_inl_eq, Category.assoc] using hinl
  · simpa [prod_inr_eq, Category.assoc] using hinr

/-- The two standard projection-inclusion composites reconstruct the identity of the
product. -/
@[simp]
theorem prod_fst_inl_add_snd_inr (M N : FGComoduleCat.{u, v, w} R C) :
    (Limits.prod.fst : Limits.limit (Limits.pair M N) ⟶ M) ≫
        (Limits.prod.inl M N : M ⟶ Limits.limit (Limits.pair M N)) +
      (Limits.prod.snd : Limits.limit (Limits.pair M N) ⟶ N) ≫
        (Limits.prod.inr M N : N ⟶ Limits.limit (Limits.pair M N)) =
        𝟙 (Limits.limit (Limits.pair M N)) := by
  apply Limits.prod.hom_ext
  · rw [comp_add]
    simp only [prod_inl_eq, prod_inr_eq, Category.assoc, prodIso_inv_fst, concreteInl_fst,
      concreteInr_fst, Category.comp_id, Category.id_comp, comp_zero, add_zero]
  · rw [comp_add]
    simp only [prod_inl_eq, prod_inr_eq, Category.assoc, prodIso_inv_snd, concreteInl_snd,
      concreteInr_snd, Category.comp_id, Category.id_comp, comp_zero, zero_add]

/-- Finitely generated comodules have categorical binary products. -/
instance hasBinaryProducts : Limits.HasBinaryProducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.hasBinaryProducts_of_hasLimit_pair (FGComoduleCat.{u, v, w} R C)

/-- Finitely generated comodules have finite products. -/
instance hasFiniteProducts : Limits.HasFiniteProducts (FGComoduleCat.{u, v, w} R C) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The preadditive binary product is also a binary biproduct. -/
instance hasBinaryBiproduct (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.HasBinaryBiproduct M N :=
  Limits.HasBinaryBiproduct.of_hasBinaryProduct M N

/-- Finitely generated comodules over a commutative ring have binary biproducts. -/
instance hasBinaryBiproducts : Limits.HasBinaryBiproducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.HasBinaryBiproducts.of_hasBinaryProducts

/-- Finitely generated comodules over a commutative ring have finite biproducts. -/
instance hasFiniteBiproducts : Limits.HasFiniteBiproducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

end Ring

end FGComoduleCat

end TauCeti
