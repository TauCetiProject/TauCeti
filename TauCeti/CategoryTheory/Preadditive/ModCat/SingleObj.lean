/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
public import TauCeti.CategoryTheory.Preadditive.SingleObj
public import TauCeti.Logic.Small.Opposite

import TauCeti.Algebra.Category.ModuleCat.Biproducts

/-!
# Rings as preadditive categories with one object

A ring `A` is a preadditive category `SingleObj A` with one object `∗`, whose endomorphisms are
the elements of `A`, composed by `f ≫ g = g * f`. A left `A`-module `M` is then the additive
functor on `(SingleObj Aᵐᵒᵖ)ᵒᵖ` with value `M`, on which `op a` acts as `a • -`
([Mac Lane, IX.6]). This gives the equivalence
`TauCeti.moduleCatEquivModCat A : ModuleCat A ≌ ModCat (SingleObj Aᵐᵒᵖ)`, which sends `A` to the
representable module `Hom(-, ∗)`. Right `A`-modules are left `Aᵐᵒᵖ`-modules, and the
isomorphism `CategoryTheory.SingleObj.mulOppositeEquiv : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`
(`TauCeti/CategoryTheory/SingleObj.lean`), through
`CategoryTheory.Equivalence.modCatCongr` (`TauCeti/CategoryTheory/Preadditive/ModCat/Basic.lean`),
turns them into covariant additive functors on `SingleObj Aᵐᵒᵖ`:
`TauCeti.moduleCatMulOppositeEquivModCatOp A`.

When `A` is an `R`-algebra, `SingleObj A` is `R`-linear by the instance
`CategoryTheory.SingleObj.linear` (`TauCeti/CategoryTheory/Preadditive/SingleObj.lean`). Since
`Aᵐᵒᵖ` is again an `R`-algebra, after `open scoped TauCeti.ModCat` the scoped instance
`TauCeti.ModCat.linear` makes `ModCat (SingleObj Aᵐᵒᵖ)` an `R`-linear category, with `r` acting
through the source as in `CategoryTheory.AdditiveFunctor.sourceLinear`. If `A` is `w`-small, then
`SingleObj Aᵐᵒᵖ` is essentially `w`-small, by `TauCeti.small_mulOpposite`
(`TauCeti/Logic/Small/Opposite.lean`).

The equivalence transfers the notions of `TauCeti.ModCat`: projectivity, exactness of short
complexes, finite generation and finite presentation. For the last two, a finite free module
`Aⁿ` corresponds to the finite sum of `n` copies of `Hom(-, ∗)`.

## Main definitions

* `TauCeti.moduleCatEquivModCat A : ModuleCat.{v} A ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ)`.
* `TauCeti.moduleCatMulOppositeEquivModCatOp A :
  ModuleCat.{v} Aᵐᵒᵖ ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ)ᵒᵖ`.
* `TauCeti.ModCat.singleObjToEnd A F : A →+* AddMonoid.End (F(∗))`: the action of `A` on the
  value at `∗` of a module over `SingleObj Aᵐᵒᵖ`.
* `TauCeti.moduleCatEquivModCatFreeIso A n`: `Aⁿ` corresponds to the sum of `n` copies of
  `Hom(-, ∗)`, with the characteristic equations `TauCeti.ι_moduleCatEquivModCatFreeIso_inv` and
  `TauCeti.moduleCatEquivModCatFreeIso_hom_comp_π`.

## Main results

* `TauCeti.moduleCatEquivModCatSelfIso A`: `A` corresponds to `Hom(-, ∗)`.
* `ModuleCat.projective_moduleCatEquivModCat_functor_obj_iff`,
  `CategoryTheory.ShortComplex.exact_map_moduleCatEquivModCat_functor_iff`,
  `ModuleCat.isFinitelyGeneratedFunctor_moduleCatEquivModCat_iff`,
  `ModuleCat.isFinitelyPresentedFunctor_moduleCatEquivModCat_iff`: the transfer lemmas.

## References

* S. Mac Lane, *Categories for the working mathematician*, 2nd ed., Springer, 1998, IX.6.
* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti

/-- A `w`-small ring gives an essentially `w`-small category `SingleObj Aᵐᵒᵖ`, by
`small_mulOpposite`. -/
example (A : Type u) [Ring A] [Small.{w} A] : EssentiallySmall.{w} (SingleObj Aᵐᵒᵖ) :=
  inferInstance

/-- On `SingleObj A`, a contravariant functor reverses the multiplication:
`F(a * b) = F(b) ∘ F(a)`, since `a * b` is the composite `b ≫ a`. This example checks the
multiplication order; it is why, for a ring `A`, additive contravariant functors on `SingleObj A`
are right `A`-modules. -/
example (A : Type*) [Monoid A] (F : (SingleObj A)ᵒᵖ ⥤ AddCommGrpCat) (a b : A) :
    F.map (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) (a * b)) =
      F.map (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) a) ≫
        F.map (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) b) :=
  F.map_comp (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) a)
    (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) b)

open scoped TauCeti.ModCat in
/-- For an `R`-algebra `A`, the category `ModCat (SingleObj Aᵐᵒᵖ)` of left `A`-modules is
`R`-linear through `SingleObj.linear` and the scoped instance `ModCat.linear`. -/
example (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    Linear R (ModCat.{w} (SingleObj Aᵐᵒᵖ)) :=
  inferInstance

section OneObject

variable (A : Type u) [Ring A]

/-- The left `A`-module `M` as the additive functor on `(SingleObj Aᵐᵒᵖ)ᵒᵖ` with value `M`,
on which `op a` acts as `a • -`. -/
@[expose] def moduleCatToModCat : ModuleCat.{v} A ⥤ ModCat.{v} (SingleObj Aᵐᵒᵖ) where
  obj M :=
    ⟨{ obj _ := AddCommGrpCat.of M
       map f := AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom M (MulOpposite.unop (α := A) f.unop))
       map_id _ := by ext; exact one_smul A _
       map_comp f g := by ext; exact mul_smul _ _ _ },
      ⟨fun {_ _ f g} ↦ by ext; exact add_smul _ _ _⟩⟩
  map φ := ObjectProperty.homMk
    { app _ := AddCommGrpCat.ofHom φ.hom.toAddMonoidHom
      naturality _ _ f := by ext; simp }

/-- The action of `A` on the value at `∗` of a module over `SingleObj Aᵐᵒᵖ`: `a` acts by
`F(op a)`. -/
def ModCat.singleObjToEnd (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) :
    A →+* AddMonoid.End (F.obj.obj (op (SingleObj.star Aᵐᵒᵖ))) where
  toFun a := (F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ)
    (MulOpposite.op a))).hom
  map_one' := by exact congrArg AddCommGrpCat.Hom.hom (F.obj.map_id _)
  map_mul' a b := by exact congrArg AddCommGrpCat.Hom.hom (F.obj.map_comp
    (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op b))
    (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a)))
  map_zero' := by exact congrArg AddCommGrpCat.Hom.hom (F.obj.map_zero _ _)
  map_add' a b := by exact congrArg AddCommGrpCat.Hom.hom (F.obj.map_add
    (f := Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a))
    (g := Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op b)))

/-- `ModCat.singleObjToEnd A F` sends `a` to `F(op a)`. -/
@[simp]
theorem ModCat.singleObjToEnd_apply (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) (a : A) :
    ModCat.singleObjToEnd A F a = (F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ)
      (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a))).hom :=
  (rfl)

/-- The module over `SingleObj Aᵐᵒᵖ` as the left `A`-module of its value at `∗`. -/
@[expose] def modCatToModuleCat : ModCat.{v} (SingleObj Aᵐᵒᵖ) ⥤ ModuleCat.{v} A where
  obj F :=
    letI := Module.compHom (F.obj.obj (op (SingleObj.star Aᵐᵒᵖ))) (ModCat.singleObjToEnd A F)
    ModuleCat.of A (F.obj.obj (op (SingleObj.star Aᵐᵒᵖ)))
  map {F G} φ :=
    letI := Module.compHom (F.obj.obj (op (SingleObj.star Aᵐᵒᵖ))) (ModCat.singleObjToEnd A F)
    letI := Module.compHom (G.obj.obj (op (SingleObj.star Aᵐᵒᵖ))) (ModCat.singleObjToEnd A G)
    ModuleCat.ofHom
      { toFun := φ.hom.app _
        map_add' := map_add _
        map_smul' a x := by
          exact ConcreteCategory.congr_hom (φ.hom.naturality
            (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ)
              (MulOpposite.op a))) x }

/-- **Left `A`-modules are modules over `SingleObj Aᵐᵒᵖ`** ([Mac Lane, IX.6]): a module `M`
corresponds to the additive functor with value `M` on which `op a` acts as `a • -`. -/
@[expose] def moduleCatEquivModCat : ModuleCat.{v} A ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ) :=
  .mk (moduleCatToModCat A) (modCatToModuleCat A)
    -- The round trip `(modCatToModuleCat A).obj ((moduleCatToModCat A).obj M)` has carrier `M`,
    -- with `a` acting by `ModCat.singleObjToEnd`, that is, by
    -- `DistribSMul.toAddMonoidHom M (MulOpposite.unop (MulOpposite.op a))`, which unfolds to
    -- `a • -`. So the identity of `M` is `A`-linear and `map_smul'` holds by `rfl`; it is a tactic
    -- proof because this exposed body cannot unfold the non-exposed `ModCat.singleObjToEnd` in a
    -- term. The `show` names this `Module.compHom` structure as the target, so that
    -- `LinearEquiv.toModuleIso` produces an isomorphism with the round trip, not with
    -- `ModuleCat.of A M`.
    (NatIso.ofComponents fun M ↦ LinearEquiv.toModuleIso
      (show M ≃ₗ[A] (modCatToModuleCat A).obj ((moduleCatToModCat A).obj M) from
      { toFun x := x
        invFun x := x
        map_add' _ _ := rfl
        map_smul' _ _ := by exact rfl
        left_inv _ := rfl
        right_inv _ := rfl }))
    (NatIso.ofComponents fun F ↦ ObjectProperty.isoMk _ (NatIso.ofComponents fun _ ↦ Iso.refl _))

/-- The functor of `moduleCatEquivModCat A` sends `M` to the functor with value `M`. -/
@[simp]
theorem moduleCatEquivModCat_functor_obj_obj_obj (M : ModuleCat.{v} A)
    (X : (SingleObj Aᵐᵒᵖ)ᵒᵖ) :
    ((moduleCatEquivModCat A).functor.obj M).obj.obj X = AddCommGrpCat.of M :=
  rfl

/-- The functor of `moduleCatEquivModCat A` makes `op a` act on `M` as `a • -`. -/
@[simp]
theorem moduleCatEquivModCat_functor_obj_obj_map (M : ModuleCat.{v} A)
    {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    ((moduleCatEquivModCat A).functor.obj M).obj.map f = AddCommGrpCat.ofHom
      (DistribSMul.toAddMonoidHom M (MulOpposite.unop (α := A) f.unop)) :=
  rfl

/-- The functor of `moduleCatEquivModCat A` sends a linear map to itself at every object. -/
@[simp]
theorem moduleCatEquivModCat_functor_map_hom_app {M N : ModuleCat.{v} A} (φ : M ⟶ N)
    (X : (SingleObj Aᵐᵒᵖ)ᵒᵖ) :
    ((moduleCatEquivModCat A).functor.map φ).hom.app X =
      AddCommGrpCat.ofHom φ.hom.toAddMonoidHom :=
  rfl

/-- The inverse of `moduleCatEquivModCat A` sends `F` to its value at `∗`, on which `a` acts as
`F(op a)`. -/
@[simp]
theorem moduleCatEquivModCat_inverse_obj_smul (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) (a : A)
    (x : (moduleCatEquivModCat A).inverse.obj F) :
    a • x = (F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ)
      (MulOpposite.op a))).hom x :=
  (rfl)

/-- The inverse of `moduleCatEquivModCat A` sends a morphism to its component at `∗`. -/
@[simp]
theorem moduleCatEquivModCat_inverse_map_hom_apply {F G : ModCat.{v} (SingleObj Aᵐᵒᵖ)}
    (φ : F ⟶ G) (x : (moduleCatEquivModCat A).inverse.obj F) :
    ((moduleCatEquivModCat A).inverse.map φ).hom x = (φ.hom.app (op (SingleObj.star _))).hom x :=
  rfl

instance : (moduleCatEquivModCat.{v} A).functor.Additive where
  map_add := rfl

/-- **The module `A` corresponds to the representable module `Hom(-, ∗)`**: the isomorphism
`MulOpposite.op : A ≃+ Aᵐᵒᵖ` turns left multiplication by `a` into precomposition with `op a`. -/
def moduleCatEquivModCatSelfIso :
    (moduleCatEquivModCat.{u} A).functor.obj (ModuleCat.of A A) ≅
      (ModCat.yoneda (SingleObj Aᵐᵒᵖ)).obj (SingleObj.star Aᵐᵒᵖ) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun _ ↦ (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddCommGrpIso) fun _ ↦ rfl)

/-- The isomorphism `moduleCatEquivModCatSelfIso A` sends `a` to `op a`, stated with the
simp-normal source `AddCommGrpCat.of A` and target `(preadditiveYoneda.obj ∗).obj X`. -/
@[simp]
theorem moduleCatEquivModCatSelfIso_hom_hom_app_hom_apply (X : (SingleObj Aᵐᵒᵖ)ᵒᵖ) (a : A) :
    ConcreteCategory.hom (X := AddCommGrpCat.of A)
      (Y := (preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)).obj X)
      ((moduleCatEquivModCatSelfIso A).hom.hom.app X) a = MulOpposite.op a :=
  (rfl)

/-- The inverse of `moduleCatEquivModCatSelfIso A` sends `op a` to `a`. -/
@[simp]
theorem moduleCatEquivModCatSelfIso_inv_hom_app_hom_apply (X : (SingleObj Aᵐᵒᵖ)ᵒᵖ)
    (a : Aᵐᵒᵖ) :
    ConcreteCategory.hom (X := (preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)).obj X)
      (Y := AddCommGrpCat.of A) ((moduleCatEquivModCatSelfIso A).inv.hom.app X) a =
      MulOpposite.unop a :=
  (rfl)

/-- **Right `A`-modules are covariant additive functors on `SingleObj Aᵐᵒᵖ`**: a right
`A`-module, that is, a left `Aᵐᵒᵖ`-module, is a module over `SingleObj Aᵐᵒᵖᵐᵒᵖ` by
`moduleCatEquivModCat Aᵐᵒᵖ`, and `SingleObj Aᵐᵒᵖᵐᵒᵖ ≌ (SingleObj Aᵐᵒᵖ)ᵒᵖ`. -/
@[expose] def moduleCatMulOppositeEquivModCatOp :
    ModuleCat.{v} Aᵐᵒᵖ ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ)ᵒᵖ :=
  (moduleCatEquivModCat Aᵐᵒᵖ).trans (SingleObj.mulOppositeEquiv Aᵐᵒᵖ).modCatCongr

/-- The functor of `moduleCatMulOppositeEquivModCatOp A` sends a right `A`-module `M` to the
covariant functor with value `M` on which `a : Aᵐᵒᵖ` acts as `a • -`. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_functor_obj_obj_map (M : ModuleCat.{v} Aᵐᵒᵖ)
    {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ} (f : X ⟶ Y) :
    ((moduleCatMulOppositeEquivModCatOp A).functor.obj M).obj.map f =
      AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M := Aᵐᵒᵖ) M
        (Quiver.Hom.unop (X := op (SingleObj.star Aᵐᵒᵖ)) (Y := op (SingleObj.star Aᵐᵒᵖ)) f.unop)) :=
  congrArg (fun a ↦ AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M := Aᵐᵒᵖ) M a))
    (congrArg MulOpposite.unop (SingleObj.mulOppositeEquiv_inverse_map (M := Aᵐᵒᵖ) f.unop))

end OneObject

section FreeIso

variable (A : Type u) [Ring A]

/-- **The free module `Aⁿ` corresponds to the finite sum of `n` copies of `Hom(-, ∗)`.** -/
noncomputable def moduleCatEquivModCatFreeIso (n : ℕ) :
    ((moduleCatEquivModCat.{u} A).functor.obj (ModuleCat.of A (Fin n → A))).obj ≅
      ∐ fun _ : Fin n ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ) :=
  have : HasFiniteBiproducts ((SingleObj Aᵐᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  Φ.mapIso (ModuleCat.biproductIsoPi fun _ : Fin n ↦ ModuleCat.of A A).symm ≪≫
    Φ.mapBiproduct _ ≪≫
    biproduct.mapIso (g := fun _ : Fin n ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ))
      (fun _ ↦ (additiveFunctor _ _).ι.mapIso (moduleCatEquivModCatSelfIso A)) ≪≫
    biproduct.isoCoproduct _

/-- **The inverse of `moduleCatEquivModCatFreeIso A n` on the `i`-th summand** is the image of
the inclusion `A ⟶ Aⁿ` of the `i`-th coordinate, after `Hom(-, ∗) ≅ A`. -/
theorem ι_moduleCatEquivModCatFreeIso_inv {n : ℕ} (i : Fin n) :
    Sigma.ι (fun _ : Fin n ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)) i ≫
        (moduleCatEquivModCatFreeIso A n).inv =
      (moduleCatEquivModCatSelfIso A).inv.hom ≫ ((moduleCatEquivModCat A).functor.map
        (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin n ↦ A) i))).hom := by
  have : HasFiniteBiproducts ((SingleObj Aᵐᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  simp only [moduleCatEquivModCatFreeIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    biproduct.mapIso_inv, biproduct.isoCoproduct_inv, Functor.mapBiproduct_inv, Category.assoc,
    Sigma.ι_comp_desc_assoc, biproduct.ι_map_assoc, biproduct.ι_desc_assoc, ← Functor.map_comp,
    ModuleCat.ι_biproductIsoPi_hom]
  rfl

/-- **The `i`-th coordinate of `moduleCatEquivModCatFreeIso A n`** is the image of the projection
`Aⁿ ⟶ A` to the `i`-th coordinate, followed by `A ≅ Hom(-, ∗)`. The coordinate is read through
any biproduct structure on the sum of copies of `Hom(-, ∗)`. -/
theorem moduleCatEquivModCatFreeIso_hom_comp_π {n : ℕ}
    [HasBiproduct fun _ : Fin n ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)] (i : Fin n) :
    (moduleCatEquivModCatFreeIso A n).hom ≫ (biproduct.isoCoproduct _).inv ≫ biproduct.π _ i =
      ((moduleCatEquivModCat A).functor.map
        (ModuleCat.ofHom (LinearMap.proj (R := A) (φ := fun _ : Fin n ↦ A) i))).hom ≫
        (moduleCatEquivModCatSelfIso A).hom.hom := by
  simp only [moduleCatEquivModCatFreeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    biproduct.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc, biproduct.map_π,
    Functor.mapBiproduct_hom, Function.comp_def, biproduct.lift_π_assoc]
  rw [← Functor.map_comp_assoc, ModuleCat.biproductIsoPi_inv_comp_π]
  rfl

end FreeIso

section Transfer

variable {A : Type u} [Ring A]

/-- A linear map `p : Aⁿ ⟶ M` is surjective exactly when the corresponding morphism from a finite
sum of copies of `Hom(-, ∗)` is an epimorphism. -/
private theorem epi_moduleCatEquivModCatFreeIso_inv_comp_iff {n : ℕ} {M : ModuleCat.{u} A}
    (p : ModuleCat.of A (Fin n → A) ⟶ M) :
    Epi ((moduleCatEquivModCatFreeIso A n).inv ≫ ((moduleCatEquivModCat A).functor.map p).hom) ↔
      Function.Surjective p.hom := by
  have := (additiveFunctor (SingleObj Aᵐᵒᵖ)ᵒᵖ
    AddCommGrpCat.{u}).preservesEpimorphisms_ι_of_isNormalMonoCategory
  rw [epi_comp_iff_of_epi, ← ModuleCat.epi_iff_surjective]
  exact ((moduleCatEquivModCat A).functor ⋙ (additiveFunctor _ _).ι).epi_map_iff_epi p

/-- A complex `Aᵐ ⟶ Aⁿ ⟶ M` of left `A`-modules is exact exactly when the corresponding complex
of finite sums of copies of `Hom(-, ∗)` is. -/
private theorem exact_moduleCatEquivModCatFreeIso_iff {m n : ℕ} {M : ModuleCat.{u} A}
    (f : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A))
    (p : ModuleCat.of A (Fin n → A) ⟶ M) (h : f ≫ p = 0)
    (h' : ((moduleCatEquivModCatFreeIso A m).inv ≫ ((moduleCatEquivModCat A).functor.map f).hom ≫
      (moduleCatEquivModCatFreeIso A n).hom) ≫ (moduleCatEquivModCatFreeIso A n).inv ≫
        ((moduleCatEquivModCat A).functor.map p).hom = 0) :
    (ShortComplex.mk _ _ h').Exact ↔ LinearMap.range f.hom = LinearMap.ker p.hom := by
  have : (additiveFunctor (SingleObj Aᵐᵒᵖ)ᵒᵖ AddCommGrpCat.{u}).IsClosedUnderFiniteLimits := {}
  have : (additiveFunctor (SingleObj Aᵐᵒᵖ)ᵒᵖ AddCommGrpCat.{u}).IsClosedUnderFiniteColimits := {}
  rw [← ShortComplex.moduleCat_exact_iff_range_eq_ker (ShortComplex.mk f p h),
    ← ShortComplex.exact_map_iff_of_faithful _
      ((moduleCatEquivModCat A).functor ⋙ (additiveFunctor _ _).ι)]
  exact ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (moduleCatEquivModCatFreeIso A m).symm
    (moduleCatEquivModCatFreeIso A n).symm (Iso.refl _) (by simp) (by simp))

end Transfer

end TauCeti

namespace ModuleCat

open TauCeti

variable {A : Type u} [Ring A]

/-- **Transfer of projectivity**: a left `A`-module is projective exactly when the corresponding
module over `SingleObj Aᵐᵒᵖ` is. -/
theorem projective_moduleCatEquivModCat_functor_obj_iff (M : ModuleCat.{v} A) :
    Projective ((moduleCatEquivModCat A).functor.obj M) ↔ Projective M :=
  (moduleCatEquivModCat A).map_projective_iff M

/-- **Transfer of finite generation**: a left `A`-module is finitely generated exactly when the
corresponding module over `SingleObj Aᵐᵒᵖ` is a quotient of a finite sum of representable
functors. -/
theorem isFinitelyGeneratedFunctor_moduleCatEquivModCat_iff (M : ModuleCat.{u} A) :
    IsFinitelyGeneratedFunctor ((moduleCatEquivModCat A).functor.obj M).obj ↔
      Module.Finite A M := by
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  rw [isFinitelyGeneratedFunctor_def]
  constructor
  · rintro ⟨n, Y, p, hp⟩
    obtain rfl : Y = fun _ ↦ SingleObj.star Aᵐᵒᵖ := rfl
    obtain ⟨p, rfl⟩ : ∃ p₀, p = (moduleCatEquivModCatFreeIso A n).inv ≫ Φ.map p₀ :=
      ⟨Φ.preimage ((moduleCatEquivModCatFreeIso A n).hom ≫ p), by simp⟩
    exact Module.Finite.of_surjective _ ((epi_moduleCatEquivModCatFreeIso_inv_comp_iff p).1 hp)
  · intro
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
    exact ⟨n, fun _ ↦ SingleObj.star Aᵐᵒᵖ, _,
      (epi_moduleCatEquivModCatFreeIso_inv_comp_iff (ModuleCat.ofHom f)).2 hf⟩

/-- **Transfer of finite presentation**: a left `A`-module is finitely presented exactly when the
corresponding module over `SingleObj Aᵐᵒᵖ` is the cokernel of a morphism between finite sums of
representable functors. -/
theorem isFinitelyPresentedFunctor_moduleCatEquivModCat_iff (M : ModuleCat.{u} A) :
    IsFinitelyPresentedFunctor ((moduleCatEquivModCat A).functor.obj M).obj ↔
      Module.FinitePresentation A M := by
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  let e := moduleCatEquivModCatFreeIso A
  rw [isFinitelyPresentedFunctor_def]
  constructor
  · rintro ⟨m, n, X, Y, f, p, h, hp, hS⟩
    obtain rfl : X = fun _ ↦ SingleObj.star Aᵐᵒᵖ := rfl
    obtain rfl : Y = fun _ ↦ SingleObj.star Aᵐᵒᵖ := rfl
    obtain ⟨f, rfl⟩ : ∃ f₀, f = (e m).inv ≫ Φ.map f₀ ≫ (e n).hom :=
      ⟨Φ.preimage ((e m).hom ≫ f ≫ (e n).inv), by simp⟩
    obtain ⟨p, rfl⟩ : ∃ p₀, p = (e n).inv ≫ Φ.map p₀ :=
      ⟨Φ.preimage ((e n).hom ≫ p), by simp⟩
    have h₀ : f ≫ p = 0 := Φ.map_injective <| by
      rw [Φ.map_comp, Φ.map_zero, ← cancel_epi (e m).inv, comp_zero, ← h]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hker := (exact_moduleCatEquivModCatFreeIso_iff f p h₀ h).1 hS
    refine Module.finitePresentation_of_surjective p.hom
      ((epi_moduleCatEquivModCatFreeIso_inv_comp_iff p).1 hp) ?_
    rw [← hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · intro
    obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' A M
    have h₀ : ModuleCat.ofHom g ≫ ModuleCat.ofHom f = 0 :=
      ModuleCat.hom_ext hgf.linearMap_comp_eq_zero
    have h : ((e m).inv ≫ Φ.map (ModuleCat.ofHom g) ≫ (e n).hom) ≫ (e n).inv ≫
        Φ.map (ModuleCat.ofHom f) = 0 := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Φ.map_comp, h₀, Φ.map_zero, comp_zero]
    exact ⟨m, n, fun _ ↦ SingleObj.star Aᵐᵒᵖ, fun _ ↦ SingleObj.star Aᵐᵒᵖ, _, _, h,
      (epi_moduleCatEquivModCatFreeIso_inv_comp_iff (ModuleCat.ofHom f)).2 hf,
      (exact_moduleCatEquivModCatFreeIso_iff _ _ h₀ h).2 (LinearMap.exact_iff.1 hgf).symm⟩

end ModuleCat

namespace CategoryTheory.ShortComplex

open TauCeti

/-- **Transfer of exactness**: a short complex of left `A`-modules is exact exactly when the
corresponding short complex of modules over `SingleObj Aᵐᵒᵖ` is. -/
theorem exact_map_moduleCatEquivModCat_functor_iff {A : Type u} [Ring A]
    (S : ShortComplex (ModuleCat.{v} A)) :
    (S.map (moduleCatEquivModCat A).functor).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful _

end CategoryTheory.ShortComplex
