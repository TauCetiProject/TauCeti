/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.CategoryTheory.Preadditive.Endomorphism
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
public import TauCeti.CategoryTheory.Preadditive.SingleObj
public import TauCeti.Logic.Small.Opposite

import Mathlib.RingTheory.Finiteness.Cardinality
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
`CategoryTheory.Equivalence.additiveCongrLeft`,
turns them into covariant additive functors on `SingleObj Aᵐᵒᵖ`:
`TauCeti.moduleCatMulOppositeEquivModCatOp A`.

When `A` is an `R`-algebra, `SingleObj A` is `R`-linear by the instance
`CategoryTheory.SingleObj.linear` (`TauCeti/CategoryTheory/Preadditive/SingleObj.lean`). When
`R` is a commutative ring, after `open scoped TauCeti.ModCat` the scoped instance
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
* `TauCeti.ModCat.singleObjToEnd A F : A →+* End (F(∗))`: the action of `A` on the
  value at `∗` of a module over `SingleObj Aᵐᵒᵖ`.
* `TauCeti.moduleCatEquivModCatFreeIso A J`: for finite `J`, the free module `J → A` corresponds
  to the coproduct of copies of `Hom(-, ∗)` indexed by `J`, with characteristic equations
  `TauCeti.ι_moduleCatEquivModCatFreeIso_inv` and
  `TauCeti.moduleCatEquivModCatFreeIso_hom_comp_π`.

## Main results

* `TauCeti.moduleCatEquivModCatSelfIso A`: `A` corresponds to `Hom(-, ∗)`.
* `TauCeti.moduleCatMulOppositeEquivModCatOpSelfIso A`: the regular right module corresponds to
  `Hom(∗, -)`.
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

private theorem mulOppositeEquiv_op_comp_unopUnop_map
    {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    ((SingleObj.mulOppositeEquiv A).op.functor ⋙ unopUnop (SingleObj A)).map f =
      (MulOpposite.unop f.unop : A) :=
  congrArg Quiver.Hom.unop (SingleObj.mulOppositeEquiv_functor_map f.unop)

/-- The action of `A` on the value at `∗` of a module over `SingleObj Aᵐᵒᵖ`: `a` acts by
`F(op a)`. -/
def ModCat.singleObjToEnd (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) :
    A →+* End (F.obj.obj (op (SingleObj.star Aᵐᵒᵖ))) :=
  (F.obj.mapEndRingHom (op (SingleObj.star Aᵐᵒᵖ))).comp
    { toFun a := End.of (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ)
        (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a))
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- `ModCat.singleObjToEnd A F` sends `a` to `F(op a)`. -/
@[simp]
theorem ModCat.singleObjToEnd_apply_asHom (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) (a : A) :
    (ModCat.singleObjToEnd A F a).asHom = F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ)
      (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a)) := by
  simp only [ModCat.singleObjToEnd, RingHom.comp_apply, Functor.mapEndRingHom_apply_asHom]
  rfl

private theorem singleObjFunctor_obj_map (M : ModuleCat.{v} A)
    {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    (((SingleObj.mulOppositeEquiv A).op.functor ⋙ unopUnop (SingleObj A)) ⋙
        SingleObj.functor M.smul.toMonoidHom).map f = AddCommGrpCat.ofHom
      (DistribSMul.toAddMonoidHom M (MulOpposite.unop (α := A) f.unop)) :=
  congrArg (fun a ↦ (M.smul a).asHom) (mulOppositeEquiv_op_comp_unopUnop_map A f)

private theorem mkOfSMul_singleObjToEnd_smul (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) (a : A)
    (x : ModuleCat.mkOfSMul (ModCat.singleObjToEnd A F)) :
    a • x = (F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ)
      (MulOpposite.op a))).hom x :=
  ConcreteCategory.congr_hom (ModCat.singleObjToEnd_apply_asHom A F a) x

/-- **Left `A`-modules are modules over `SingleObj Aᵐᵒᵖ`** ([Mac Lane, IX.6]): a module `M`
corresponds to the additive functor with value `M` on which `op a` acts as `a • -`. -/
@[expose] def moduleCatEquivModCat : ModuleCat.{v} A ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ) :=
  let S := (SingleObj.mulOppositeEquiv A).op.functor ⋙ unopUnop (SingleObj A)
  let toModCat : ModuleCat.{v} A ⥤ ModCat.{v} (SingleObj Aᵐᵒᵖ) :=
    { obj M :=
        ⟨S ⋙ SingleObj.functor M.smul.toMonoidHom, (additiveFunctor_iff _).2 ⟨fun {_ _ f g} ↦ by
          -- Keep the transport functor folded so its map equation applies.
          change (SingleObj.functor M.smul.toMonoidHom).map (S.map (f + g)) =
            (SingleObj.functor M.smul.toMonoidHom).map (S.map f) +
              (SingleObj.functor M.smul.toMonoidHom).map (S.map g)
          simp only [S, mulOppositeEquiv_op_comp_unopUnop_map, SingleObj.functor_map]
          exact congrArg End.asHom (map_add M.smul (MulOpposite.unop f.unop)
            (MulOpposite.unop g.unop))⟩⟩
      map φ := ObjectProperty.homMk <|
        Functor.whiskerLeft S (SingleObj.natTrans
          ((forget₂ (ModuleCat A) AddCommGrpCat).map φ)
          (fun a ↦ (ModuleCat.smul_naturality φ a).symm)) }
  let toModuleCat : ModCat.{v} (SingleObj Aᵐᵒᵖ) ⥤ ModuleCat.{v} A :=
    { obj F := ModuleCat.mkOfSMul (ModCat.singleObjToEnd A F)
      map φ := ModuleCat.homMk (φ.hom.app _) fun a ↦ by
          rw [ModuleCat.mkOfSMul_smul, ModuleCat.mkOfSMul_smul,
            ModCat.singleObjToEnd_apply_asHom, ModCat.singleObjToEnd_apply_asHom]
          exact (φ.hom.naturality _).symm }
  have hmap (M : ModuleCat.{v} A) {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
      (toModCat.obj M).obj.map f = AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom M (MulOpposite.unop (α := A) f.unop)) := by
    exact singleObjFunctor_obj_map A M f
  have hsmul (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) (a : A) (x : toModuleCat.obj F) :
      a • x = (F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ)
        (MulOpposite.op a))).hom x := by
    exact mkOfSMul_singleObjToEnd_smul A F a x
  .mk toModCat toModuleCat
    (NatIso.ofComponents (fun M ↦ ModuleCat.isoMk
      (M := M) (N := toModuleCat.obj (toModCat.obj M)) (Iso.refl _) (by
        intro a
        ext x
        exact (hsmul (toModCat.obj M) a x).trans
          (ConcreteCategory.congr_hom (hmap M (Quiver.Hom.op (MulOpposite.op a))) x))) (by
          intros
          ext
          rfl))
    (NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun X ↦ Iso.refl (F.obj.obj X)) (by
        intro X Y f
        ext x
        have hs := hsmul F (MulOpposite.unop (α := A) f.unop) x
        rw [MulOpposite.op_unop, Quiver.Hom.op_unop] at hs
        exact (ConcreteCategory.congr_hom (hmap (toModuleCat.obj F) f) x).trans hs))) (by
          intros
          ext
          rfl))

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
  singleObjFunctor_obj_map A M f

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
  mkOfSMul_singleObjToEnd_smul A F a x

/-- The inverse of `moduleCatEquivModCat A` sends a morphism to its component at `∗`. -/
@[simp]
theorem moduleCatEquivModCat_inverse_map_hom_apply {F G : ModCat.{v} (SingleObj Aᵐᵒᵖ)}
    (φ : F ⟶ G) (x : (moduleCatEquivModCat A).inverse.obj F) :
    ((moduleCatEquivModCat A).inverse.map φ).hom x = (φ.hom.app (op (SingleObj.star _))).hom x :=
  rfl

/-- The forward functor of `moduleCatEquivModCat A` preserves addition of morphisms. -/
instance : (moduleCatEquivModCat.{v} A).functor.Additive where
  map_add := rfl

/-- **The module `A` corresponds to the representable module `Hom(-, ∗)`**: the isomorphism
`MulOpposite.op : A ≃+ Aᵐᵒᵖ` turns left multiplication by `a` into precomposition with `op a`. -/
def moduleCatEquivModCatSelfIso :
    (moduleCatEquivModCat.{u} A).functor.obj (ModuleCat.of A A) ≅
      (ModCat.yoneda (SingleObj Aᵐᵒᵖ)).obj (SingleObj.star Aᵐᵒᵖ) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun _ ↦ (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddCommGrpIso) (by
      intros
      rw [moduleCatEquivModCat_functor_obj_obj_map]
      rfl))

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
  let e := SingleObj.mulOppositeEquiv Aᵐᵒᵖ
  letI : e.op.functor.Additive := inferInstanceAs e.functor.op.Additive
  (moduleCatEquivModCat Aᵐᵒᵖ).trans e.op.additiveCongrLeft

/-- The forward functor of `moduleCatMulOppositeEquivModCatOp A` preserves addition. -/
instance : (moduleCatMulOppositeEquivModCatOp.{v} A).functor.Additive := by
  let e := SingleObj.mulOppositeEquiv Aᵐᵒᵖ
  have : e.op.functor.Additive := inferInstanceAs e.functor.op.Additive
  rw [moduleCatMulOppositeEquivModCatOp, Equivalence.trans_functor]
  infer_instance

/-- The functor of `moduleCatMulOppositeEquivModCatOp A` sends a right module to the covariant
functor with value its underlying abelian group. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_functor_obj_obj_obj (M : ModuleCat.{v} Aᵐᵒᵖ)
    (X : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ) :
    ((moduleCatMulOppositeEquivModCatOp A).functor.obj M).obj.obj X = AddCommGrpCat.of M :=
  (rfl)

/-- The functor of `moduleCatMulOppositeEquivModCatOp A` sends a right `A`-module `M` to the
covariant functor with value `M` on which `a : Aᵐᵒᵖ` acts as `a • -`. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_functor_obj_obj_map (M : ModuleCat.{v} Aᵐᵒᵖ)
    {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ} (f : X ⟶ Y) :
    ((moduleCatMulOppositeEquivModCatOp A).functor.obj M).obj.map f =
      AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M := Aᵐᵒᵖ) M
        (Quiver.Hom.unop (X := op (SingleObj.star Aᵐᵒᵖ)) (Y := op (SingleObj.star Aᵐᵒᵖ)) f.unop)) :=
  by simp [moduleCatMulOppositeEquivModCatOp]

/-- The functor of `moduleCatMulOppositeEquivModCatOp A` takes a right-module morphism to its
underlying group homomorphism at every object. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_functor_map_hom_app
    {M N : ModuleCat.{v} Aᵐᵒᵖ} (φ : M ⟶ N) (X : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ) :
    ((moduleCatMulOppositeEquivModCatOp A).functor.map φ).hom.app X =
      AddCommGrpCat.ofHom φ.hom.toAddMonoidHom :=
  (rfl)

/-- On the right module associated to `F`, the scalar `a` acts by the value of `F` on `a.op.op`. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_inverse_obj_smul
    (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)ᵒᵖ) (a : Aᵐᵒᵖ)
    (x : (moduleCatMulOppositeEquivModCatOp A).inverse.obj F) :
    a • x = (F.obj.map (Quiver.Hom.op (Quiver.Hom.op
      (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) a))).hom x := by
  let e := SingleObj.mulOppositeEquiv Aᵐᵒᵖ
  have : e.op.functor.Additive := inferInstanceAs e.functor.op.Additive
  let G := e.op.additiveCongrLeft.inverse.obj F
  -- The inverse first precomposes `F` and then reads off its scalar action.
  change ↑((moduleCatEquivModCat Aᵐᵒᵖ).inverse.obj G) at x
  have h := moduleCatEquivModCat_inverse_obj_smul Aᵐᵒᵖ G a x
  simp only [G, Equivalence.additiveCongrLeft_inverse_obj_obj, Functor.comp_map,
    Equivalence.op_functor, Functor.op_map, Quiver.Hom.unop_op,
    SingleObj.mulOppositeEquiv_functor_map, MulOpposite.unop_op, e] at h
  exact h

/-- The inverse of `moduleCatMulOppositeEquivModCatOp A` evaluates morphisms at the unique
object. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_inverse_map_hom_apply
    {F G : ModCat.{v} (SingleObj Aᵐᵒᵖ)ᵒᵖ} (φ : F ⟶ G)
    (x : (moduleCatMulOppositeEquivModCatOp A).inverse.obj F) :
    ((moduleCatMulOppositeEquivModCatOp A).inverse.map φ).hom x =
      (φ.hom.app (op (op (SingleObj.star Aᵐᵒᵖ)))).hom x :=
  (rfl)

/-- The regular right `A`-module corresponds to the covariant representable `Hom(∗, -)`. -/
def moduleCatMulOppositeEquivModCatOpSelfIso :
    (moduleCatMulOppositeEquivModCatOp.{u} A).functor.obj (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≅
      (ModCat.yoneda (SingleObj Aᵐᵒᵖ)ᵒᵖ).obj (op (SingleObj.star Aᵐᵒᵖ)) := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun X ↦
    (AddEquiv.mk (opEquiv X.unop (op (SingleObj.star Aᵐᵒᵖ))).symm
      (fun f g ↦ op_add _ f g)).toAddCommGrpIso) ?_)
  intro X Y f
  rw [moduleCatMulOppositeEquivModCatOp_functor_obj_obj_map]
  rfl

/-- The right regular-module comparison sends `a` to `a.op` in
`Hom(X.unop, op ∗)`. -/
@[simp↓]
theorem moduleCatMulOppositeEquivModCatOpSelfIso_hom_hom_app_hom_apply
    (X : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ) (a : Aᵐᵒᵖ) :
    AddCommGrpCat.Hom.hom (X := AddCommGrpCat.of Aᵐᵒᵖ)
      (Y := AddCommGrpCat.of (X.unop ⟶ op (SingleObj.star Aᵐᵒᵖ)))
      ((moduleCatMulOppositeEquivModCatOpSelfIso A).hom.hom.app X) a =
        Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := X.unop.unop) a :=
  (rfl)

/-- The inverse of the right regular-module comparison removes the opposite from a morphism. -/
@[simp↓]
theorem moduleCatMulOppositeEquivModCatOpSelfIso_inv_hom_app_hom_apply
    (X : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ) (f : X.unop ⟶ op (SingleObj.star Aᵐᵒᵖ)) :
    AddCommGrpCat.Hom.hom (X := AddCommGrpCat.of (X.unop ⟶ op (SingleObj.star Aᵐᵒᵖ)))
      (Y := AddCommGrpCat.of Aᵐᵒᵖ) ((moduleCatMulOppositeEquivModCatOpSelfIso A).inv.hom.app X) f =
        f.unop :=
  (rfl)

end OneObject

section FreeIso

variable (A : Type u) [Ring A]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- **For finite `J`, the free module `J → A` corresponds to the coproduct of copies of
`Hom(-, ∗)` indexed by `J`.** -/
noncomputable def moduleCatEquivModCatFreeIso (J : Type) [Finite J] :
    ((moduleCatEquivModCat.{u} A).functor.obj (ModuleCat.of A (J → A))).obj ≅
      ∐ fun _ : J ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ) :=
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  Φ.mapIso (ModuleCat.biproductIsoPi fun _ : J ↦ ModuleCat.of A A).symm ≪≫
    Φ.mapBiproduct _ ≪≫
    biproduct.mapIso (g := fun _ : J ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ))
      (fun _ ↦ (additiveFunctor _ _).ι.mapIso (moduleCatEquivModCatSelfIso A)) ≪≫
    biproduct.isoCoproduct _

/-- **The inverse of `moduleCatEquivModCatFreeIso A J` on the `i`-th summand** is the image of
the inclusion `A ⟶ (J → A)` of the `i`-th coordinate, after `Hom(-, ∗) ≅ A`. -/
@[simp, reassoc (attr := simp)]
theorem ι_moduleCatEquivModCatFreeIso_inv {J : Type} [Finite J] [DecidableEq J] (i : J) :
    Sigma.ι (fun _ : J ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)) i ≫
        (moduleCatEquivModCatFreeIso A J).inv =
      (moduleCatEquivModCatSelfIso A).inv.hom ≫ ((moduleCatEquivModCat A).functor.map
        (ModuleCat.ofHom (LinearMap.single A (fun _ : J ↦ A) i))).hom := by
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  let P : J → ModuleCat.{u} A := fun _ ↦ ModuleCat.of A A
  let Y : J → (SingleObj Aᵐᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    fun _ ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)
  let e (j : J) : Φ.obj (P j) ≅ Y j :=
    (additiveFunctor _ _).ι.mapIso (moduleCatEquivModCatSelfIso A)
  have hι : Sigma.ι Y i ≫ (biproduct.isoCoproduct Y).inv = biproduct.ι Y i := by
    rw [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc]
  -- Expose the four comparison maps while keeping the functor `Φ` folded.
  change Sigma.ι Y i ≫ (biproduct.isoCoproduct Y).inv ≫
      biproduct.map (fun j ↦ (e j).inv) ≫ Φ.biproductComparison' P ≫
        Φ.map (ModuleCat.biproductIsoPi P).hom =
    (e i).inv ≫ Φ.map (ModuleCat.ofHom (LinearMap.single A (fun _ : J ↦ A) i))
  simp only [reassoc_of% hι, biproduct.ι_map_assoc]
  -- The injection from `biproduct.ι_map_assoc` uses a lambda for the composed family.
  change (e i).inv ≫ biproduct.ι (Φ.obj ∘ P) i ≫ Φ.biproductComparison' P ≫
    Φ.map (ModuleCat.biproductIsoPi P).hom = _
  rw [Functor.ι_biproductComparison'_assoc, ← Φ.map_comp, ModuleCat.ι_biproductIsoPi_hom]

/-- **The `i`-th coordinate of `moduleCatEquivModCatFreeIso A J`** is the image of the projection
`(J → A) ⟶ A` to the `i`-th coordinate, followed by `A ≅ Hom(-, ∗)`. The coordinate on the
coproduct is its canonical projection `Sigma.π`, which is zero on the other summands. -/
@[simp, reassoc (attr := simp)]
theorem moduleCatEquivModCatFreeIso_hom_comp_π {J : Type} [Finite J] [DecidableEq J] (i : J) :
    (moduleCatEquivModCatFreeIso A J).hom ≫
        Sigma.π (fun _ : J ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)) i =
      ((moduleCatEquivModCat A).functor.map
        (ModuleCat.ofHom (LinearMap.proj (R := A) (φ := fun _ : J ↦ A) i))).hom ≫
        (moduleCatEquivModCatSelfIso A).hom.hom := by
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  let P : J → ModuleCat.{u} A := fun _ ↦ ModuleCat.of A A
  let Y : J → (SingleObj Aᵐᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    fun _ ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ)
  let e (j : J) : Φ.obj (P j) ≅ Y j :=
    (additiveFunctor _ _).ι.mapIso (moduleCatEquivModCatSelfIso A)
  have hπ : (biproduct.isoCoproduct Y).inv ≫ biproduct.π Y i = Sigma.π Y i := by
    apply Sigma.hom_ext
    intro j
    rw [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc, Sigma.ι_π, biproduct.ι_π]
  -- Expose the four comparison maps while keeping the functor `Φ` folded.
  change Φ.map (ModuleCat.biproductIsoPi P).inv ≫ Φ.biproductComparison P ≫
      biproduct.map (fun j ↦ (e j).hom) ≫ (biproduct.isoCoproduct Y).hom ≫ Sigma.π Y i =
    Φ.map (ModuleCat.ofHom (LinearMap.proj (R := A) (φ := fun _ : J ↦ A) i)) ≫ (e i).hom
  simp only [← hπ, Iso.hom_inv_id_assoc, biproduct.map_π, Functor.biproductComparison_π_assoc,
    ← Φ.map_comp_assoc, ModuleCat.biproductIsoPi_inv_comp_π]

end FreeIso

section Transfer

variable {A : Type u} [Ring A]

/-- A linear map `p : Aⁿ ⟶ M` is surjective exactly when the corresponding morphism from a finite
sum of copies of `Hom(-, ∗)` is an epimorphism. -/
private theorem epi_moduleCatEquivModCatFreeIso_inv_comp_iff {n : ℕ} {M : ModuleCat.{u} A}
    (p : ModuleCat.of A (Fin n → A) ⟶ M) :
    Epi ((moduleCatEquivModCatFreeIso A (Fin n)).inv ≫
      ((moduleCatEquivModCat A).functor.map p).hom) ↔ Function.Surjective p.hom := by
  have := (additiveFunctor (SingleObj Aᵐᵒᵖ)ᵒᵖ
    AddCommGrpCat.{u}).preservesEpimorphisms_ι_of_isNormalMonoCategory
  rw [epi_comp_iff_of_epi, ← ModuleCat.epi_iff_surjective]
  exact ((moduleCatEquivModCat A).functor ⋙ (additiveFunctor _ _).ι).epi_map_iff_epi p

/-- A complex `Aᵐ ⟶ Aⁿ ⟶ M` of left `A`-modules is exact exactly when the corresponding complex
of finite sums of copies of `Hom(-, ∗)` is. -/
private theorem exact_moduleCatEquivModCatFreeIso_iff {m n : ℕ} {M : ModuleCat.{u} A}
    (f : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A))
    (p : ModuleCat.of A (Fin n → A) ⟶ M) (h : f ≫ p = 0)
    (h' : ((moduleCatEquivModCatFreeIso A (Fin m)).inv ≫
      ((moduleCatEquivModCat A).functor.map f).hom ≫ (moduleCatEquivModCatFreeIso A (Fin n)).hom) ≫
      (moduleCatEquivModCatFreeIso A (Fin n)).inv ≫
        ((moduleCatEquivModCat A).functor.map p).hom = 0) :
    (ShortComplex.mk _ _ h').Exact ↔ LinearMap.range f.hom = LinearMap.ker p.hom := by
  have : (additiveFunctor (SingleObj Aᵐᵒᵖ)ᵒᵖ AddCommGrpCat.{u}).IsClosedUnderFiniteLimits := {}
  have : (additiveFunctor (SingleObj Aᵐᵒᵖ)ᵒᵖ AddCommGrpCat.{u}).IsClosedUnderFiniteColimits := {}
  rw [← ShortComplex.moduleCat_exact_iff_range_eq_ker (ShortComplex.mk f p h),
    ← ShortComplex.exact_map_iff_of_faithful _
      ((moduleCatEquivModCat A).functor ⋙ (additiveFunctor _ _).ι)]
  exact ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (moduleCatEquivModCatFreeIso A (Fin m)).symm (moduleCatEquivModCatFreeIso A (Fin n)).symm
    (Iso.refl _) (by simp) (by simp))

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
    obtain rfl : Y = fun _ ↦ SingleObj.star Aᵐᵒᵖ := funext fun _ ↦ Quiver.SingleObj.ext
    obtain ⟨p, rfl⟩ : ∃ p₀, p = (moduleCatEquivModCatFreeIso A (Fin n)).inv ≫ Φ.map p₀ :=
      ⟨Φ.preimage ((moduleCatEquivModCatFreeIso A (Fin n)).hom ≫ p), by simp⟩
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
  let e (n : ℕ) := moduleCatEquivModCatFreeIso A (Fin n)
  rw [isFinitelyPresentedFunctor_def]
  constructor
  · rintro ⟨m, n, X, Y, f, p, h, hp, hS⟩
    obtain rfl : X = fun _ ↦ SingleObj.star Aᵐᵒᵖ := funext fun _ ↦ Quiver.SingleObj.ext
    obtain rfl : Y = fun _ ↦ SingleObj.star Aᵐᵒᵖ := funext fun _ ↦ Quiver.SingleObj.ext
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
    exact (Submodule.fg_iff_exists_fin_linearMap A (Fin n → A)).2 ⟨m, f.hom, hker⟩
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
