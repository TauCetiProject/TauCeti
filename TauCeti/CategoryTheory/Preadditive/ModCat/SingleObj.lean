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
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.RingTheory.Finiteness.Cardinality
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# Rings as preadditive categories with one object

A ring `A` is a preadditive category `SingleObj A` with one object `∗`, whose endomorphisms are
the elements of `A`, composed by `f ≫ g = g * f`. A left `A`-module `M` is then the additive
functor on `(SingleObj Aᵐᵒᵖ)ᵒᵖ` with value `M`, on which `op a` acts as `a • -`
([Mac Lane, IX.6]). This gives the equivalence
`TauCeti.moduleCatEquivModCat A : ModuleCat A ≌ ModCat (SingleObj Aᵐᵒᵖ)`, which sends `A` to the
representable module `Hom(-, ∗)`. Right `A`-modules are left `Aᵐᵒᵖ`-modules, and the
isomorphism `SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ` turns them into covariant additive functors on
`SingleObj Aᵐᵒᵖ`: `TauCeti.moduleCatMulOppositeEquivModCatOp A`.

When `A` is an `R`-algebra, `SingleObj A` is `R`-linear through the scalar action on `A`. At
`R = ℤ` this linear structure agrees with Mathlib's `preadditiveIntLinear` up to reducible and
instance unfolding, so it is a global instance without creating a non-definitional diamond.
Since `Aᵐᵒᵖ` is again an `R`-algebra, after `open scoped TauCeti.ModCat` the scoped instance
`TauCeti.ModCat.linear` makes `ModCat (SingleObj Aᵐᵒᵖ)` an `R`-linear category, with `r` acting
through the source as in `CategoryTheory.AdditiveFunctor.sourceLinear`.

The equivalence transfers the notions of `TauCeti.ModCat`: projectivity, exactness of short
complexes, finite generation and finite presentation. For the last two, a finite free module
`Aⁿ` corresponds to the finite sum of `n` copies of `Hom(-, ∗)`.

## Main definitions

* `TauCeti.moduleCatEquivModCat A : ModuleCat.{v} A ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ)`.
* `TauCeti.moduleCatMulOppositeEquivModCatOp A :
  ModuleCat.{v} Aᵐᵒᵖ ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ)ᵒᵖ`.
* `CategoryTheory.SingleObj.mulOppositeEquiv M : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`.
* `TauCeti.ModCat.congr e : ModCat C ≌ ModCat D` for an additive equivalence `e : C ≌ D`.
* `TauCeti.moduleCatEquivModCatFreeIso A n`: `Aⁿ` corresponds to the sum of `n` copies of
  `Hom(-, ∗)`.

## Main results

* `TauCeti.moduleCatEquivModCatSelfIso A`: `A` corresponds to `Hom(-, ∗)`.
* `TauCeti.small_mulOpposite`, the instance `EssentiallySmall.{w} (SingleObj M)`, and the
  instance `CategoryTheory.SingleObj.linear : Linear R (SingleObj A)`.
* `TauCeti.projective_moduleCatEquivModCat_functor_obj_iff`,
  `TauCeti.exact_map_moduleCatEquivModCat_functor_iff`,
  `TauCeti.isFinitelyGeneratedFunctor_moduleCatEquivModCat_iff`,
  `TauCeti.isFinitelyPresentedFunctor_moduleCatEquivModCat_iff`: the transfer lemmas.

## References

* S. Mac Lane, *Categories for the working mathematician*, 2nd ed., Springer, 1998, IX.6.
* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.SingleObj

variable (M : Type*) [Monoid M]

/-- The isomorphism of categories `SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`: a morphism `op a` goes to
`a.op`. -/
@[expose] def mulOppositeEquiv : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ where
  functor :=
    { obj _ := op (SingleObj.star M)
      map f := Quiver.Hom.op (X := SingleObj.star M) (Y := SingleObj.star M) (MulOpposite.unop f)
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse :=
    { obj _ := SingleObj.star Mᵐᵒᵖ
      map f := (MulOpposite.op f.unop : Mᵐᵒᵖ)
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance [Small.{w} M] : EssentiallySmall.{w} (SingleObj M) :=
  have : Small.{w} (SingleObj M) := inferInstanceAs (Small.{w} Unit)
  have : LocallySmall.{w} (SingleObj M) := ⟨fun _ _ ↦ inferInstanceAs (Small.{w} M)⟩
  essentiallySmall_of_small_of_locallySmall _

end CategoryTheory.SingleObj

namespace TauCeti

/-- If `A` is `v`-small, so is its opposite monoid `Aᵐᵒᵖ`. -/
instance small_mulOpposite (A : Type u) [Small.{v} A] : Small.{v} Aᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

end TauCeti

namespace CategoryTheory.SingleObj

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- **`SingleObj A` is `R`-linear** for an `R`-algebra `A`, with the scalar action on `A`. At
`R = ℤ` it is definitionally `preadditiveIntLinear`. -/
instance linear : Linear R (SingleObj A) where
  homModule _ _ := inferInstanceAs (Module R A)
  smul_comp _ _ _ r f g := mul_smul_comm r g f
  comp_smul _ _ _ f r g := smul_mul_assoc r g f

/-- At `R = ℤ`, with the canonical algebra `Ring.toIntAlgebra`, `linear ℤ A` is Mathlib's
`preadditiveIntLinear` up to reducible and instance unfolding, so the two instances do not form a
non-definitional diamond. -/
example : Linear.preadditiveIntLinear (C := SingleObj A) = linear ℤ A := by
  with_reducible_and_instances rfl

/-- The same holds for `A = ℤ` with the algebra `Algebra.id ℤ`. -/
example : Linear.preadditiveIntLinear (C := SingleObj ℤ) = @linear ℤ ℤ _ _ (Algebra.id ℤ) := by
  with_reducible_and_instances rfl

/-- On `SingleObj A` itself, contravariant functors are right modules: `F(a * b) = F(b) ∘ F(a)`,
since `a * b` is the composite `b ≫ a`. -/
example (F : (SingleObj A)ᵒᵖ ⥤ AddCommGrpCat) (a b : A) :
    F.map (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) (a * b)) =
      F.map (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) a) ≫
        F.map (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) b) :=
  F.map_comp (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) a)
    (Quiver.Hom.op (X := SingleObj.star A) (Y := SingleObj.star A) b)

end CategoryTheory.SingleObj

namespace TauCeti

open scoped TauCeti.ModCat in
/-- For an `R`-algebra `A`, the category `ModCat (SingleObj Aᵐᵒᵖ)` of left `A`-modules is
`R`-linear through `SingleObj.linear` and the scoped instance `ModCat.linear`. -/
example (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    Linear R (ModCat.{w} (SingleObj Aᵐᵒᵖ)) :=
  inferInstance

variable {C : Type*} [Category* C] [Preadditive C] {D : Type*} [Category* D] [Preadditive D]

/-- Precomposition with an additive equivalence `e : C ≌ D` is an equivalence
`ModCat C ≌ ModCat D`: a module `F` over `C` goes to `e⁻¹ᵒᵖ ⋙ F`. -/
@[expose] def ModCat.congr (e : C ≌ D) [e.functor.Additive] :
    ModCat.{w} C ≌ ModCat.{w} D :=
  (e.op.congrLeft (E := AddCommGrpCat.{w})).congrFullSubcategory <| by
    have : e.op.functor.Additive := inferInstanceAs e.functor.op.Additive
    have : e.op.inverse.Additive := inferInstanceAs e.inverse.op.Additive
    ext F
    refine ⟨fun (_ : (e.op.inverse ⋙ F).Additive) ↦ ?_, fun (_ : F.Additive) ↦ ?_⟩
    · exact Functor.additive_of_iso (e.op.funInvIdAssoc F)
    · exact (inferInstance : (e.op.inverse ⋙ F).Additive)

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
@[expose] def ModCat.singleObjToEnd (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) :
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
    (NatIso.ofComponents fun M ↦ LinearEquiv.toModuleIso
      (show M ≃ₗ[A] (modCatToModuleCat A).obj ((moduleCatToModCat A).obj M) from
      { toFun x := x
        invFun x := x
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
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
theorem moduleCatEquivModCat_inverse_obj_smul (F : ModCat.{v} (SingleObj Aᵐᵒᵖ)) (a : A)
    (x : (moduleCatEquivModCat A).inverse.obj F) :
    a • x = (F.obj.map (Quiver.Hom.op (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ)
      (MulOpposite.op a))).hom x :=
  rfl

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
@[expose] def moduleCatEquivModCatSelfIso :
    (moduleCatEquivModCat.{u} A).functor.obj (ModuleCat.of A A) ≅
      (ModCat.yoneda (SingleObj Aᵐᵒᵖ)).obj (SingleObj.star Aᵐᵒᵖ) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun _ ↦ (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddCommGrpIso) fun _ ↦ rfl)

/-- The isomorphism `moduleCatEquivModCatSelfIso A` sends `a` to `op a`. -/
theorem moduleCatEquivModCatSelfIso_hom_hom_app_apply (X : (SingleObj Aᵐᵒᵖ)ᵒᵖ) (a : A) :
    (moduleCatEquivModCatSelfIso A).hom.hom.app X a = MulOpposite.op a :=
  rfl

instance : (SingleObj.mulOppositeEquiv A).functor.Additive where
  map_add := rfl

/-- **Right `A`-modules are covariant additive functors on `SingleObj Aᵐᵒᵖ`**: a right
`A`-module, that is, a left `Aᵐᵒᵖ`-module, is a module over `SingleObj Aᵐᵒᵖᵐᵒᵖ` by
`moduleCatEquivModCat Aᵐᵒᵖ`, and `SingleObj Aᵐᵒᵖᵐᵒᵖ ≌ (SingleObj Aᵐᵒᵖ)ᵒᵖ`. -/
@[expose] def moduleCatMulOppositeEquivModCatOp :
    ModuleCat.{v} Aᵐᵒᵖ ≌ ModCat.{v} (SingleObj Aᵐᵒᵖ)ᵒᵖ :=
  (moduleCatEquivModCat Aᵐᵒᵖ).trans (ModCat.congr (SingleObj.mulOppositeEquiv Aᵐᵒᵖ))

/-- The functor of `moduleCatMulOppositeEquivModCatOp A` sends a right `A`-module `M` to the
covariant functor with value `M` on which `a : Aᵐᵒᵖ` acts as `a • -`. -/
@[simp]
theorem moduleCatMulOppositeEquivModCatOp_functor_obj_obj_map (M : ModuleCat.{v} Aᵐᵒᵖ)
    {X Y : (SingleObj Aᵐᵒᵖ)ᵒᵖᵒᵖ} (f : X ⟶ Y) :
    ((moduleCatMulOppositeEquivModCatOp A).functor.obj M).obj.map f =
      AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M := Aᵐᵒᵖ) M
        (Quiver.Hom.unop (X := op (SingleObj.star Aᵐᵒᵖ)) (Y := op (SingleObj.star Aᵐᵒᵖ)) f.unop)) :=
  rfl

end OneObject

section Transfer

variable {A : Type u} [Ring A]

/-- **Transfer of projectivity**: a left `A`-module is projective exactly when the corresponding
module over `SingleObj Aᵐᵒᵖ` is. -/
theorem projective_moduleCatEquivModCat_functor_obj_iff (M : ModuleCat.{v} A) :
    Projective ((moduleCatEquivModCat A).functor.obj M) ↔ Projective M :=
  (moduleCatEquivModCat A).map_projective_iff M

/-- **Transfer of exactness**: a short complex of left `A`-modules is exact exactly when the
corresponding short complex of modules over `SingleObj Aᵐᵒᵖ` is. -/
theorem exact_map_moduleCatEquivModCat_functor_iff (S : ShortComplex (ModuleCat.{v} A)) :
    (S.map (moduleCatEquivModCat A).functor).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful _

variable (A) in
/-- **The free module `Aⁿ` corresponds to the finite sum of `n` copies of `Hom(-, ∗)`.** -/
noncomputable def moduleCatEquivModCatFreeIso (n : ℕ) :
    ((moduleCatEquivModCat.{u} A).functor.obj (ModuleCat.of A (Fin n → A))).obj ≅
      ∐ fun _ : Fin n ↦ preadditiveYoneda.obj (SingleObj.star Aᵐᵒᵖ) :=
  have : HasFiniteBiproducts ((SingleObj Aᵐᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let Φ := (moduleCatEquivModCat.{u} A).functor ⋙ (additiveFunctor _ AddCommGrpCat.{u}).ι
  Φ.mapIso (ModuleCat.biproductIsoPi fun _ : Fin n ↦ ModuleCat.of A A).symm ≪≫
    Φ.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ (additiveFunctor _ _).ι.mapIso (moduleCatEquivModCatSelfIso A)) ≪≫
    biproduct.isoCoproduct _

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
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
    have := Module.Finite.iff_fg.2 (Module.FinitePresentation.fg_ker f hf)
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' A (LinearMap.ker f)
    have h₀ : ModuleCat.ofHom ((LinearMap.ker f).subtype ∘ₗ g) ≫ ModuleCat.ofHom f = 0 := by
      exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.mem_ker.1 (g x).property)
    have h : ((e m).inv ≫ Φ.map (ModuleCat.ofHom ((LinearMap.ker f).subtype ∘ₗ g)) ≫
        (e n).hom) ≫ (e n).inv ≫ Φ.map (ModuleCat.ofHom f) = 0 := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Φ.map_comp, h₀, Φ.map_zero, comp_zero]
    refine ⟨m, n, fun _ ↦ SingleObj.star Aᵐᵒᵖ, fun _ ↦ SingleObj.star Aᵐᵒᵖ, _, _, h,
      (epi_moduleCatEquivModCatFreeIso_inv_comp_iff (ModuleCat.ofHom f)).2 hf,
      (exact_moduleCatEquivModCatFreeIso_iff _ _ h₀ h).2 ?_⟩
    rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, LinearMap.range_comp,
      LinearMap.range_eq_top.2 hg, Submodule.map_top, Submodule.range_subtype]

end Transfer

end TauCeti
