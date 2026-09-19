/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# The sheaf of linear morphisms

For two sheaves of modules over a sheaf of rings, local linear morphisms form a sheaf of
sets. This is the gluing input for the dual sheaf: take the target to be the structure sheaf.
The construction works over any site and does not require commutativity of the rings.

We use Mathlib's `presheafHom` of the underlying additive presheaves and cut out its
subpresheaf of linear morphisms. Linearity is local because equality of sections of the
target sheaf can be checked on a covering sieve. Thus Mathlib's sheaf theorem for
`presheafHom` supplies the gluing, without reconstructing additive morphisms sectionwise.

The equivalences `linearHomObjEquiv` and `linearHomSectionsEquiv` identify local and global
sections with module-sheaf morphisms, and `linearHomObjEquiv_map_app` describes restriction.

This file constructs the underlying sheaf of sets; it does not equip it with a module
structure or identify it with a categorical internal Hom.
-/

public section

open CategoryTheory Opposite

noncomputable section

namespace TauCeti.SheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M N : SheafOfModules.{w'} R)

/-- The subpresheaf of additive local morphisms that commute with scalar multiplication. -/
private def linearHomSubfunctor : Subfunctor (presheafHom M.val.presheaf N.val.presheaf) where
  obj U := {φ | ∀ (V : Over U.unop) (r : R.obj.obj (op V.left)) (m : M.val.obj (op V.left)),
    φ.app (op V) (r • m) =
      (r • · : N.val.obj (op V.left) → N.val.obj (op V.left)) (φ.app (op V) m)}
  map f _ h V r m := h ((Over.map f.unop).obj V) r m

/-- Membership in the local linear-morphism presheaf means linearity at every object of the
slice site. -/
@[simp]
private theorem mem_linearHomSubfunctor {U : Cᵒᵖ}
    (φ : (presheafHom M.val.presheaf N.val.presheaf).obj U) :
    φ ∈ (linearHomSubfunctor M N).obj U ↔
      ∀ (V : Over U.unop) (r : R.obj.obj (op V.left)) (m : M.val.obj (op V.left)),
        φ.app (op V) (r • m) =
          (r • · : N.val.obj (op V.left) → N.val.obj (op V.left)) (φ.app (op V) m) := Iff.rfl

/-- Linearity of a local additive morphism can be checked on a covering sieve. -/
private theorem mem_linearHomSubfunctor_of_cover {U : Cᵒᵖ}
    (φ : (presheafHom M.val.presheaf N.val.presheaf).obj U)
    (S : Sieve U.unop) (hS : S ∈ J U.unop)
    (hφ : ∀ ⦃V⦄ (f : V ⟶ U.unop), S f →
      (presheafHom M.val.presheaf N.val.presheaf).map f.op φ ∈
        (linearHomSubfunctor M N).obj (op V)) :
    φ ∈ (linearHomSubfunctor M N).obj U := by
  dsimp only [presheafHom] at φ
  intro V r m
  have hN := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf J N.val.presheaf (forget _) N.isSheaf)
  apply (hN _ (J.pullback_stable V.hom hS)).isSeparatedFor.ext
  intro W f hf
  have hlin := hφ (f ≫ V.hom) hf (Over.mk (𝟙 W))
    (R.obj.map f.op r) (M.val.presheaf.map f.op m)
  -- Read the restricted morphism at the identity of the slice.
  have hmap (s : M.val.obj (op W)) := ConcreteCategory.congr_hom
    (presheafHom_map_app_op_mk_id (F := M.val.presheaf) (G := N.val.presheaf)
      (f ≫ V.hom) φ) s
  have hlin' := (hmap (R.obj.map f.op r • M.val.presheaf.map f.op m)).symm.trans <|
    hlin.trans (congrArg (fun s : N.val.obj (op W) => R.obj.map f.op r • s)
      (hmap (M.val.presheaf.map f.op m)))
  -- Naturality and semilinearity identify this local equality with the restriction
  -- of the desired equality on V.
  have hnat (s : M.val.obj (op V.left)) :
      φ.app (op (Over.mk (f ≫ V.hom))) (M.val.presheaf.map f.op s) =
        N.val.presheaf.map f.op (φ.app (op V) s) :=
    congrArg (fun g => g s) (φ.naturality (Over.homMk f : Over.mk (f ≫ V.hom) ⟶ V).op)
  exact (hnat (r • m)).symm.trans <|
    (congrArg (φ.app (op (Over.mk (f ≫ V.hom))))) (M.val.map_smul f.op r m) |>.trans <|
      hlin'.trans <| (congrArg (fun s : N.val.obj (op W) => R.obj.map f.op r • s) (hnat m)).trans
        (N.val.map_smul f.op r (φ.app (op V) m)).symm

/-- Local linear morphisms satisfy the sheaf condition. -/
private theorem isSheaf_linearHomSubfunctor :
    Presheaf.IsSheaf J (linearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply ((linearHomSubfunctor M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).1 (N.isSheaf.hom M.val.presheaf))).2
  intro U φ hφ
  exact mem_linearHomSubfunctor_of_cover M N φ _ hφ (fun _ _ hf => hf)

/-- The sheaf of sets of local linear morphisms between two sheaves of modules. -/
def linearHom : Sheaf J (Type (max u v w')) where
  obj := (linearHomSubfunctor M N).toFunctor
  property := isSheaf_linearHomSubfunctor M N

/-- Sections of the linear Hom sheaf over an object are precisely morphisms between the
restricted sheaves of modules. -/
def linearHomObjEquiv (U : C) :
    (linearHom M N).obj.obj (op U) ≃ (M.over U ⟶ N.over U) where
  toFun φ := ⟨PresheafOfModules.homMk φ.val (fun V => φ.property V.unop)⟩
  invFun φ := ⟨(PresheafOfModules.toPresheaf _).map φ.val,
    fun V r m => (φ.val.app (op V)).hom.map_smul r m⟩
  left_inv φ := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    rfl
  right_inv φ := by
    ext V m
    rfl

private theorem linearHomObjEquiv_app (U : C)
    (φ : (linearHom M N).obj.obj (op U)) (V : Over U) (m : M.val.obj (op V.left)) :
    ((linearHomObjEquiv M N U φ).val.app (op V)) m = φ.val.app (op V) m := by
  rfl

/-- Restriction of a Hom section restricts its component linear maps. -/
@[simp]
theorem linearHomObjEquiv_map_app {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (φ : (linearHom M N).obj.obj (op U)) (m : M.val.obj (op W)) :
    ((linearHomObjEquiv M N V ((linearHom M N).obj.map f.op φ)).val.app
      (op (Over.mk g))) m =
        ((linearHomObjEquiv M N U φ).val.app (op (Over.mk (g ≫ f)))) m := by
  rw [linearHomObjEquiv_app, linearHomObjEquiv_app]
  exact ConcreteCategory.congr_hom (presheafHom_map_app g f (g ≫ f) rfl φ.val) m

/-- Global sections of the linear Hom sheaf are morphisms of sheaves of modules. -/
def linearHomSectionsEquiv : (linearHom M N).obj.sections ≃ (M ⟶ N) where
  toFun s := ⟨PresheafOfModules.homMk
    (presheafHomSectionsEquiv M.val.presheaf N.val.presheaf
      ⟨fun U => (s.val U).val, fun f => congrArg Subtype.val (s.property f)⟩)
    (fun U => (s.val U).property (Over.mk (𝟙 U.unop)))⟩
  invFun φ :=
    ⟨fun U => (linearHomObjEquiv M N U.unop).symm (φ.over U.unop), by
      intro U V f
      apply Subtype.ext
      apply NatTrans.ext
      funext W
      ext m
      -- Subtype projection removes the linearity witness; the remaining map is presheaf Hom.
      exact ConcreteCategory.congr_hom
        (presheafHom_map_app W.unop.hom f.unop (W.unop.hom ≫ f.unop) rfl
          ((linearHomObjEquiv M N U.unop).symm (φ.over U.unop)).val) m⟩
  left_inv s := by
    apply Subtype.ext
    funext U
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let t : (presheafHom M.val.presheaf N.val.presheaf).sections :=
      ⟨fun U => (s.val U).val, fun f => congrArg Subtype.val (s.property f)⟩
    exact congrArg (fun z => (z.val U).app V m)
      ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).left_inv t)
  right_inv φ := by
    ext U m
    rfl

/-- The morphism associated to a global Hom section is read at the identity of each slice. -/
@[simp]
theorem linearHomSectionsEquiv_app (s : (linearHom M N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsEquiv M N s).val.app U) m =
      ((linearHomObjEquiv M N U.unop (s.val U)).val.app
        (op (Over.mk (𝟙 U.unop)))) m := by rfl

/-- The global Hom section defined by a morphism restricts to that morphism on each slice. -/
@[simp]
theorem linearHomObjEquiv_sectionsEquiv_symm (φ : M ⟶ N) (U : C) :
    linearHomObjEquiv M N U (((linearHomSectionsEquiv M N).symm φ).val (op U)) =
      φ.over U :=
  (linearHomObjEquiv M N U).apply_symm_apply (φ.over U)

end TauCeti.SheafOfModules
