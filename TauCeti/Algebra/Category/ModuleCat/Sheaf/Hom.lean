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

Over an object `U`, a section is an additive morphism between the restrictions of the two
sheaves to the slice over `U`, whose components are linear over the restricted structure
sheaf. Restriction pulls such morphisms back along arrows. Linearity is local because
equality of target sections can be checked on a covering sieve, so compatible local linear
morphisms glue uniquely.

The resulting sheaf has local sections over `U` equivalent to morphisms between the
restricted module sheaves, and global sections equivalent to morphisms of the original
module sheaves. The declarations `linearHomObjEquiv`, `linearHomSectionsEquiv`, and
`linearHomObjEquiv_map_app` expose these identifications and their behavior under
restriction. They support dot notation directly, for example `M.linearHom N` and
`M.linearHomObjEquiv N U`.

## Sources

The construction builds on Mathlib's `presheafHom`. Its gluing proof uses the sheaf result
`Presheaf.IsSheaf.hom` together with the subfunctor criterion `Subfunctor.isSheaf_iff`.

This file constructs the underlying sheaf of sets; it does not equip it with a module
structure or identify it with a categorical internal Hom.
-/

public section

open CategoryTheory Opposite

noncomputable section

namespace TauCeti
namespace SheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M N : SheafOfModules.{w'} R)

/-- The subpresheaf of additive local morphisms that commute with scalar multiplication. -/
private def linearHomSubfunctor : Subfunctor (presheafHom M.val.presheaf N.val.presheaf) where
  obj U := {φ | ∀ (V : Over U.unop) (r : R.obj.obj (op V.left)) (m : M.val.obj (op V.left)),
    φ.app (op V) (r • m) =
      (r • · : N.val.obj (op V.left) → N.val.obj (op V.left)) (φ.app (op V) m)}
  map f _ h V r m := h ((Over.map f.unop).obj V) r m

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
    (Presheaf.isSheaf_comp_of_isSheaf J N.val.presheaf (CategoryTheory.forget _) N.isSheaf)
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

end SheafOfModules
end TauCeti

namespace SheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M N : SheafOfModules.{w'} R)

/-- The sheaf of sets of local linear morphisms between two sheaves of modules. -/
def linearHom : Sheaf J (Type (max u v w')) where
  obj := (TauCeti.SheafOfModules.linearHomSubfunctor M N).toFunctor
  property := TauCeti.SheafOfModules.isSheaf_linearHomSubfunctor M N

/-- Convert a linear Hom section over `U` to a morphism of the restricted module sheaves. -/
private def linearHomObjToFun (U : C) (φ : (linearHom M N).obj.obj (op U)) :
    M.over U ⟶ N.over U :=
  ⟨PresheafOfModules.homMk φ.val (fun V ↦ φ.property V.unop)⟩

/-- Convert a morphism of restricted module sheaves to its underlying linear Hom section. -/
private def linearHomObjInvFun (U : C) (φ : M.over U ⟶ N.over U) :
    (linearHom M N).obj.obj (op U) :=
  ⟨(PresheafOfModules.toPresheaf _).map φ.val,
    fun V r m ↦ (φ.val.app (op V)).hom.map_smul r m⟩

/-- The forward conversion evaluates by applying the original local morphism. -/
private theorem linearHomObjToFun_app (U : C)
    (φ : (linearHom M N).obj.obj (op U)) (V : Over U) (m : M.val.obj (op V.left)) :
    ((linearHomObjToFun M N U φ).val.app (op V)) m = φ.val.app (op V) m := by
  rfl

/-- The inverse conversion evaluates by applying the original restricted morphism. -/
private theorem linearHomObjInvFun_app (U : C) (φ : M.over U ⟶ N.over U)
    (V : Over U) (m : M.val.obj (op V.left)) :
    (linearHomObjInvFun M N U φ).val.app (op V) m = (φ.val.app (op V)) m := by
  rfl

/-- The two objectwise conversions cancel on every component. -/
private theorem linearHomObjInvToFun_app (U : C)
    (φ : (linearHom M N).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (m : (M.over U).val.obj V) :
    (linearHomObjInvFun M N U (linearHomObjToFun M N U φ)).val.app V m =
      φ.val.app V m := by
  rfl

/-- The two objectwise conversions cancel on every component in the other direction. -/
private theorem linearHomObjToInvFun_app (U : C) (φ : M.over U ⟶ N.over U)
    (V : (Over U)ᵒᵖ) (m : (M.over U).val.obj V) :
    (linearHomObjToFun M N U (linearHomObjInvFun M N U φ)).val.app V m =
      φ.val.app V m := by
  rfl

/-- Sections of the linear Hom sheaf over an object are precisely morphisms between the
restricted sheaves of modules.

Evaluate a section `s` on a slice object `V` using
`((linearHomObjEquiv M N U s).val.app (op V)) m`. Construct a section from a morphism
with `(linearHomObjEquiv M N U).symm`; its evaluation simplifies by
`Equiv.apply_symm_apply`, without unfolding the sheaf construction. -/
def linearHomObjEquiv (U : C) :
    (linearHom M N).obj.obj (op U) ≃ (M.over U ⟶ N.over U) where
  toFun := linearHomObjToFun M N U
  invFun := linearHomObjInvFun M N U
  left_inv φ := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    exact linearHomObjInvToFun_app M N U φ V m
  right_inv φ := by
    ext V m
    exact linearHomObjToInvFun_app M N U φ V m

private theorem linearHomObjEquiv_app (U : C)
    (φ : (linearHom M N).obj.obj (op U)) (V : Over U) (m : M.val.obj (op V.left)) :
    ((linearHomObjEquiv M N U φ).val.app (op V)) m = φ.val.app (op V) m := by
  exact linearHomObjToFun_app M N U φ V m

/-- Restriction of a Hom section restricts its component linear maps. -/
@[simp]
theorem linearHomObjEquiv_map_app {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (φ : (linearHom M N).obj.obj (op U)) (m : M.val.obj (op W)) :
    ((linearHomObjEquiv M N V ((linearHom M N).obj.map f.op φ)).val.app
      (op (Over.mk g))) m =
        ((linearHomObjEquiv M N U φ).val.app (op (Over.mk (g ≫ f)))) m := by
  rw [linearHomObjEquiv_app, linearHomObjEquiv_app]
  exact ConcreteCategory.congr_hom (presheafHom_map_app g f (g ≫ f) rfl φ.val) m

/-- Convert a global linear Hom section to its morphism of module sheaves. -/
private def linearHomSectionsToFun (s : (linearHom M N).obj.sections) : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    (presheafHomSectionsEquiv M.val.presheaf N.val.presheaf
      ⟨fun U ↦ (s.val U).val, fun f ↦ congrArg Subtype.val (s.property f)⟩)
    (fun U ↦ (s.val U).property (Over.mk (𝟙 U.unop)))⟩

/-- The morphism converted from a global section evaluates at the identity slice. -/
private theorem linearHomSectionsToFun_app (s : (linearHom M N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsToFun M N s).val.app U) m =
      (s.val U).val.app (op (Over.mk (𝟙 U.unop))) m := by
  rfl

/-- Global conversion agrees componentwise with the objectwise conversion. -/
private theorem linearHomSectionsToObjFun_app (s : (linearHom M N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsToFun M N s).val.app U) m =
      ((linearHomObjToFun M N U.unop (s.val U)).val.app
        (op (Over.mk (𝟙 U.unop)))) m := by
  rfl

/-- Global sections of the linear Hom sheaf are morphisms of sheaves of modules. -/
def linearHomSectionsEquiv : (linearHom M N).obj.sections ≃ (M ⟶ N) where
  toFun := linearHomSectionsToFun M N
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
    -- Forget the module structure and use the inverse law for additive presheaf morphisms.
    exact congrArg (fun ψ => ψ.app U m)
      ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).right_inv
        ((PresheafOfModules.toPresheaf _).map φ.val))

/-- The morphism associated to a global Hom section is read at the identity of each slice. -/
@[simp]
theorem linearHomSectionsEquiv_app (s : (linearHom M N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsEquiv M N s).val.app U) m =
      ((linearHomObjEquiv M N U.unop (s.val U)).val.app
        (op (Over.mk (𝟙 U.unop)))) m := by
  exact linearHomSectionsToObjFun_app M N s U m

/-- The global Hom section associated to a morphism restricts to that morphism on each slice. -/
@[simp]
theorem linearHomSectionsEquiv_symm_apply (φ : M ⟶ N) (U : Cᵒᵖ) :
    ((linearHomSectionsEquiv M N).symm φ).val U =
      (linearHomObjEquiv M N U.unop).symm (φ.over U.unop) := by rfl

end SheafOfModules
