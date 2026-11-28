/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.NatTrans

/-!
# Simplicial homotopies of nerves

Building on `CategoryTheory.NatTrans.nerveHomotopy` in
`TauCeti.AlgebraicTopology.SimplicialSet.Nerve.NatTrans`, this file adds the universe-polymorphic
cylinder action `CategoryTheory.NatTrans.mapNerveCylinderObj`, left and right whiskering lemmas
(`CategoryTheory.NatTrans.whiskerLeft_nerveHomotopy_h`,
`CategoryTheory.NatTrans.whiskerRight_nerveHomotopy_h`), and contracting homotopies on the nerve of
a category with an initial or terminal object (`CategoryTheory.Limits.IsInitial.nerveHomotopy`,
`CategoryTheory.Limits.IsTerminal.nerveHomotopy`). Weak contractibility of `nerve C` from these
homotopies is in `TauCeti.AlgebraicTopology.SimplicialSet.Nerve.WeaklyContractible`, and
cross-universe topological homotopies are in
`TauCeti.AlgebraicTopology.SimplicialSet.Nerve.ClassifyingSpace`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter I, §1.
-/

public section

universe v u v₁ u₁ v₂ u₂ v₃ u₃
open CategoryTheory MonoidalCategory Opposite Simplicial

namespace CategoryTheory
namespace NatTrans
section
variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
  {D : Type u₃} [Category.{v₃} D]
/-- Universe-polymorphic action of a natural transformation `η : F₀ ⟶ F₁` on a cylinder simplex
`(σ, β)` of `nerve C` paired with `β : n.unop ⟶ ⦋1⦌`. -/
def mapNerveCylinderObj {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) {n : SimplexCategoryᵒᵖ}
    (σ : ComposableArrows C n.unop.len) (β : n.unop ⟶ ⦋1⦌) : ComposableArrows D n.unop.len :=
  σ.prod' ((nerve (C ⥤ D)).map β.op (ComposableArrows.mk₁ η)) ⋙ evaluationUncurried C D
lemma mapNerveCylinderObj_def {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) {n : SimplexCategoryᵒᵖ}
    (σ : ComposableArrows C n.unop.len) (β : n.unop ⟶ ⦋1⦌) :
    η.mapNerveCylinderObj σ β =
      σ.prod' ((nerve (C ⥤ D)).map β.op (ComposableArrows.mk₁ η)) ⋙ evaluationUncurried C D := (rfl)

@[simp] lemma whiskerLeft_mapNerveCylinderObj (K : B ⥤ C) {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁)
    {n : SimplexCategoryᵒᵖ} (σ : ComposableArrows B n.unop.len) (β : n.unop ⟶ ⦋1⦌) :
    (Functor.whiskerLeft K η).mapNerveCylinderObj σ β =
      η.mapNerveCylinderObj ((K.mapComposableArrows n.unop.len).obj σ) β := by
  rcases n with ⟨m⟩; induction m using SimplexCategory.rec with | _ m =>
  rw [mapNerveCylinderObj_def, mapNerveCylinderObj_def, ← Functor.whiskeringLeft_obj_map,
    nerve.map_mk₁]
  -- `evaluationUncurried` on `(σ, (K.mapComposableArrows _ ≫ _))` and on `((σ ⋙ K), _)` agree
  -- definitionally on both objects and morphisms.
  exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl

@[simp] lemma whiskerRight_mapNerveCylinderObj {F₀ F₁ : B ⥤ C} (η : F₀ ⟶ F₁) (G : C ⥤ D)
    {n : SimplexCategoryᵒᵖ} (σ : ComposableArrows B n.unop.len) (β : n.unop ⟶ ⦋1⦌) :
    (Functor.whiskerRight η G).mapNerveCylinderObj σ β =
      (G.mapComposableArrows n.unop.len).obj (η.mapNerveCylinderObj σ β) := by
  rcases n with ⟨m⟩; induction m using SimplexCategory.rec with | _ m =>
  rw [mapNerveCylinderObj_def, mapNerveCylinderObj_def, ← Functor.whiskeringRight_obj_map,
    nerve.map_mk₁]
  exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (G.map_comp _ _).symm
end

section
variable {B C D E : Type u} [Category.{v} B] [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- `η.nerveHomotopy.h` agrees with the universe-polymorphic `mapNerveCylinderObj` action. -/
lemma nerveHomotopy_h_app_eq_mapNerveCylinderObj {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁)
    (n : SimplexCategoryᵒᵖ) (p : (nerve C ⊗ Δ[1] : SSet.{max u v}).obj n) :
    η.nerveHomotopy.h.app n p = η.mapNerveCylinderObj p.1 (SSet.stdSimplex.objEquiv p.2) := by
  rw [nerveHomotopy_h_app]
  dsimp only [mapNerveCylinderObj]
  rcases n with ⟨m⟩; induction m using SimplexCategory.rec with | _ m =>
  refine Functor.hext (fun _ ↦ rfl) fun i j g ↦ heq_of_eq ?_
  dsimp [evaluationUncurried, Functor.uncurry]
  exact (((ComposableArrows.mk₁ η).map (homOfLE ((SSet.stdSimplex.asOrderHom p.2).monotone
    (leOfHom g)))).naturality (p.1.map g)).symm

@[simp] lemma whiskerLeft_nerveHomotopy_h (K : B ⥤ C) {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    (Functor.whiskerLeft K η).nerveHomotopy.h = nerveMap K ▷ Δ[1] ≫ η.nerveHomotopy.h := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun p ↦ ?_)
  simp only [nerveHomotopy_h_app_eq_mapNerveCylinderObj, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  exact whiskerLeft_mapNerveCylinderObj K η p.1 (SSet.stdSimplex.objEquiv p.2)

@[simp] lemma whiskerRight_nerveHomotopy_h {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (G : D ⥤ E) :
    (Functor.whiskerRight η G).nerveHomotopy.h = η.nerveHomotopy.h ≫ nerveMap G := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun p ↦ ?_)
  simp only [nerveHomotopy_h_app_eq_mapNerveCylinderObj, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  exact whiskerRight_mapNerveCylinderObj η G p.1 (SSet.stdSimplex.objEquiv p.2)
end
end NatTrans

namespace Limits
variable {C : Type u} [Category.{v} C]
/-- An initial object `x : C` induces a simplicial homotopy from `SSet.const` at `x` to
`𝟙 (nerve C)`. -/
noncomputable def IsInitial.nerveHomotopy {x : C} (hx : IsInitial x) :
    SSet.Homotopy (SSet.const (nerveEquiv.symm x)) (𝟙 (nerve C)) :=
  let η : (Functor.const C).obj x ⟶ 𝟭 C :=
    { app := fun c ↦ hx.to c, naturality := fun _ _ _ ↦ hx.hom_ext _ _ }
  SSet.Homotopy.mk' η.nerveHomotopy.h
    (by rw [η.nerveHomotopy.h₀, nerveMap_const])
    (by rw [η.nerveHomotopy.h₁, nerveMap_id])
/-- The homotopy morphism of `IsInitial.nerveHomotopy` agrees with that of the natural
transformation `{ app := hx.to }`. -/
@[simp] lemma IsInitial.nerveHomotopy_h {x : C} (hx : IsInitial x) :
    hx.nerveHomotopy.h =
      ({ app := fun c ↦ hx.to c, naturality := fun _ _ _ ↦ hx.hom_ext _ _ } :
        (Functor.const C).obj x ⟶ 𝟭 C).nerveHomotopy.h := (rfl)
/-- A terminal object `x : C` induces a simplicial homotopy from `𝟙 (nerve C)` to `SSet.const` at
`x`. -/
noncomputable def IsTerminal.nerveHomotopy {x : C} (hx : IsTerminal x) :
    SSet.Homotopy (𝟙 (nerve C)) (SSet.const (nerveEquiv.symm x)) :=
  let η : 𝟭 C ⟶ (Functor.const C).obj x :=
    { app := fun c ↦ hx.from c, naturality := fun _ _ _ ↦ hx.hom_ext _ _ }
  SSet.Homotopy.mk' η.nerveHomotopy.h
    (by rw [η.nerveHomotopy.h₀, nerveMap_id])
    (by rw [η.nerveHomotopy.h₁, nerveMap_const])
/-- The homotopy morphism of `IsTerminal.nerveHomotopy` agrees with that of the natural
transformation `{ app := hx.from }`. -/
@[simp] lemma IsTerminal.nerveHomotopy_h {x : C} (hx : IsTerminal x) :
    hx.nerveHomotopy.h =
      ({ app := fun c ↦ hx.from c, naturality := fun _ _ _ ↦ hx.hom_ext _ _ } :
        𝟭 C ⟶ (Functor.const C).obj x).nerveHomotopy.h := (rfl)
end Limits
end CategoryTheory
