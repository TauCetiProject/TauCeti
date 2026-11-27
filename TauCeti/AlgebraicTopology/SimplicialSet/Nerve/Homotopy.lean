/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Simplicial homotopies of nerves

A natural transformation `η : F₀ ⟶ F₁` between functors `C ⥤ D` induces a simplicial map
`nerve C ⊗ Δ[1] ⟶ nerve D` whose endpoints are `nerveMap F₀` and `nerveMap F₁`
(`CategoryTheory.NatTrans.nerveHomotopy`), with vertical edge track `η.app c` and left/right
whiskering compatibilities (backed by the universe-polymorphic simplex action
`CategoryTheory.NatTrans.mapNerveCylinderObj`). In particular, an initial or terminal object of `C`
gives a contracting homotopy on `nerve C` (`CategoryTheory.Limits.IsInitial.nerveHomotopy`,
`CategoryTheory.Limits.IsTerminal.nerveHomotopy`); weak contractibility of `nerve C` from these
homotopies is in `TauCeti.AlgebraicTopology.SimplicialSet.Nerve.WeaklyContractible`. These
simplicial homotopies realize via `TauCeti.AlgebraicTopology.SimplicialSet.Realization.Prism` to
topological homotopies and contractibility of classifying spaces in
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
private def nerveHomotopyMap {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun p ↦ η.mapNerveCylinderObj p.1 (SSet.stdSimplex.objEquiv p.2)
  naturality _ _ _ := rfl
/-- A natural transformation `η : F₀ ⟶ F₁` induces a simplicial homotopy from `nerveMap F₀` to
`nerveMap F₁`. -/
noncomputable def nerveHomotopy {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    SSet.Homotopy (nerveMap F₀) (nerveMap F₁) :=
  SSet.Homotopy.mk' (nerveHomotopyMap η)
    (by ext ⟨m⟩ σ : 4; induction m using SimplexCategory.rec with | _ m =>
        exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Category.comp_id _))
    (by ext ⟨m⟩ σ : 4; induction m using SimplexCategory.rec with | _ m =>
        exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Category.comp_id _))
lemma nerveHomotopy_h_app {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (n : SimplexCategoryᵒᵖ)
    (p : (nerve C ⊗ Δ[1]).obj n) :
    η.nerveHomotopy.h.app n p = η.mapNerveCylinderObj p.1 (SSet.stdSimplex.objEquiv p.2) := (rfl)
@[simp] lemma nerveHomotopy_h_verticalEdge {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (c : C) :
    dsimp% η.nerveHomotopy.h.app (op ⦋1⦌)
        (SSet.verticalEdge (X := nerve C) (nerveEquiv.symm c)) =
      ComposableArrows.mk₁ (η.app c) := by
  let v : (nerve C) _⦋0⦌ := nerveEquiv.symm c
  have h₁ : (SSet.verticalEdge v).1 = ComposableArrows.mk₁ (𝟙 c) :=
    (SSet.verticalEdge_fst v).trans (nerve.σ_zero_nerveEquiv_symm c)
  let η₁ : (nerve (C ⥤ D)) _⦋1⦌ := ComposableArrows.mk₁ η
  have h₂ : (nerve (C ⥤ D)).map (SSet.stdSimplex.objEquiv (SSet.verticalEdge v).2).op η₁ = η₁ := by
    rw [SSet.objEquiv_verticalEdge_snd, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
    exact types_id_apply _ _
  refine ((nerveHomotopy_h_app η (op ⦋1⦌) (SSet.verticalEdge v)).trans
    (η.mapNerveCylinderObj_def _ _)).trans ((congrArg (· ⋙ evaluationUncurried C D)
      (congrArg₂ Functor.prod' h₁ h₂)).trans (ComposableArrows.ext₁ rfl rfl ?_))
  dsimp [η₁, evaluationUncurried, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
    ComposableArrows.Mk₁.map, ComposableArrows.hom]; simp
@[simp] lemma whiskerLeft_nerveHomotopy_h (K : B ⥤ C) {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    (Functor.whiskerLeft K η).nerveHomotopy.h = nerveMap K ▷ Δ[1] ≫ η.nerveHomotopy.h := by
  ext n p : 4
  exact whiskerLeft_mapNerveCylinderObj K η p.1 (SSet.stdSimplex.objEquiv p.2)
@[simp] lemma whiskerRight_nerveHomotopy_h {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (G : D ⥤ E) :
    (Functor.whiskerRight η G).nerveHomotopy.h = η.nerveHomotopy.h ≫ nerveMap G := by
  ext n p : 4
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
