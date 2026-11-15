/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.Intertwiner.Basic
public import TauCeti.CategoryTheory.Grothendieck.SingleObj

/-!
# Intertwiners of one-object label systems

An equivariant map of coefficient diagrams, together with a map of group diagrams
over a change of base, gives an `ActionIntertwiner` of their one-object
representations. Its coefficient component at a total object is the original
comparison at that object’s base, retaining both restriction and label actions.
It applies in particular to filtered representations with different cutoff moduli.

The construction uses `Functor.singleObjRepresentation` and
`ActionIntertwiner`, so their section-limit and label-equivariance laws apply
without choosing new completion carriers.

## Attribution

Adapted from `Mei/CategoryTheory/Grothendieck/Intertwiner/SingleObj.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ w u v

namespace CategoryTheory.Functor

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {V : Type u} [Category.{v} V]
  {F : D ⥤ GrpCat.{w}} {F' : E ⥤ GrpCat.{w}}
  {X : D ⥤ V} {X' : E ⥤ V} (G : E ⥤ D) (φ : G ⋙ F ⟶ F')

variable (ρ : ∀ d, F.obj d →* Aut (X.obj d))
  (σ : ∀ e, F'.obj e →* Aut (X'.obj e))
  (hρ : ∀ {d e : D} (f : d ⟶ e) (g : F.obj d),
    (ρ d g).asIso.hom ≫ X.map f = X.map f ≫ (ρ e (F.map f g)).asIso.hom)
  (hσ : ∀ {d e : E} (f : d ⟶ e) (g : F'.obj d),
    (σ d g).asIso.hom ≫ X'.map f = X'.map f ≫ (σ e (F'.map f g)).asIso.hom)
  (ψ : G ⋙ X ⟶ X')
  (hequiv : ∀ e (g : F.obj (G.obj e)),
    (ρ (G.obj e) g).asIso.hom ≫ ψ.app e =
      ψ.app e ≫ (σ e (φ.app e g)).asIso.hom)

/-- Equivariant coefficient maps define an intertwiner of the represented
one-object label systems, over an arbitrary change of base. -/
def singleObjActionIntertwiner :
    TauCeti.ActionIntertwiner G (F.singleObjRepresentation X ρ hρ)
      (F'.singleObjRepresentation X' σ hσ) where
  labelMap := whiskerRight φ (forget₂ GrpCat MonCat ⋙ MonCat.toCat)
  coefficient :=
    { app := fun a => ψ.app a.base
      naturality := by
        intro a b f
        simp only [comp_map, singleObjFiber_map_whiskerRight, singleObjFiber_pre,
          Grothendieck.pre_map_base, Grothendieck.pre_obj_base,
          Grothendieck.map_map_base]
        let g := (G ⋙ F).singleObjFiber f
        calc
          (X.map (G.map f.base) ≫ (ρ (G.obj b.base) g).asIso.hom) ≫ ψ.app b.base =
              X.map (G.map f.base) ≫ ψ.app b.base ≫
                (σ b.base (φ.app b.base g)).asIso.hom :=
            (Category.assoc _ _ _).trans
              (congrArg (X.map (G.map f.base) ≫ ·) (hequiv b.base g))
          _ = ψ.app a.base ≫ X'.map f.base ≫ (σ b.base (φ.app b.base g)).asIso.hom := by
            simpa only [Functor.comp_map, Category.assoc] using
              congrArg (· ≫ (σ b.base (φ.app b.base g)).asIso.hom) (ψ.naturality f.base) }

/-- The label comparison is induced by the original natural map of groups. -/
@[simp]
theorem singleObjActionIntertwiner_labelMap :
    (singleObjActionIntertwiner G φ ρ σ hρ hσ ψ hequiv).labelMap =
      whiskerRight φ (forget₂ GrpCat MonCat ⋙ MonCat.toCat) := (rfl)

/-- The represented coefficient comparison has exactly the original components. -/
@[simp]
theorem singleObjActionIntertwiner_coefficient_app
    (a : Grothendieck (G ⋙ (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat))) :
    (singleObjActionIntertwiner G φ ρ σ hρ hσ ψ hequiv).coefficient.app a =
      ψ.app a.base := (rfl)

/-- Along identity transport, the section comparison has the original coefficient
components. In particular its limit map compares the original coefficient towers. -/
theorem singleObjActionIntertwiner_sectionComparison_app (e : E) :
    ((singleObjActionIntertwiner G φ ρ σ hρ hσ ψ hequiv).sectionComparison
      F.singleObjSection.toSection).app e = ψ.app e := by
  rw [TauCeti.ActionIntertwiner.sectionComparison_app]
  -- Pullback of the identity-transport section has the same total object;
  -- reduce its strict-section wrappers to express the identifying arrow as an identity.
  change (F.singleObjRepresentation X ρ hρ).map
      (𝟙 (F.singleObjSection.toFunctor.obj (G.obj e))) ≫ ψ.app e = ψ.app e
  rw [Functor.map_id, Category.id_comp]

end CategoryTheory.Functor
