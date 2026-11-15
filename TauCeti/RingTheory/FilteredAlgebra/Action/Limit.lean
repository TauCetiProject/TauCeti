/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Action.Algebra

/-!
# Algebra completion actions as limit actions

Compatible representations on the quotient algebras of a filtered algebra define
natural automorphisms of its quotient diagram. The canonical algebra-limit
comparison intertwines their limit actions with the existing action on the
concrete compatible-family completion. This identifies categorical coefficient
transport with an action on actual completed algebra elements, retaining products
and the scalar algebra structure.

The construction uses Mathlib's `AlgEquiv.toAlgebraIso`, `NatIso.ofComponents` and
`HasLimit.isoOfNatIso`. The concrete action is `TauCeti.AlgFiltration.completedAlgebraAction`.

Adapted from `Mei/RingTheory/FilteredAlgebra/LimitAction.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace TauCeti.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (F : AlgFiltration A) {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* ((A ⧸ F.ideal (k + 1)) ≃ₐ[R]
    (A ⧸ F.ideal (k + 1))))
  (hρ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : A ⧸ F.ideal (l + 1)),
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) (ρ l g x) =
      ρ k (G.map (homOfLE h).op g)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) x))

/-- A completed label acts by a natural automorphism of the quotient algebra diagram. -/
def quotientAction (g : completedGroup G) :
    F.quotientAlgebraDiagram (R := R) ≅ F.quotientAlgebraDiagram (R := R) :=
  NatIso.ofComponents (fun k => (ρ k.unop (CompletedGroup.projection k.unop g)).toAlgebraIso)
    (by
      intro k l f
      apply AlgCat.hom_ext
      apply AlgHom.ext
      intro x
      -- The categorical objects retain their diagram types after extensionality;
      -- identify their arrows with the concrete quotient maps to use compatibility.
      change ρ l.unop (CompletedGroup.projection l.unop g)
          (Ideal.Quotient.factor (F.antitone
            (Nat.add_le_add_right (leOfHom f.unop) 1)) x) =
        Ideal.Quotient.factor (F.antitone
          (Nat.add_le_add_right (leOfHom f.unop) 1))
            (ρ k.unop (CompletedGroup.projection k.unop g) x)
      simpa only [CompletedGroup.map_projection] using
        (hρ (leOfHom f.unop) (CompletedGroup.projection k.unop g) x).symm)

/-- The forward component is the prescribed finite algebra representation. -/
@[simp]
theorem quotientAction_hom_app (g : completedGroup G) (k : ℕᵒᵖ) :
    (F.quotientAction ρ hρ g).hom.app k =
      AlgCat.ofHom (ρ k.unop (CompletedGroup.projection k.unop g)).toAlgHom := (rfl)

/-- The inverse component uses the inverse finite algebra automorphism. -/
@[simp]
theorem quotientAction_inv_app (g : completedGroup G) (k : ℕᵒᵖ) :
    (F.quotientAction ρ hρ g).inv.app k =
      AlgCat.ofHom (ρ k.unop (CompletedGroup.projection k.unop g)).symm.toAlgHom := (rfl)

/-- The identity completed label acts identically on the quotient diagram. -/
@[simp]
theorem quotientAction_one : F.quotientAction ρ hρ 1 = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  simp
  rfl

/-- Label multiplication acts in function-composition order. -/
@[simp]
theorem quotientAction_mul (g h : completedGroup G) :
    F.quotientAction ρ hρ (g * h) =
      F.quotientAction ρ hρ h ≪≫ F.quotientAction ρ hρ g := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp
  rfl

/-- Inversion of a completed label inverts its quotient-diagram action. -/
@[simp]
theorem quotientAction_inv (g : completedGroup G) :
    F.quotientAction ρ hρ g⁻¹ = (F.quotientAction ρ hρ g).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp

/-- Taking the limit of the quotient action recovers the concrete algebra completion action. -/
theorem completedAlgebraAction_completionAlgebraIsoLimit (g : completedGroup G) :
    (F.completedAlgebraAction ρ hρ g).toAlgebraIso ≪≫ F.completionAlgebraIsoLimit =
      F.completionAlgebraIsoLimit ≪≫ HasLimit.isoOfNatIso (F.quotientAction ρ hρ g) := by
  apply Iso.ext
  apply limit.hom_ext
  intro k
  simp only [Iso.trans_hom, Category.assoc]
  -- Identify the diagram's objects with their concrete quotient algebras.
  erw [completionAlgebraIsoLimit_hom_π, HasLimit.isoOfNatIso_hom_π,
    completionAlgebraIsoLimit_hom_π_assoc]
  rw [quotientAction_hom_app, AlgEquiv.toAlgebraIso_hom]
  apply AlgCat.hom_ext
  -- Reconcile the categorical diagram objects with the concrete algebra carriers.
  erw [AlgCat.hom_comp, AlgCat.hom_comp]
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply]
  erw [AlgCat.hom_ofHom, AlgCat.hom_ofHom, AlgCat.hom_ofHom,
    F.projectionₐ_apply, F.projectionₐ_apply]
  exact F.projection_completedAlgebraAction ρ hρ g x k.unop

end TauCeti.AlgFiltration
