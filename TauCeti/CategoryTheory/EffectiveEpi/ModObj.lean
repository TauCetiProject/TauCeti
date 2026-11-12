/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.EffectiveEpi.Descent
public import TauCeti.CategoryTheory.Monoidal.Mod.Faithful

/-!
# Descent of actions and pseudo-torsors along effective epimorphisms

Let `p : S' ⟶ S` be a morphism in a category with pullbacks, all of whose base changes are
effective epimorphisms, and let `S'' = S' ×_S S'`. An action over `S` of a monoid object `G` over
`S`, such as a constant finite group or a group scheme, on an object `X` over `S` is an action in
the cartesian monoidal category `Over S`, whose product is the fibre product over `S`. For `X` over
`S` write `X' = X ×_S S'`, the image of `X` under the base change functor `Over.pullback p`; then
`G'` acts on `X'` by the base change of the action (`CategoryTheory.Functor.modObjObj`).

This file descends actions on objects which have already been descended. Let `G` be a monoid
object and `X` an object over `S`, and suppose that `G'` acts on `X'` over `S'`. If the action
morphism `G' ×_{S'} X' ⟶ X'` satisfies the descent condition of `TauCeti.descendHom`, namely that
its two pullbacks to `S''` agree, then it descends to a morphism `G ×_S X ⟶ X` over `S`. This is
the action morphism of the unique action of `G` on `X` whose base change is the given action.
Equivariant morphisms satisfying the descent condition descend to equivariant morphisms.

Base change along `p` reflects isomorphisms (`TauCeti.reflectsIsomorphisms_pullback`), so the
pseudo-torsor condition descends as well: the morphism `G ×_S X ⟶ X ×_S X`,
`(g, x) ↦ (g • x, x)`, of the descended action is an isomorphism exactly when that of the given
action is.

The base change functor is faithful and monoidal, so the action axioms on `X` follow from those on
`X'` (`CategoryTheory.Functor.modObjOfFaithful`); descent of morphisms supplies the action
morphism itself. For schemes, Mathlib shows that a flat surjective morphism which is
quasi-compact, or locally of finite presentation, is an effective epimorphism, and that these
properties are stable under base change (`Mathlib.AlgebraicGeometry.Sites.Fpqc`), so the results
apply to fpqc and fppf descent of actions of group schemes and of finite groups.

## Main definitions

* `TauCeti.descendModObj`: the action of `G` on `X` descended from an action of `G ×_S S'` on
  `X ×_S S'` whose action morphism satisfies the descent condition.

## Main statements

* `TauCeti.modObjObj_descendModObj`: the base change of the descended action is the given one.
* `TauCeti.eq_descendModObj`: uniqueness of the descended action.
* `TauCeti.isModHom_descendHom`: an equivariant morphism satisfying the descent condition descends
  to an equivariant morphism.
* `TauCeti.isIso_lift_smul_snd_descendModObj_iff`: the descended action satisfies the
  pseudo-torsor condition exactly when the given one does.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

namespace TauCeti

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)
  [∀ {Z : C} (g : Z ⟶ S), EffectiveEpi (pullback.fst g p)]
  (G : Over S) [MonObj G]

section ModObj

variable (X : Over S) [ModObj ((Over.pullback p).obj G) ((Over.pullback p).obj X)]

/-- **Descent of an action.** Let `G` be a monoid object and `X` an object over `S` such that
`G ×_S S'` acts on `X ×_S S'` over `S'`. If the action morphism satisfies the descent condition of
`TauCeti.descendHom` (its two pullbacks to `S' ×_S S'` agree), then it descends to an action of `G`
on `X` over `S` (`modObjObj_descendModObj`). -/
noncomputable abbrev descendModObj
    (h_smul : pullback.mapSnd (G ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) G X ≫
          γ[(Over.pullback p).obj G,(Over.pullback p).obj X]).left ≫ pullback.fst X.hom p =
      pullback.mapSnd (G ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) G X ≫
          γ[(Over.pullback p).obj G,(Over.pullback p).obj X]).left ≫ pullback.fst X.hom p) :
    ModObj G X :=
  (Over.pullback p).modObjOfFaithful G X (descendHom p _ h_smul)
    (pullback_map_descendHom p _ h_smul)

variable
    {h_smul : pullback.mapSnd (G ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) G X ≫
          γ[(Over.pullback p).obj G,(Over.pullback p).obj X]).left ≫ pullback.fst X.hom p =
      pullback.mapSnd (G ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) G X ≫
          γ[(Over.pullback p).obj G,(Over.pullback p).obj X]).left ≫ pullback.fst X.hom p}

/-- **Effectiveness of descent of actions.** The base change of the descended action is the given
one. -/
theorem modObjObj_descendModObj :
    letI := descendModObj p G X h_smul
    (Over.pullback p).modObjObj G X =
      ‹ModObj ((Over.pullback p).obj G) ((Over.pullback p).obj X)› :=
  (Over.pullback p).modObjObj_modObjOfFaithful G X _ _

/-- **Uniqueness of descended actions.** An action of `G` on `X` whose base change is the given
action is the descended action. -/
theorem eq_descendModObj (h : ModObj G X)
    (e : (Over.pullback p).modObjObj G X =
      ‹ModObj ((Over.pullback p).obj G) ((Over.pullback p).obj X)›) :
    h = descendModObj p G X h_smul :=
  (Over.pullback p).modObjObj_injective G X <| e.trans (modObjObj_descendModObj p G X).symm

/-- **Descent of the pseudo-torsor condition.** The morphism `G ×_S X ⟶ X ×_S X`,
`(g, x) ↦ (g • x, x)`, of the descended action is an isomorphism if and only if that of the given
action of `G ×_S S'` on `X ×_S S'` is. In particular, if `G ×_S S'` acts on `X ×_S S'` as a
pseudo-torsor, so does `G` on `X`. -/
theorem isIso_lift_smul_snd_descendModObj_iff :
    letI := descendModObj p G X h_smul
    IsIso (lift γ[G,X] (snd G X)) ↔
      IsIso (lift γ[(Over.pullback p).obj G,(Over.pullback p).obj X]
        (snd ((Over.pullback p).obj G) ((Over.pullback p).obj X))) := by
  let := descendModObj p G X h_smul
  rw [← (Over.pullback p).isIso_lift_smul_snd_modObjObj_iff G X, modObjObj_descendModObj]

end ModObj

/-- **Descent of equivariant morphisms.** Let `G` act on `X` and `Y` over `S`. A morphism
`φ : X ×_S S' ⟶ Y ×_S S'` which is equivariant for the base-changed actions of `G ×_S S'` and whose
two pullbacks to `S' ×_S S'` agree descends to an equivariant morphism `X ⟶ Y`. -/
theorem isModHom_descendHom {X Y : Over S} [ModObj G X] [ModObj G Y]
    (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (hφ : letI := (Over.pullback p).modObjObj G X
      letI := (Over.pullback p).modObjObj G Y
      IsModHom ((Over.pullback p).obj G) φ)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    IsModHom G (descendHom p φ h) := by
  rw [← (Over.pullback p).isModHom_map_iff, pullback_map_descendHom]
  exact hφ

end TauCeti
