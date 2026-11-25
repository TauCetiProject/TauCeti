/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Shift.Induced

/-!
# The shift on the idempotent completion

A shift on a category `C` by an additive monoid `A` induces a shift on its idempotent completion
`Karoubi C`: the shift by `a` sends an object `(X, e)` to `(X⟦a⟧, e⟦a⟧')` and a morphism `f` to
`f⟦a⟧'`, that is, it is the extension `(functorExtension₂ C C).obj (shiftFunctor C a)` of the shift
functor of `C`. The structure isomorphisms of the shift are determined by those of `C`, since the
restriction of functors along `toKaroubi C` is fully faithful (`Karoubi C` is idempotent
complete); this is Mathlib's `HasShift.induced`. With this shift the embedding `toKaroubi C`
commutes with the shifts, and its comparison isomorphisms have identity underlying morphisms.

When `C` is preadditive and its shift functors are additive, so are the shift functors of
`Karoubi C`. This is the shift used to make the idempotent completion of a pretriangulated
category pretriangulated (`TauCeti/CategoryTheory/Triangulated/Karoubi.lean`).

## Main definitions

* The instance `HasShift (Karoubi C) A` induced by a shift on `C`.
* The instance `(toKaroubi C).CommShift A`.

## Main results

* `CategoryTheory.Idempotents.Karoubi.shiftFunctor_obj_X`, `shiftFunctor_obj_p` and
  `shiftFunctor_map_f`: the shift acts on underlying objects, idempotents and morphisms by the
  shift of `C`.
* `CategoryTheory.Idempotents.Karoubi.shiftFunctorZero_hom_app_f` and
  `shiftFunctorAdd_hom_app_f` (with their `inv` versions): the structure isomorphisms of the shift
  are cut down from those of `C` by the idempotents.
* The instances `((functorExtension₁ C D).obj F).Additive` and
  `((functorExtension₂ C D).obj F).Additive` for an additive functor `F`, and hence additivity of
  the shift functors of `Karoubi C`.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, J. Algebra
  236 (2001), Section 1.
-/

public section

namespace CategoryTheory.Idempotents

open Category CategoryTheory.Functor

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Additive

variable [Preadditive C] [Preadditive D]

/-- The extension to `Karoubi C` of an additive functor `C ⥤ Karoubi D` is additive. -/
instance (F : C ⥤ Karoubi D) [F.Additive] : ((functorExtension₁ C D).obj F).Additive where
  map_add {_ _ f g} := by
    ext
    -- The extension applies `F.map` to underlying morphisms, and sums of morphisms of
    -- `Karoubi C` are sums of underlying morphisms, both definitionally.
    exact (congr_arg Karoubi.Hom.f (F.map_add (f := f.f) (g := g.f)) :)

/-- The extension to the idempotent completions of an additive functor `C ⥤ D` is additive. -/
instance (F : C ⥤ D) [F.Additive] : ((functorExtension₂ C D).obj F).Additive :=
  inferInstanceAs (((functorExtension₁ C D).obj (F ⋙ toKaroubi D)).Additive)

end Additive

variable (C) (A : Type w) [AddMonoid A] [HasShift C A]

namespace Karoubi

/-- The shift on the idempotent completion induced by a shift on `C`: the shift by `a` is the
extension of the shift functor `shiftFunctor C a` to `Karoubi C`. -/
noncomputable instance instHasShift : HasShift (Karoubi C) A :=
  HasShift.induced (toKaroubi C) A (fun a ↦ (functorExtension₂ C C).obj (shiftFunctor C a))
    (fun a ↦ (functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app (shiftFunctor C a))

/-- The embedding `toKaroubi C` commutes with the shifts. -/
noncomputable instance instCommShiftToKaroubi : (toKaroubi C).CommShift A :=
  Functor.CommShift.ofInduced (toKaroubi C) A _ _

variable {C A}

@[simp]
theorem shiftFunctor_obj_X (P : Karoubi C) (a : A) :
    ((shiftFunctor (Karoubi C) a).obj P).X = (shiftFunctor C a).obj P.X :=
  (rfl)

@[simp]
theorem shiftFunctor_obj_p (P : Karoubi C) (a : A) :
    ((shiftFunctor (Karoubi C) a).obj P).p = (shiftFunctor C a).map P.p :=
  (rfl)

@[simp]
theorem shiftFunctor_map_f {P Q : Karoubi C} (f : P ⟶ Q) (a : A) :
    ((shiftFunctor (Karoubi C) a).map f).f = (shiftFunctor C a).map f.f :=
  (rfl)

/-- The shift functors of `Karoubi C` are additive when those of `C` are. -/
instance [Preadditive C] (a : A) [(shiftFunctor C a).Additive] :
    (shiftFunctor (Karoubi C) a).Additive :=
  inferInstanceAs (((functorExtension₂ C C).obj (shiftFunctor C a)).Additive)

@[simp]
theorem toKaroubi_commShiftIso_hom_app_f (X : C) (a : A) :
    (((toKaroubi C).commShiftIso a).hom.app X).f = 𝟙 _ :=
  (rfl)

@[simp]
theorem toKaroubi_commShiftIso_inv_app_f (X : C) (a : A) :
    (((toKaroubi C).commShiftIso a).inv.app X).f = 𝟙 _ :=
  (rfl)

/- The components of the structure isomorphisms of the shift at objects of `C`, viewed in
`Karoubi C` through the coercion (which is the form `natTrans_eq` produces), read off from
Mathlib's description of an induced shift, which is stated at `(toKaroubi C).obj X`. In each proof
the coercion of `X` is replaced by `(toKaroubi C).obj X`, which it is by definition, and the
comparison isomorphisms of the induced shift are left as `_`, to be found by unification.
Their components have identity underlying morphisms only up to unfolding, on objects that are
not syntactically those of the neighbouring morphisms, so `id_comp` and `comp_id` are applied
with `exact` (which unifies up to unfolding) rather than by `simp`. -/

private theorem shiftFunctorZero_hom_app_coe_f (X : C) :
    ((shiftFunctorZero (Karoubi C) A).hom.app (X : Karoubi C)).f =
      (shiftFunctorZero C A).hom.app X := by
  change ((shiftFunctorZero (Karoubi C) A).hom.app ((toKaroubi C).obj X)).f = _
  rw [shiftFunctorZero_hom_app_obj_of_induced (toKaroubi C) A _ _ X]
  exact id_comp _

private theorem shiftFunctorZero_inv_app_coe_f (X : C) :
    ((shiftFunctorZero (Karoubi C) A).inv.app (X : Karoubi C)).f =
      (shiftFunctorZero C A).inv.app X := by
  change ((shiftFunctorZero (Karoubi C) A).inv.app ((toKaroubi C).obj X)).f = _
  rw [shiftFunctorZero_inv_app_obj_of_induced (toKaroubi C) A _ _ X]
  exact comp_id _

private theorem shiftFunctorAdd_hom_app_coe_f (X : C) (a b : A) :
    ((shiftFunctorAdd (Karoubi C) a b).hom.app (X : Karoubi C)).f =
      (shiftFunctorAdd C a b).hom.app X := by
  change ((shiftFunctorAdd (Karoubi C) a b).hom.app ((toKaroubi C).obj X)).f = _
  rw [shiftFunctorAdd_hom_app_obj_of_induced (toKaroubi C) _ _ a b X]
  exact (id_comp _).trans (by simp)

private theorem shiftFunctorAdd_inv_app_coe_f (X : C) (a b : A) :
    ((shiftFunctorAdd (Karoubi C) a b).inv.app (X : Karoubi C)).f =
      (shiftFunctorAdd C a b).inv.app X := by
  change ((shiftFunctorAdd (Karoubi C) a b).inv.app ((toKaroubi C).obj X)).f = _
  rw [shiftFunctorAdd_inv_app_obj_of_induced (toKaroubi C) _ _ a b X]
  -- The first factor is the shift by `b` of an identity morphism.
  exact (congr_arg (· ≫ _) ((shiftFunctor C b).map_id _)).trans ((id_comp _).trans (by simp))

@[simp]
theorem shiftFunctorZero_hom_app_f (P : Karoubi C) :
    ((shiftFunctorZero (Karoubi C) A).hom.app P).f =
      (shiftFunctor C (0 : A)).map P.p ≫ (shiftFunctorZero C A).hom.app P.X := by
  rw [natTrans_eq, comp_f, comp_f, shiftFunctorZero_hom_app_coe_f]
  simp

@[simp]
theorem shiftFunctorZero_inv_app_f (P : Karoubi C) :
    ((shiftFunctorZero (Karoubi C) A).inv.app P).f =
      P.p ≫ (shiftFunctorZero C A).inv.app P.X := by
  rw [natTrans_eq, comp_f, comp_f, shiftFunctorZero_inv_app_coe_f]
  simp only [Functor.id_map, decompId_i_f, shiftFunctor_map_f, decompId_p_f]
  rw [← (shiftFunctorZero C A).inv.naturality, Functor.id_map, P.idem_assoc]

@[simp]
theorem shiftFunctorAdd_hom_app_f (P : Karoubi C) (a b : A) :
    ((shiftFunctorAdd (Karoubi C) a b).hom.app P).f =
      (shiftFunctor C (a + b)).map P.p ≫ (shiftFunctorAdd C a b).hom.app P.X := by
  rw [natTrans_eq, comp_f, comp_f, shiftFunctorAdd_hom_app_coe_f]
  simp [← Functor.map_comp, P.idem]

@[simp]
theorem shiftFunctorAdd_inv_app_f (P : Karoubi C) (a b : A) :
    ((shiftFunctorAdd (Karoubi C) a b).inv.app P).f =
      (shiftFunctor C b).map ((shiftFunctor C a).map P.p) ≫
        (shiftFunctorAdd C a b).inv.app P.X := by
  rw [natTrans_eq, comp_f, comp_f, shiftFunctorAdd_inv_app_coe_f]
  simp only [comp_obj, Functor.comp_map, shiftFunctor_map_f, decompId_i_f, decompId_p_f]
  rw [← (shiftFunctorAdd C a b).inv.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp, P.idem]

end Karoubi

end CategoryTheory.Idempotents
