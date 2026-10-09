/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.EffectiveEpi.Descent
public import TauCeti.CategoryTheory.Monoidal.Grp.Faithful

/-!
# Descent of group objects along effective epimorphisms

Let `p : S' ⟶ S` be a morphism in a category with pullbacks, all of whose base changes are
effective epimorphisms, and let `S'' = S' ×_S S'`. Group objects over `S` are group objects in the
cartesian monoidal category `Over S`, whose product is the fibre product over `S`. For `X` over
`S` write `X' = X ×_S S'`, the image of `X` under the base change functor `Over.pullback p`.

This file descends group structures on an object which has already been descended. Let `X` be an
object over `S`, and suppose that `X'` carries a monoid (group) object structure over `S'`. If its
unit, multiplication (and inverse) satisfy the descent condition of `TauCeti.descendHom`, namely
that their two pullbacks to `S''` agree, then they descend to morphisms over `S`. These are the
structure morphisms of the unique monoid (group) object structure on `X` whose base change is the
given one. Descending a homomorphism of group objects gives a homomorphism, and commutativity
descends as well.

The base change functor is faithful and monoidal, so the group axioms on `X` follow from those on
`X'` (`CategoryTheory.Functor.monObjOfFaithful`). Descent of morphisms supplies the structure
morphisms themselves.

For schemes, Mathlib shows that a flat surjective morphism which is quasi-compact, or locally of
finite presentation, is an effective epimorphism, and that these properties are stable under base
change (`Mathlib.AlgebraicGeometry.Sites.Fpqc`). Instance search therefore discharges the
hypothesis on `p` for any fpqc or fppf morphism of schemes, so the results are effective fpqc
(and fppf) descent of group schemes, group laws and their axioms, and homomorphisms.

## Main definitions

* `TauCeti.descendMonObj`, `TauCeti.descendGrpObj`: the monoid (group) object structure on `X`
  descended from one on `X ×_S S'` whose structure morphisms satisfy the descent condition.

## Main statements

* `TauCeti.monObjObj_descendMonObj`, `TauCeti.grpObjObj_descendGrpObj`: the base change of the
  descended structure is the given one.
* `TauCeti.eq_descendMonObj`, `TauCeti.eq_descendGrpObj`: uniqueness of the descended structure.
* `TauCeti.isCommMonObj_descendMonObj`: the descended structure is commutative if the given one is.
* `TauCeti.isMonHom_descendHom`: a homomorphism satisfying the descent condition descends to a
  homomorphism.
-/

public section

namespace TauCeti

open CategoryTheory Limits MonoidalCategory MonObj
open scoped Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)
  [∀ {Z : C} (g : Z ⟶ S), EffectiveEpi (pullback.fst g p)]

section MonObj

variable (X : Over S) [MonObj ((Over.pullback p).obj X)]

/-- **Descent of a monoid object.** Let `X` be an object over `S` such that `X ×_S S'` is a monoid
object over `S'`. If the unit and the multiplication of `X ×_S S'` satisfy the descent condition of
`TauCeti.descendHom` (their two pullbacks to `S' ×_S S'` agree), then they descend to a monoid
object structure on `X` over `S` (`monObjObj_descendMonObj`). -/
noncomputable abbrev descendMonObj
    (h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p)
    (h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p) :
    MonObj X :=
  (Over.pullback p).monObjOfFaithful X (descendHom p _ h_one) (descendHom p _ h_mul)
    (pullback_map_descendHom p _ h_one) (pullback_map_descendHom p _ h_mul)

variable
    {h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}
    {h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}

/-- **Effectiveness of descent of monoid objects.** The base change of the descended monoid
object structure is the given one. -/
theorem monObjObj_descendMonObj :
    letI := descendMonObj p X h_one h_mul
    Functor.monObjObj (F := Over.pullback p) X = ‹MonObj ((Over.pullback p).obj X)› :=
  (Over.pullback p).monObjObj_monObjOfFaithful X _ _ _ _

/-- **Uniqueness of descended monoid objects.** A monoid object structure on `X` whose base change
is the given one is the descended structure. -/
theorem eq_descendMonObj (h : MonObj X)
    (e : Functor.monObjObj (F := Over.pullback p) X = ‹MonObj ((Over.pullback p).obj X)›) :
    h = descendMonObj p X h_one h_mul :=
  (Over.pullback p).monObjObj_injective X <| e.trans (monObjObj_descendMonObj p X).symm

/-- **Descent of commutativity.** If the given monoid object structure on `X ×_S S'` is
commutative, so is the descended monoid object structure on `X`. -/
theorem isCommMonObj_descendMonObj [IsCommMonObj ((Over.pullback p).obj X)] :
    letI := descendMonObj p X h_one h_mul
    IsCommMonObj X := by
  let := descendMonObj p X h_one h_mul
  refine ((Over.pullback p).isCommMonObj_obj_iff X).1 ?_
  rw [monObjObj_descendMonObj p X]
  infer_instance

end MonObj

section GrpObj

variable (X : Over S) [GrpObj ((Over.pullback p).obj X)]

/-- **Descent of a group object.** Let `X` be an object over `S` such that `X ×_S S'` is a group
object over `S'`. If the unit, the multiplication and the inverse of `X ×_S S'` satisfy the descent
condition of `TauCeti.descendHom` (their two pullbacks to `S' ×_S S'` agree), then they descend to a
group object structure on `X` over `S` (`grpObjObj_descendGrpObj`). -/
noncomputable abbrev descendGrpObj
    (h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p)
    (h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p)
    (h_inv : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p) :
    GrpObj X :=
  (Over.pullback p).grpObjOfFaithful X (descendHom p _ h_one) (descendHom p _ h_mul)
    (descendHom p _ h_inv) (pullback_map_descendHom p _ h_one)
    (pullback_map_descendHom p _ h_mul) (pullback_map_descendHom p _ h_inv)

variable
    {h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}
    {h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}
    {h_inv : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p}

/-- **Effectiveness of descent of group objects.** The base change of the descended group object
structure is the given one. -/
theorem grpObjObj_descendGrpObj :
    letI := descendGrpObj p X h_one h_mul h_inv
    Functor.grpObjObj (F := Over.pullback p) (G := X) = ‹GrpObj ((Over.pullback p).obj X)› :=
  (Over.pullback p).grpObjObj_grpObjOfFaithful X _ _ _ _ _ _

/-- **Uniqueness of descended group objects.** A group object structure on `X` whose base change
is the given one is the descended structure. -/
theorem eq_descendGrpObj (h : GrpObj X)
    (e : Functor.grpObjObj (F := Over.pullback p) (G := X) = ‹GrpObj ((Over.pullback p).obj X)›) :
    h = descendGrpObj p X h_one h_mul h_inv :=
  (Over.pullback p).grpObjObj_injective X <| e.trans (grpObjObj_descendGrpObj p X).symm

end GrpObj

/-- **Descent of homomorphisms.** Let `X` and `Y` be monoid objects over `S`. A homomorphism
`φ : X ×_S S' ⟶ Y ×_S S'` of the base-changed monoid objects whose two pullbacks to `S' ×_S S'`
agree descends to a homomorphism `X ⟶ Y`. -/
instance isMonHom_descendHom {X Y : Over S} [MonObj X] [MonObj Y]
    (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y) [IsMonHom φ]
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    IsMonHom (descendHom p φ h) := by
  rw [← (Over.pullback p).isMonHom_map_iff, pullback_map_descendHom]
  infer_instance

end TauCeti
