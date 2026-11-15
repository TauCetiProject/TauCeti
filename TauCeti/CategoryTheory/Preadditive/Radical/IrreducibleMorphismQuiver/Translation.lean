/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The partial translation on the quiver of irreducible morphisms

An Auslander–Reiten translate on a class `P` of objects of a category is recorded by
`TauCeti.ARTranslation P`: an operation `τ` on the objects satisfying `P` that preserves `P` and
isomorphism, is indecomposable on an indecomposable object exactly when that object is not
projective, is injective exactly on projectives, reflects isomorphism on non-projective
indecomposables, and reaches every non-injective indecomposable. These are the properties of
`D Tr` on finitely generated modules over a finite-dimensional algebra
(`ModuleCat.arTranslate`) and on finite-dimensional quiver representations
(`TauCeti.arTranslate`).

Such a translate descends to a partial map `ARTranslation.translate` on the vertices of
`TauCeti.IrreducibleMorphismQuiver k P`, undefined exactly at the projective vertices. Its values
are non-injective vertices, it is injective where defined, and every non-injective vertex is a
value (`ARTranslation.existsUnique_translate_eq_some_iff`). So it is a bijection from the
non-projective vertices onto the non-injective ones, the partial translation of the
Auslander–Reiten quiver.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1 and VII.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasBinaryBiproducts C]

/-- An Auslander–Reiten translate on the objects satisfying `P`: an operation preserving `P` and
isomorphism, indecomposable exactly away from projectives, injective exactly on projectives,
reflecting isomorphism on non-projective indecomposables, and reaching every non-injective
indecomposable. -/
structure ARTranslation (P : ObjectProperty C) where
  /-- The translate of an object satisfying `P`. -/
  obj (M : C) (hM : P M) : C
  /-- The translate satisfies `P`. -/
  prop_obj (M : C) (hM : P M) : P (obj M hM)
  /-- Isomorphic objects have isomorphic translates. -/
  nonempty_iso_obj_of_iso {M N : C} (hM : P M) (hN : P N) (e : M ≅ N) :
    Nonempty (obj M hM ≅ obj N hN)
  /-- The translate of an indecomposable is indecomposable exactly when it is not projective. -/
  indecomposable_obj_iff (M : C) (hM : P M) (hI : Indecomposable M) :
    Indecomposable (obj M hM) ↔ ¬ Projective M
  /-- The translate is injective exactly when the object is projective. -/
  injective_obj_iff (M : C) (hM : P M) : Injective (obj M hM) ↔ Projective M
  /-- On non-projective indecomposables, isomorphic translates come from isomorphic objects. -/
  nonempty_iso_of_nonempty_iso_obj {M N : C} (hM : P M) (hN : P N) (hiM : Indecomposable M)
    (hiN : Indecomposable N) (hpM : ¬ Projective M) :
    Nonempty (obj M hM ≅ obj N hN) → Nonempty (M ≅ N)
  /-- Every non-injective indecomposable is a translate of a non-projective indecomposable. -/
  exists_nonempty_iso_obj (N : C) (hN : P N) (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (M : C) (hM : P M), Indecomposable M ∧ ¬ Projective M ∧ Nonempty (obj M hM ≅ N)

namespace ARTranslation

variable {k : Type w} {P : ObjectProperty C} (T : ARTranslation P)

open IrreducibleMorphismQuiver

/-- The partial translation on isomorphism classes: the translate away from projectives, and
`none` on projectives. -/
noncomputable def translate (a : IrreducibleMorphismQuiver k P) :
    Option (IrreducibleMorphismQuiver k P) := by
  classical
  exact if hp : Projective a.representative then none else
    some (of k (T.prop_obj _ a.representative_property.1)
      ((T.indecomposable_obj_iff _ a.representative_property.1
        a.representative_property.2).mpr hp))

/-- Translation is undefined exactly at projective classes. -/
@[simp]
theorem translate_eq_none_iff (a : IrreducibleMorphismQuiver k P) :
    T.translate a = none ↔ Projective a.representative := by
  classical
  by_cases hp : Projective a.representative <;> simp [translate, hp]

/-- The class of an object has undefined translation exactly when the object is projective. -/
-- Simplify a specified representative before the general chosen-representative rule.
@[simp high]
theorem translate_of_eq_none_iff {M : C} (hM : P M) (hI : Indecomposable M) :
    T.translate (of k hM hI) = none ↔ Projective M := by
  rw [translate_eq_none_iff]
  exact Projective.iso_iff (representativeIso k hM hI)

/-- Any representative computes translation: the class of a non-projective object is sent to
the class of its translate. -/
theorem translate_of {M : C} (hM : P M) (hI : Indecomposable M) (hp : ¬ Projective M) :
    T.translate (of k hM hI) =
      some (of k (T.prop_obj M hM) ((T.indecomposable_obj_iff M hM hI).mpr hp)) := by
  classical
  have hrep : ¬ Projective (of k hM hI).representative :=
    fun h ↦ hp ((Projective.iso_iff (representativeIso k hM hI)).mp h)
  simp only [translate, dite_eq_right hrep, Option.some.injEq]
  exact (of_eq_of_iff _ _ _ _).mpr (T.nonempty_iso_obj_of_iso _ _ (representativeIso k hM hI))

/-- Translation of one class is another class exactly when the first is non-projective and its
translate is isomorphic to a representative of the second. -/
@[simp]
theorem translate_of_eq_some_of_iff {M N : C} (hM : P M) (hI : Indecomposable M) (hN : P N)
    (hJ : Indecomposable N) :
    T.translate (of k hM hI) = some (of k hN hJ) ↔
      ¬ Projective M ∧ Nonempty (T.obj M hM ≅ N) := by
  by_cases hp : Projective M
  · simp [(T.translate_of_eq_none_iff hM hI).mpr hp, hp]
  · rw [T.translate_of hM hI hp, Option.some.injEq, of_eq_of_iff]
    simp [hp]

/-- Every defined translation lands at a non-injective class. -/
theorem not_injective_of_translate_eq_some {a b : IrreducibleMorphismQuiver k P}
    (h : T.translate a = some b) : ¬ Injective b.representative := by
  have hp : ¬ Projective a.representative := fun hp ↦ by
    rw [(T.translate_eq_none_iff a).mpr hp] at h
    contradiction
  have ha := T.translate_of (k := k) a.representative_property.1 a.representative_property.2 hp
  rw [of_representative, h, Option.some.injEq] at ha
  rw [ha]
  intro hi
  exact hp ((T.injective_obj_iff _ a.representative_property.1).mp
    (Injective.of_iso (representativeIso k _ _) hi))

/-- Two classes with the same defined translation are equal. -/
theorem eq_of_translate_eq_some {a b c : IrreducibleMorphismQuiver k P}
    (ha : T.translate a = some c) (hb : T.translate b = some c) : a = b := by
  have ha' := (T.translate_of_eq_some_of_iff (k := k) a.representative_property.1
    a.representative_property.2 c.representative_property.1 c.representative_property.2).mp
      (by simpa only [of_representative] using ha)
  have hb' := (T.translate_of_eq_some_of_iff (k := k) b.representative_property.1
    b.representative_property.2 c.representative_property.1 c.representative_property.2).mp
      (by simpa only [of_representative] using hb)
  obtain ⟨ea⟩ := ha'.2
  obtain ⟨eb⟩ := hb'.2
  have h := T.nonempty_iso_of_nonempty_iso_obj a.representative_property.1
    b.representative_property.1 a.representative_property.2 b.representative_property.2 ha'.1
    ⟨ea ≪≫ eb.symm⟩
  simpa only [of_representative] using (of_eq_of_iff (k := k)
    a.representative_property.1 a.representative_property.2
    b.representative_property.1 b.representative_property.2).mpr h

/-- Translation is injective on the non-projective vertices. -/
theorem translate_injective :
    Function.Injective (fun a : {a : IrreducibleMorphismQuiver k P //
      ¬ Projective a.representative} ↦ T.translate a.val) := by
  intro a b hab
  apply Subtype.ext
  cases ha : T.translate a.val with
  | none => exact False.elim (a.property ((T.translate_eq_none_iff a.val).mp ha))
  | some c => exact T.eq_of_translate_eq_some ha (hab.symm.trans ha)

/-- A vertex has a unique preimage under defined translation exactly when it is non-injective.
Thus translation bijects the non-projective and the non-injective classes. -/
@[simp]
theorem existsUnique_translate_eq_some_iff (b : IrreducibleMorphismQuiver k P) :
    (∃! a, T.translate a = some b) ↔ ¬ Injective b.representative := by
  refine ⟨fun ⟨a, ha, _⟩ ↦ T.not_injective_of_translate_eq_some ha, fun hb ↦ ?_⟩
  obtain ⟨M, hM, hiM, hpM, e⟩ := T.exists_nonempty_iso_obj b.representative
    b.representative_property.1 b.representative_property.2 hb
  have ha : T.translate (of k hM hiM) = some b := by
    simpa only [of_representative] using (T.translate_of_eq_some_of_iff (k := k) hM hiM
      b.representative_property.1 b.representative_property.2).mpr ⟨hpM, e⟩
  exact ⟨of k hM hiM, ha, fun a h ↦ T.eq_of_translate_eq_some h ha⟩

end ARTranslation

end TauCeti
