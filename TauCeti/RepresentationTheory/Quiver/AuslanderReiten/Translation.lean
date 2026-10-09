/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver
public import TauCeti.RepresentationTheory.Quiver.Representation.Translate

/-!
# Translation on the quiver of irreducible morphisms

For a quiver with finitely many paths, the Auslander–Reiten translate `D Tr` descends to a
partial map on the isomorphism classes of finite-dimensional indecomposables. It is undefined
exactly at projective classes, and its defined values are non-injective classes.

`irreducibleMorphismQuiver.translate_of_eq_some_of_iff` characterizes the partial map using any
representatives, so computations can use a convenient minimal presentation rather than the
chosen representative of a skeleton class. This file does not establish an inverse translation
or the mesh relation between arrows.

The construction uses `TauCeti.arTranslate` and its independence of the minimal presentation.
No algebraic closedness assumption is needed.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1 and VII.1.
-/

public section

namespace TauCeti.irreducibleMorphismQuiver

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

local instance : Finite Q :=
  Finite.of_injective (fun q : Q ↦ (⟨q, q, Quiver.Path.nil⟩ : Quiver.TotalPath Q))
    (fun _ _ h ↦ congrArg Sigma.fst h)

/-- The partial Auslander–Reiten translation on isomorphism classes: `D Tr` away from
projectives, and `none` on projectives. -/
noncomputable def translate (a : irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q) :
    Option (irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q) := by
  classical
  exact if hp : Projective a.representative then none else
    some (of (isFinDim_arTranslate.{u, v, w, t} k Q a.representative a.representative_property.1)
      ((indecomposable_arTranslate_iff.{u, v, w, t} k Q a.representative a.representative_property.1
        a.representative_property.2).mpr hp))

/-- Translation is undefined exactly at projective classes. -/
@[simp]
theorem translate_eq_none_iff
    (a : irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q) :
    translate.{u, v, w, t} a = none ↔ Projective a.representative := by
  classical
  by_cases hp : Projective a.representative <;> simp [translate, hp]

/-- The class of a representation has undefined translation exactly when the representation
is projective. -/
-- Simplify a specified representative before the general chosen-representative rule.
@[simp high]
theorem translate_of_eq_none_iff {M : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M) :
    translate.{u, v, w, t} (of hM hI) = none ↔ Projective M := by
  rw [translate_eq_none_iff.{u, v, w, t}]
  exact Projective.iso_iff (representativeIso hM hI)

/-- Any representative computes translation: the class of a non-projective representation
is sent to the class of its `D Tr` translate. -/
theorem translate_of {M : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M) (hp : ¬ Projective M) :
    translate.{u, v, w, t} (of hM hI) = some (of (isFinDim_arTranslate.{u, v, w, t} k Q M hM)
      ((indecomposable_arTranslate_iff.{u, v, w, t} k Q M hM hI).mpr hp)) := by
  classical
  have hrep : ¬ Projective (of hM hI).representative :=
    fun h ↦ hp ((Projective.iso_iff (representativeIso hM hI)).mp h)
  simp only [translate, dite_eq_right hrep, Option.some.injEq]
  apply (of_eq_of_iff _ _ _ _).mpr
  exact nonempty_iso_arTranslate_of_iso.{u, v, w, t} _ _ _ _ (representativeIso hM hI)

/-- Translation of one class is another class exactly when the first is non-projective and
its `D Tr` translate is isomorphic to a representative of the second. -/
@[simp]
theorem translate_of_eq_some_of_iff {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M)
    (hN : IsFinDim k Q N) (hJ : Indecomposable N) :
    translate.{u, v, w, t} (of hM hI) = some (of hN hJ) ↔
      ¬ Projective M ∧ Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅ N) := by
  by_cases hp : Projective M
  · have hz := (translate_of_eq_none_iff.{u, v, w, t} hM hI).mpr hp
    simp [hz, hp]
  · rw [translate_of.{u, v, w, t} hM hI hp, Option.some.injEq, of_eq_of_iff]
    simp [hp]

/-- Every defined translation lands at a non-injective class. -/
theorem not_injective_of_translate_eq_some
    {a b : irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q}
    (h : translate.{u, v, w, t} a = some b) : ¬ Injective b.representative := by
  have hp : ¬ Projective a.representative := by
    intro hp
    have hn := (translate_eq_none_iff.{u, v, w, t} a).mpr hp
    rw [hn] at h
    contradiction
  have ha := translate_of.{u, v, w, t} a.representative_property.1 a.representative_property.2 hp
  rw [of_representative, h, Option.some.injEq] at ha
  rw [ha]
  intro hi
  have ht := Injective.of_iso (representativeIso
    (isFinDim_arTranslate.{u, v, w, t} k Q a.representative a.representative_property.1)
    ((indecomposable_arTranslate_iff.{u, v, w, t} k Q a.representative a.representative_property.1
      a.representative_property.2).mpr hp)) hi
  exact hp ((injective_arTranslate_iff.{u, v, w, t} k Q a.representative
    a.representative_property.1).mp ht)

end TauCeti.irreducibleMorphismQuiver
