/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Relative properties by descent

Let `F : C ⥤ D` be full and faithful, and let `f : X ⟶ Y` in `D` be relatively representable
with respect to `F`. Mathlib's `MorphismProperty.relative_of_snd` shows that `f` satisfies
`P.relative F` once every base change `hf.snd g` along `g : F.obj a ⟶ Y` satisfies `P`. This file
weakens the hypothesis when `P` descends along `Q`: it suffices that each such base change
satisfies `P` after a further base change along a morphism satisfying `Q`.

## Main results

* `CategoryTheory.MorphismProperty.relative_of_forall_exists_cover`: if `P` descends along `Q`,
  and for every `g : F.obj a ⟶ Y` there is `p : a' ⟶ a` satisfying `Q` such that the base change
  of `f` along `F.map p ≫ g` satisfies `P`, then `f` satisfies `P.relative F`.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D} [F.Full] [F.Faithful]
  {P Q : MorphismProperty C} {X Y : D} {f : X ⟶ Y}

/-- Let `F` be full and faithful, `f` relatively representable with respect to `F`, and let `P`
descend along `Q`. If for every `g : F.obj a ⟶ Y` there is a morphism `p : a' ⟶ a` satisfying `Q`
such that the base change of `f` along `F.map p ≫ g` satisfies `P`, then `f` satisfies
`P.relative F`. -/
theorem relative_of_forall_exists_cover [P.RespectsIso] [P.DescendsAlong Q]
    (hf : F.relativelyRepresentable f)
    (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (a' : C) (p : a' ⟶ a), Q p ∧ P (hf.snd (F.map p ≫ g))) :
    P.relative F f := by
  refine relative_of_snd hf fun a g ↦ ?_
  obtain ⟨a', p, hp, hP⟩ := h g
  let k := hf.lift (hf.fst (F.map p ≫ g)) (hf.snd (F.map p ≫ g) ≫ p)
    (by simpa using hf.w (F.map p ≫ g))
  have sq : IsPullback (F.map k) (F.map (hf.snd (F.map p ≫ g))) (F.map (hf.snd g)) (F.map p) :=
    IsPullback.of_right (by simpa [k] using hf.isPullback (F.map p ≫ g))
      (by simp [k, ← Functor.map_comp]) (hf.isPullback g)
  exact of_isPullback_of_descendsAlong (sq.of_map_of_faithful F).flip hp hP

end CategoryTheory.MorphismProperty
