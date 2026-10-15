/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base changes of base changes

Let `P` be a property of morphisms stable under base change. If the base change
`pullback.snd f k` of `f` along `k` has `P`, then so does every further base change of `f` along a
morphism factoring through `k`: this file records the forms of this used when reducing a property
of morphisms of schemes to an affine base. Mathlib's `MorphismProperty.pullback_snd` is the case
where `f` itself has `P`.

## Main results

* `CategoryTheory.MorphismProperty.pullback_snd_comp`: `P (pullback.snd f k)` implies
  `P (pullback.snd f (e ≫ k))`; `pullback_snd_of_comp_eq` is the same for a morphism equal to
  `e ≫ k`.
* `CategoryTheory.MorphismProperty.pullback_snd_pullback_fst_comp`: the base change of `f` along
  `Y ×_S T ⟶ Y` passes its property to the base change along `Y ×_S T' ⟶ Y` for any `T' ⟶ T`.
* `CategoryTheory.MorphismProperty.pullback_snd_pullback_snd`: `P (pullback.snd f k)` implies
  `P (pullback.snd (pullback.snd f v) a)` whenever `a ≫ v` factors through `k`.
* `CategoryTheory.MorphismProperty.pullback_snd_comp_left`: if `P` is moreover stable under
  composition, `P e` and `P (pullback.snd f k)` imply `P (pullback.snd (e ≫ f) k)`.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C] [HasPullbacks C] {P : MorphismProperty C}
  [P.IsStableUnderBaseChange] {X Y W W' : C}

/-- A base change of `pullback.snd f k` along `e` is the base change of `f` along `e ≫ k`, so it
inherits every property stable under base change. -/
theorem pullback_snd_comp (f : X ⟶ Y) (k : W ⟶ Y) (e : W' ⟶ W) (h : P (pullback.snd f k)) :
    P (pullback.snd f (e ≫ k)) := by
  refine (P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f k e).hom _).mp ?_
  simpa using P.pullback_snd _ e h

/-- A form of `pullback_snd_comp` for a morphism `a` known to factor as `e ≫ k`. Its conclusion
does not mention the composite, so it can be applied where rewriting with the factorisation inside
`pullback` is not possible. -/
theorem pullback_snd_of_comp_eq (f : X ⟶ Y) (k : W ⟶ Y) (e : W' ⟶ W) {a : W' ⟶ Y}
    (hfac : e ≫ k = a) (h : P (pullback.snd f k)) : P (pullback.snd f a) := by
  subst hfac
  exact pullback_snd_comp f k e h

/-- If the base change of `f` along `Y ×_S T ⟶ Y` has `P`, then so does its base change along
`Y ×_S T' ⟶ Y` for every `t : T' ⟶ T`, since the latter factors through the former. -/
theorem pullback_snd_pullback_fst_comp {S T T' : C} (f : X ⟶ Y) (g : Y ⟶ S) (r : T ⟶ S)
    (t : T' ⟶ T) (h : P (pullback.snd f (pullback.fst g r))) :
    P (pullback.snd f (pullback.fst g (t ≫ r))) :=
  pullback_snd_of_comp_eq f _ ((pullbackLeftPullbackSndIso g r t).inv ≫ pullback.fst _ _)
    (by simp) h

/-- If `a ≫ v` factors as `e ≫ k`, then the base change of `pullback.snd f v` along `a` inherits
from `pullback.snd f k` every property stable under base change. -/
theorem pullback_snd_pullback_snd {Y' T : C} (f : X ⟶ Y) (v : Y' ⟶ Y) (a : T ⟶ Y')
    (k : W ⟶ Y) (e : T ⟶ W) (hfac : a ≫ v = e ≫ k) (h : P (pullback.snd f k)) :
    P (pullback.snd (pullback.snd f v) a) := by
  have := pullback_snd_of_comp_eq f k e hfac.symm h
  refine (P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f v a).inv _).mp ?_
  simpa using this

/-- For a property stable under base change and composition, precomposing `f` with a morphism
having the property keeps the property of `pullback.snd f k`. -/
theorem pullback_snd_comp_left [P.IsStableUnderComposition] {X' : C} (f : X ⟶ Y) (k : W ⟶ Y)
    (e : X' ⟶ X) (he : P e) (h : P (pullback.snd f k)) : P (pullback.snd (e ≫ f) k) := by
  refine (P.cancel_left_of_respectsIso (pullbackRightPullbackFstIso f k e).hom _).mp ?_
  simpa using P.comp_mem _ _ (P.pullback_snd _ _ he) h

end CategoryTheory.MorphismProperty
