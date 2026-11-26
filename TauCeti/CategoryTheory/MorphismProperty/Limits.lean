/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import TauCeti.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Base changes of base changes

Let `P` be a property of morphisms stable under base change. If the base change
`pullback.snd f k` of `f` along `k` has `P`, then so does every further base change of `f` along a
morphism factoring through `k`: this file records the forms of this used when reducing a property
of morphisms of schemes to an affine base. Mathlib's `MorphismProperty.pullback_snd` is the case
where `f` itself has `P`. If `P` is moreover stable under composition, then the product of two
morphisms of `Over S` has `P` on underlying morphisms whenever both factors do and the source,
target, and intermediate binary products exist.

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
* `CategoryTheory.MorphismProperty.prod_map_left`: if `P` is moreover stable under composition,
  `P f.left` and `P g.left` imply `P (prod.map f g).left` for morphisms `f` and `g` of `Over S`,
  assuming the source, target, and intermediate binary products exist.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C] {P : MorphismProperty C} [P.IsStableUnderBaseChange]
  {X Y W W' : C}

/-- A base change of `pullback.snd f k` along `e` is the base change of `f` along `e ≫ k`, so it
inherits every property stable under base change. -/
theorem pullback_snd_comp (f : X ⟶ Y) (k : W ⟶ Y) (e : W' ⟶ W) [HasPullback f k]
    [HasPullback f (e ≫ k)] (h : P (pullback.snd f k)) : P (pullback.snd f (e ≫ k)) :=
  P.of_isPullback ((IsPullback.of_hasPullback f (e ≫ k)).of_right' (.of_hasPullback f k)) h

/-- A form of `pullback_snd_comp` for a morphism `a` known to factor as `e ≫ k`. Its conclusion
does not mention the composite, so it can be applied where rewriting with the factorisation inside
`pullback` is not possible. -/
theorem pullback_snd_of_comp_eq (f : X ⟶ Y) (k : W ⟶ Y) (e : W' ⟶ W) {a : W' ⟶ Y}
    [HasPullback f k] [HasPullback f a] (hfac : e ≫ k = a) (h : P (pullback.snd f k)) :
    P (pullback.snd f a) := by
  subst hfac
  exact pullback_snd_comp f k e h

/-- If the base change of `f` along `Y ×_S T ⟶ Y` has `P`, then so does its base change along
`Y ×_S T' ⟶ Y` for every `t : T' ⟶ T`, since the latter factors through the former. -/
theorem pullback_snd_pullback_fst_comp {S T T' : C} (f : X ⟶ Y) (g : Y ⟶ S) (r : T ⟶ S)
    (t : T' ⟶ T) [HasPullback g r] [HasPullback g (t ≫ r)]
    [HasPullback f (pullback.fst g r)] [HasPullback f (pullback.fst g (t ≫ r))]
    (h : P (pullback.snd f (pullback.fst g r))) :
    P (pullback.snd f (pullback.fst g (t ≫ r))) :=
  pullback_snd_of_comp_eq f _
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by simp [pullback.condition]))
    (pullback.lift_fst _ _ _) h

/-- If `a ≫ v` factors as `e ≫ k`, then the base change of `pullback.snd f v` along `a` inherits
from `pullback.snd f k` every property stable under base change. -/
theorem pullback_snd_pullback_snd {Y' T : C} (f : X ⟶ Y) (v : Y' ⟶ Y) (a : T ⟶ Y')
    (k : W ⟶ Y) (e : T ⟶ W) [HasPullback f v] [HasPullback (pullback.snd f v) a] [HasPullback f k]
    (hfac : a ≫ v = e ≫ k) (h : P (pullback.snd f k)) : P (pullback.snd (pullback.snd f v) a) := by
  have hpb := (IsPullback.of_hasPullback (pullback.snd f v) a).paste_horiz (.of_hasPullback f v)
  rw [hfac] at hpb
  exact P.of_isPullback (hpb.of_right' (.of_hasPullback f k)) h

/-- For a property stable under base change and composition, precomposing `f` with a morphism
having the property keeps the property of `pullback.snd f k`. -/
theorem pullback_snd_comp_left [P.IsStableUnderComposition] {X' : C} (f : X ⟶ Y) (k : W ⟶ Y)
    (e : X' ⟶ X) [HasPullback f k] [HasPullback (e ≫ f) k] (he : P e) (h : P (pullback.snd f k)) :
    P (pullback.snd (e ≫ f) k) := by
  simpa using P.comp_mem _ _ (P.of_isPullback
    ((IsPullback.of_hasPullback (e ≫ f) k).of_bot' (.of_hasPullback f k)) he) h

/-- For a property stable under base change and composition, a product `prod.map f g` of morphisms
`f : X ⟶ X'` and `g : Y ⟶ Y'` in `Over S` has the property on underlying morphisms when both
factors do and the source product `X ⨯ Y`, target product `X' ⨯ Y'`, and intermediate product
`X' ⨯ Y` exist. This parallels Mathlib's `MorphismProperty.pullbackMap`, which treats
`pullback.map`. -/
theorem prod_map_left [P.IsStableUnderComposition] {S : C} {X Y X' Y' : Over S}
    [HasBinaryProduct X Y] [HasBinaryProduct X' Y] [HasBinaryProduct X' Y'] (f : X ⟶ X')
    (g : Y ⟶ Y') (hf : P f.left) (hg : P g.left) : P (prod.map f g).left := by
  have h₁ : P (prod.map f (𝟙 Y)).left :=
    P.of_isPullback ((IsPullback.of_prod_fst_with_id f Y).map (Over.forget S)) hf
  have h₂ : P (prod.map (𝟙 X') g).left :=
    P.of_isPullback ((IsPullback.of_prod_snd_with_id X' g).map (Over.forget S)) hg
  simpa [← Over.comp_left] using P.comp_mem _ _ h₁ h₂

end CategoryTheory.MorphismProperty
