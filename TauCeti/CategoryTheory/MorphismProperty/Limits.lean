/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import TauCeti.CategoryTheory.Limits.Shapes.BinaryProducts
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Diagonal

/-!
# Base changes of base changes and stability of products and diagonals

Let `P` be a property of morphisms stable under base change. If the base change
`pullback.snd f k` of `f` along `k` has `P`, then so does every further base change of `f` along a
morphism factoring through `k`: this file records the forms of this used when reducing a property
of morphisms of schemes to an affine base. Mathlib's `MorphismProperty.pullback_snd` is the case
where `f` itself has `P`. If `P` is moreover stable under composition, then the product of two
morphisms of `Over S` has `P` on underlying morphisms whenever both factors do and the source,
target, and intermediate binary products exist, and membership of the diagonal `diag X : X ⟶ X ⨯ X`
in `P` passes along monomorphisms and is preserved by binary products and pullbacks.

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
* `CategoryTheory.MorphismProperty.diag_of_mono`,
  `CategoryTheory.MorphismProperty.diag_prod`,
  `CategoryTheory.MorphismProperty.diag_pullback`, and
  `CategoryTheory.MorphismProperty.diag_of_isPullback`: membership of `Limits.diag X` in `P` passes
  along monomorphisms and is preserved by binary products and pullbacks.
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

/-- For a morphism property `P` stable under base change, membership of the diagonal passes along
monomorphisms. -/
theorem diag_of_mono [HasBinaryProduct X X] [HasBinaryProduct Y Y] (ι : X ⟶ Y) [Mono ι]
    (hY : P (Limits.diag Y)) : P (Limits.diag X) :=
  P.of_isPullback (Limits.isPullback_diag_of_mono ι) hY

/-- For a morphism property `P` stable under base change and composition, membership of the
diagonal is preserved by binary products. -/
theorem diag_prod [P.IsStableUnderComposition] [HasBinaryProducts C]
    (hX : P (Limits.diag X)) (hY : P (Limits.diag Y)) : P (Limits.diag (X ⨯ Y)) := by
  have h₁ : P (prod.map (Limits.diag X) (𝟙 Y)) :=
    P.of_isPullback (IsPullback.of_prod_fst_with_id (Limits.diag X) Y) hX
  have h₂ : P (prod.map (𝟙 (X ⨯ X)) (Limits.diag Y)) :=
    P.of_isPullback (IsPullback.of_prod_snd_with_id (X ⨯ X) (Limits.diag Y)) hY
  obtain ⟨e, hfac⟩ : ∃ e : (X ⨯ Y) ⨯ (X ⨯ Y) ≅ (X ⨯ X) ⨯ (Y ⨯ Y),
      Limits.diag (X ⨯ Y) =
        (prod.map (Limits.diag X) (𝟙 Y) ≫ prod.map (𝟙 (X ⨯ X)) (Limits.diag Y)) ≫ e.inv :=
    ⟨{ hom := prod.lift (prod.map prod.fst prod.fst) (prod.map prod.snd prod.snd)
       inv := prod.lift (prod.map prod.fst prod.fst) (prod.map prod.snd prod.snd)
       hom_inv_id := by ext <;> simp
       inv_hom_id := by ext <;> simp }, by ext <;> simp⟩
  rw [hfac, P.cancel_right_of_respectsIso]
  exact P.comp_mem _ _ h₁ h₂

/-- For a morphism property `P` stable under base change and composition, membership of the
diagonal is preserved by pullbacks. -/
theorem diag_pullback [P.IsStableUnderComposition] [HasBinaryProducts C] {Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (hX : P (Limits.diag X)) (hY : P (Limits.diag Y)) :
    P (Limits.diag (pullback f g)) :=
  diag_of_mono (prod.lift (pullback.fst f g) (pullback.snd f g)) (diag_prod hX hY)

/-- Pullback-square form of `diag_pullback`: if `W` is a pullback of `f : X ⟶ Z` and `g : Y ⟶ Z`,
membership of the diagonal in `P` passes from `X` and `Y` to `W`. -/
theorem diag_of_isPullback [P.IsStableUnderComposition] [HasBinaryProducts C] {Z : C}
    {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hX : P (Limits.diag X)) (hY : P (Limits.diag Y)) :
    P (Limits.diag W) := by
  have : HasPullback f g := sq.hasPullback
  have hfac : Limits.diag W =
      sq.isoPullback.hom ≫ Limits.diag (pullback f g) ≫
        (prod.mapIso sq.isoPullback sq.isoPullback).inv := by
    ext <;> simp
  rw [hfac, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact diag_pullback f g hX hY

end CategoryTheory.MorphismProperty
