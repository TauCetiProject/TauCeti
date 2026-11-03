/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks along equal maps

When the right-hand map `g'` of a pullback is equal to another map `g`, the two pullback objects
are equal, and the resulting `eqToHom` between them commutes with the projections
(`CategoryTheory.Limits.eqToHom_comp_pullback_fst` and
`CategoryTheory.Limits.eqToHom_comp_pullback_snd`). This is useful when a coherence statement
involves base change along maps that agree only propositionally, such as `f ≫ 𝟙 Y` and `f`.
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- Rewriting the right-hand map `g'` of a pullback to an equal map `g` transports the first
projection along the resulting `eqToHom`. -/
@[reassoc]
theorem eqToHom_comp_pullback_fst {X Y Z : C} (f : X ⟶ Z) {g g' : Y ⟶ Z} (e : g' = g)
    [HasPullback f g] [HasPullback f g'] (e' : pullback f g' = pullback f g) :
    eqToHom e' ≫ pullback.fst f g = pullback.fst f g' := by
  subst e; simp

/-- Rewriting the right-hand map `g'` of a pullback to an equal map `g` transports the second
projection along the resulting `eqToHom`. -/
@[reassoc]
theorem eqToHom_comp_pullback_snd {X Y Z : C} (f : X ⟶ Z) {g g' : Y ⟶ Z} (e : g' = g)
    [HasPullback f g] [HasPullback f g'] (e' : pullback f g' = pullback f g) :
    eqToHom e' ≫ pullback.snd f g = pullback.snd f g' := by
  subst e; simp

end CategoryTheory.Limits
