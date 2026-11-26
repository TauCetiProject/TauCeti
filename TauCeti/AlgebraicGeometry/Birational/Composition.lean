/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# Composition of rational maps with morphisms

Mathlib composes a partial or rational map with a morphism on the right (`compHom`) and composes
partial or rational maps with each other (`comp`). This file shows that the two compositions
associate: composing `f.comp g` with a morphism `h` is composing `f` with `g.compHom h`.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.comp_compHom` and
  `AlgebraicGeometry.Scheme.RationalMap.comp_compHom`:
  `(f.comp g).compHom h = f.comp (g.compHom h)`.
* `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative_comp_representative`: the
  composite of the representatives of `f` and `g` represents `f.comp g`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z W : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]

/-- Composing a composite of partial maps with a morphism. -/
@[simp]
theorem PartialMap.comp_compHom (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (h : Z ⟶ W) : (f.comp g).compHom h = f.comp (g.compHom h) := by
  -- the two domains agree only up to unfolding `compHom`, so `ext` would leave an `isoOfEq` that
  -- `simp` cannot remove; both sides are the same structure up to associativity
  simp only [PartialMap.comp, PartialMap.compHom, Category.assoc]

/-- Composing a composite of rational maps with a morphism. -/
@[simp]
theorem RationalMap.comp_compHom (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) (h : Z ⟶ W) :
    (f.comp g).compHom h = f.comp (g.compHom h) := by
  obtain ⟨g, rfl⟩ := g.exists_rep
  rw [← compHom_toRationalMap, comp_def, comp_def, ← compHom_toRationalMap,
    PartialMap.comp_compHom]

/-- The composite of the representatives of `f` and `g` represents `f.comp g`. -/
theorem RationalMap.toRationalMap_representative_comp_representative (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ Z) : (f.representative.comp g.representative).toRationalMap = f.comp g := by
  rw [← RationalMap.comp_def, g.toRationalMap_representative]

end AlgebraicGeometry.Scheme
