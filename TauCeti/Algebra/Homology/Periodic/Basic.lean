/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Data.ZMod.Defs

/-!
# Two-periodic complexes

A two-periodic complex is a homological complex indexed by `ZMod 2`, typically for the shape
`ComplexShape.up (ZMod 2)`. Its morphisms are determined by their components in degrees `0`
and `1`.
-/

public section

universe v u

open CategoryTheory Limits

namespace HomologicalComplex

/-- Morphisms of complexes indexed by `ZMod 2` are determined by their components in degrees `0`
and `1`. -/
theorem hom_ext_two {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {c : ComplexShape (ZMod 2)}
    {K L : HomologicalComplex C c} {f g : K ⟶ L} (h₀ : f.f 0 = g.f 0) (h₁ : f.f 1 = g.f 1) :
    f = g := by
  ext i
  match i with
  | 0 => exact h₀
  | 1 => exact h₁

end HomologicalComplex
