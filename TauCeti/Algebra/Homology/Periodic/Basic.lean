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

A two-periodic complex is a homological complex for `ComplexShape.up (ZMod 2)`. Its morphisms
are determined by their components in degrees `0` and `1`.
-/

public section

universe v u

namespace TauCeti

open CategoryTheory Limits

namespace HomologicalComplex

/-- Morphisms of two-periodic complexes are determined by their components in degrees `0`
and `1`. -/
theorem hom_ext_two {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {K L : _root_.HomologicalComplex C (ComplexShape.up (ZMod 2))} {f g : K ⟶ L}
    (h₀ : f.f 0 = g.f 0) (h₁ : f.f 1 = g.f 1) : f = g := by
  ext i
  match i with
  | 0 => exact h₀
  | 1 => exact h₁

end HomologicalComplex

end TauCeti
