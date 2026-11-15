/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation

/-!
# The point Lie group

The point, modelled on its zero-dimensional normed vector space, is a Lie group at every
regularity over every nontrivially normed field. Its multiplication and inversion are constant.
Its Lie algebra consists only of the zero derivation.

## Main instances

* `LieGroup.punit`: the point is a Lie group at every regularity.
* `LeftInvariantDerivation.subsingleton_punit`: its Lie algebra has only one element.

## References

* `Mathlib.Geometry.Manifold.Algebra.LieGroup`, for the Lie-group regularity classes.
-/

public section

open scoped ContDiff Manifold

universe u v

/-- The unique group operations on a point are smooth at every regularity. -/
instance LieGroup.punit {𝕜 : Type u} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} :
    LieGroup 𝓘(𝕜, PUnit.{v + 1}) n PUnit.{v + 1} where
  contMDiff_mul := contMDiff_const
  contMDiff_inv := contMDiff_const

/-- The point Lie group has only the zero left-invariant derivation. -/
instance LeftInvariantDerivation.subsingleton_punit {𝕜 : Type u} [NontriviallyNormedField 𝕜] :
    Subsingleton (LeftInvariantDerivation 𝓘(𝕜, PUnit.{v + 1}) PUnit.{v + 1}) := by
  constructor
  intro D E
  apply LeftInvariantDerivation.ext
  intro f
  have hf : f = algebraMap 𝕜 C^∞⟮𝓘(𝕜, PUnit.{v + 1}), PUnit.{v + 1}; 𝕜⟯
      (f PUnit.unit) := by
    ext x
    cases x
    rfl
  rw [← LeftInvariantDerivation.coe_derivation, ← LeftInvariantDerivation.coe_derivation, hf]
  simp only [Derivation.map_algebraMap]
