/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace

/-!
# Basic properties of the character space of a topological algebra

Every element of Mathlib's `WeakDual.characterSpace 𝕜 A` is by definition a nonzero multiplicative
functional in `WeakDual 𝕜 A`, hence takes a nonzero value at some element of `A`
(`WeakDual.CharacterSpace.exists_ne_zero`).
-/

public section

namespace WeakDual.CharacterSpace

/-- Every character in `characterSpace 𝕜 A` is nonzero at some element of `A`. -/
theorem exists_ne_zero {𝕜 A : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A]
    (χ : characterSpace 𝕜 A) : ∃ a : A, χ a ≠ 0 :=
  ContinuousLinearMap.exists_ne_zero (f := toCLM χ) fun h ↦
    χ.prop.1 (WeakDual.toStrongDual.injective h)

end WeakDual.CharacterSpace
