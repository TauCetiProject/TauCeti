/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-!
# Composition with linear functionals on division semirings

A nonzero linear functional with values in a division semiring is surjective. Consequently,
composing it, after restriction of scalars, with any nonzero semilinear map gives a nonzero map.
This applies in particular to compositions of transfer functionals in a tower of field extensions.
-/

public section

namespace LinearMap

variable {K K' L E M : Type*} [Semiring K] [Semiring K'] [DivisionSemiring L]
  [AddCommMonoid E] [AddCommMonoid M] [Module K L] [Module K E] [Module L E]
  [Module K' M] [CompatibleSMul E L K L] {σ : K →+* K'}

/-- Composing a nonzero semilinear map with a nonzero linear functional on a division semiring,
after restricting scalars, gives a nonzero map. -/
theorem comp_restrictScalars_ne_zero (s : L →ₛₗ[σ] M) (t : E →ₗ[L] L)
    (hs : s ≠ 0) (ht : t ≠ 0) : s.comp (t.restrictScalars K) ≠ 0 := by
  simpa using (Function.Surjective.injective_linearMapComp_right (g := t.restrictScalars K)
    (t.surjective ht)).ne hs

end LinearMap
