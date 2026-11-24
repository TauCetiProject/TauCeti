/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.LaurentSeries

/-!
# Transcendence of Laurent expansions of rational functions

The Laurent expansion at `0` of a nonconstant rational function `p ∈ K(X)` is transcendental over
`K` in `K⸨X⸩`: the embedding `K(X) → K⸨X⸩` is an injective `K`-algebra map, and `p` itself is
transcendental over `K` by `RatFunc.transcendental_of_ne_C`.

## Main results

* `RatFunc.transcendental_coe`: the Laurent expansion of a nonconstant rational function is
  transcendental over the constants.
-/

public section

open scoped LaurentSeries

namespace RatFunc

variable {K : Type*} [Field K]

/-- The Laurent expansion at `0` of a nonconstant rational function is transcendental over the
field of constants. -/
theorem transcendental_coe {p : RatFunc K} (hp : ¬∃ c, p = C c) :
    Transcendental K (p : K⸨X⸩) := by
  -- The embedding `K(X) → K⸨X⸩` is a `K`-algebra map, so it preserves algebraicity.
  let φ : RatFunc K →ₐ[K] K⸨X⸩ :=
    { algebraMap (RatFunc K) K⸨X⸩ with
      commutes' := fun c ↦ by
        simp [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply,
          HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply'] }
  exact fun h ↦ p.transcendental_of_ne_C hp
    ((isAlgebraic_algHom_iff φ φ.toRingHom.injective).mp h)

end RatFunc
