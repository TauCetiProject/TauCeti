/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Multiplicative maps applied entrywise

A multiplicative map applied entrywise to a scalar multiple `c • v` of a family gives
`f c • (f ∘ v)`. This is the scalar companion of Mathlib's `map_comp_mul` and `map_comp_pow`.

## Main results

* `TauCeti.map_comp_smul`: `f ∘ (c • v) = f c • (f ∘ v)`.
-/

public section

namespace TauCeti

/-- A multiplicative map applied entrywise to `c • v` gives `f c • (f ∘ v)`. -/
@[simp]
theorem map_comp_smul {F M N ι : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (c : M) (v : ι → M) : f ∘ (c • v) = f c • (f ∘ v) :=
  funext fun _ ↦ map_mul f _ _

end TauCeti
