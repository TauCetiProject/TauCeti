/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# The dominant diagonal torus submonoid for a valuation

Given a valuation `v : Valuation R Γ₀` and a preordered index type `m`, the dominant diagonal
torus `TauCeti.dominantTorus m v` is the submonoid of `m → Rˣ` consisting of diagonal tuples `t`
whose entry valuations are monotone (`i ≤ j → v (t i) ≤ v (t j)`). This submonoid `T⁺` is the
domain of the multiplicative `U_t` operator homomorphism on pro-`p` Iwahori invariants.

* `TauCeti.dominantTorus`: the submonoid `{t : m → Rˣ | Monotone fun i ↦ v (t i : R)}`.
* `TauCeti.mem_dominantTorus_iff`: membership characterization.

## References

* W. Casselman, *Introduction to admissible representations of p-adic groups: `GL_n`*, notes.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), file `src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` (`New.dominantTorus`).
-/

public section

namespace TauCeti

variable (m : Type*) [Preorder m] {R Γ₀ : Type*} [Ring R]
  [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- The submonoid of diagonal tuples `t : m → Rˣ` whose valuations are monotone in the index:
`i ≤ j → v (t i : R) ≤ v (t j : R)`. -/
def dominantTorus : Submonoid (m → Rˣ) where
  carrier := {t | Monotone fun i ↦ v (t i : R)}
  one_mem' _ _ _ := le_rfl
  mul_mem' ht ht' _ _ hij := by
    simpa [map_mul] using mul_le_mul' (ht hij) (ht' hij)

@[simp]
theorem mem_dominantTorus_iff {t : m → Rˣ} :
    t ∈ dominantTorus m v ↔ Monotone fun i ↦ v (t i : R) :=
  Iff.rfl

end TauCeti
