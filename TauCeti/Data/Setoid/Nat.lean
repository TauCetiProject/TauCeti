/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Congruence modulo `k + 1` as a kernel

Congruence modulo `k + 1` on `ℕ` is the kernel `Setoid.ker (Fin.ofNat (k + 1))` of reduction into
`Fin (k + 1)`. This file counts its classes and their elements.

## Main results

* `Setoid.infinite_setOf_ker_finOfNat`: every class of congruence modulo `k + 1` is infinite.
* `Setoid.enatCard_quotient_ker_finOfNat`: congruence modulo `k + 1` has `k + 1` classes.
-/

public section

namespace Setoid

/-- Congruence modulo `k + 1` on `ℕ` has infinite classes. -/
theorem infinite_setOf_ker_finOfNat (k x : ℕ) :
    {x' | ker (Fin.ofNat (k + 1)) x x'}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => x + (k + 1) * t)
    (fun a b h => by simpa using h) fun t => ?_
  simp [ker_def, Fin.ext_iff]

/-- Congruence modulo `k + 1` on `ℕ` has `k + 1` classes. -/
theorem enatCard_quotient_ker_finOfNat (k : ℕ) :
    ENat.card (Quotient (ker (Fin.ofNat (k + 1)))) = k + 1 := by
  rw [ENat.card_congr (quotientKerEquivOfSurjective (Fin.ofNat (k + 1))
    fun j => ⟨j, Fin.ofNat_val_eq_self j⟩)]
  simp

end Setoid
