/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Length of a thickened polynomial point

For an irreducible polynomial `f` over a field, the algebra `k[X]/(fⁿ)` has length `n`
as a module over itself, not its dimension `n * natDegree f` over `k`.
This computation retains the multiplicity of a nonreduced point in a fibre.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.1 (divisor multiplicities).
-/

public section

open Polynomial

namespace AdjoinRoot

/-- The length of `k[X]/(fⁿ)` at an irreducible polynomial `f` is `n`. -/
@[simp]
theorem length_pow {k : Type*} [Field k] {f : k[X]} (hf : Irreducible f) (n : ℕ) :
    Module.length (AdjoinRoot (f ^ n)) (AdjoinRoot (f ^ n)) = n := by
  -- Use the quotient's polynomial action, rather than its usual coefficient action.
  let := (AdjoinRoot.mk (f ^ n)).toAlgebra
  -- `AdjoinRoot` is the quotient by the principal ideal defining `Ring.ord`.
  have hlen : Module.length k[X] (AdjoinRoot (f ^ n)) = Ring.ord k[X] (f ^ n) := rfl
  rw [← Module.length_eq_of_surjective (M := AdjoinRoot (f ^ n))
    (S := k[X]) (by exact AdjoinRoot.mk_surjective), hlen,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hf.ne_zero),
    Ring.ord_of_irreducible hf]
  simp

end AdjoinRoot
