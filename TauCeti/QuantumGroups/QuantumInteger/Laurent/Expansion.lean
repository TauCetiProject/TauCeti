/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Laurent.Basic

/-!
# The Laurent expansion of a quantum integer

The exponents of the symmetric quantum integer `[n]` run from `1 - n` to `n - 1`
in steps of two. Evaluating this Laurent polynomial gives a division-free formula
for the loop parameter `q + q⁻¹`, including at `q = ±1`.
-/

public section

open Finset LaurentPolynomial

namespace TauCeti

/-- The integral Laurent polynomial `[n]` is a sum of `n` monomials with coefficient one. -/
theorem laurentQuantumInteger_natCast_eq_sum (n : ℕ) :
    laurentQuantumInteger n = ∑ j ∈ range n, T (2 * (j : ℤ) + 1 - n) := by
  refine eq_of_forall_laurentEval_eq fun K _ u hu => ?_
  simpa only [laurentEval_laurentQuantumInteger hu, map_sum, laurentEval_T,
    Units.val_zpow_eq_zpow_val] using quantumInteger_natCast_eq_sum hu n

/-- At a unit of a commutative ring, the quantum integer at loop parameter `q + q⁻¹`
is the sum of the corresponding integer powers of `q`. -/
theorem qInt_add_inv_eq_sum {R : Type*} [CommRing R] (q : Rˣ) (n : ℕ) :
    qInt R (q + ↑q⁻¹) n = ∑ j ∈ range n, ↑(q ^ (2 * (j : ℤ) + 1 - n)) := by
  rw [qInt_add_inv_eq_laurentEval, laurentQuantumInteger_natCast_eq_sum, map_sum]
  simp only [laurentEval_T]

end TauCeti
