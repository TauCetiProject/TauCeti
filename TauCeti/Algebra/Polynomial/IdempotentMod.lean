/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.LinearCombination

/-!
# Non-trivial idempotents modulo reducible separable polynomials

In any commutative ring `R`, a factorisation `a * b` into coprime non-units yields an element `p`
that is idempotent modulo `a * b` (`a * b ∣ p * p - p`) and such that neither `p` nor `1 - p` is
coprime to `a * b` (`IsCoprime.exists_idempotent_mod`).

Applying this to a separable, reducible non-unit polynomial `P : R[X]` gives an idempotent `p`
modulo `P` with neither `p` nor `1 - p` coprime to `P` (`Polynomial.exists_idempotent_mod`).

## Main results

* `IsCoprime.exists_idempotent_mod`: coprime non-units `a, b` in a commutative ring admit an
  idempotent `p` modulo `a * b` with neither `p` nor `1 - p` coprime to `a * b`.
* `Polynomial.exists_idempotent_mod`: a separable, reducible non-unit polynomial `P : R[X]` admits
  an idempotent `p` modulo `P` with neither `p` nor `1 - p` coprime to `P`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/Shimura/TraceFormula/MarkedDefiniteSums.lean (`exists_idempotent_mod`).
-/

public section

/-- In any commutative ring, if `a` and `b` are coprime non-units, there exists an element `p`
that is idempotent modulo `a * b` (`a * b ∣ p * p - p`) such that neither `p` nor `1 - p` is
coprime to `a * b`. -/
theorem IsCoprime.exists_idempotent_mod {R : Type*} [CommRing R] {a b : R}
    (hcop : IsCoprime a b) (ha : ¬IsUnit a) (hb : ¬IsUnit b) :
    ∃ p : R, a * b ∣ p * p - p ∧ ¬IsCoprime (a * b) p ∧ ¬IsCoprime (a * b) (1 - p) := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u * a, ⟨-u * v, by linear_combination u * a * huv⟩, ?_, ?_⟩
  · intro h
    exact ha (isCoprime_self.mp h.of_mul_left_left.of_mul_right_right)
  · intro h
    rw [← huv, add_sub_cancel_left] at h
    exact hb (isCoprime_self.mp h.of_mul_left_right.of_mul_right_right)

namespace Polynomial

/-- Every separable, reducible non-unit polynomial `P` over a commutative ring admits an idempotent
`p` modulo `P` (`P ∣ p * p - p`) such that neither `p` nor `1 - p` is coprime to `P`. -/
theorem exists_idempotent_mod {R : Type*} [CommRing R] {P : R[X]}
    (hsep : P.Separable) (hred : ¬Irreducible P) (hunit : ¬IsUnit P) :
    ∃ p : R[X], P ∣ p * p - p ∧ ¬IsCoprime P p ∧ ¬IsCoprime P (1 - p) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := (irreducible_or_factor hunit).resolve_left hred
  exact hsep.isCoprime.exists_idempotent_mod hA hB

end Polynomial
