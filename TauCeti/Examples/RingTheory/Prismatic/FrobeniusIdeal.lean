/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.Expand
import TauCeti.RingTheory.Prismatic.FrobeniusIdeal

/-!
# Checks for the Frobenius ideals `I_r`

The ideals `I_r = ∏_{s < r} φ^s(I) A` start with `I_0 = A` and `I_1 = I`. For `φ = id` and
`I = (p)` (as for the crystalline prism `(ℤ_p, (p))`), `I_r = (p ^ r)`. On a `δ`-ring with
`δ(q) = 0`, the ideal `I = ([p]_q)` has `I_r = ([p ^ r]_q)`. In `ℤ[X]` with the Frobenius lift
`X ↦ X ^ 2` and `q = X`, this reads `I_2 = ((1 + X)(1 + X ^ 2)) = (1 + X + X ^ 2 + X ^ 3)`, and
`[4]_X - 2 [2]_X = (1 + X) ^ 2 (X - 1)` lies in `I_1 ^ 2`.
-/

open Ideal Finset Polynomial TauCeti.QCrys TauCeti.Prismatic.BKTwist

namespace TauCeti.FrobeniusIdealChecks

variable {A : Type*} [CommRing A]

/-- `I_0 = A` and `I_1 = I`. -/
example (φ : A →+* A) (I : Ideal A) : Ir φ I 0 = ⊤ ∧ Ir φ I 1 = I := by
  simp

/-- For `φ = id` and `I = (p)`, `I_r = (p ^ r)`. -/
example (p r : ℕ) : Ir (RingHom.id A) (span {(p : A)}) r = span {(p : A) ^ r} := by
  simp

/-- On a `δ`-ring with `δ(q) = 0`, the ideal `I = ([p]_q)` has `I_r = ([p ^ r]_q)`. -/
example (p : ℕ) [Fact p.Prime] [DeltaRing p A] {q : A} (hq : DeltaRing.delta p q = 0) (r : ℕ) :
    Ir (DeltaRing.frobenius p A) (span {qInteger q p}) r = span {qInteger q (p ^ r)} :=
  Ir_span_qInteger (DeltaRing.frobenius_apply_of_delta_eq_zero hq) r

/-- In `ℤ[X]` with `φ(X) = X ^ 2` and `q = X`, `I_2 = (1 + X + X ^ 2 + X ^ 3)` for `I = (1 + X)`. -/
example : Ir (expand ℤ 2 : ℤ[X] →+* ℤ[X]) (span {1 + X}) 2 = span {1 + X + X ^ 2 + X ^ 3} := by
  simpa [qInteger_eq_sum, sum_range_succ, add_assoc] using
    Ir_span_qInteger (φ := (expand ℤ 2 : ℤ[X] →+* ℤ[X])) (q := X) (p := 2) (by simp) 2

/-- In `ℤ[X]` with `φ(X) = X ^ 2` and `I = (1 + X)`, `[4]_X - 2 [2]_X ∈ I_1 ^ 2`. -/
example : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) - 2 * (1 + X) ∈ span {(1 + X : ℤ[X])} ^ 2 := by
  simpa [qInteger_eq_sum, sum_range_succ, add_assoc] using
    qInteger_pow_succ_sub_mem_Ir_sq (φ := (expand ℤ 2 : ℤ[X] →+* ℤ[X])) (q := X) (p := 2)
      (by simp) 1

end TauCeti.FrobeniusIdealChecks
