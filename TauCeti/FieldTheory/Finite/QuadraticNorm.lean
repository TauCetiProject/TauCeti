/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.FieldTheory.Finite.PowNeOne

/-!
# The quadratic norm `b ↦ b ^ q * b` over a field with `q²` elements

Let `K` be a finite field with `q²` elements. When `3 ≤ q`, `q² - 1 > q + 1`, so some element
`b ∈ Kˣ` satisfies `b ^ (q + 1) ≠ 1`. Its quadratic norm `c = b ^ q * b = b ^ (q + 1)` is fixed by
`x ↦ x ^ q` and is distinct from `0` and `1`, which supplies the `|𝔽_q| ≥ 3` condition (excluding
`SU₃(2)`) for the finite unitary groups `SU_{r+1}(q)` / `²A_r(q)`.

## Main results

* `TauCeti.FiniteField.exists_pow_eq_self_and_ne_zero_and_ne_one`: when `3 ≤ q`, some `c` satisfies
  `c ^ q = c`, `c ≠ 0`, and `c ≠ 1`.

## References

Surjectivity of the quadratic norm for an explicit `Algebra` structure is Mathlib's
`FiniteField.norm_surjective`; the additive trace companion is
`TauCeti.FieldTheory.Finite.PowAddSelf`.
-/

public section

namespace TauCeti.FiniteField

variable {K : Type*} [Field K]

/-- In a field with `q²` elements and `3 ≤ q`, some element `c` satisfies `c ^ q = c`, `c ≠ 0`,
and `c ≠ 1`. -/
theorem exists_pow_eq_self_and_ne_zero_and_ne_one {q : ℕ} (hq : 3 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ c : K, c ^ q = c ∧ c ≠ 0 ∧ c ≠ 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let := Fintype.ofFinite K
  obtain ⟨b, hb0, hb1⟩ := exists_ne_zero_pow_ne_one (F := K) (k := q + 1) (by omega)
    (by rw [hK]; nlinarith)
  refine ⟨b ^ q * b, ?_, mul_ne_zero (pow_ne_zero q hb0) hb0, by rwa [← pow_succ]⟩
  rw [mul_pow, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, _root_.FiniteField.pow_card,
    mul_comm]

end TauCeti.FiniteField
