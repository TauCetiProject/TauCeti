/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.LinearCombination

/-!
# Square roots of unipotent elements

Let `R` be a commutative ring in which `2` is a unit, and let `x` be a nilpotent element of an
`R`-algebra `A`, which need not be commutative. Then `1 + x` is the square of a polynomial
expression in `x` with coefficients in `R`. Because the square root is a polynomial in `x`, it
commutes with everything that commutes with `x`, and it is compatible with any relation of the
form `a * x = y * a`: then `a * q(x) = q(y) * a` (`SemiconjBy.smeval_right`, with
`Polynomial.aeval_eq_smeval`). This is what makes it usable for congruences of Gram matrices,
where the relevant `x` is self-adjoint for a bilinear form.

The polynomial is obtained by successive approximation in `R[X]`: if `q ≡ 1 (mod X)` and
`q ^ 2 ≡ 1 + X (mod X^{k+1})`, then the correction `q - ½ X^{k+1} e` by the error term `e` is a
square root of `1 + X` modulo `X^{k+2}`. Evaluating at `x` kills the error once `x^{k+1} = 0`.
Mathlib's Newton iteration `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero` produces roots
in a commutative algebra; here the algebra is not commutative, and the point is that the square
root is a polynomial in `x`.

## Main results

* `IsNilpotent.exists_aeval_sq_eq_one_add`: if `2` is a unit of `R` and `x` is nilpotent, then
  `(aeval x q) ^ 2 = 1 + x` for some `q : R[X]`.
-/

public section

open Polynomial

namespace IsNilpotent

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The successive approximations of a square root of `1 + X`: for every `k` there are `q ≡ 1`
modulo `X` and `e` with `q ^ 2 = 1 + X + X^{k+1} e`. -/
private theorem exists_sq_eq_one_add_X_add_X_pow_mul (h2 : IsUnit (2 : R)) (k : ℕ) :
    ∃ q e s : R[X], q ^ 2 = 1 + X + X ^ (k + 1) * e ∧ q = 1 + X * s := by
  induction k with
  | zero => exact ⟨1, -1, 0, by ring, by ring⟩
  | succ k ih =>
    obtain ⟨q, e, s, hq, hs⟩ := ih
    obtain ⟨c, hc⟩ : ∃ c : R, c * 2 = 1 := ⟨↑h2.unit⁻¹, h2.val_inv_mul⟩
    have hc' : C c * 2 = 1 := by rw [← map_ofNat C 2, ← C_mul, hc, C_1]
    refine ⟨q - C c * X ^ (k + 1) * e, -(e * s) + C c ^ 2 * X ^ k * e ^ 2,
      s - C c * X ^ k * e, ?_, ?_⟩
    · linear_combination hq + (-(X ^ (k + 1) * e * q)) * hc' + (-(X ^ (k + 1) * e)) * hs
    · linear_combination hs

/-- **Square roots of unipotent elements.** If `2` is a unit of `R` and `x` is a nilpotent element
of an `R`-algebra, then `1 + x` is the square of a polynomial in `x`. -/
theorem exists_aeval_sq_eq_one_add (h2 : IsUnit (2 : R)) {x : A} (hx : IsNilpotent x) :
    ∃ q : R[X], aeval x q ^ 2 = 1 + x := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨q, e, -, hq, -⟩ := exists_sq_eq_one_add_X_add_X_pow_mul h2 k
  exact ⟨q, by simpa [_root_.pow_succ x, hk] using congrArg (aeval x) hq⟩

end IsNilpotent
