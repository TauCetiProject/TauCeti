/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Componentwise arithmetic along an idempotent

An idempotent `e` of a commutative ring `R` splits it as `R ≅ e R × (1 - e) R`. Without reference
to the product decomposition, an element `e x + (1 - e) y` has `e`-component `e x` and
`(1 - e)`-component `(1 - e) y`, and since `e² = e` and `e (1 - e) = 0` such elements multiply
componentwise.

For an idempotent `p` of any ring, `2 p - 1` squares to `1`. For a star projection this is the
self-adjoint unitary `IsStarProjection.two_mul_sub_one_mem_unitary`. Conversely, for any element
`u` with `u * u = 1`, `1 + u` squares to `(1 + u) + (1 + u)`, and when `v` anticommutes with `u`
(`u * v + v * u = 0`), the sandwich `(1 + u) * (1 + v) * (1 + u)` also reduces to
`(1 + u) + (1 + u)`.

The cubic analogue: for `u ^ 3 = 1`, `1 + u + u ^ 2` squares to `3 * (1 + u + u ^ 2)`, and when
`v` commutes with `u` up to a scalar `c` with `1 + c + c ^ 2 = 0` (a primitive cube root of unity,
`v * u = c • (u * v)`), the sandwich `(1 + u + u ^ 2) * (1 + v + v ^ 2) * (1 + u + u ^ 2)` also
reduces to `3 * (1 + u + u ^ 2)`. These are the Temperley–Lieb relations at loop value `√3` for the
projections `3⁻¹ • (1 + u + u ^ 2)` built from the generators of a cubic quantum torus.

## Main results

* `IsIdempotentElem.mul_add_one_sub_mul`: elements of the form `e x + (1 - e) y` multiply
  componentwise.
* `IsIdempotentElem.two_mul_sub_one_mul_self`: `(2 p - 1) * (2 p - 1) = 1`.
* `IsIdempotentElem.compress_sub_compress_mul_compress`:
  `p x p - (p y p)(p z p) = p (x - y z) p + p y (1 - p) · (1 - p) z p`.
* `IsIdempotentElem.one_sub_mul_mul_sub_smul_sub`,
  `IsIdempotentElem.one_sub_mul_mul_sub_smul_eq`: replacing balanced idempotents `p, q` by
  `1 - p, 1 - q` negates the balanced defect and preserves the balanced relation.
* `TauCeti.one_add_mul_self_of_mul_self_eq_one`: if `u * u = 1`, then
  `(1 + u) * (1 + u) = (1 + u) + (1 + u)`.
* `TauCeti.one_add_mul_one_add_mul_one_add_of_mul_self_eq_one`: if `u * u = 1` and
  `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u)`.
* `TauCeti.one_add_add_sq_mul_of_pow_three_eq_one` and
  `TauCeti.one_add_add_sq_mul_sq_of_pow_three_eq_one`: if `u ^ 3 = 1`, then right multiplication
  by `u` and by `u ^ 2` fixes `1 + u + u ^ 2`.
* `TauCeti.one_add_add_sq_mul_self_of_pow_three_eq_one`: if `u ^ 3 = 1`, then
  `(1 + u + u ^ 2) * (1 + u + u ^ 2) = 3 * (1 + u + u ^ 2)`.
* `TauCeti.one_add_add_sq_mul_one_add_add_sq_mul_one_add_add_sq_of_pow_three_eq_one`: if
  `u ^ 3 = 1`, `v * u = c • (u * v)` and `1 + c + c ^ 2 = 0`, then
  `(1 + u + u ^ 2) * (1 + v + v ^ 2) * (1 + u + u ^ 2) = 3 * (1 + u + u ^ 2)`.
-/

public section

namespace IsIdempotentElem

section CommRing

variable {R : Type*} [CommRing R] {e : R}

/-- **Componentwise multiplication**: for an idempotent `e` of a commutative ring, elements of the
form `e x + (1 - e) y` multiply componentwise, as they would in `e R × (1 - e) R`. -/
theorem mul_add_one_sub_mul (he : IsIdempotentElem e) (x y x' y' : R) :
    (e * x + (1 - e) * y) * (e * x' + (1 - e) * y') = e * (x * x') + (1 - e) * (y * y') := by
  linear_combination (x * x' - x * y' - y * x' + y * y') * he.eq

end CommRing

section Ring

variable {R : Type*} [Ring R] {p : R}

/-- For an idempotent `p`, `2 p - 1` squares to `1`. -/
theorem two_mul_sub_one_mul_self (hp : IsIdempotentElem p) : (2 * p - 1) * (2 * p - 1) = 1 := by
  simp only [two_mul, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hp.eq]
  abel

/-- **Compressing a product by an idempotent.** For an idempotent `p`, the compression of `x`
differs from the product of the compressions of `y` and `z` by the compression of `x - y z` plus
the cross term through `1 - p`:
`p x p - (p y p)(p z p) = p (x - y z) p + p y (1 - p) · (1 - p) z p`. -/
theorem compress_sub_compress_mul_compress (hp : IsIdempotentElem p) (x y z : R) :
    p * x * p - p * y * p * (p * z * p) =
      p * (x - y * z) * p + p * y * (1 - p) * ((1 - p) * z * p) := by
  have hp' (w : R) : p * (p * w) = p * w := by rw [← mul_assoc, hp.eq]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hp']
  abel

end Ring

section Balanced

variable {S A : Type*} [Ring S] [Ring A] [Module S A] {t : S} {p q : A}

/-- Replacing idempotents `p` and `q` by `1 - p` and `1 - q` negates their balanced defect. -/
theorem one_sub_mul_mul_sub_smul_sub (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    ((1 - p) * (1 - q) * (1 - p) - t • (1 - p)) -
        ((1 - q) * (1 - p) * (1 - q) - t • (1 - q)) =
      -((p * q * p - t • p) - (q * p * q - t • q)) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hp.eq, hq.eq, smul_sub]
  abel

/-- If idempotents `p` and `q` satisfy the balanced relation with parameter `t`, so do `1 - p` and
`1 - q`. -/
theorem one_sub_mul_mul_sub_smul_eq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : p * q * p - t • p = q * p * q - t • q) :
    (1 - p) * (1 - q) * (1 - p) - t • (1 - p) = (1 - q) * (1 - p) * (1 - q) - t • (1 - q) :=
  sub_eq_zero.mp <| by rw [hp.one_sub_mul_mul_sub_smul_sub hq, sub_eq_zero.mpr h, neg_zero]

end Balanced

end IsIdempotentElem

namespace TauCeti

/-- If `u * u = 1`, then `1 + u` squares to `(1 + u) + (1 + u)` (so after dividing by `2`,
`2⁻¹ • (1 + u)` is idempotent). -/
theorem one_add_mul_self_of_mul_self_eq_one {R : Type*} [NonAssocSemiring R] {u : R}
    (hu : u * u = 1) :
    (1 + u) * (1 + u) = (1 + u) + (1 + u) := by
  rw [add_mul, one_mul, mul_add, mul_one, hu, add_comm u 1]

/-- If `u * u = 1` and `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u)` reduces to
`(1 + u) + (1 + u)`. -/
theorem one_add_mul_one_add_mul_one_add_of_mul_self_eq_one {R : Type*} [Semiring R] {u v : R}
    (hu : u * u = 1) (huv : u * v + v * u = 0) :
    (1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u) := by
  have hv : v + u * v * u = 0 :=
    calc
      v + u * v * u = 1 * v + u * (v * u) := by rw [one_mul, mul_assoc]
      _ = u * u * v + u * (v * u) := by rw [hu]
      _ = u * (u * v + v * u) := by rw [mul_assoc, mul_add]
      _ = 0 := by rw [huv, mul_zero]
  calc
    (1 + u) * (1 + v) * (1 + u)
        = ((1 + u) + (u + u * u)) + (u * v + v * u) + (v + u * v * u) := by
          simp only [add_mul, mul_add, one_mul, mul_one]
          ac_rfl
    _ = (1 + u) + (1 + u) := by
          rw [hu, huv, hv, add_zero, add_zero, add_comm u 1]

/-- If `u ^ 3 = 1`, then right multiplication by `u` fixes `1 + u + u ^ 2`. -/
theorem one_add_add_sq_mul_of_pow_three_eq_one {R : Type*} [Semiring R] {u : R}
    (hu : u ^ 3 = 1) : (1 + u + u ^ 2) * u = 1 + u + u ^ 2 := by
  rw [add_mul, add_mul, one_mul, ← pow_two, ← pow_succ, hu, add_comm _ (1 : R), add_assoc]

/-- If `u ^ 3 = 1`, then right multiplication by `u ^ 2` fixes `1 + u + u ^ 2`. -/
theorem one_add_add_sq_mul_sq_of_pow_three_eq_one {R : Type*} [Semiring R] {u : R}
    (hu : u ^ 3 = 1) : (1 + u + u ^ 2) * u ^ 2 = 1 + u + u ^ 2 := by
  rw [sq u, ← mul_assoc, ← sq, one_add_add_sq_mul_of_pow_three_eq_one hu,
    one_add_add_sq_mul_of_pow_three_eq_one hu]

/-- If `u ^ 3 = 1`, then `1 + u + u ^ 2` squares to `3 * (1 + u + u ^ 2)` (so after dividing by
`3`, `3⁻¹ • (1 + u + u ^ 2)` is idempotent). -/
theorem one_add_add_sq_mul_self_of_pow_three_eq_one {R : Type*} [Semiring R] {u : R}
    (hu : u ^ 3 = 1) :
    (1 + u + u ^ 2) * (1 + u + u ^ 2) = 3 * (1 + u + u ^ 2) := by
  rw [mul_add, mul_add, mul_one, one_add_add_sq_mul_of_pow_three_eq_one hu,
    one_add_add_sq_mul_sq_of_pow_three_eq_one hu, ← two_add_one_eq_three, add_mul, two_mul,
    one_mul]

/-- If `u ^ 3 = 1` and `v` commutes with `u` up to a scalar `c` with `1 + c + c ^ 2 = 0`
(`v * u = c • (u * v)`), then `(1 + u + u ^ 2) * (1 + v + v ^ 2) * (1 + u + u ^ 2)` reduces to
`3 * (1 + u + u ^ 2)`. -/
theorem one_add_add_sq_mul_one_add_add_sq_mul_one_add_add_sq_of_pow_three_eq_one {k A : Type*}
    [CommRing k] [Semiring A] [Algebra k A] {c : k} {u v : A} (hc : 1 + c + c ^ 2 = 0)
    (hu : u ^ 3 = 1) (hvu : v * u = c • (u * v)) :
    (1 + u + u ^ 2) * (1 + v + v ^ 2) * (1 + u + u ^ 2) = 3 * (1 + u + u ^ 2) := by
  -- Right multiplication by `u` fixes `1 + u + u ^ 2`, so it absorbs any `1 + a • u + b • u ^ 2`.
  have hSlin (a b : k) :
      (1 + u + u ^ 2) * (1 + a • u + b • u ^ 2) = (1 + a + b) • (1 + u + u ^ 2) := by
    rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, one_add_add_sq_mul_of_pow_three_eq_one hu,
      one_add_add_sq_mul_sq_of_pow_three_eq_one hu, mul_one, add_smul, add_smul, one_smul]
  -- Moving `v` to the right through `1 + a • u + b • u ^ 2` twists the coefficients by `c`.
  have hvu2 : v * u ^ 2 = c ^ 2 • (u ^ 2 * v) := by
    rw [sq u, sq c, ← mul_assoc, hvu, smul_mul_assoc, mul_assoc, hvu, mul_smul_comm, smul_smul,
      ← mul_assoc]
  have hvlin (a b : k) :
      v * (1 + a • u + b • u ^ 2) = (1 + (a * c) • u + (b * c ^ 2) • u ^ 2) * v := by
    rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, hvu, hvu2, add_mul, add_mul,
      smul_mul_assoc, smul_mul_assoc, smul_smul, smul_smul, mul_one, one_mul]
  have hvS : v * (1 + u + u ^ 2) = (1 + c • u + c ^ 2 • u ^ 2) * v := by
    simpa using hvlin 1 1
  have hv2S : v ^ 2 * (1 + u + u ^ 2) = (1 + c ^ 2 • u + c ^ 4 • u ^ 2) * v ^ 2 := by
    rw [sq v, mul_assoc, hvS, ← mul_assoc, hvlin, mul_assoc]
    congr 4 <;> ring
  have hc' : 1 + c ^ 2 + c ^ 4 = 0 := by linear_combination (c ^ 2 - c + 1) * hc
  have hSS := one_add_add_sq_mul_self_of_pow_three_eq_one hu
  set S := 1 + u + u ^ 2
  clear_value S
  calc S * (1 + v + v ^ 2) * S = S * S + S * (v * S) + S * (v ^ 2 * S) := by
        rw [mul_add, mul_add, mul_one, add_mul, add_mul, mul_assoc, mul_assoc]
    _ = 3 * S := by
        rw [hvS, hv2S, ← mul_assoc, ← mul_assoc, hSlin, hSlin, hc, hc', hSS]
        simp only [zero_smul, zero_mul, add_zero]

end TauCeti
