/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic

/-!
# The Atkin–Lehner normalizing constant

The raw weight-`k` slash by an Atkin–Lehner matrix for a divisor `Q` of the level is not an
involution: the matrix squares to `Q` times an element of `Γ₀(N)`, so the slash squares to the
scalar `Q ^ (k - 2)`. The **arithmetic normalization** divides that away by multiplying the slash
by

`atkinLehnerNormalizer Q k = (√Q) ^ (2 - k)`,

whose square is `Q ^ (2 - k)` (`TauCeti.atkinLehnerNormalizer_sq`). The constant depends only on
the divisor and the weight, so it is isolated here, away from any modular form: the Fricke
operator — the member `Q = N` of the Atkin–Lehner family — is normalized by it just as the general
`𝒲_Q` is.

The square root is taken in `ℝ` and cast to `ℂ`, rather than as a complex power, so that no branch
of `(·) ^ (2 - k)` has to be chosen.

## Main definitions

* `TauCeti.atkinLehnerNormalizer`: the constant `(√Q) ^ (2 - k)`.

## Main results

* `TauCeti.atkinLehnerNormalizer_sq`: it squares to `Q ^ (2 - k)`.
* `TauCeti.atkinLehnerNormalizer_sq_mul`: consequently it cancels the scalar `Q ^ (k - 2)` that
  the raw slash squares to.
* `TauCeti.atkinLehnerNormalizer_mul`: it is multiplicative in the divisor, which is what makes
  the normalized operators multiply the way the raw ones do.
* `TauCeti.atkinLehnerNormalizer_one`: at `Q = 1` it is `1`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
-/

public section

namespace TauCeti

variable {Q : ℕ}

/-- The constant `(√Q) ^ (2 - k)` by which the raw Atkin–Lehner slash for the divisor `Q` is
multiplied, so that the normalized operator squares to `1` rather than to `Q ^ (k - 2)`. -/
noncomputable def atkinLehnerNormalizer (Q : ℕ) (k : ℤ) : ℂ :=
  ((Real.sqrt Q : ℝ) : ℂ) ^ (2 - k)

/-- Defining equation for `atkinLehnerNormalizer`. The definition is `public` but is not marked
`@[expose]`, so a downstream module rewrites with this rather than unfolding the body. -/
theorem atkinLehnerNormalizer_def (Q : ℕ) (k : ℤ) :
    atkinLehnerNormalizer Q k = ((Real.sqrt Q : ℝ) : ℂ) ^ (2 - k) := (rfl)

/-- `√Q` is nonzero in `ℂ` for `Q ≠ 0`, the base of `atkinLehnerNormalizer`. Both facts this file
needs about the constant — that it is invertible, and that it squares to `Q ^ (2 - k)` — rest on
this. -/
private theorem ofReal_sqrt_natCast_ne_zero (hQ : Q ≠ 0) : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ))

/-- `atkinLehnerNormalizer Q k` is nonzero, which is what makes the normalized operator a
bijection and lets the normalization be undone. -/
theorem atkinLehnerNormalizer_ne_zero (hQ : Q ≠ 0) (k : ℤ) : atkinLehnerNormalizer Q k ≠ 0 :=
  zpow_ne_zero _ (ofReal_sqrt_natCast_ne_zero hQ)

/-- **The normalizer squares to `Q ^ (2 - k)`.** -/
theorem atkinLehnerNormalizer_sq (hQ : Q ≠ 0) (k : ℤ) :
    atkinLehnerNormalizer Q k ^ 2 = (Q : ℂ) ^ (2 - k) := by
  have hs : (Q : ℂ) = ((Real.sqrt Q : ℝ) : ℂ) ^ (2 : ℤ) := by
    rw [zpow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg Q),
      Complex.ofReal_natCast]
  rw [atkinLehnerNormalizer_def, hs, ← zpow_mul, pow_two,
    ← zpow_add₀ (ofReal_sqrt_natCast_ne_zero hQ), two_mul]

/-- **The normalization cancels the scalar the raw slash squares to.** Multiplying
`Q ^ (k - 2)` by the square of the normalizer leaves `1`; this single identity is the whole
arithmetic content of the normalization. -/
theorem atkinLehnerNormalizer_sq_mul (hQ : Q ≠ 0) (k : ℤ) :
    atkinLehnerNormalizer Q k ^ 2 * (Q : ℂ) ^ (k - 2) = 1 := by
  have hQ' : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  rw [atkinLehnerNormalizer_sq hQ, ← zpow_add₀ hQ']
  simp

/-- **The normalizer is multiplicative in the divisor**, because the square root is: `√(Q R)` is
`√Q · √R`. This is what lets the composition law of the Atkin–Lehner operators be read off from
the composition law of the raw slashes. -/
theorem atkinLehnerNormalizer_mul (Q R : ℕ) (k : ℤ) :
    atkinLehnerNormalizer (Q * R) k = atkinLehnerNormalizer Q k * atkinLehnerNormalizer R k := by
  rw [atkinLehnerNormalizer_def, atkinLehnerNormalizer_def, atkinLehnerNormalizer_def,
    ← mul_zpow]
  norm_cast
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg Q)]

/-- **At `Q = 1` the normalizer is `1`**, matching the raw slash by an element of `Γ₀(N)` being
the identity. -/
@[simp]
theorem atkinLehnerNormalizer_one (k : ℤ) : atkinLehnerNormalizer 1 k = 1 := by
  rw [atkinLehnerNormalizer_def]
  simp

end TauCeti
