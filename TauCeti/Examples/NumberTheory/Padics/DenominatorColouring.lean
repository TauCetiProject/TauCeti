/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.DenominatorColouring

/-!
# Checks for the dense colouring of the rationals

Colour a rational `r` by `ν r = multiplicity 2 r.den`, the exponent of `2` in its reduced
denominator. These checks cover:

* the values `ν (3/4) = 2`, `ν 5 = 0`, `ν (-1/6) = 1`, and `1/8008`, with `8008 = 8 · 1001`, a
  rational of colour `3` in `(0, 1/1000)`;
* the coloured Cantor theorem for the identity permutation, where `π = id` works, and for the
  transposition of `0` and `1`, where `π` must send `1/2`, of colour `1`, to a rational of
  colour `0`;
* density of the colour classes is needed: for the two-colouring "negative or not", no order
  automorphism of `ℚ` swaps the two colours, since the negatives form an initial segment.
-/

public section

namespace TauCeti.Examples.DenominatorColouring

/-- The colour of a rational: the exponent of `2` in its reduced denominator. -/
noncomputable abbrev ν (r : ℚ) : ℕ := multiplicity 2 r.den

private theorem multiplicity_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) :
    multiplicity 2 (2 ^ k * m) = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.multiplicity_mul (by positivity) (by rintro rfl; simp at hm),
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]

example : ν (3 / 4) = 2 := by
  have h : (3 / 4 : ℚ).den = 2 ^ 2 * 1 := by decide +kernel
  rw [ν, h, multiplicity_two_pow_mul_odd _ _ (by decide)]

example : ν 5 = 0 := by
  simp [ν]

example : ν (-1 / 6) = 1 := by
  have h : (-1 / 6 : ℚ).den = 2 ^ 1 * 3 := by decide +kernel
  rw [ν, h, multiplicity_two_pow_mul_odd _ _ (by decide)]

example : ν (1 / 8008) = 3 ∧ 0 < (1 / 8008 : ℚ) ∧ (1 / 8008 : ℚ) < 1 / 1000 := by
  have h : (1 / 8008 : ℚ).den = 2 ^ 3 * 1001 := by decide +kernel
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [ν, h, multiplicity_two_pow_mul_odd _ _ (by decide)]

/-! ### The coloured Cantor theorem -/

-- For the identity permutation, the identity order automorphism realizes it.
example : ∀ r, ν ((OrderIso.refl ℚ) r) = (Equiv.refl ℕ) (ν r) := fun _ => rfl

-- For the transposition of the colours `0` and `1`, every realizing automorphism sends `1/2`, of
-- colour `1`, to a rational of colour `0`.
example (π : ℚ ≃o ℚ) (hπ : ∀ r, ν (π r) = Equiv.swap 0 1 (ν r)) : ν (π (1 / 2)) = 0 := by
  have h : (1 / 2 : ℚ).den = 2 ^ 1 * 1 := by decide +kernel
  rw [hπ, ν, h, multiplicity_two_pow_mul_odd _ _ (by decide), Equiv.swap_apply_right]

-- The coloured Cantor theorem applies to the transposition.
example : ∃ π : ℚ ≃o ℚ, ∀ r, ν (π r) = Equiv.swap 0 1 (ν r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Rat.exists_orderIso_multiplicity_den_eq _

/-! ### Density of the colour classes is needed -/

-- For the colouring by "negative or not", no order automorphism swaps the two colours: the
-- negatives form an initial segment, and so does their image.
example : ¬ ∃ π : ℚ ≃o ℚ, ∀ r, (if π r < 0 then 0 else 1) = Equiv.swap 0 1
    (if r < 0 then 0 else 1 : ℕ) := by
  rintro ⟨π, hπ⟩
  have h₁ := hπ (-1)
  have h₀ := hπ 0
  by_cases hn : π (-1) < 0 <;> by_cases hz : π 0 < 0 <;>
    simp_all [Equiv.swap_apply_left, Equiv.swap_apply_right]
  linarith [π.lt_iff_lt.2 (show (-1 : ℚ) < 0 by norm_num)]

end TauCeti.Examples.DenominatorColouring
