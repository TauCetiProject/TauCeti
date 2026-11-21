/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.Algebra.Polynomial.Expand

/-!
# Hasse derivatives of `q`-th powers over a finite field

Over a finite field `K` with `q` elements, the Hasse derivatives of `f ^ q` vanish at every
order not divisible by `q` (`Polynomial.hasseDeriv_pow_natCard_eq_zero` with `q = Nat.card K`,
and `Polynomial.hasseDeriv_pow_card_eq_zero` with `q = Fintype.card K`). In particular they vanish
at every order `k` with `0 < k < q`, since `Nat.not_dvd_of_pos_of_lt` shows that `q` does not
divide such a `k`. Mathlib's `FiniteField.card'` writes `q` as a power of the characteristic, which
reduces the claim to `Polynomial.hasseDeriv_pow_expChar_pow_eq_zero`.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- Over a finite field with `q = Nat.card K` elements, the Hasse derivatives of `f ^ q` vanish at
every order `k` not divisible by `q`, for instance at every `k` with `0 < k < q`. -/
@[simp]
theorem hasseDeriv_pow_natCard_eq_zero [Finite K] {k : ℕ} (hk : ¬Nat.card K ∣ k) (f : K[X]) :
    hasseDeriv k (f ^ Nat.card K) = 0 := by
  have := Fintype.ofFinite K
  -- Mathlib's `FiniteField.card'` writes `q` as a power `p ^ n` of the characteristic.
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_eq_fintype_card, hcard] at hk ⊢
  exact hasseDeriv_pow_expChar_pow_eq_zero hk f

/-- Over a finite field with `q = Fintype.card K` elements, the Hasse derivatives of `f ^ q` vanish
at every order `k` not divisible by `q`, for instance at every `k` with `0 < k < q`. -/
@[simp]
theorem hasseDeriv_pow_card_eq_zero [Fintype K] {k : ℕ} (hk : ¬Fintype.card K ∣ k) (f : K[X]) :
    hasseDeriv k (f ^ Fintype.card K) = 0 := by
  rw [← Nat.card_eq_fintype_card] at hk ⊢
  exact hasseDeriv_pow_natCard_eq_zero hk f

end Polynomial
