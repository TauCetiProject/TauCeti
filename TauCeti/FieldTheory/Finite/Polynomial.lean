/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Hasse derivatives of `q`-th powers over a finite field

Over a finite field `K` with `q` elements, the Hasse derivatives of `f ^ q` vanish at every
order not divisible by `q` (`Polynomial.hasseDeriv_pow_natCard_eq_zero` with `q = Nat.card K`,
and `Polynomial.hasseDeriv_pow_card_eq_zero` with `q = Fintype.card K`). The `Nat.card` form
also holds over an infinite field, where `Nat.card K = 0`. In particular they vanish
at every order `k` with `0 < k < q`, since `Nat.not_dvd_of_pos_of_lt` shows that `q` does not
divide such a `k`. Mathlib's `FiniteField.card'` writes `q` as a power of the characteristic, which
reduces the claim to `Polynomial.hasseDeriv_pow_expChar_pow_eq_zero`.

The polynomial `X ^ q ^ n - X` is separable for `n ≠ 0` over any commutative ring with `q`
elements (`Polynomial.separable_X_pow_card_pow_sub_X`).
-/

public section

namespace Polynomial

/-- `X ^ q ^ n - X` is separable over a commutative ring with `q` elements, for `n ≠ 0`: its
derivative is `q ^ n X ^ (q ^ n - 1) - 1 = -1` (Mathlib's `galois_poly_separable`). Over an
infinite ring, where `Nat.card R = 0`, the polynomial is `1 - X`, also separable. -/
theorem separable_X_pow_card_pow_sub_X {R : Type*} [CommRing R] {n : ℕ} (hn : n ≠ 0) :
    (X ^ Nat.card R ^ n - X : R[X]).Separable := by
  refine galois_poly_separable (ringChar R) _ (dvd_pow ?_ hn)
  rw [← CharP.cast_eq_zero_iff R, ← nsmul_one, card_nsmul_eq_zero']

variable {K : Type*} [Field K]

/-- Over a finite field with `q = Nat.card K` elements, the Hasse derivatives of `f ^ q` vanish at
every order `k` not divisible by `q`, for instance at every `k` with `0 < k < q`. The statement also
holds over an infinite field, where `Nat.card K = 0`, `k ≠ 0` and `f ^ 0 = 1`. -/
@[simp]
theorem hasseDeriv_pow_natCard_eq_zero {k : ℕ} (hk : ¬Nat.card K ∣ k) (f : K[X]) :
    hasseDeriv k (f ^ Nat.card K) = 0 := by
  cases finite_or_infinite K with
  | inl _ =>
    have := Fintype.ofFinite K
    -- Mathlib's `FiniteField.card'` writes `q` as a power `p ^ n` of the characteristic.
    obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' K
    have : Fact p.Prime := ⟨hp⟩
    rw [Nat.card_eq_fintype_card, hcard] at hk ⊢
    exact hasseDeriv_pow_expChar_pow_eq_zero hk f
  | inr _ =>
    rw [Nat.card_eq_zero_of_infinite, zero_dvd_iff] at hk
    rw [Nat.card_eq_zero_of_infinite, pow_zero, hasseDeriv_apply_one k (Nat.pos_of_ne_zero hk)]

/-- Over a finite field with `q = Fintype.card K` elements, the Hasse derivatives of `f ^ q` vanish
at every order `k` not divisible by `q`, for instance at every `k` with `0 < k < q`. -/
@[simp]
theorem hasseDeriv_pow_card_eq_zero [Fintype K] {k : ℕ} (hk : ¬Fintype.card K ∣ k) (f : K[X]) :
    hasseDeriv k (f ^ Fintype.card K) = 0 := by
  rw [← Nat.card_eq_fintype_card] at hk ⊢
  exact hasseDeriv_pow_natCard_eq_zero hk f

end Polynomial
