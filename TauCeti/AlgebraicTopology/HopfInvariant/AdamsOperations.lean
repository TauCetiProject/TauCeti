/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.NumberTheory.Multiplicity

/-!
# The Adams-operation argument for Hopf invariant one

Let `f : S⁴ʳ⁻¹ → S²ʳ` with `r ≥ 1` have mapping cone `C_f`. Its reduced complex K-group is free
abelian on two classes `x` and `y`: `y` comes from the top cell `S⁴ʳ`, and `x` restricts to a
generator of the reduced K-group of `S²ʳ`. The Hopf invariant `h` of `f` is defined by
`x² = h y`. The Adams operations `ψˢ` are additive, commute with one another, and act by
`ψˢ x = sʳ x + b_s y` and `ψˢ y = s²ʳ y` for integers `b_s`. Moreover `ψ² x ≡ x² (mod 2)`.

Adams and Atiyah deduce from these facts alone that `h` odd forces `r ∈ {1, 2, 4}`. This file
proves that deduction for an arbitrary abelian group carrying additive maps with these
properties. The K-theory of `C_f` and the Adams operations themselves are not constructed here.

* Comparing the `y`-coefficients of `ψˢ ψᵗ x = ψᵗ ψˢ x` gives
  `tʳ (tʳ - 1) b_s = sʳ (sʳ - 1) b_t` (`TauCeti.pow_mul_pow_sub_one_mul_eq_of_comm`).
* Reducing `ψ² x = 2ʳ x + b₂ y` modulo `2` gives `b₂ ≡ h`, so `b₂` is odd when `h` is.
* With `s = 2` and `t = 3`, `2ʳ` divides `3ʳ (3ʳ - 1) b₂` and is prime to `3ʳ b₂`, so
  `2ʳ ∣ 3ʳ - 1`. By `Nat.two_pow_dvd_three_pow_sub_one_iff` this happens for `r ≥ 1` only when
  `r ∈ {1, 2, 4}` (`TauCeti.eq_one_or_eq_two_or_eq_four_of_adamsOperations`).

## Main statements

* `TauCeti.pow_mul_pow_sub_one_mul_eq_of_comm`: the coefficient identity for two commuting
  operations.
* `TauCeti.eq_one_or_eq_two_or_eq_four_of_adamsOperations`: odd Hopf invariant forces
  `r ∈ {1, 2, 4}`.

## References

* J. F. Adams and M. F. Atiyah, *K-theory and the Hopf invariant*, Quart. J. Math. Oxford (2) 17
  (1966), 31–38.
* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017), §2.3.
-/

public section

namespace TauCeti

variable {A : Type*} [AddCommGroup A]

/-- Let `ψ` and `ψ'` be additive endomorphisms acting on `x` and on an element `y` of infinite
order by `ψ x = sʳ x + b y`, `ψ y = s²ʳ y`, `ψ' x = tʳ x + b' y` and `ψ' y = t²ʳ y`. If `ψ` and
`ψ'` commute on `x`, then `tʳ (tʳ - 1) b = sʳ (sʳ - 1) b'`. -/
theorem pow_mul_pow_sub_one_mul_eq_of_comm (ψ ψ' : A →+ A) {x y : A}
    (hy : ¬IsOfFinAddOrder y) {r : ℕ} {s t b b' : ℤ}
    (hψx : ψ x = s ^ r • x + b • y) (hψy : ψ y = s ^ (2 * r) • y)
    (hψ'x : ψ' x = t ^ r • x + b' • y) (hψ'y : ψ' y = t ^ (2 * r) • y)
    (hcomm : ψ (ψ' x) = ψ' (ψ x)) :
    t ^ r * (t ^ r - 1) * b = s ^ r * (s ^ r - 1) * b' := by
  rw [hψ'x, hψx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul, hψx, hψy,
    hψ'x, hψ'y] at hcomm
  have h0 : (t ^ r * (t ^ r - 1) * b - s ^ r * (s ^ r - 1) * b') • y = 0 := by
    linear_combination (norm := module) -hcomm
  by_contra hne
  exact hy (isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨_, sub_ne_zero.2 hne, h0⟩)

/-- **Adams–Atiyah**: let `ψ₂` and `ψ₃` be additive endomorphisms commuting on `x`, with
`ψ₂ x = 2ʳ x + b₂ y`, `ψ₂ y = 2²ʳ y`, `ψ₃ x = 3ʳ x + b₃ y` and `ψ₃ y = 3²ʳ y`, where `r ≠ 0` and
`y` has infinite order and is not twice an element. If `ψ₂ x ≡ h y` modulo twice the group for
an odd integer `h`, then `r` is `1`, `2` or `4`.

In the intended application `A` is the reduced K-group of the mapping cone of
`f : S⁴ʳ⁻¹ → S²ʳ`, the maps are the Adams operations `ψ²` and `ψ³`, `h y = x²` and `h` is the
Hopf invariant of `f`; the conclusion then restricts maps of odd Hopf invariant to
`S³ → S²`, `S⁷ → S⁴` and `S¹⁵ → S⁸`. -/
theorem eq_one_or_eq_two_or_eq_four_of_adamsOperations (ψ₂ ψ₃ : A →+ A) {x y : A}
    (hy : ¬IsOfFinAddOrder y) (hy₂ : ∀ w : A, 2 • w ≠ y) {r : ℕ} (hr : r ≠ 0) {h b₂ b₃ : ℤ}
    (hψ₂x : ψ₂ x = (2 : ℤ) ^ r • x + b₂ • y) (hψ₂y : ψ₂ y = (2 : ℤ) ^ (2 * r) • y)
    (hψ₃x : ψ₃ x = (3 : ℤ) ^ r • x + b₃ • y) (hψ₃y : ψ₃ y = (3 : ℤ) ^ (2 * r) • y)
    (hcomm : ψ₂ (ψ₃ x) = ψ₃ (ψ₂ x)) (hmod : ∃ z : A, ψ₂ x = h • y + 2 • z) (hh : Odd h) :
    r = 1 ∨ r = 2 ∨ r = 4 := by
  -- Reducing `ψ₂ x` modulo `2` shows that `b₂ ≡ h` is odd.
  have hb₂ : Odd b₂ := by
    obtain ⟨z, hz⟩ := hmod
    by_contra hb
    obtain ⟨k, hk⟩ := (Int.not_odd_iff_even.1 hb).sub_odd hh
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr
    apply hy₂ (z - (2 : ℤ) ^ r • x - k • y)
    rw [hψ₂x] at hz
    have : (b₂ - h) • y = (2 * k + 1) • y := by rw [hk]
    linear_combination (norm := module) this - hz
  -- `2 ^ r` divides `3 ^ r (3 ^ r - 1) b₂ = 2 ^ r (2 ^ r - 1) b₃` and is prime to `3 ^ r b₂`.
  have key := pow_mul_pow_sub_one_mul_eq_of_comm ψ₂ ψ₃ hy hψ₂x hψ₂y hψ₃x hψ₃y hcomm
  have hdvd : (2 : ℤ) ^ r ∣ 3 ^ r - 1 := by
    have hcop : IsCoprime ((2 : ℤ) ^ r) (3 ^ r * b₂) :=
      ((Int.isCoprime_two_left.2 ⟨1, rfl⟩).pow_right.mul_right
        (Int.isCoprime_two_left.2 hb₂)).pow_left
    refine hcop.dvd_of_dvd_mul_left ⟨(2 ^ r - 1) * b₃, ?_⟩
    linear_combination key
  have hdvd' : 2 ^ r ∣ 3 ^ r - 1 := by
    rw [← Int.natCast_dvd_natCast]
    push_cast [Nat.one_le_pow r 3 (by norm_num)]
    exact hdvd
  have := Nat.two_pow_dvd_three_pow_sub_one_iff.1 hdvd'
  omega

end TauCeti
