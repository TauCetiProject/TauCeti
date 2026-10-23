/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Cyclotomic extensions of odd level

When `n` is odd and `2 ≠ 0`, the `n`-th and `2n`-th roots of unity generate the same algebra: if
`ζ` is a primitive `n`-th root of unity then `-ζ` is a primitive `2n`-th one, and conversely every
`2n`-th root of unity is `±` an `n`-th one. So an `n`-th cyclotomic extension is the same thing as a
`2n`-th one. Over `ℚ` this is `ℚ(ζ₃) = ℚ(ζ₆)`, and in general `ℚ(ζ_n) = ℚ(ζ_{n/2})` for
`n ≡ 2 mod 4`. It is the reason a cyclotomic field has a well-defined *conductor*, the least level
presenting it, which is never `≡ 2 mod 4`.

## Main results

* `IsCyclotomicExtension.singleton_two_mul_iff_of_odd`: for odd `n`, a commutative ring `B`
  without zero divisors is a `2n`-th cyclotomic extension of `A` iff `2 ≠ 0` in `B` and it is
  an `n`-th cyclotomic extension of `A`.
* `IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two`: for `n ≡ 2 mod 4`, an `n`-th
  cyclotomic extension is an `n / 2`-th one.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

namespace IsCyclotomicExtension

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Odd levels may be doubled exactly when `2 ≠ 0`.** For odd `n`, a commutative ring `B`
without zero divisors is a `2n`-th cyclotomic extension of `A` exactly when `2 ≠ 0` in `B` and
it is an `n`-th cyclotomic extension of `A`. For example, a sixth cyclotomic field over `ℚ` is
also a third cyclotomic field. -/
theorem singleton_two_mul_iff_of_odd [NoZeroDivisors B] {n : ℕ} (hn : Odd n) :
    IsCyclotomicExtension {2 * n} A B ↔ (2 : B) ≠ 0 ∧ IsCyclotomicExtension {n} A B := by
  have hn2 : 0 < 2 * n := Nat.mul_pos (by decide) hn.pos
  have : NeZero n := ⟨hn.pos.ne'⟩
  have : NeZero (2 * n) := ⟨hn2.ne'⟩
  rw [iff_singleton, iff_singleton]
  constructor
  · rintro ⟨⟨ζ, hζ⟩, hgen⟩
    have hζ₂ : IsPrimitiveRoot (ζ ^ n) 2 := hζ.pow hn2 (mul_comm 2 n)
    refine ⟨fun h2 ↦ hζ₂.ne_one one_lt_two ?_, ⟨ζ ^ 2, hζ.pow hn2 rfl⟩, fun x ↦ ?_⟩
    · rw [hζ₂.eq_neg_one_of_two_right]
      exact neg_eq_iff_add_eq_zero.mpr (by simpa only [one_add_one_eq_two] using h2)
    refine Algebra.adjoin_le (fun b hb ↦ ?_) (hgen x)
    have hsq : (b ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, hb]
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact Algebra.subset_adjoin h
    · have hneg : (-b) ^ n = 1 := by rw [hn.neg_pow, h, neg_neg]
      simpa using neg_mem (Algebra.subset_adjoin hneg :
        -b ∈ Algebra.adjoin A {b : B | b ^ n = 1})
  · rintro ⟨h2, ⟨ζ, hζ⟩, hgen⟩
    refine ⟨⟨-ζ, hζ.neg_of_odd hn h2⟩, fun x ↦ ?_⟩
    exact Algebra.adjoin_mono (fun b hb ↦ by
      rw [Set.mem_ofPred_eq, mul_comm 2 n, pow_mul, hb, one_pow]) (hgen x)

/-- **Levels `≡ 2 mod 4` may be halved.** If `n ≡ 2 mod 4`, an `n`-th cyclotomic extension `B` of
`A`, with `B` a commutative ring without zero divisors, is also an `n / 2`-th cyclotomic
extension of `A`. -/
theorem singleton_div_two_of_mod_four_eq_two [NoZeroDivisors B] {n : ℕ} (hn : n % 4 = 2)
    [IsCyclotomicExtension {n} A B] : IsCyclotomicExtension {n / 2} A B := by
  have hodd : Odd (n / 2) := Nat.odd_iff.mpr (by omega)
  have H : IsCyclotomicExtension {2 * (n / 2)} A B := by
    rw [Nat.mul_div_cancel' (by omega : 2 ∣ n)]
    infer_instance
  exact ((singleton_two_mul_iff_of_odd hodd).mp H).2

end IsCyclotomicExtension
