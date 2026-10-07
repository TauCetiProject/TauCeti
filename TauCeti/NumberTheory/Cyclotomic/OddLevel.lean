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

* `IsCyclotomicExtension.singleton_two_mul_iff_of_odd`: for odd `n`, a domain `B` with `2 ≠ 0` is
  a `2n`-th cyclotomic extension of `A` iff it is an `n`-th cyclotomic extension of `A`.
* `IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two`: for `n ≡ 2 mod 4`, an `n`-th
  cyclotomic extension is an `n / 2`-th one.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

namespace IsCyclotomicExtension

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Odd levels may be doubled.** For odd `n`, a domain `B` in which `2 ≠ 0` is a `2n`-th
cyclotomic extension of `A` exactly when it is an `n`-th cyclotomic extension of `A`. For example,
a sixth cyclotomic field over `ℚ` is a third cyclotomic field. -/
theorem singleton_two_mul_iff_of_odd [IsDomain B] {n : ℕ} (hn : Odd n) (h2 : (2 : B) ≠ 0) :
    IsCyclotomicExtension {2 * n} A B ↔ IsCyclotomicExtension {n} A B := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have : NeZero n := ⟨hn0⟩
  constructor
  · intro H
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot A B (Set.mem_singleton (2 * n)) (by omega)
    rw [iff_singleton]
    refine ⟨⟨ζ ^ 2, hζ.pow (by omega) rfl⟩, fun x ↦ ?_⟩
    refine Algebra.adjoin_le (fun b hb ↦ ?_) (H.adjoin_roots x)
    obtain ⟨m, hm, -, hbm⟩ := hb
    rw [Set.mem_singleton_iff.mp hm] at hbm
    have hsq : (b ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, hbm]
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact Algebra.subset_adjoin h
    · have hneg : (-b) ^ n = 1 := by rw [hn.neg_pow, h, neg_neg]
      simpa using neg_mem (Algebra.subset_adjoin hneg :
        -b ∈ Algebra.adjoin A {b : B | b ^ n = 1})
  · intro H
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot A B (Set.mem_singleton n) hn0
    have := union_of_isPrimitiveRoot (S := {n}) (A := A) (B := B) (hζ.neg_of_odd hn h2)
    rw [iff_union_of_dvd (S := {2 * n}) (n := n) A B ⟨2 * n, rfl, by omega, dvd_mul_left n 2⟩,
      Set.union_comm]
    exact this

/-- **Levels `≡ 2 mod 4` may be halved.** If `n ≡ 2 mod 4`, an `n`-th cyclotomic extension `B` of
`A`, with `B` a domain in which `2 ≠ 0`, is also an `n / 2`-th cyclotomic extension of `A`. -/
theorem singleton_div_two_of_mod_four_eq_two [IsDomain B] {n : ℕ} (hn : n % 4 = 2)
    (h2 : (2 : B) ≠ 0) [IsCyclotomicExtension {n} A B] : IsCyclotomicExtension {n / 2} A B := by
  rw [← singleton_two_mul_iff_of_odd (Nat.odd_iff.mpr (by omega)) h2,
    Nat.mul_div_cancel' (by omega : 2 ∣ n)]
  infer_instance

end IsCyclotomicExtension
