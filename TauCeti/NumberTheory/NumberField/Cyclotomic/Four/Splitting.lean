/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting

/-!
# The splitting law in `ℚ(i)`

Let `K = ℚ(i)`, here any `4`-th cyclotomic extension of `ℚ`, and let `p` be an odd prime. The
cyclotomic splitting law (`TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting`) specializes
at `n = 4` to:

* `TauCeti.NumberField.ncard_primesOver_eq_one_of_mod_four_eq_three` and
  `TauCeti.NumberField.ncard_primesOver_eq_two_of_mod_four_eq_one`: in `ℚ(i)`, one prime lies
  above `p ≡ 3 mod 4` and two primes lie above `p ≡ 1 mod 4`.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 2.13.
-/

public section
noncomputable section

open Ideal NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **A prime `p ≡ 3 mod 4` is inert in `ℚ(i)`.** A single prime lies above `p` in a `4`-th
cyclotomic field over `ℚ`: `p` has order `2 = φ(4)` modulo `4`. -/
theorem ncard_primesOver_eq_one_of_mod_four_eq_three (p : ℕ) [hp : Fact p.Prime] (h : p % 4 = 3) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 := by
  have h4 : ¬p ∣ 4 := fun h' ↦ by
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow (n := 2) h')
    omega
  have key := ncard_primesOver_mul_orderOf_eq_totient (K := K) p h4
  rw [← ZMod.natCast_mod, h, show orderOf ((3 : ℕ) : ZMod 4) = 2 from
    orderOf_eq_prime (by decide) (by decide), show Nat.totient 4 = 2 by decide] at key
  omega

/-- **A prime `p ≡ 1 mod 4` splits in `ℚ(i)`.** Two primes lie above `p` in a `4`-th cyclotomic
field over `ℚ`. This is `ncard_primesOver_eq_totient_iff` at `n = 4`. -/
theorem ncard_primesOver_eq_two_of_mod_four_eq_one (p : ℕ) [Fact p.Prime] (h : p % 4 = 1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 := by
  rw [← show Nat.totient 4 = 2 by decide, ncard_primesOver_eq_totient_iff (by decide),
    ← ZMod.natCast_mod, h, Nat.cast_one]

end TauCeti.NumberField

end
