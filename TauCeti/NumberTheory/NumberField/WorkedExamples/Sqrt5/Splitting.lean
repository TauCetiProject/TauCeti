/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Splitting
import TauCeti.Algebra.Algebra.Subalgebra.Adjoin
import TauCeti.NumberTheory.LegendreSymbol.Five
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Invariants

/-!
# The splitting law of `ℚ(√5)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1`, the
element `2θ − 1` is a square root of `5`, so the quadratic splitting law applies: an odd prime
`p` splits in `K` if and only if `legendreSym p 5 = 1`, that is, if and only if `5` is a nonzero
square modulo `p`, which by quadratic reciprocity is the congruence `p ≡ ±1 (mod 5)`. The
ramified prime `5` has a single prime above it and Legendre symbol `0`, so both sides of each
equivalence are false there.

## Main results

* `TauCeti.NumberField.Sqrt5.minpoly_two_mul_sub_one`: `minpoly ℤ (2θ − 1) = X² − 5`.
* `TauCeti.NumberField.Sqrt5.ncard_primesOver_eq_two_iff_legendreSym`: for an odd prime `p`,
  there are two primes above `p` if and only if `legendreSym p 5 = 1`.
* `TauCeti.NumberField.Sqrt5.ncard_primesOver_eq_two_iff_mod_five`: for an odd prime `p`, there
  are two primes above `p` if and only if `p % 5 = 1 ∨ p % 5 = 4`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- `2θ − 1` is a square root of `5`: its minimal polynomial over `ℤ` is `X² − 5`. -/
theorem minpoly_two_mul_sub_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1) :
    minpoly ℤ (2 * θ - 1) = X ^ 2 - C 5 := by
  have h := minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add (minpoly_eq_X_sq_sub_X_add hmin)
  norm_num at h
  exact h

/-- **The splitting law of `ℚ(√5)` at odd primes.** An odd prime `p` splits in `ℚ(√5)`, that is,
there are two primes above `p`, if and only if `legendreSym p 5 = 1`, that is, `5` is a nonzero
square modulo `p`. At `p = 5` both sides are false: `5` ramifies. -/
theorem ncard_primesOver_eq_two_iff_legendreSym (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = 2 ↔ legendreSym p 5 = 1 := by
  by_cases hp5 : p = 5
  · -- `5` ramifies: a single prime above it, and `legendreSym 5 5 = 0`.
    subst hp5
    have hmem : 5 ∈ ramifiedPrimes K := by
      rw [mem_ramifiedPrimes_iff_dvd_discr Nat.prime_five, discr_eq_five hmin hgen]
      norm_num
    rw [ncard_primesOver_eq_one_of_mem_ramifiedPrimes (finrank_eq_two hmin hgen) hmem,
      (legendreSym.eq_zero_iff 5 5).mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd 5 5).mpr (by norm_num))]
    norm_num
  have hcop : ¬ (p : ℤ) ∣ 5 := by
    intro h
    have h' : p ∣ 5 := by exact_mod_cast h
    rcases Nat.prime_five.eq_one_or_self_of_dvd p h' with h1 | h1
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp5 h1
  have hgen' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K (2 * θ - 1)} = ⊤ := by
    rw [map_sub, map_mul, map_one, map_ofNat]
    exact TauCeti.Algebra.adjoin_two_mul_sub_one_eq_top two_ne_zero.isUnit hgen
  rw [← finrank_eq_two hmin hgen]
  exact ncard_primesOver_quadratic_iff (minpoly_two_mul_sub_one hmin) hgen' hodd hcop

/-- **The splitting law of `ℚ(√5)` at odd primes, congruence form.** An odd prime `p` splits in
`ℚ(√5)` if and only if `p ≡ ±1 (mod 5)`. -/
theorem ncard_primesOver_eq_two_iff_mod_five (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = 2 ↔ p % 5 = 1 ∨ p % 5 = 4 :=
  (ncard_primesOver_eq_two_iff_legendreSym hmin hgen hodd).trans (legendreSym_five_eq_one_iff hodd)

end TauCeti.NumberField.Sqrt5
