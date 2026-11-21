/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Integer and natural-number units in localizations at submonoids of `ℤ`

Let `A` be a commutative ring, let `M` be a submonoid of `ℤ`, and let `S` be a localization of `A`
at `Algebra.algebraMapSubmonoid A M`. Every integer `m ∈ M` casts to an element of that submonoid
in `A`, and therefore casts to a unit in `S`. Specializing `M` to the complement of a prime ideal
`(p)` of `ℤ` shows that every natural number `n` not divisible by `p` (in particular every prime
`q ≠ p`) casts to a unit in `S`.

## Main results

* `TauCeti.IsLocalization.isUnit_intCast_of_mem`: if `S` is a localization of `A` at
  `Algebra.algebraMapSubmonoid A M` (`M : Submonoid ℤ`), then `(m : S)` is a unit for every
  `m ∈ M`.
* `TauCeti.IsLocalization.isUnit_natCast_of_not_dvd`: if `S` is a localization of `A` at the prime
  ideal `(p)` of `ℤ`, then `(n : S)` is a unit whenever `¬ p ∣ n`.
* `TauCeti.IsLocalization.isUnit_natCast_of_prime_ne`: in such a localization, `(q : S)` is a unit
  for every prime `q ≠ p`.
-/

public section

namespace TauCeti.IsLocalization

/-- In a localization `S` of a commutative ring `A` at `Algebra.algebraMapSubmonoid A M` for a
submonoid `M : Submonoid ℤ`, every integer `m ∈ M` casts to a unit in `S`. -/
theorem isUnit_intCast_of_mem (A : Type*) [CommRing A] {M : Submonoid ℤ} {S : Type*}
    [CommRing S] [Algebra A S] [IsLocalization (Algebra.algebraMapSubmonoid A M) S] {m : ℤ}
    (hm : m ∈ M) : IsUnit (m : S) := by
  have hmem : (m : A) ∈ Algebra.algebraMapSubmonoid A M :=
    ⟨m, hm, eq_intCast (algebraMap ℤ A) m⟩
  simpa only [map_intCast] using _root_.IsLocalization.map_units S ⟨(m : A), hmem⟩

/-- In a localization `S` of a commutative ring `A` at the prime ideal `(p)` of `ℤ`, every natural
number `n` not divisible by `p` casts to a unit in `S`. -/
theorem isUnit_natCast_of_not_dvd (A : Type*) [CommRing A] {S : Type*} [CommRing S]
    [Algebra A S] (p : ℕ) [(Ideal.span {(p : ℤ)}).IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid A (Ideal.span {(p : ℤ)}).primeCompl) S]
    {n : ℕ} (hn : ¬ p ∣ n) : IsUnit (n : S) := by
  have hmem : (n : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
    rwa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
  simpa only [Int.cast_natCast] using isUnit_intCast_of_mem A hmem

/-- In a localization `S` of a commutative ring `A` at the prime ideal `(p)` of `ℤ`, every prime
`q ≠ p` casts to a unit in `S`. -/
theorem isUnit_natCast_of_prime_ne (A : Type*) [CommRing A] {S : Type*} [CommRing S]
    [Algebra A S] (p : ℕ) [hp : (Ideal.span {(p : ℤ)}).IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid A (Ideal.span {(p : ℤ)}).primeCompl) S]
    ⦃q : ℕ⦄ (hq : q.Prime) (hqp : q ≠ p) : IsUnit (q : S) := by
  refine isUnit_natCast_of_not_dvd A p fun hdvd ↦ ?_
  rcases hq.eq_one_or_self_of_dvd p hdvd with rfl | rfl
  · exact hp.ne_top (by simp)
  · exact hqp rfl

end TauCeti.IsLocalization
