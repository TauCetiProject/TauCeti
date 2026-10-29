/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Euler products of Dirichlet `L`-series over a set of primes

Mathlib's Euler product `DirichletCharacter.LSeries_eulerProduct_hasProd` runs over all primes.
The local factor at a prime where the character vanishes is `1`, so the same product taken over
any set of primes containing all the others has the same value. This file records that, and its
instance for the trivial character modulo `N`: the product of `(1 - p⁻ˢ)⁻¹` over the primes not
dividing `N` is the `L`-function of the trivial character modulo `N`, which is the Riemann zeta
function with its Euler factors at the primes dividing `N` removed
(`DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`). Such partial Euler products are
the shape in which products of local factors over the good primes of an arithmetic object appear.

## Main results

* `DirichletCharacter.LSeries_eulerProduct_hasProd_subtype`: the Euler product of `L(χ, s)` over
  any set of primes outside which `χ` vanishes.
* `DirichletCharacter.LFunctionTrivChar_eulerProduct_hasProd`: the Euler product of `ζ(s)` over
  the primes not dividing `N` converges to the `L`-function of the trivial character modulo `N`.
* `TauCeti.hasProd_prod_inv_one_sub_cpow`: the Euler product over the primes not dividing `N` of a
  finite product of truncated zeta values `∏_{q ∣ N} (1 - q⁻ˢ) · ζ(s)`.
* `TauCeti.prod_mul_riemannZeta_ne_zero`: such a finite product is nonzero where `1 ≤ re s` and
  `s ≠ 1`.
-/

public section

open scoped LSeries.notation

namespace DirichletCharacter

/-- **The Euler product of a Dirichlet `L`-series over a set of primes**: if `χ` vanishes at every
prime outside `P`, then for `1 < re s` the product of `(1 - χ(p) p⁻ˢ)⁻¹` over the primes in `P`
converges to `L(χ, s)`. -/
theorem LSeries_eulerProduct_hasProd_subtype {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) {P : Nat.Primes → Prop} (hP : ∀ p, ¬ P p → χ p = 0) :
    HasProd (fun p : {p : Nat.Primes // P p} => (1 - χ p * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (L ↗χ s) := by
  refine (hasProd_subtype_iff_of_mulSupport_subset (s := {p | P p}) fun p hp => ?_).mpr
    (LSeries_eulerProduct_hasProd χ hs)
  by_contra h
  exact hp (by simp [hP p h])

/-- **The Euler product of `ζ` over the primes not dividing `N`**: for `1 < re s` the product of
`(1 - p⁻ˢ)⁻¹` over the primes `p ∤ N` converges to the `L`-function of the trivial character
modulo `N`, that is, to `∏_{q ∣ N} (1 - q⁻ˢ) · ζ(s)`. -/
theorem LFunctionTrivChar_eulerProduct_hasProd (N : ℕ) [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ N} => (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (LFunctionTrivChar N s) := by
  rw [LFunctionTrivChar, LFunction_eq_LSeries _ hs]
  convert (1 : DirichletCharacter ℂ N).LSeries_eulerProduct_hasProd_subtype hs
    (P := fun p => ¬ (p : ℕ) ∣ N) (fun p hp => ?_) using 3 with p
  · rw [MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd p.1.prop).mpr p.prop), one_mul]
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_prime_iff_not_dvd p.prop])

end DirichletCharacter

namespace TauCeti

variable {ι : Type*}

/-- **The Euler product of a finite product of truncated zeta values**: if `1 < re (s i)` for every
`i ∈ t`, then over the primes `p ∤ N` the product of `∏_{i ∈ t} (1 - p^{-s i})⁻¹` converges to
`∏_{i ∈ t} ζ^{(S)}(s i)`, where `ζ^{(S)}(s) = ∏_{q ∣ N} (1 - q⁻ˢ) · ζ(s)` has the Euler factors at
the primes dividing `N` removed. -/
theorem hasProd_prod_inv_one_sub_cpow (N : ℕ) [NeZero N] (t : Finset ι) (s : ι → ℂ)
    (hs : ∀ i ∈ t, 1 < (s i).re) :
    HasProd (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ N} =>
        ∏ i ∈ t, (1 - ((p : ℕ) : ℂ) ^ (-s i))⁻¹)
      (∏ i ∈ t, (∏ q ∈ N.primeFactors, (1 - (q : ℂ) ^ (-s i))) * riemannZeta (s i)) := by
  rw [Finset.prod_congr rfl fun i hi =>
    (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := N) fun h => by
      simpa [h] using hs i hi).symm]
  exact hasProd_prod fun i hi =>
    DirichletCharacter.LFunctionTrivChar_eulerProduct_hasProd N (hs i hi)

/-- **A finite product of truncated zeta values is nonzero** on the closed half-plane `1 ≤ re s`
away from the pole `s = 1`. -/
theorem prod_mul_riemannZeta_ne_zero (N : ℕ) [NeZero N] (t : Finset ι) {s : ι → ℂ}
    (hs₁ : ∀ i ∈ t, s i ≠ 1) (hs : ∀ i ∈ t, 1 ≤ (s i).re) :
    (∏ i ∈ t, (∏ q ∈ N.primeFactors, (1 - (q : ℂ) ^ (-s i))) * riemannZeta (s i)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [← DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (hs₁ i hi)]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr (hs₁ i hi)) (hs i hi)

end TauCeti
