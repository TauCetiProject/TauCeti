/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic

/-!
# Scalar divisibility and the algebra norm

For a free algebra `S` of rank `n` over `R`, the norm of `algebraMap R S r` is `r ^ n`
(Mathlib's `Algebra.norm_algebraMap`) and the norm is multiplicative, so divisibility of `a` by
`algebraMap R S r ^ e` gives `r ^ (n * e) ∣ Algebra.norm R a`.

## Main results

* `Algebra.pow_finrank_dvd_norm_of_algebraMap_dvd`: `r ^ finrank R S ∣ norm R a` whenever
  `algebraMap R S r ∣ a`.
* `Algebra.pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd`: `r ^ (finrank R S * e) ∣ norm R a`
  whenever `algebraMap R S r ^ e ∣ a`.

## References

* J. S. Milne, *Algebraic Number Theory*, Chapter 2, p. 31.
-/

public section

open Module

namespace Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Free R S]

/-- If `algebraMap R S r` divides `a` in a free `R`-algebra `S`, then `r ^ finrank R S` divides the
norm of `a`. -/
theorem pow_finrank_dvd_norm_of_algebraMap_dvd {r : R} {a : S} (h : algebraMap R S r ∣ a) :
    r ^ finrank R S ∣ norm R a := by
  simpa using map_dvd (norm R) h

/-- If `algebraMap R S r ^ e` divides `a` in a free `R`-algebra `S`, then `r ^ (finrank R S * e)`
divides the norm of `a`. -/
theorem pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd {r : R} {e : ℕ} {a : S}
    (h : algebraMap R S r ^ e ∣ a) : r ^ (finrank R S * e) ∣ norm R a := by
  rw [mul_comm, pow_mul]
  exact pow_finrank_dvd_norm_of_algebraMap_dvd (by simpa using h)

end Algebra
