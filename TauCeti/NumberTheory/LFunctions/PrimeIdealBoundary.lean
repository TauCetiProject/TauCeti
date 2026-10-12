/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.DedekindZeta
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Boundary data from the Dedekind zeta function

The Dedekind zeta function of a number field continues meromorphically across `Re s = 1`, has a
simple pole at `1`, and has no zeros on that line. Consequently its logarithmic derivative, after
subtracting the pole, extends continuously to the closed half-plane. This file packages that
analytic information as `TauCeti.LFunctions.primeIdealVonMangoldtBoundary`, the input expected by
the generic prime-number-theorem transfer for the set of all prime ideals.

## Main results

* `TauCeti.LFunctions.primeIdealVonMangoldtBoundary`: boundary data with residue one for all prime
  ideals of a number field.
* `TauCeti.LFunctions.primeIdealVonMangoldtBoundary_series`: its series is `-ζ_K'/ζ_K` on
  `Re s > 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* H. Davenport, *Multiplicative Number Theory*, Chapter 17.
-/

public section

namespace TauCeti.LFunctions

open NumberField

/-- **Boundary data for all primes of a number field.** The von Mangoldt series of all primes of
`K` sums to `-ζ_K'(s)/ζ_K(s)` on `Re s > 1`, and `-ζ_K'(s)/ζ_K(s) - 1/(s - 1)` extends continuously
to `Re s ≥ 1` (`TauCeti.exists_continuousOn_eq_neg_deriv_dedekindZeta_div_sub`). -/
noncomputable def primeIdealVonMangoldtBoundary (K : Type*) [Field K] [NumberField K] :
    PrimeBoundaryRemainder K Set.univ 1 :=
  PrimeBoundaryRemainder.ofDedekindZeta _
    (exists_continuousOn_eq_neg_deriv_dedekindZeta_div_sub K).choose_spec.1
    (exists_continuousOn_eq_neg_deriv_dedekindZeta_div_sub K).choose_spec.2

/-- The series of `primeIdealVonMangoldtBoundary K` is the negative logarithmic derivative
`-ζ_K'(s)/ζ_K(s)` of the Dedekind zeta function on `Re s > 1`. -/
@[simp]
theorem primeIdealVonMangoldtBoundary_series {K : Type*} [Field K] [NumberField K]
    (s : {s : ℂ // 1 < s.re}) :
    (primeIdealVonMangoldtBoundary K).series s =
      -deriv (dedekindZeta K) (s : ℂ) / dedekindZeta K (s : ℂ) := by
  rw [primeIdealVonMangoldtBoundary, PrimeBoundaryRemainder.ofDedekindZeta_series]

end TauCeti.LFunctions
