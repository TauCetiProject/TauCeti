/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet

/-!
# The unramified primes carry all of the density

Let `L / K` be an extension of number fields. The primes of `𝓞 K` ramified in `L` form the finite
set `ramifiedPrimes K L`, so their complement has Dirichlet density `1`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_compl_ramifiedPrimes`: the primes outside the finite
  ramified set have Dirichlet density `1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)

-- `primeIdealZetaSum` and `HasDirichletDensity` live in `NumberField.Set`, so dot notation on a
-- set of primes finds them only while `NumberField` is open.
open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [IsGalois K L] in
variable (K L) in
/-- **The unramified primes have density one.** Only finitely many primes of `𝓞 K` ramify in
`L`, so they carry density `0` and their complement carries all of it. -/
theorem hasDirichletDensity_compl_ramifiedPrimes :
    ((↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ).HasDirichletDensity 1 := by
  simpa using (Set.hasDirichletDensity_of_finite
    (ramifiedPrimes K L).finite_toSet).compl

end NumberField.Chebotarev
