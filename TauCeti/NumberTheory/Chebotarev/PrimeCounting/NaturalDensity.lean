/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Cyclotomic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer

/-!
# The prime ideal theorem

`NumberField.Set.HasNaturalDensity` measures a set `S` of primes of a number field `K` by the
ratio `π_S(x) / π_K(x)` of prime counts. This file derives the size of the denominator `π_K(x)`,
the prime ideal theorem, in its `ϑ` and `π` forms from the `ψ` form
`NumberField.Chebotarev.primePsi_univ_asymptotic`, which is proved by the Wiener--Ikehara theorem
with no boundary hypothesis:

```text
ϑ_K(x) = x + o(x),      π_K(x) = Li(x) + o(x / log x),      π_K(x) ~ Li(x).
```

The two passages are the generic transfers `TauCeti.primeTheta_asymptotic_of_primePsi`, which
removes the prime powers with exponent at least two, and
`TauCeti.primeCount_sub_mul_logIntegral_isLittleO`, which is Abel summation.

## Main results

* `NumberField.Chebotarev.primeTheta_univ_asymptotic`: `ϑ_K(x) = x + o(x)`.
* `NumberField.Chebotarev.primeCount_univ_sub_logIntegral_isLittleO`:
  `π_K(x) = Li(x) + o(x / log x)`.
* `NumberField.Chebotarev.primeCount_univ_isEquivalent_logIntegral`: `π_K(x) ~ Li(x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13, for natural density and the
  Chebotarev density theorem.
* S. Lang, *Algebraic Number Theory*, Chapter XV, for the prime ideal theorem and the passage
  from `ψ` to `π`.
-/

public section

open Asymptotics Filter IsDedekindDomain NumberField TauCeti
open scoped Topology

namespace NumberField.Chebotarev

variable (K : Type*) [Field K] [NumberField K]

/-- **The prime ideal theorem, for `ϑ`.** For every number field `K`, the logarithmically weighted
prime count `ϑ_K(x) = ∑_{N𝔭 ≤ x} log N𝔭` satisfies `ϑ_K(x) = x + o(x)`. -/
theorem primeTheta_univ_asymptotic :
    (fun x : ℝ ↦ primeTheta K Set.univ x - x) =o[atTop] fun x : ℝ ↦ x := by
  simpa using primeTheta_asymptotic_of_primePsi (δ := 1) (standardPrimePowerRemoval K Set.univ)
    (by simpa using primePsi_univ_asymptotic K)

/-- **The prime ideal theorem, with the logarithmic integral.** For every number field `K`, the
number of primes of `K` of norm at most `x` is `Li(x) + o(x / log x)`. -/
theorem primeCount_univ_sub_logIntegral_isLittleO :
    (fun x : ℝ ↦ primeCount K Set.univ x - Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
  simpa using primeCount_sub_mul_logIntegral_isLittleO (δ := 1)
    ((primeTheta_univ_asymptotic K).congr_left fun x ↦ by rw [one_mul])

/-- **The prime ideal theorem.** The number of primes of a number field of norm at most `x` is
asymptotic to the logarithmic integral `Li(x)`. -/
theorem primeCount_univ_isEquivalent_logIntegral :
    primeCount K Set.univ ~[atTop] Real.logIntegral :=
  (primeCount_univ_sub_logIntegral_isLittleO K).trans_isBigO
    Real.logIntegral_isEquivalent_div_log.isBigO_symm

end NumberField.Chebotarev
