/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.DedekindZeta
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer

/-!
# The prime ideal theorem with the logarithmic integral

`NumberField.Set.HasNaturalDensity` measures a set `S` of primes of a number field `K` by the
ratio `π_S(x) / π_K(x)` of prime counts. This file sharpens the prime ideal theorem
`TauCeti.primeIdealTheorem`, which gives `ϑ_K(x) ~ x` and `π_K(x) ~ Li(x)`, to

```text
π_K(x) = Li(x) + o(x / log x).
```

The passage from `ϑ` is Abel summation, `TauCeti.primeCount_sub_mul_logIntegral_isLittleO`.

## Main results

* `NumberField.Chebotarev.primeCount_univ_sub_logIntegral_isLittleO`:
  `π_K(x) = Li(x) + o(x / log x)`.

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

/-- **The prime ideal theorem, with the logarithmic integral.** For every number field `K`, the
number of primes of `K` of norm at most `x` is `Li(x) + o(x / log x)`. -/
theorem primeCount_univ_sub_logIntegral_isLittleO :
    (fun x : ℝ ↦ primeCount K Set.univ x - Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
  simpa using primeCount_sub_mul_logIntegral_isLittleO (δ := 1)
    ((primeIdealTheorem K).2.1.isLittleO.congr_left fun x ↦ by simp)

end NumberField.Chebotarev
