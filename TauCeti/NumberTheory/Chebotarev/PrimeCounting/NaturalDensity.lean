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
# The prime ideal theorem and natural density

`NumberField.Set.HasNaturalDensity` measures a set `S` of primes of a number field `K` by the
ratio `π_S(x) / π_K(x)` of prime counts, so any use of it needs the size of the denominator
`π_K(x)`, the number of all primes of `K` of norm at most `x`. That size is the prime ideal
theorem. This file derives it, in its `ϑ` and `π` forms, from the `ψ` form
`NumberField.Chebotarev.primePsi_univ_asymptotic`, which is proved by the Wiener--Ikehara theorem
with no boundary hypothesis:

```text
ϑ_K(x) = x + o(x),      π_K(x) = Li(x) + o(x / log x),      π_K(x) ~ Li(x).
```

The two passages are the generic transfers `TauCeti.primeTheta_asymptotic_of_primePsi`, which
removes the prime powers with exponent at least two, and
`TauCeti.primeCount_sub_mul_logIntegral_isLittleO`, which is Abel summation.

With the denominator in hand, natural density follows from a linear asymptotic for the
logarithmically weighted count alone: if `ϑ_S(x) = δ x + o(x)`, then `S` has natural density `δ`.
For a Frobenius fibre `frobeniusPrimeSet K L C` the weighted count that analytic arguments produce
is the Frobenius `ψ` function `frobeniusPsi K L C`, whose higher prime powers are selected by
powers of the Artin class rather than by `C` itself; they are `o(x)` all the same, so a linear
asymptotic for `frobeniusPsi K L C` already gives the natural density of the fibre. Combined with
the cyclotomic weighted theorem this gives natural-density Chebotarev for cyclotomic extensions.

Natural density is not a consequence of Dirichlet density, so none of this is deduced from the
Dirichlet-density results of `TauCeti.NumberTheory.Chebotarev.Density`; in the opposite direction,
`NumberField.Set.hasDirichletDensity_of_hasNaturalDensity` recovers them.

## Main results

* `NumberField.Chebotarev.primeTheta_univ_asymptotic`: `ϑ_K(x) = x + o(x)`.
* `NumberField.Chebotarev.primeCount_univ_sub_logIntegral_isLittleO`:
  `π_K(x) = Li(x) + o(x / log x)`.
* `NumberField.Chebotarev.primeCount_univ_isEquivalent_logIntegral`: `π_K(x) ~ Li(x)`.
* `NumberField.Set.hasNaturalDensity_of_primeTheta_asymptotic`: a set of primes with
  `ϑ_S(x) = δ x + o(x)` has natural density `δ`.
* `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet_of_frobeniusPsi_asymptotic`: a
  Frobenius fibre whose Frobenius `ψ` function satisfies `ψ_C(x) = δ x + o(x)` has natural
  density `δ`.
* `NumberField.Chebotarev.hasNaturalDensity_cyclotomicFrobenius`: for `F = K(μ_m)`, the Frobenius
  fibre of every `σ ∈ Gal(F/K)` has natural density `1 / #Gal(F/K)`.

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

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- **Natural density from the weighted prime count.** If the primes of `S` satisfy
`ϑ_S(x) = δ x + o(x)`, then `S` has natural density `δ`. This covers `δ = 0`. -/
theorem hasNaturalDensity_of_primeTheta_asymptotic
    (h : (fun x : ℝ ↦ primeTheta K S x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    HasNaturalDensity S δ :=
  hasNaturalDensity_of_isLittleO_logIntegral (primeCount_sub_mul_logIntegral_isLittleO h)
    (Chebotarev.primeCount_univ_sub_logIntegral_isLittleO K)

end NumberField.Set

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **Natural density of a Frobenius fibre from its Frobenius `ψ` function.** If the Frobenius `ψ`
function of a conjugacy class `C` satisfies `ψ_C(x) = δ x + o(x)`, then the primes of `K` whose
Artin class in `L` is `C` have natural density `δ`.

The higher prime powers counted by `ψ_C` are those whose powered Artin class is `C`, not those
whose base lies in `frobeniusPrimeSet K L C`; they are negligible nonetheless, so only the prime
terms `ϑ_C` matter. -/
theorem hasNaturalDensity_frobeniusPrimeSet_of_frobeniusPsi_asymptotic
    {C : ConjClasses (L ≃ₐ[K] L)} {δ : ℝ}
    (h : (fun x : ℝ ↦ frobeniusPsi K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L C) δ :=
  NumberField.Set.hasNaturalDensity_of_primeTheta_asymptotic <|
    (h.sub (frobeniusPsi_sub_frobeniusTheta_isLittleO C)).congr_left fun x ↦ by
      rw [frobeniusTheta_apply, primeTheta_apply]
      ring

variable (K) (F : Type*) [Field F] [NumberField F] [Algebra K F] [IsGalois K F]

/-- **Natural-density Chebotarev for cyclotomic extensions.** For `F = K(μ_m)` and
`σ ∈ Gal(F/K)`, the primes of `K` whose Frobenius in `F` is `σ` have natural density
`1 / #Gal(F/K)`. -/
theorem hasNaturalDensity_cyclotomicFrobenius (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (σ : F ≃ₐ[K] F) :
    NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K F (ConjClasses.mk σ))
      (1 / (Nat.card (F ≃ₐ[K] F) : ℝ)) :=
  hasNaturalDensity_frobeniusPrimeSet_of_frobeniusPsi_asymptotic
    (frobeniusPsi_asymptotic_of_isCyclotomicExtension K F m σ)

end NumberField.Chebotarev
