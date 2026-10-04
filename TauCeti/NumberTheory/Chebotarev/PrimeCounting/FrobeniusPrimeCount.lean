/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Chebotarev
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity
import TauCeti.Algebra.Group.ConjFinite
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer

/-!
# Prime counting and natural density for Frobenius classes

For a finite Galois extension `L/K` of number fields, the primes of `K` in a conjugacy class
`C`, counted by `NumberField.Chebotarev.frobeniusPrimeCount`, have count asymptotic to
`(#C / #Gal(L/K)) Li(x)`. The weighted Chebotarev theorem gives the corresponding result for
`ψ_C`; removing higher prime powers and Abel summation give the count.
The count for the trivial extension gives the all-prime denominator, and comparison with it
then gives natural density. Thus the denominator, like the numerator, comes from the weighted
cyclotomic theorem and the generic transfers from `ψ` to `ϑ` to prime counting.

## Main results

* `NumberField.Chebotarev.tendsto_frobeniusTheta`: the weighted prime count divided by `x`
  tends to `#C / #Gal(L/K)`.
* `NumberField.Chebotarev.tendsto_frobeniusPrimeCount`: the prime count divided by `x / log x`
  tends to `#C / #Gal(L/K)`.
* `NumberField.Chebotarev.frobeniusPrimeCount_isEquivalent_logIntegral`: the prime count is
  asymptotic to `(#C / #Gal(L/K)) Li(x)`.
* `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`: the same ratio is the natural
  density of the Frobenius prime set.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV, for the passage from `ψ` to prime counting.
-/

public section

open Asymptotics Filter NumberField TauCeti
open scoped NumberField Topology

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The logarithmically weighted count of a Frobenius class satisfies
`ϑ_C(x) = (#C / #Gal(L/K)) x + o(x)`. -/
private theorem frobeniusTheta_asymptotic (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ frobeniusTheta K L C x -
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) * x) =o[atTop] id := by
  have h := (frobeniusPsi_asymptotic K L C).sub
    (frobeniusPsi_sub_frobeniusTheta_isLittleO C)
  exact h.congr_left fun x ↦ by ring

/-- The Frobenius `ϑ` function divided by `x` tends to `#C / #Gal(L/K)`. -/
theorem tendsto_frobeniusTheta (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto (fun x : ℝ ↦ frobeniusTheta K L C x / x) atTop
      (𝓝 ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) :=
  (isLittleO_sub_mul_iff_tendsto_div (eventually_ne_atTop 0)).mp
    (frobeniusTheta_asymptotic K L C)

/-- The Frobenius prime count is `(#C / #Gal(L/K)) Li(x) + o(x / log x)`. -/
private theorem frobeniusPrimeCount_sub_mul_logIntegral_isLittleO
    (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ) -
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) * Real.logIntegral x)
      =o[atTop] fun x : ℝ ↦ x / Real.log x := by
  simpa only [natCast_frobeniusPrimeCount] using
    (primeCount_sub_mul_logIntegral_isLittleO (K := K)
      (S := frobeniusPrimeSet K L C)
      (δ := (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))
      (by simpa only [← frobeniusTheta_def] using frobeniusTheta_asymptotic K L C))

/-- The Frobenius prime count is asymptotic to `(#C / #Gal(L/K)) Li(x)`. -/
theorem frobeniusPrimeCount_isEquivalent_logIntegral
    (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ)) ~[atTop]
      (fun x ↦ ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) *
        Real.logIntegral x) :=
  (frobeniusPrimeCount_sub_mul_logIntegral_isLittleO K L C).trans_isBigO
    (Real.logIntegral_isEquivalent_div_log.isBigO_symm.const_mul_right
      (C.card_carrier_div_card_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')))

/-- Qualitative prime-counting Chebotarev: the proportion relative to `x / log x` of primes
whose arithmetic Frobenius lies in `C` tends to `#C / #Gal(L/K)`. -/
theorem tendsto_frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ) / (x / Real.log x))
      atTop (𝓝 ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) :=
  Real.tendsto_div_div_log_of_isLittleO_logIntegral
    (frobeniusPrimeCount_sub_mul_logIntegral_isLittleO K L C)

/-- Natural-density Chebotarev: among the primes of `K`, the primes with arithmetic Frobenius
class `C` have density `#C / #Gal(L/K)`. -/
theorem hasNaturalDensity_frobeniusPrimeSet (C : ConjClasses (L ≃ₐ[K] L)) :
    NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L C)
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  have hself (D : ConjClasses (K ≃ₐ[K] K)) : frobeniusPrimeSet K K D = Set.univ := by
    ext 𝔭
    simp
  -- The trivial extension counts all primes. Its asymptotic uses the same `ψ → ϑ → π`
  -- transfers as the numerator, not a separately supplied zeta boundary package.
  have hden : Tendsto (fun x : ℝ ↦ primeCount K Set.univ x / (x / Real.log x))
      atTop (𝓝 1) := by
    simpa only [natCast_frobeniusPrimeCount, hself, ConjClasses.one_eq_mk_one,
      TauCeti.ConjClasses.card_carrier_mk_one, Nat.card_unique, Nat.cast_one, div_one] using
      tendsto_frobeniusPrimeCount K K 1
  rw [NumberField.Set.hasNaturalDensity_def]
  have h := (tendsto_frobeniusPrimeCount K L C).div hden one_ne_zero
  simp only [div_one, natCast_frobeniusPrimeCount] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact div_div_div_cancel_right₀
    (div_ne_zero (by linarith) (Real.log_pos hx).ne') _ _

end NumberField.Chebotarev
