/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Chebotarev
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.NaturalDensity
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer

/-!
# Prime counting and natural density for Frobenius classes

For a finite Galois extension `L/K` of number fields, the primes of `K` in a conjugacy class
`C` have count asymptotic to `(#C / #Gal(L/K)) Li(x)`. The weighted Chebotarev theorem gives the
corresponding result for `ψ_C`; removing higher prime powers and Abel summation give the count.
Comparison with the prime ideal theorem for all primes then gives natural density.

## Main results

* `NumberField.Chebotarev.frobeniusPrimeCount`: the number of primes of norm at most `x`
  whose arithmetic Frobenius class is `C`.
* `NumberField.Chebotarev.tendsto_frobeniusPrimeCount`: the prime count divided by `x / log x`
  tends to `#C / #Gal(L/K)`.
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

/-- The number of primes of `K` of norm at most `x` whose arithmetic Frobenius in `L/K`
belongs to `C`. Only primes unramified in `L` are counted. -/
noncomputable def frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℕ :=
  by
    classical
    exact ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)).card

/-- The Frobenius prime count is the generic count of its prime set. -/
@[simp]
theorem natCast_frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    (frobeniusPrimeCount K L C x : ℝ) = primeCount K (frobeniusPrimeSet K L C) x := by
  classical
  simpa only [frobeniusPrimeCount] using
    (primeCount_eq_card (frobeniusPrimeSet K L C) x).symm

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

/-- Qualitative prime-counting Chebotarev: the proportion relative to `x / log x` of primes
whose arithmetic Frobenius lies in `C` tends to `#C / #Gal(L/K)`. -/
theorem tendsto_frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ) / (x / Real.log x))
      atTop (𝓝 ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) := by
  let δ : ℝ := (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)
  have herror := (primeCount_sub_mul_logIntegral_isLittleO (K := K)
    (S := frobeniusPrimeSet K L C) (δ := δ) (by
    simpa only [← frobeniusTheta_def] using frobeniusTheta_asymptotic K L C)).tendsto_div_nhds_zero
  have hLi : Tendsto (fun x : ℝ ↦ Real.logIntegral x / (x / Real.log x)) atTop (𝓝 1) := by
    refine Real.tendsto_logIntegral_mul_log_div_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x _
    simp only [div_div_eq_mul_div]
  have h := herror.add (hLi.const_mul δ)
  have hcount : Tendsto
      (fun x : ℝ ↦ primeCount K (frobeniusPrimeSet K L C) x / (x / Real.log x))
      atTop (𝓝 ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) := by
    simpa only [zero_add, mul_one] using h.congr' (Eventually.of_forall fun x ↦ by
      dsimp [δ]
      ring)
  simpa only [← natCast_frobeniusPrimeCount] using hcount

/-- Natural-density Chebotarev: among the primes of `K`, the primes with arithmetic Frobenius
class `C` have density `#C / #Gal(L/K)`. -/
theorem hasNaturalDensity_frobeniusPrimeSet (C : ConjClasses (L ≃ₐ[K] L)) :
    NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L C)
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  apply NumberField.Set.hasNaturalDensity_of_isLittleO_logIntegral
  · exact primeCount_sub_mul_logIntegral_isLittleO (K := K)
      (S := frobeniusPrimeSet K L C) (δ :=
        (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) (by
      simpa only [← frobeniusTheta_def] using frobeniusTheta_asymptotic K L C)
  · exact primeCount_univ_sub_logIntegral_isLittleO K

end NumberField.Chebotarev
