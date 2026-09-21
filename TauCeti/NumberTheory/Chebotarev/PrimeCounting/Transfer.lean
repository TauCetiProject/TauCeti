/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# Transferring Frobenius weighted counts

The Frobenius `ψ` and `ϑ` functions use different carriers: `frobeniusPsi` retains all prime
powers whose powered Artin class is the chosen conjugacy class, while `frobeniusTheta` retains only
the underlying primes. The higher-prime-power estimate already proved for the former is therefore
the precise input needed to transfer a linear asymptotic from `ψ` to `ϑ`.

The results isolate the elementary `ψ → ϑ → π` transfer from its analytic input and express its
unweighted count using the canonical Frobenius prime-counting carrier.

## Main results

* `frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO` removes higher prime powers
  from a Frobenius asymptotic.
* `tendsto_frobeniusTheta` is the corresponding quotient form.
* `frobeniusPrimeCount_asymptotic_of_tendsto_frobeniusPsi_div` and
  `tendsto_frobeniusPrimeCount` transfer the result to the unweighted count.

The transfer statements are parameterized by their analytic asymptotic hypotheses, separating the
elementary counting deductions from the theorem that supplies those hypotheses.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti Asymptotics
open scoped Asymptotics NumberField Topology
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

variable (K L) in
/-- The number of primes in the Frobenius fibre with absolute norm at most `x`. -/
noncomputable def frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℕ := by
  classical
  exact ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)).card

/-- The Frobenius prime count as the cardinality of its filtered prime carrier. -/
theorem frobeniusPrimeCount_apply (C : ConjClasses (L ≃ₐ[K] L))
    [DecidablePred (fun v ↦ v ∈ frobeniusPrimeSet K L C)] (x : ℝ) :
    frobeniusPrimeCount K L C x =
      ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)).card := by
  classical
  simp [frobeniusPrimeCount]

/-- The real coercion of the Frobenius prime count is the generic prime count of its fibre. -/
theorem frobeniusPrimeCount_eq_primeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    (frobeniusPrimeCount K L C x : ℝ) = primeCount K (frobeniusPrimeSet K L C) x := by
  classical
  simpa [frobeniusPrimeCount] using
    (primeCount_eq_card (K := K) (S := frobeniusPrimeSet K L C) x).symm

/-- The little-`o` asymptotic for a Frobenius `ϑ` fibre obtained by removing its higher prime
powers.

The hypothesis is stated for `ψ` rather than as a bundled boundary object, so this bridge can be
used by either a Tauberian theorem or a crossing argument. -/
theorem frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hψ : (fun x : ℝ ↦ frobeniusPsi K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    (fun x : ℝ ↦ frobeniusTheta K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
  refine ((hψ.sub (frobeniusPsi_sub_frobeniusTheta_isLittleO C)).congr
    (fun x ↦ ?_) fun _ ↦ rfl)
  ring

/-- A quotient-form Frobenius `ϑ` asymptotic follows from the corresponding `ψ` asymptotic. -/
theorem tendsto_frobeniusTheta
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hψ : Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop (𝓝 δ)) :
    Tendsto (fun x : ℝ ↦ frobeniusTheta K L C x / x) atTop (𝓝 δ) := by
  have hψ' := isLittleO_sub_mul_id_of_tendsto_div hψ
  have hsmall := frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO C hψ'
  have hθ := hsmall.tendsto_div_nhds_zero
  have hlim : Tendsto
      (fun x : ℝ ↦ (frobeniusTheta K L C x - δ * x) / x + δ) atTop (𝓝 δ) :=
    by simpa using hθ.add (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ δ) atTop (𝓝 δ))
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp
  ring

/-- The qualitative prime-counting asymptotic obtained from a Frobenius `ψ` quotient limit.

This is the `ψ → ϑ → π` part of the counting argument. The hypothesis is a quotient limit for
the weighted Frobenius count. -/
theorem frobeniusPrimeCount_asymptotic_of_tendsto_frobeniusPsi_div
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ} (hδ : δ ≠ 0)
    (hψ : Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop (𝓝 δ)) :
    (fun x ↦ (frobeniusPrimeCount K L C x : ℝ)) ~[atTop]
      fun x : ℝ ↦ δ * Real.logIntegral x := by
  have hψ' := isLittleO_sub_mul_id_of_tendsto_div hψ
  have hθ : (fun x : ℝ ↦ frobeniusTheta K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
    frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO C hψ'
  have hθ' : (fun x : ℝ ↦ primeTheta K (frobeniusPrimeSet K L C) x - δ * x) =o[atTop]
      fun x : ℝ ↦ x := by
    have heq : ∀ x : ℝ, frobeniusTheta K L C x =
        primeTheta K (frobeniusPrimeSet K L C) x := by
      intro x
      rw [frobeniusTheta_apply, primeTheta_apply]
    exact hθ.congr' (Eventually.of_forall fun x ↦ by
      simpa only [Pi.sub_apply] using congrArg (fun t ↦ t - δ * x) (heq x)) EventuallyEq.rfl
  have hθeq : primeTheta K (frobeniusPrimeSet K L C) ~[atTop]
      fun x : ℝ ↦ δ * x := by
    rw [Asymptotics.IsEquivalent]
    exact (hθ'.const_mul_right hδ).congr'
      (Eventually.of_forall fun x ↦ by simp) EventuallyEq.rfl
  simpa only [frobeniusPrimeCount_eq_primeCount] using
    (primeCount_asymptotic_of_primeTheta
      (K := K) (S := frobeniusPrimeSet K L C) hδ hθeq)

/-- The prime-counting quotient form obtained from a Frobenius `ψ` quotient limit. -/
theorem tendsto_frobeniusPrimeCount
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hψ : Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop (𝓝 δ)) :
    Tendsto
      (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ) / (x / Real.log x)) atTop
        (𝓝 δ) := by
  have hψ' := isLittleO_sub_mul_id_of_tendsto_div hψ
  have hθ : (fun x : ℝ ↦ frobeniusTheta K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
    frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO C hψ'
  have hcount := primeCount_sub_mul_logIntegral_isLittleO
    (K := K) (S := frobeniusPrimeSet K L C) (δ := δ) (by
      have heq : ∀ x : ℝ, frobeniusTheta K L C x =
          primeTheta K (frobeniusPrimeSet K L C) x := by
        intro x
        rw [frobeniusTheta_apply, primeTheta_apply]
      exact hθ.congr' (Eventually.of_forall fun x ↦ by
        simpa only [Pi.sub_apply] using congrArg (fun t ↦ t - δ * x) (heq x)) EventuallyEq.rfl)
  have herror := hcount.tendsto_div_nhds_zero
  have hli : Tendsto
    (fun x : ℝ ↦ Real.logIntegral x / (x / Real.log x)) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      have hlog : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
      exact div_ne_zero hx0 hlog)).mp
      Real.logIntegral_isEquivalent_div_log
  have hsum : Tendsto
      (fun x : ℝ ↦ (primeCount K (frobeniusPrimeSet K L C) x -
        δ * Real.logIntegral x) / (x / Real.log x) +
        δ * (Real.logIntegral x / (x / Real.log x))) atTop (𝓝 δ) := by
    simpa only [zero_add, mul_one] using herror.add (tendsto_const_nhds.mul hli)
  have hprime : Tendsto
      (fun x : ℝ ↦ primeCount K (frobeniusPrimeSet K L C) x / (x / Real.log x)) atTop
        (𝓝 δ) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    field_simp
    ring
  simpa only [frobeniusPrimeCount_eq_primeCount] using hprime

end NumberField.Chebotarev
