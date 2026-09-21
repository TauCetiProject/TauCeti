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

This file also introduces the unweighted count of a Frobenius fibre and identifies it with the
generic prime count. The later analytic theorem supplies the `ψ` asymptotic; these results isolate
the elementary `ψ → ϑ → π` part from that analytic input.

## Main results

* `frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO` removes higher prime powers
  from a Frobenius asymptotic.
* `tendsto_frobeniusTheta_div_of_tendsto_frobeniusPsi_div` is the corresponding quotient form.
* `frobeniusPrimeCount` and `frobeniusPrimeCount_eq_primeCount` provide the canonical unweighted
  Frobenius count and its generic arithmetic realization.
* `frobeniusPrimeCount_sub_mul_logIntegral_isLittleO` applies Abel summation to that count.
* `frobeniusPrimeCount_asymptotic_of_tendsto_frobeniusPsi_div` packages the resulting asymptotic
  in the logarithmic-integral normalization.

The transfer statements are deliberately parameterized by their analytic asymptotic hypotheses:
they do not assume the Chebotarev theorem they are intended to support.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti Asymptotics
open scoped Asymptotics NumberField Topology
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- The little-`o` asymptotic for a Frobenius `ϑ` fibre obtained by removing its higher prime
powers.

The hypothesis is stated for `ψ` rather than as a bundled boundary object, so this bridge can be
used by either a Tauberian theorem or a later crossing argument. -/
theorem frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hψ : (fun x : ℝ ↦ frobeniusPsi K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    (fun x : ℝ ↦ frobeniusTheta K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
  refine ((hψ.sub (frobeniusPsi_sub_frobeniusTheta_isLittleO C)).congr
    (fun x ↦ ?_) fun _ ↦ rfl)
  ring

/-- A quotient-form Frobenius `ϑ` asymptotic follows from the corresponding `ψ` asymptotic. -/
theorem tendsto_frobeniusTheta_div_of_tendsto_frobeniusPsi_div
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hψ : Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop (𝓝 δ)) :
    Tendsto (fun x : ℝ ↦ frobeniusTheta K L C x / x) atTop (𝓝 δ) := by
  have hψ' : (fun x : ℝ ↦ frobeniusPsi K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
    refine (isLittleO_iff_tendsto'
      ((eventually_ne_atTop (0 : ℝ)).mono fun _ hx hzero ↦ (hx hzero).elim)).2 ?_
    have h := hψ.sub_const δ
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  have hsmall := frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO C hψ'
  have hθ := hsmall.tendsto_div_nhds_zero
  have hlim : Tendsto
      (fun x : ℝ ↦ (frobeniusTheta K L C x - δ * x) / x + δ) atTop (𝓝 δ) :=
    by simpa using hθ.add (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ δ) atTop (𝓝 δ))
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp
  ring

variable (K L) in
/-- The number of primes in a Frobenius fibre with absolute norm at most `x`. -/
noncomputable def frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℕ :=
  Nat.card {𝔭 : HeightOneSpectrum (𝓞 K) //
    𝔭 ∈ frobeniusPrimeSet K L C ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x}

/-- The Frobenius prime count is the generic prime count of its Frobenius fibre. -/
theorem frobeniusPrimeCount_eq_primeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    (frobeniusPrimeCount K L C x : ℝ) =
      primeCount K (frobeniusPrimeSet K L C) x := by
  classical
  rw [frobeniusPrimeCount, primeCount_eq_card]
  let e : {𝔭 : HeightOneSpectrum (𝓞 K) //
      𝔭 ∈ frobeniusPrimeSet K L C ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} ≃
      ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)) :=
    { toFun := fun 𝔭 ↦ ⟨𝔭.1, Finset.mem_filter.mpr ⟨by
          simpa only [mem_normLE] using 𝔭.2.2, 𝔭.2.1⟩⟩
      invFun := fun 𝔭 ↦ ⟨𝔭.1, (Finset.mem_filter.mp 𝔭.2).2, by
          simpa only [mem_normLE] using (Finset.mem_filter.mp 𝔭.2).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let _ : Fintype {𝔭 : HeightOneSpectrum (𝓞 K) //
      𝔭 ∈ frobeniusPrimeSet K L C ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} :=
    Fintype.ofEquiv _ e.symm
  rw [Nat.card_eq_fintype_card]
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe] at hc
  exact_mod_cast hc

/-- The Frobenius prime count inherits the generic Abel-summation error estimate from its `ϑ`
fibre. -/
theorem frobeniusPrimeCount_sub_mul_logIntegral_isLittleO
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hθ : (fun x : ℝ ↦ frobeniusTheta K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ) - δ * Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
  have hcount := primeCount_sub_mul_logIntegral_isLittleO
    (K := K) (S := frobeniusPrimeSet K L C) (δ := δ) (by
      have heq : ∀ x : ℝ, frobeniusTheta K L C x =
          primeTheta K (frobeniusPrimeSet K L C) x := by
        intro x
        rw [frobeniusTheta_apply, primeTheta_apply]
      exact hθ.congr' (Eventually.of_forall fun x ↦ by
        simpa only [Pi.sub_apply] using congrArg (fun t ↦ t - δ * x) (heq x)) EventuallyEq.rfl)
  refine hcount.congr' ?_ EventuallyEq.rfl
  filter_upwards [] with x
  rw [frobeniusPrimeCount_eq_primeCount]

/-- The qualitative prime-counting asymptotic obtained from a Frobenius `ψ` quotient limit.

This is the `ψ → ϑ → π` part of the counting argument. The hypothesis is the analytic output
that the weighted Chebotarev theorem still has to provide. -/
theorem frobeniusPrimeCount_asymptotic_of_tendsto_frobeniusPsi_div
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ} (hδ : δ ≠ 0)
    (hψ : Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop (𝓝 δ)) :
    (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ)) ~[atTop]
      fun x : ℝ ↦ δ * Real.logIntegral x := by
  have hψ' : (fun x : ℝ ↦ frobeniusPsi K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
    refine (isLittleO_iff_tendsto'
      ((eventually_ne_atTop (0 : ℝ)).mono fun _ hx hzero ↦ (hx hzero).elim)).2 ?_
    have h := hψ.sub_const δ
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
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
  have hcount := primeCount_asymptotic_of_primeTheta
    (K := K) (S := frobeniusPrimeSet K L C) hδ hθeq
  have hcount' : (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ)) ~[atTop]
      fun x : ℝ ↦ δ * Real.logIntegral x := by
    rw [Asymptotics.IsEquivalent]
    refine hcount.isLittleO.congr' ?_ EventuallyEq.rfl
    filter_upwards [] with x
    simpa only [Pi.sub_apply] using congrArg (fun t : ℝ ↦
      t - δ * Real.logIntegral x) (frobeniusPrimeCount_eq_primeCount C x).symm
  exact hcount'

/-- The prime-counting quotient form obtained from a Frobenius `ψ` quotient limit. -/
theorem tendsto_frobeniusPrimeCount_div_log_of_tendsto_frobeniusPsi_div
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ}
    (hψ : Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop (𝓝 δ)) :
    Tendsto
      (fun x : ℝ ↦ (frobeniusPrimeCount K L C x : ℝ) / (x / Real.log x)) atTop (𝓝 δ) := by
  have hψ' : (fun x : ℝ ↦ frobeniusPsi K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
    refine (isLittleO_iff_tendsto'
      ((eventually_ne_atTop (0 : ℝ)).mono fun _ hx hzero ↦ (hx hzero).elim)).2 ?_
    have h := hψ.sub_const δ
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  have hθ : (fun x : ℝ ↦ frobeniusTheta K L C x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
    frobeniusTheta_sub_mul_isLittleO_of_frobeniusPsi_sub_mul_isLittleO C hψ'
  have hcount := frobeniusPrimeCount_sub_mul_logIntegral_isLittleO C hθ
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
      (fun x : ℝ ↦ ((frobeniusPrimeCount K L C x : ℝ) -
        δ * Real.logIntegral x) / (x / Real.log x) +
        δ * (Real.logIntegral x / (x / Real.log x))) atTop (𝓝 δ) := by
    simpa only [zero_add, mul_one] using herror.add (tendsto_const_nhds.mul hli)
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  field_simp
  ring

end NumberField.Chebotarev
