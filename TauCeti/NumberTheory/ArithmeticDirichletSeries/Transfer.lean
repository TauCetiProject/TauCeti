/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.AbelSummation

import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# From the weighted prime count to the unweighted one

A prime-number-theorem argument delivers its conclusion for a *logarithmically weighted* count: a
Tauberian theorem applied to a logarithmic derivative sees the von Mangoldt coefficients, hence the
count `ψ` weighted by `log p` and taken over prime powers, and a separate elementary estimate for
the prime-power contribution passes from `ψ` to the count `ϑ` over primes alone.  The statement one
wants is about the *unweighted* count `π`.  This file carries out that last passage for the primes
of a number field, taking the asymptotic for `ϑ` as given: if `ϑ(x) = δx + o(x)`, then
`π(x) = δ Li(x) + o(x/log x)`, where `Li` is the offset logarithmic integral of
`TauCeti/Analysis/SpecialFunctions/LogIntegral.lean`.

The bridge is the exact Abel-summation identity
`TauCeti.primeCount_eq_primeTheta_div_log_add_integral` together with the
antiderivative identity `TauCeti.Real.logIntegral_eq_div_log_sub_add` for `Li`.  Subtracting the two
cancels the main terms and leaves
`TauCeti.primeCount_sub_mul_logIntegral_eq`, an identity valid for every `x ≥ 2` and every `δ`,
whose three remaining summands are each `o (x / log x)`.

Nothing here uses an analytic continuation or a nonvanishing statement: the hypothesis on `ϑ` is
taken as given, and the transfer covers the zero-density case `δ = 0` as well.

## Main results

* `TauCeti.primeCount_sub_mul_logIntegral_eq`: the exact identity
  `π(x) - δ Li(x) = (ϑ(x) - δx)/log x + ∫ t in 2..x, (ϑ(t) - δt)/(t log² t) + 2δ/log 2`.
* `TauCeti.primeCount_sub_mul_logIntegral_isLittleO`: the transfer itself, stated so that it covers
  the density `δ = 0` as well.
* `TauCeti.primeCount_asymptotic_of_primeTheta`: the quotient form `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`
  for every `δ`, and `TauCeti.primeCount_isLittleO_logIntegral` for the zero-density case, where
  `π(x) = o(Li x)` is the meaningful statement.
* `TauCeti.primeCount_sub_mul_logIntegral_sub_sum_eq` and
  `TauCeti.primeCount_sub_mul_logIntegral_sub_sum_isLittleO`: effective Abel-summation transfer on
  the de la Vallée Poussin scale `x exp (-c √log x)` with a finite sum of secondary power terms
  `∑ i ∈ s, a i * (x ^ β i / β i)` matching `∑ i ∈ s, a i * Li (x ^ β i)` with no loss in `c`,
  together with `TauCeti.primeCount_sub_mul_logIntegral_isLittleO_of_sub_sum_isBigO` absorbing
  secondary terms with `β i < 1` and
  `TauCeti.primeCount_sub_mul_logIntegral_isLittleO_of_isBigO_exp_neg_mul_sqrt_log` for the case
  without secondary terms.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.

Mathlib's `Chebyshev.primeCounting_sub_theta_div_log_isBigO` performs the same partial-summation
step for the rational primes; the argument below follows it, and replaces its explicit Chebyshev
bound by the hypothesis on `ϑ`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- The error term `ϑ(t) - δ t` is interval integrable: `ϑ` is monotone and `t ↦ δ t` is
continuous. -/
theorem intervalIntegrable_primeTheta_sub_const_mul (S : Set (HeightOneSpectrum (𝓞 K)))
    (δ a b : ℝ) :
    IntervalIntegrable (fun t ↦ primeTheta K S t - δ * t) volume a b :=
  (primeTheta_mono S).intervalIntegrable.sub
    (Continuous.intervalIntegrable (by fun_prop) a b)

/-- **The exact remainder identity.**  Subtracting `δ Li(x)` from the Abel-summation formula for
`π(x)` cancels the two `x / log x` main terms and leaves a boundary quotient, an integral against
`(t log² t)⁻¹` of the same error term, and the constant coming from the base point `2` of `Li`.

The identity holds for every real `δ`; no hypothesis relating `ϑ` and `δ` is used. -/
theorem primeCount_sub_mul_logIntegral_eq (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) {x : ℝ}
    (hx : 2 ≤ x) :
    primeCount K S x - δ * Real.logIntegral x =
      (primeTheta K S x - δ * x) / Real.log x +
        (∫ t in (2 : ℝ)..x, (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) +
        2 * δ / Real.log 2 := by
  have hsplit := Real.integral_div_mul_log_sq_eq_sub_add δ one_lt_two (by linarith)
    (primeTheta_mono S).intervalIntegrable
  rw [primeCount_eq_primeTheta_div_log_add_integral, ← intervalIntegral.integral_of_le hx, hsplit,
    Real.logIntegral_eq_div_log_sub_add hx, sub_div]
  ring

/-- **The transfer from `ϑ` to `π`.**  If the logarithmically weighted count of the primes of `S`
satisfies `ϑ(x) = δx + o(x)`, then the unweighted count satisfies `π(x) = δ Li(x) + o(x/log x)`.

Stated with an error term rather than as an equivalence, this covers `δ = 0` as well; the two
quotient forms are `TauCeti.primeCount_asymptotic_of_primeTheta` and
`TauCeti.primeCount_isLittleO_logIntegral`. -/
theorem primeCount_sub_mul_logIntegral_isLittleO
    (h : (fun x ↦ primeTheta K S x - δ * x) =o[atTop] id) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x) =o[atTop] fun x : ℝ ↦ x / Real.log x := by
  have hboundary : (fun x ↦ (primeTheta K S x - δ * x) / Real.log x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
    simpa [div_eq_mul_inv] using
      h.mul_isBigO (isBigO_refl (fun x : ℝ ↦ (Real.log x)⁻¹) atTop)
  have hintegral :
      (fun x ↦ ∫ t in (2 : ℝ)..x, (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) =o[atTop]
        fun x : ℝ ↦ x / Real.log x :=
    Real.isLittleO_integral_div_mul_log_sq
      (fun x _ ↦ intervalIntegrable_primeTheta_sub_const_mul S δ 2 x) h.isBigO
  have hconst := Real.isLittleO_const_div_log (2 * δ / Real.log 2)
  refine ((hboundary.add hintegral).add hconst).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact (primeCount_sub_mul_logIntegral_eq S δ hx).symm

/-- **The zero-density case.**  If the logarithmically weighted count of `S` is `o(x)`, then `S`
contains `o(Li x)` primes up to `x`.  An asymptotic equivalence is *not* the right statement here:
`π ~ 0` would force `π` to vanish eventually. -/
theorem primeCount_isLittleO_logIntegral (h : primeTheta K S =o[atTop] id) :
    primeCount K S =o[atTop] Real.logIntegral := by
  have h0 : (fun x ↦ primeCount K S x - (0 : ℝ) * Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x :=
    primeCount_sub_mul_logIntegral_isLittleO (by simpa using h)
  simpa using h0.trans_isBigO Real.logIntegral_isEquivalent_div_log.isBigO_symm

/-- **`ϑ(x) ∼ δx` implies `π(x) ∼ δ Li(x)`.**  This is the transfer the prime-number-theorem chain
consumes: it turns an asymptotic for `ϑ`, as produced by a Tauberian theorem, into one for `π`.
For `δ = 0` both asymptotic equivalences say that the counts vanish eventually. -/
theorem primeCount_asymptotic_of_primeTheta
    (h : primeTheta K S ~[atTop] fun x ↦ δ * x) :
    primeCount K S ~[atTop] fun x ↦ δ * Real.logIntegral x := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp only [zero_mul] at h ⊢
    exact isEquivalent_zero_iff_eventually_zero.2
      ((isEquivalent_zero_iff_eventually_zero.1 h).mono
        fun x hx ↦ primeCount_eq_zero_of_primeTheta_eq_zero hx)
  have hlin : (fun x : ℝ ↦ δ * x) =O[atTop] (id : ℝ → ℝ) :=
    (isBigO_refl (id : ℝ → ℝ) atTop).const_mul_left δ
  have h' : (fun x ↦ primeTheta K S x - δ * x) =o[atTop] id :=
    h.isLittleO.trans_isBigO hlin
  exact (primeCount_sub_mul_logIntegral_isLittleO h').trans_isBigO
    (Real.logIntegral_isEquivalent_div_log.isBigO_symm.const_mul_right hδ)

/-- **Exact remainder identity with power secondary terms.** Subtracting
`δ Li(x) + ∑ i ∈ s, a i * Li(x ^ β i)` from `π(x)` matches `δ x + ∑ i ∈ s, a i * (x ^ β i / β i)`
against `ϑ(x)` inside both the boundary term and the Abel-summation integral on `[2, x]`, leaving
only an explicit base-point constant at `2`. -/
theorem primeCount_sub_mul_logIntegral_sub_sum_eq {ι : Type*} (S : Set (HeightOneSpectrum (𝓞 K)))
    (δ : ℝ) (s : Finset ι) (a β : ι → ℝ) (hβ : ∀ i ∈ s, 0 < β i) {x : ℝ} (hx : 2 ≤ x) :
    primeCount K S x - δ * Real.logIntegral x - ∑ i ∈ s, a i * Real.logIntegral (x ^ β i) =
      (primeTheta K S x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)) / Real.log x +
        (∫ t in (2 : ℝ)..x,
          (primeTheta K S t - δ * t - ∑ i ∈ s, a i * (t ^ β i / β i)) / (t * Real.log t ^ 2)) +
        (2 * δ / Real.log 2 +
          ∑ i ∈ s, a i * (2 ^ β i / (β i * Real.log 2) - Real.logIntegral (2 ^ β i))) := by
  have hx1 : 1 < x := by linarith
  have hi0 : IntervalIntegrable
      (fun t ↦ (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) volume 2 x :=
    Real.intervalIntegrable_div_mul_log_sq one_lt_two hx1
      (intervalIntegrable_primeTheta_sub_const_mul S δ 2 x)
  have his : ∀ i ∈ s, IntervalIntegrable
      (fun t ↦ a i * ((t ^ β i / β i) / (t * Real.log t ^ 2))) volume 2 x := fun i _ ↦
    (Real.intervalIntegrable_div_mul_log_sq one_lt_two hx1 <|
      ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt <|
        (Real.continuousAt_rpow_const t (β i) (Or.inl (by
          rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]))).div_const _).const_mul _
  have hint : (∫ t in (2 : ℝ)..x,
        (primeTheta K S t - δ * t - ∑ i ∈ s, a i * (t ^ β i / β i)) / (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..x, (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) -
        ∑ i ∈ s, a i * ∫ t in (2 : ℝ)..x, (t ^ β i / β i) / (t * Real.log t ^ 2) := by
    have hcongr : (fun t ↦
          (primeTheta K S t - δ * t - ∑ i ∈ s, a i * (t ^ β i / β i)) / (t * Real.log t ^ 2)) =
        fun t ↦ (primeTheta K S t - δ * t) / (t * Real.log t ^ 2) -
          ∑ i ∈ s, a i * ((t ^ β i / β i) / (t * Real.log t ^ 2)) := by
      funext t
      rw [sub_div, Finset.sum_div]
      simp only [mul_div_assoc]
    have hsum_int : IntervalIntegrable
        (fun t ↦ ∑ i ∈ s, a i * ((t ^ β i / β i) / (t * Real.log t ^ 2))) volume 2 x := by
      rw [← Finset.sum_fn]
      exact IntervalIntegrable.sum s his
    rw [hcongr, intervalIntegral.integral_sub hi0 hsum_int, intervalIntegral.integral_finsetSum his]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ intervalIntegral.integral_const_mul _ _
  have hbnd : (primeTheta K S x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)) / Real.log x =
      (primeTheta K S x - δ * x) / Real.log x -
        ∑ i ∈ s, a i * ((x ^ β i / β i) / Real.log x) := by
    rw [sub_div, Finset.sum_div]
    simp only [mul_div_assoc]
  have hsec : ∑ i ∈ s, a i * ((x ^ β i / β i) / Real.log x) +
        ∑ i ∈ s, a i * ∫ t in (2 : ℝ)..x, (t ^ β i / β i) / (t * Real.log t ^ 2) =
      ∑ i ∈ s, a i * Real.logIntegral (x ^ β i) +
        ∑ i ∈ s, a i * (2 ^ β i / (β i * Real.log 2) - Real.logIntegral (2 ^ β i)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hid := Real.rpow_div_mul_log_add_integral_eq_logIntegral_rpow (hβ i hi) hx1
    rw [← mul_add, div_div, hid]
    ring
  rw [primeCount_sub_mul_logIntegral_eq S δ hx, hint, hbnd]
  linarith [hsec]

/-- Auxiliary positive-exponent case of `primeCount_sub_mul_logIntegral_sub_sum_isLittleO`. -/
private theorem primeCount_sub_mul_logIntegral_sub_sum_isLittleO_of_pos {ι : Type*}
    (s : Finset ι) (a β : ι → ℝ) {c : ℝ} (hβ : ∀ i ∈ s, 0 < β i)
    (h : (fun x ↦ primeTheta K S x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x -
      ∑ i ∈ s, a i * Real.logIntegral (x ^ β i)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  set E : ℝ → ℝ := fun x ↦ primeTheta K S x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)
  have hinv_log : (fun x : ℝ ↦ (Real.log x)⁻¹) =o[atTop] fun _ : ℝ ↦ (1 : ℝ) := by
    rw [isLittleO_one_iff]
    exact tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hboundary : (fun x ↦ E x / Real.log x) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
    simpa [div_eq_mul_inv] using h.mul_isLittleO hinv_log
  have hintegral := Real.isLittleO_integral_div_mul_log_sq_of_isBigO_exp_neg_mul_sqrt_log h
  have hconst : (fun _ : ℝ ↦ 2 * δ / Real.log 2 +
      ∑ i ∈ s, a i * (2 ^ β i / (β i * Real.log 2) - Real.logIntegral (2 ^ β i))) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
    simpa only [Real.rpow_zero, mul_one] using
      (Real.isLittleO_rpow_mul_exp_neg_mul_sqrt_log zero_lt_one c).const_mul_left
        (2 * δ / Real.log 2 +
          ∑ i ∈ s, a i * (2 ^ β i / (β i * Real.log 2) - Real.logIntegral (2 ^ β i)))
  refine ((hboundary.add hintegral).add hconst).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact (primeCount_sub_mul_logIntegral_sub_sum_eq S δ s a β hβ hx).symm

/-- **Effective transfer from `ϑ` to `π` with secondary power terms.** If
`ϑ(x) = δ x + ∑ i ∈ s, a i * (x ^ β i / β i) + O(x exp (-c √log x))`, then
`π(x) = δ Li(x) + ∑ i ∈ s, a i * Li(x ^ β i) + o(x exp (-c √log x))` with no loss in `c`. -/
theorem primeCount_sub_mul_logIntegral_sub_sum_isLittleO {ι : Type*} (s : Finset ι)
    (a β : ι → ℝ) {c : ℝ}
    (h : (fun x ↦ primeTheta K S x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x -
      ∑ i ∈ s, a i * Real.logIntegral (x ^ β i)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  classical
  set sPos := s.filter fun i ↦ 0 < β i
  set sNonpos := s.filter fun i ↦ ¬ 0 < β i
  have hnonpos : (fun x : ℝ ↦ ∑ i ∈ sNonpos, a i * (x ^ β i / β i)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) :=
    IsLittleO.fun_sum fun i hi ↦ by
      have hβi : β i ≤ 0 := not_lt.mp (Finset.mem_filter.mp hi).2
      have hrpow := (Real.isLittleO_rpow_mul_exp_neg_mul_sqrt_log
        (lt_of_le_of_lt hβi zero_lt_one) c).const_mul_left (a i / β i)
      exact hrpow.congr' (Eventually.of_forall fun x ↦ by ring) EventuallyEq.rfl
  have hpos : (fun x ↦ primeTheta K S x - δ * x - ∑ i ∈ sPos, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
    refine (h.add hnonpos.isBigO).congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
    have hpart := Finset.sum_filter_add_sum_filter_not s (fun i ↦ 0 < β i)
      (fun i ↦ a i * (x ^ β i / β i))
    linarith
  refine (primeCount_sub_mul_logIntegral_sub_sum_isLittleO_of_pos sPos a β
    (fun i hi ↦ (Finset.mem_filter.mp hi).2) hpos).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hpart := Finset.sum_filter_add_sum_filter_not s (fun i ↦ 0 < β i)
    (fun i ↦ a i * Real.logIntegral (x ^ β i))
  have hzero : ∑ i ∈ sNonpos, a i * Real.logIntegral (x ^ β i) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      have hβi : β i ≤ 0 := not_lt.mp (Finset.mem_filter.mp hi).2
      rw [Real.logIntegral_of_le_one (Real.rpow_le_one_of_one_le_of_nonpos hx hβi), mul_zero]
  linarith

/-- **Effective transfer absorbing sublinear secondary terms.** When every exponent satisfies
`β i < 1`, each `Li (x ^ β i)` is itself `o(x exp (-c √log x))`, so an expansion of `ϑ(x)` with
secondary power terms transfers to `π(x) = δ Li(x) + o(x exp (-c √log x))`. -/
theorem primeCount_sub_mul_logIntegral_isLittleO_of_sub_sum_isBigO {ι : Type*}
    (s : Finset ι) (a β : ι → ℝ) {c : ℝ} (hβ : ∀ i ∈ s, β i < 1)
    (h : (fun x ↦ primeTheta K S x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  have hmain := primeCount_sub_mul_logIntegral_sub_sum_isLittleO s a β h
  have hsec : (fun x : ℝ ↦ ∑ i ∈ s, a i * Real.logIntegral (x ^ β i)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) :=
    IsLittleO.fun_sum fun i hi ↦
      (Real.isLittleO_logIntegral_rpow_mul_exp_neg_mul_sqrt_log (hβ i hi) c).const_mul_left (a i)
  exact (hmain.add hsec).congr' (Eventually.of_forall fun x ↦ sub_add_cancel _ _) EventuallyEq.rfl

/-- **Effective transfer from `ϑ` to `π` on the de la Vallée Poussin scale.** If
`ϑ(x) = δ x + O(x exp (-c √log x))`, then `π(x) = δ Li(x) + o(x exp (-c √log x))` with no loss in
the constant `c`. -/
theorem primeCount_sub_mul_logIntegral_isLittleO_of_isBigO_exp_neg_mul_sqrt_log {c : ℝ}
    (h : (fun x ↦ primeTheta K S x - δ * x) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  simpa only [Finset.sum_empty, sub_zero] using
    primeCount_sub_mul_logIntegral_sub_sum_isLittleO (∅ : Finset Unit) 0 0
      (by simpa only [Finset.sum_empty, sub_zero] using h)

end TauCeti
