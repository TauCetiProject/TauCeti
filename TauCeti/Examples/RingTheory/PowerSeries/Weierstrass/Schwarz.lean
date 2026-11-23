/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.GaussNorm
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.Analysis.Normed.Ring.DualNumber
import TauCeti.RingTheory.PowerSeries.CoeffProd
import TauCeti.RingTheory.PowerSeries.Weierstrass.Schwarz

/-!
# Examples and counterexamples for Schwarz contraction of power series

These examples exercise the two-radii Gauss-norm contraction and the characteristic-zero unit-disc
coefficient and evaluation bounds in `TauCeti.RingTheory.PowerSeries.Weierstrass.Schwarz`:

* **Sharpness over `ℚ_[p]`.** For `f = (X - 1) ^ S` over `ℚ_[p]` and any outer radius `r > 1`,
  `‖coeff k f‖ * r ^ k ≤ r ^ S` for all `k` and the iterated formal derivatives of order `j < S`
  vanish at `1`. Both `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` and
  `PowerSeries.norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero` give the bound
  `r ^ S * (r ^ S)⁻¹ = 1`, which is attained at `k = 0` and at `x = 0`.
* **Non-restricted boundary series over `ℚ_[p]`.** The series
  `f = (X - 1) * ∑ p ^ n X ^ n` over `ℚ_[p]` satisfies `‖coeff (n + 1) f‖ * p ^ (n + 1) = p` for
  every `n`, so it is *not* restricted at the outer radius `r = p` and restricted-series Schwarz
  bounds such as `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod` do not apply at
  `r = p`. Its weighted coefficients are nevertheless bounded by `M = p`, it vanishes at `1`, and
  `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` yields the sharp bound
  `‖coeff k f‖ ≤ 1` for all `k`.
* **Necessity of `‖a‖ ≤ 1`.** Over `ℚ_[p]` at radius `r = p > 1`, the polynomial `f = X - p⁻¹` has
  `‖coeff k f‖ * p ^ k ≤ p` for all `k` and vanishes at `a = p⁻¹`, which lies outside the unit disc
  (`‖p⁻¹‖ = p > 1`); its constant coefficient has norm `p > 1 = p * (p ^ 1)⁻¹`.
* **Trivial valuation: non-`NontriviallyNormedField` witness and necessity of `[CharZero K]`.**
  Equipping a field `F` with `AbsoluteValue.trivial` gives a complete ultrametric `NormedField`
  whose norms lie in `{0, 1}`, so it is never nontrivially normed. Taking `F = ℚ` exercises
  `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` outside
  `NontriviallyNormedField`. Taking `F = ZMod p` (`p` prime), the polynomial `f = X ^ p - 1`
  vanishes at `1` and has `(d⁄dX)^[j] f = 0` for every `j ≥ 1`, so all formal derivatives of order
  `< p + 1` vanish at `1`, yet at `r = 2` (`M = 2 ^ p`) we have
  `‖coeff 0 f‖ = 1 > 2⁻¹ = 2 ^ p * (2 ^ (p + 1))⁻¹`; meanwhile `(D⁽ᵖ⁾ f)(1) = 1 ≠ 0` and the
  Hasse-derivative contraction `PowerSeries.HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow_sum`
  applies in characteristic `p` with multiplicity `p`.
* **Integral domains vs. zero divisors.** Over `ℤ_[p]` (a non-field domain), two-radii Gauss-norm
  contraction applies directly; over `MaxDualNumber ℚ_[p]` (`ε ^ 2 = 0`, `‖ε‖ = 1`), the monomial
  `ε X` vanishes at both `0` and `ε` in the unit disc yet `‖ε X‖₁ = 1 > 2 * (1 / 2) ^ 2`, showing
  `[NoZeroDivisors R]` is necessary.
-/

open PowerSeries TauCeti.PowerSeries TauCeti.MaxDualNumber

namespace TauCeti.Examples

section PadicSharpness

variable (p : ℕ) [hp : Fact p.Prime]

-- Over `ℚ_[p]`, for `(X - 1) ^ S` and any `r > 1`, every coefficient and every unit-disc value has
-- norm at most `r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹`, attained at `k = 0` and `x = 0`.
example (S : ℕ) {r : ℝ} (hr : 1 < r) :
    (∀ k, ‖coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)‖ ≤
        r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹) ∧
      (∀ x : ℚ_[p], ‖x‖ ≤ 1 →
        ‖FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
            (fun k ↦ coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)) x‖ ≤
          r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹) ∧
      ‖coeff 0 ((X - 1 : ℚ_[p]⟦X⟧) ^ S)‖ =
        r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹ ∧
      ‖FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
          (fun k ↦ coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)) 0‖ =
        r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹ := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hfR : ((X - 1 : ℚ_[p]⟦X⟧) ^ S).IsRestricted r := by
    rw [← map_one C]
    exact (IsRestricted.subring r).pow_mem (isRestricted_X_sub_C (1 : ℚ_[p])) S
  have hM : ∀ k, ‖coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)‖ * r ^ k ≤ r ^ S := fun k ↦ by
    have hg := gaussNorm_X_sub_C_pow hr0.le (a := (1 : ℚ_[p])) (by simp [hr.le]) S
    rw [map_one] at hg
    exact hg ▸ le_gaussNorm norm r _ (hasGaussNorm_of_isRestricted hfR) k
  have hA : ∀ a ∈ ({1} : Finset ℚ_[p]), ‖a‖ ≤ 1 := by simp
  have hvan : ∀ a ∈ ({1} : Finset ℚ_[p]), ∀ j < S,
      FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
        (fun k ↦ coeff k ((⇑(derivative (R := ℚ_[p])))^[j] ((X - 1 : ℚ_[p]⟦X⟧) ^ S))) a = 0 := by
    intro a ha j hj
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [← evalAt_eq_ofScalarsSum, evalAt_iterate_derivative_eq_zero_iff, ← map_one C,
      evalAt_hasseDeriv_X_sub_C_pow]
    simp [hj.ne]
  refine ⟨norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero hr hM {1} hA S hvan,
    fun x hx ↦ norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero hr hM {1} hA S hvan
      hx, ?_, ?_⟩
  · simp [mul_inv_cancel₀ (pow_ne_zero S hr0.ne')]
  · simp [mul_inv_cancel₀ (pow_ne_zero S hr0.ne')]

end PadicSharpness

section BoundaryNonRestricted

variable (p : ℕ) [hp : Fact p.Prime]

-- `f = (X - 1) * ∑ p ^ n X ^ n` is not restricted at radius `p`, yet all its coefficients have
-- norm at most `1`, attained at `k = 0`.
example :
    let f : ℚ_[p]⟦X⟧ := (X - 1) * PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ n
    ¬ f.IsRestricted p ∧ (∀ k, ‖coeff k f‖ ≤ 1) ∧ ‖coeff 0 f‖ = 1 := by
  intro f
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsucc (n : ℕ) : ‖coeff (n + 1) f‖ * (p : ℝ) ^ (n + 1) = p := by
    have hunit : ‖(1 - p : ℚ_[p])‖ = 1 := by
      rw [sub_eq_add_neg]
      simpa [Padic.norm_p, inv_le_one_of_one_le₀ hp1.le] using
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ℚ_[p])) (y := -(p : ℚ_[p]))
          (by rw [norm_one, norm_neg, Padic.norm_p]; exact (inv_lt_one_of_one_lt₀ hp1).ne')
    have hcoeff : coeff (n + 1) f = (p : ℚ_[p]) ^ n * (1 - p) := by
      dsimp [f]
      rw [← map_one C, PowerSeries.coeff_succ_X_sub_C_mul, coeff_mk, coeff_mk]
      ring
    rw [hcoeff, norm_mul, hunit, mul_one, norm_pow, Padic.norm_p, inv_pow, pow_succ, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n hp0.ne'), one_mul]
  have hM : ∀ k, ‖coeff k f‖ * (p : ℝ) ^ k ≤ p := by
    rintro (_ | n)
    · dsimp [f]
      rw [← map_one C, PowerSeries.coeff_zero_X_sub_C_mul, coeff_mk]
      simp [hp1.le]
    · exact (hsucc n).le
  refine ⟨fun hrest ↦ ?_, fun k ↦ ?_, ?_⟩
  · have htend := ((PowerSeries.isRestricted_iff' _ _).mp hrest).comp
      (Filter.tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, hsucc] at htend
    exact hp0.ne (tendsto_nhds_unique htend tendsto_const_nhds)
  · have hg : (PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted 1 := by
      rw [PowerSeries.isRestricted_iff']
      simpa [Padic.norm_p] using tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hp1)
    have hX : (X - 1 : ℚ_[p]⟦X⟧).IsRestricted 1 := by
      simpa using isRestricted_X_sub_C (c := 1) (1 : ℚ_[p])
    have hvan : ∀ a ∈ ({1} : Finset ℚ_[p]), ∀ j < 1,
        FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
          (fun m ↦ coeff m ((⇑(derivative (R := ℚ_[p])))^[j] f)) a = 0 := by
      intro a ha j hj
      rw [Finset.mem_singleton] at ha
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      subst ha
      dsimp [f]
      rw [← evalAt_eq_ofScalarsSum, hX.evalAt_mul hg (by simp), ← map_one C, evalAt_X_sub_C]
      simp
    simpa [mul_inv_cancel₀ hp0.ne'] using
      norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero hp1 hM {1} (by simp) 1 hvan k
  · dsimp [f]
    rw [← map_one C, PowerSeries.coeff_zero_X_sub_C_mul, coeff_mk]
    simp

end BoundaryNonRestricted

section RejectionUnitDisc

variable (p : ℕ) [hp : Fact p.Prime]

-- Rejection test for `‖a‖ ≤ 1`: over `ℚ_[p]` at radius `r = p > 1`, the polynomial `f = X - p⁻¹`
-- satisfies `‖coeff k f‖ * p ^ k ≤ p` for all `k` and vanishes at `a = p⁻¹`, which violates
-- `‖a‖ ≤ 1`, and its constant coefficient has norm `p > 1 = p * (p ^ 1)⁻¹`.
example :
    (∀ k, ‖coeff k (X - C (p : ℚ_[p])⁻¹)‖ * (p : ℝ) ^ k ≤ p) ∧
      FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
        (fun k ↦ coeff k (X - C (p : ℚ_[p])⁻¹)) (p : ℚ_[p])⁻¹ = 0 ∧
      1 < ‖(p : ℚ_[p])⁻¹‖ ∧
      ¬ (‖coeff 0 (X - C (p : ℚ_[p])⁻¹)‖ ≤
          (p : ℝ) * ((p : ℝ) ^ (({(p : ℚ_[p])⁻¹} : Finset ℚ_[p]).card * 1))⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine ⟨fun k ↦ ?_, ?_, ?_, ?_⟩
  · rcases k with _ | _ | k
    · simp [Padic.norm_p]
    · simp
    · simp [coeff_X, Nat.cast_nonneg]
  · rw [← evalAt_eq_ofScalarsSum, evalAt_X_sub_C]
    simp
  · simpa [Padic.norm_p] using hp1
  · simp [Padic.norm_p, mul_inv_cancel₀ hp0, not_le.mpr hp1]

end RejectionUnitDisc

section TrivialValuationAndCharP

-- `WithAbs (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)` has no element of norm strictly greater
-- than `1`, and every coefficient of `X - 1` over it has norm at most
-- `2 * (2 ^ (({1} : Finset _).card * 1))⁻¹`.
example :
    let K := WithAbs (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
    (¬ ∃ x : K, 1 < ‖x‖) ∧
      ∀ k, ‖coeff k (X - 1 : K⟦X⟧)‖ ≤
        (2 : ℝ) * ((2 : ℝ) ^ (({1} : Finset K).card * 1))⁻¹ := by
  intro K
  refine ⟨fun ⟨x, hx⟩ ↦ (WithAbs.norm_trivial_le_one x).not_gt hx, fun k ↦ ?_⟩
  refine norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero (by norm_num : (1 : ℝ) < 2)
    (fun m ↦ ?_) {1} (fun a _ ↦ WithAbs.norm_trivial_le_one a) 1 (fun a ha j hj ↦ ?_) k
  · rcases m with _ | _ | m
    · simp
    · simp [coeff_X]
    · simp [coeff_X]
  · rw [Finset.mem_singleton] at ha
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    subst ha
    rw [Function.iterate_zero_apply, ← evalAt_eq_ofScalarsSum, ← map_one C, evalAt_X_sub_C]
    simp

-- Rejection test for `[CharZero K]`: over
-- `K = WithAbs (AbsoluteValue.trivial : AbsoluteValue (ZMod p) ℝ)` (`p` prime), the polynomial
-- `f = X ^ p - 1` has `‖coeff k f‖ * 2 ^ k ≤ 2 ^ p` for all `k` and all iterated formal derivatives
-- of order `j < p + 1` vanish at `1`, yet `‖coeff 0 f‖ = 1 > 2 ^ p * (2 ^ (p + 1))⁻¹`. By contrast,
-- `(D⁽ᵖ⁾ f)(1) = 1 ≠ 0` and the Hasse-derivative contraction bounds `‖f‖₁` by `1`.
example (p : ℕ) [hp : Fact p.Prime] :
    let K := WithAbs (AbsoluteValue.trivial : AbsoluteValue (ZMod p) ℝ)
    let f : K⟦X⟧ := X ^ p - 1
    (∀ k, ‖coeff k f‖ * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ p) ∧
      (∀ a ∈ ({1} : Finset K), ∀ j < p + 1,
        FormalMultilinearSeries.ofScalarsSum (E := K)
          (fun k ↦ coeff k ((⇑(derivative (R := K)))^[j] f)) a = 0) ∧
      ¬ (‖coeff 0 f‖ ≤ (2 : ℝ) ^ p * ((2 : ℝ) ^ (({1} : Finset K).card * (p + 1)))⁻¹) ∧
      (hasseDeriv p f).evalAt (1 : K) = 1 ∧
      f.gaussNorm norm 1 ≤ 1 := by
  intro K f
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have : CharP K⟦X⟧ p := charP_of_injective_ringHom PowerSeries.C_injective p
  have hsub : f = (X - C (1 : K)) ^ p := by
    dsimp [f]
    rw [map_one, sub_pow_char, one_pow]
  have hfR : f.IsRestricted 2 :=
    hsub ▸ (IsRestricted.subring 2).pow_mem (isRestricted_X_sub_C _) p
  have hfg : f.gaussNorm norm 2 = (2 : ℝ) ^ p :=
    hsub ▸ gaussNorm_X_sub_C_pow (by norm_num : (0 : ℝ) ≤ 2)
      ((WithAbs.norm_trivial_le_one _).trans (by norm_num)) p
  have hM : ∀ k, ‖coeff k f‖ * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ p := fun k ↦
    hfg ▸ le_gaussNorm norm 2 f (hasGaussNorm_of_isRestricted hfR) k
  have hderiv1 : derivative (R := K) f = 0 := by
    dsimp [f]
    rw [map_sub, derivative_X_pow, derivative_one]
    simp
  refine ⟨hM, fun a ha j hj ↦ ?_, ?_, ?_, ?_⟩
  · clear hj
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [← evalAt_eq_ofScalarsSum]
    rcases j with _ | j
    · rw [Function.iterate_zero_apply, hsub]
      simpa [hasseDeriv_zero, hp0.symm] using evalAt_hasseDeriv_X_sub_C_pow (1 : K) 0 p
    · rw [Function.iterate_succ_apply, hderiv1, iterate_derivative_zero, evalAt_zero]
  · have hc0 : ‖coeff 0 f‖ = 1 := by simp [hsub]
    have hRHS : (2 : ℝ) ^ p * ((2 : ℝ) ^ (({1} : Finset K).card * (p + 1)))⁻¹ = 2⁻¹ := by
      rw [Finset.card_singleton, one_mul, pow_succ]
      field_simp
    rw [hc0, hRHS]
    norm_num
  · rw [hsub, evalAt_hasseDeriv_X_sub_C_pow]
    simp
  · have hzero : ∀ b ∈ ({1} : Finset K), ∀ t < p, (hasseDeriv t f).evalAt b = 0 := by
      intro b hb t ht
      rw [Finset.mem_singleton] at hb
      subst hb
      rw [hsub, evalAt_hasseDeriv_X_sub_C_pow]
      simp [ht.ne]
    have hg := (hasGaussNorm_of_isRestricted hfR).gaussNorm_le_gaussNorm_mul_div_pow_sum
      (by norm_num : (0 : ℝ) < 2) zero_le_one (by norm_num) (A := {1}) (T := fun _ ↦ p)
      (fun b _ ↦ WithAbs.norm_trivial_le_one b) hzero
    simpa [hfg, inv_pow, mul_inv_cancel₀ (pow_ne_zero p (two_ne_zero : (2 : ℝ) ≠ 0))] using hg

end TrivialValuationAndCharP

section DomainAndZeroDivisors

variable (p : ℕ) [hp : Fact p.Prime]

-- Non-field domain witness: `ℤ_[p]` is not a field, yet
-- `PowerSeries.HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow_sum` applies directly over `ℤ_[p]`.
example : ¬ IsField ℤ_[p] ∧ (X - 1 : ℤ_[p]⟦X⟧).gaussNorm norm 1 ≤ 1 := by
  refine ⟨IsDiscreteValuationRing.not_isField ℤ_[p], ?_⟩
  have hX : (X - 1 : ℤ_[p]⟦X⟧).IsRestricted 2 := by
    simpa using isRestricted_X_sub_C (c := 2) (1 : ℤ_[p])
  have hg2 : (X - 1 : ℤ_[p]⟦X⟧).gaussNorm norm 2 = 2 := by
    simpa using gaussNorm_X_sub_C_pow (by norm_num : (0 : ℝ) ≤ 2) (a := (1 : ℤ_[p]))
      (by norm_num) 1
  have hzero : ∀ b ∈ ({1} : Finset ℤ_[p]), ∀ t < 1,
      (hasseDeriv t (X - 1 : ℤ_[p]⟦X⟧)).evalAt b = 0 := by
    intro b hb t ht
    rw [Finset.mem_singleton] at hb
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    subst hb
    rw [hasseDeriv_zero, LinearMap.id_apply, ← map_one C, evalAt_X_sub_C]
    simp
  simpa [hg2] using (hasGaussNorm_of_isRestricted hX).gaussNorm_le_gaussNorm_mul_div_pow_sum
    (by norm_num : (0 : ℝ) < 2) zero_le_one (by norm_num) (A := {1}) (T := fun _ ↦ 1) (by simp)
    hzero

-- Rejection test for `[NoZeroDivisors R]`: over `R = MaxDualNumber ℚ_[p]` (`ε ^ 2 = 0`, `‖ε‖ = 1`),
-- `f = monomial 1 ε` vanishes at both distinct points `0` and `ε` of the unit disc, yet
-- `‖f‖₁ = 1 > 2⁻¹ = ‖f‖₂ * (1 / 2) ^ ({0, ε}.card)`.
example [DecidableEq (MaxDualNumber ℚ_[p])] :
    let f : (MaxDualNumber ℚ_[p])⟦X⟧ := monomial 1 eps
    f.IsRestricted 2 ∧
      (∀ b ∈ ({0, eps} : Finset (MaxDualNumber ℚ_[p])), ‖b‖ ≤ 1) ∧
      (∀ b ∈ ({0, eps} : Finset (MaxDualNumber ℚ_[p])), ∀ t < 1,
        (hasseDeriv t f).evalAt b = 0) ∧
      ¬ (f.gaussNorm norm 1 ≤
          f.gaussNorm norm 2 * (1 / 2) ^ ∑ _b ∈ ({0, eps} : Finset (MaxDualNumber ℚ_[p])), 1) := by
  intro f
  have h0eps : (0 : MaxDualNumber ℚ_[p]) ≠ eps := fun h ↦ by simpa using congrArg norm h
  have hg (c : ℝ) (hc : 0 ≤ c) : f.gaussNorm norm c = c := by
    have h : f.gaussNorm norm c = ‖(eps : MaxDualNumber ℚ_[p])‖ * c ^ 1 :=
      PowerSeries.gaussNorm_monomial (v := normRingSeminorm (MaxDualNumber ℚ_[p])) (r := eps) hc 1
    simpa using h
  refine ⟨isRestricted_monomial 2 1 eps, ?_, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp
    · rw [Finset.mem_singleton.mp hb]; simp
  · intro b hb t ht
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    rw [hasseDeriv_zero, LinearMap.id_apply]
    dsimp [f]
    rw [evalAt_monomial, pow_one, smul_eq_mul]
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp
    · rw [Finset.mem_singleton.mp hb]; simp
  · rw [hg 1 zero_le_one, hg 2 (by norm_num), Finset.sum_const, Finset.card_pair h0eps]
    norm_num

end DomainAndZeroDivisors

end TauCeti.Examples
