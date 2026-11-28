/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters

/-!
# A parameter bound for cyclotomic differents

The bound collects a nonnegative budget for a vacuum vector, the constants of the quadratic
base, and the absolute logarithms of the cyclotomic derivative at the primitive roots of the
fixed base level. It absorbs the placewise error in the norm of a different generator, whose
common scale is the tower degree times `√d`. The loss in passing from this common scale to a
placewise norm is small relative to the logarithm of the cutoff.

The normalization and scale comparison follow `New.Parameters.constantBound` and
`New.Data.hasLogBound_deltaE` in `New/Reduction/Data/AdmissibleData.lean` and
`New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Polynomial Real
open scoped NNReal

namespace TauCeti.OneSidedBound.Parameters

/-- The fixed parameter constant `C_P` is the sum of:
* `vacuumBound`, the exponent coefficient in the bound for conjugates of the integral vacuum;
* `2d + 6` and `q₀`, which cover the quadratic prime, `64`, the base modulus and its totient;
* `|γ − Re (L′/L)(1, χ_K)|`, the correction for the archimedean scale from Euler's constant
  and the quadratic `L`-function;
* `∑_ζ |log ‖Φ′_{q₀}(ζ)‖|` over the primitive `q₀`-th roots of unity, which bounds the
  placewise logarithmic error of the different generator. -/
noncomputable def constantBound (P : Parameters) (vacuumBound : ℝ≥0) : ℝ :=
  (vacuumBound : ℝ) + (2 * (P.d : ℝ) + 6) + (P.q₀ : ℝ) +
    |eulerMascheroniConstant -
      (logDeriv (DirichletCharacter.LFunction
        ((quadraticChar (ZMod P.d)).ringHomComp (Int.castRingHom ℂ))) 1).re| +
    ∑ ζ ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval ζ‖|

/-- Formula for the parameter bound in terms of the quadratic character and the primitive
roots at the base level. -/
theorem constantBound_def (P : Parameters) (vacuumBound : ℝ≥0) :
    P.constantBound vacuumBound = (vacuumBound : ℝ) + (2 * (P.d : ℝ) + 6) + (P.q₀ : ℝ) +
      |eulerMascheroniConstant -
        (logDeriv (DirichletCharacter.LFunction
          ((quadraticChar (ZMod P.d)).ringHomComp (Int.castRingHom ℂ))) 1).re| +
      ∑ ζ ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval ζ‖| := (rfl)

/-- The fixed parameter constant dominates the vacuum budget. -/
theorem vacuumBound_le_constantBound (P : Parameters) (vacuumBound : ℝ≥0) :
    (vacuumBound : ℝ) ≤ P.constantBound vacuumBound := by
  rw [P.constantBound_def]
  calc
    _ ≤ (vacuumBound : ℝ) + (2 * (P.d : ℝ) + 6) := le_add_of_nonneg_right (by positivity)
    _ ≤ _ + (P.q₀ : ℝ) := le_add_of_nonneg_right (by positivity)
    _ ≤ _ + _ := le_add_of_nonneg_right (abs_nonneg _)
    _ ≤ _ := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- The bound dominates the quadratic prime and the modulus, and is at least `64`. -/
theorem max_le_constantBound (P : Parameters) (vacuumBound : ℝ≥0) :
    max 64 (max (P.d : ℝ) (P.q₀ : ℝ)) ≤ P.constantBound vacuumBound := by
  have hd : (64 : ℝ) ≤ P.d := by exact_mod_cast P.sixty_four_lt_d.le
  rw [max_le_iff, max_le_iff, P.constantBound_def]
  have hv : 0 ≤ (vacuumBound : ℝ) := vacuumBound.coe_nonneg
  have hq : 0 ≤ (P.q₀ : ℝ) := by positivity
  have hsum : 0 ≤ ∑ ζ ∈ primitiveRoots P.q₀ ℂ,
      |log ‖(cyclotomic P.q₀ ℂ).derivative.eval ζ‖| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have ha := abs_nonneg (eulerMascheroniConstant -
    (logDeriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod P.d)).ringHomComp (Int.castRingHom ℂ))) 1).re)
  exact ⟨by linarith only [hd, hv, hq, ha, hsum], by linarith only [hd, hv, hq, ha, hsum],
    by linarith only [hd, hv, ha, hsum]⟩

/-- The totient of the base level is also bounded by the parameter constant. -/
theorem totient_le_constantBound (P : Parameters) (vacuumBound : ℝ≥0) :
    (P.q₀.totient : ℝ) ≤ P.constantBound vacuumBound :=
  (Nat.cast_le.mpr (Nat.totient_le _)).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (P.max_le_constantBound vacuumBound)))

/-- The total logarithmic error budget at the primitive roots of the base level fits in the
parameter bound, independently of the tower exponent. -/
theorem sum_abs_log_norm_eval_cyclotomic_derivative_le_constantBound (P : Parameters)
    (vacuumBound : ℝ≥0) :
    ∑ ζ ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval ζ‖| ≤
      P.constantBound vacuumBound := by
  rw [P.constantBound_def]
  exact le_add_of_nonneg_left (by positivity)

/-- The quadratic `L`-function correction to the archimedean scale fits in the parameter bound. -/
theorem abs_eulerMascheroniConstant_sub_re_logDeriv_le_constantBound (P : Parameters)
    (vacuumBound : ℝ≥0) :
    |eulerMascheroniConstant -
      (logDeriv (DirichletCharacter.LFunction
        ((quadraticChar (ZMod P.d)).ringHomComp (Int.castRingHom ℂ))) 1).re| ≤
      P.constantBound vacuumBound := by
  rw [P.constantBound_def]
  exact (le_add_of_nonneg_left (by positivity)).trans
    (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))

/-- Once the log-log cutoff is at least `10¹²` times the parameter bound, the logarithm of the
cutoff itself dominates that bound. -/
theorem constantBound_le_log (P : Parameters) (vacuumBound : ℝ≥0) {b : ℕ}
    (hb : 10 ^ 12 * P.constantBound vacuumBound ≤ log (log (b : ℝ))) :
    P.constantBound vacuumBound ≤ log (b : ℝ) := by
  have h64 : (64 : ℝ) ≤ P.constantBound vacuumBound :=
    (le_max_left _ _).trans (P.max_le_constantBound vacuumBound)
  linarith [Real.log_le_self (Real.log_natCast_nonneg b)]

/-- A positive factor `A` whose absolute logarithm fits the parameter bound preserves the
`[x¹⁰, x¹²]` budget for a norm of scale `T * √d` under the cutoff and scale inequalities.
For the placewise size of a different generator, take `T = towerDeg s`. -/
theorem mul_sqrt_mem_Icc (P : Parameters) (vacuumBound : ℝ≥0) {b : ℕ} {x A T : ℝ}
    (hb : 10 ^ 12 * P.constantBound vacuumBound ≤ log (log (b : ℝ)))
    (hx : log (b : ℝ) ^ 100 ≤ x)
    (hT₁ : x ^ 11 ≤ T) (hT₂ : T ≤ x ^ 11 * log (b : ℝ) ^ (1 / 5 : ℝ))
    (hA : 0 < A) (hlog : |log A| ≤ P.constantBound vacuumBound) :
    A * T * √(P.d : ℝ) ∈ Set.Icc (x ^ 10) (x ^ 12) := by
  have hC := P.max_le_constantBound vacuumBound
  have h64 : (64 : ℝ) ≤ P.constantBound vacuumBound := (le_max_left _ _).trans hC
  have hlogb : 0 < log (b : ℝ) := lt_of_le_of_ne (Real.log_natCast_nonneg b) (by
    intro he
    rw [← he, Real.log_zero] at hb
    linarith)
  have hxpos : 0 < x := (pow_pos hlogb _).trans_le hx
  have hlogs : 100 * log (log (b : ℝ)) ≤ log x := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (pow_pos hlogb 100) hx
  have hlogd : log (P.d : ℝ) ≤ P.constantBound vacuumBound :=
    (Real.log_le_self (by positivity)).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hC))
  have hsqrt : 0 < √(P.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast P.prime_d.pos)
  have hsqrt₀ : 0 ≤ log (√(P.d : ℝ)) := by
    rw [Real.log_sqrt (by positivity)]
    exact div_nonneg (Real.log_natCast_nonneg _) (by norm_num)
  have hsqrt₁ : log (√(P.d : ℝ)) ≤ P.constantBound vacuumBound / 2 := by
    rw [Real.log_sqrt (by positivity)]
    linarith
  -- The logarithmic bounds turn the three factors of the norm into additive errors.
  have hT : 0 < T := (pow_pos hxpos 11).trans_le hT₁
  have hlo := Real.log_le_log (pow_pos hxpos 11) hT₁
  have hhi := Real.log_le_log hT hT₂
  simp only [Real.log_pow, Nat.cast_ofNat] at hlo
  rw [Real.log_mul (pow_ne_zero _ hxpos.ne') (Real.rpow_pos_of_pos hlogb _).ne',
    Real.log_pow, Nat.cast_ofNat, Real.log_rpow hlogb] at hhi
  have hprod : 0 < A * T * √(P.d : ℝ) := mul_pos (mul_pos hA hT) hsqrt
  have heq : log (A * T * √(P.d : ℝ)) = log A + log T + log (√(P.d : ℝ)) := by
    rw [Real.log_mul (mul_ne_zero hA.ne' hT.ne') hsqrt.ne', Real.log_mul hA.ne' hT.ne']
  refine ⟨(Real.log_le_log_iff (pow_pos hxpos _) hprod).1 ?_,
    (Real.log_le_log_iff hprod (pow_pos hxpos _)).1 ?_⟩ <;>
    simp only [Real.log_pow, Nat.cast_ofNat, heq] <;>
    linarith [(abs_le.mp hlog).1, (abs_le.mp hlog).2]

end TauCeti.OneSidedBound.Parameters
