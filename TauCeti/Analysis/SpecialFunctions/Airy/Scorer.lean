/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Airy.Equation
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.Exp.PowerDecay

/-!
# The Scorer functions `Hi` and `Gi`

The Scorer function `Hi` is defined by the Laplace-type integral (DLMF 9.12.20)

$$\operatorname{Hi}(z) = \frac{1}{\pi} \int_0^\infty \exp\!\left(-\frac{t^3}{3} + z t\right) dt,$$

which converges absolutely for every complex `z`, and `Gi = Bi − Hi` (DLMF 9.12.11).

The integrand is the power-decay kernel of `TauCeti.MeasureTheory.Integral.Exp.PowerDecay` with
`p = 3`, `b = 1/3` and `q = 0`. Differentiating under the integral sign shows that `Hi` is
entire, with the iterated derivatives given by the moments `π⁻¹ ∫₀^∞ tⁿ exp(−t³/3 + z t) dt`; at
the origin these are Gamma values, `Hi⁽ⁿ⁾(0) = 3^{(n−2)/3} Γ((n+1)/3) / π`. Since
`(t² − z) exp(−t³/3 + z t) = −∂ₜ exp(−t³/3 + z t)`, the second moment equals `z` times the zeroth
moment plus `1`, which is the inhomogeneous Airy equation `Hi'' = z Hi + 1/π` (DLMF 9.12.1). For a
cube root of unity `ν`, the rotation `f ↦ (z ↦ ν f(ν z))` preserves every equation
`w'' = z w + c` (`TauCeti.airy_inhomogeneous_ode_rotation`); with `ν = e^{∓2πi/3}` this gives the
`Hi` part of DLMF 9.12.3. On the real line `Hi` is real.

## Main results

* `TauCeti.scorerHi`, `TauCeti.scorerGi` — the Scorer functions; `Real.scorerHi`,
  `Real.scorerGi` their real restrictions, `Real.scorerHi_eq_integral` — the real integral
  formula for `Real.scorerHi`, and `Real.scorerHi_ofReal` — `Hi(x)` is the cast of
  `Real.scorerHi x`.
* `Nat.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul` — integrability of the moment
  integrands on `(0, ∞)`.
* `Nat.iterate_deriv_scorerHi` — the iterated derivatives of `Hi` as moment integrals.
* `TauCeti.differentiable_scorerHi`, `TauCeti.differentiable_scorerGi` — `Hi` and `Gi` are
  entire, and `Real.differentiable_scorerHi`, `Real.differentiable_scorerGi` — their real
  restrictions are differentiable.
* `TauCeti.scorerHi_ode` — `Hi'' = z Hi + 1/π` (DLMF 9.12.1).
* `TauCeti.scorerHi_rotation_ode` — `z ↦ ν Hi(ν z)` solves `w'' = z w + 1/π` when `ν³ = 1`
  (DLMF 9.12.3).
* `Nat.iterate_deriv_scorerHi_zero` — `Hi⁽ⁿ⁾(0) = 3^{(n−2)/3} Γ((n+1)/3) / π`, and
  `TauCeti.scorerHi_zero` — `Hi(0) = 3^{−2/3} Γ(1/3) / π`.

The norm, integrability and differentiation lemmas for the moment integrals, the decay of the
kernel at infinity and the Gamma values at the origin are shared with the integral of `Ai² + Bi²`
in `TauCeti.Analysis.SpecialFunctions.Airy.Product.Integral` through
`TauCeti.MeasureTheory.Integral.Exp.PowerDecay`, whose proofs were extracted from that file. The
argument for the equation `Hi'' = z Hi + 1/π` is proved here; it is adapted from the proof of the
product differential equation `TauCeti.airyAi_sq_add_airyBi_sq_differential_equation` in
`TauCeti.Analysis.SpecialFunctions.Airy.Product.Integral`. The rotation argument is adapted from
the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Scorer/Representations.lean`, whose `Hi` is defined by its Maclaurin series rather
than by the integral used here.

## References

* NIST Digital Library of Mathematical Functions, §9.12, <https://dlmf.nist.gov/9.12>.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace TauCeti

/-- The Scorer function `Hi(z) = π⁻¹ ∫₀^∞ exp(−t³/3 + z t) dt` (DLMF 9.12.20). -/
def scorerHi (z : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ) ^ 3 / 3 + z * t)

/-- The defining integral of `Hi`. -/
theorem _root_.Complex.scorerHi_def (z : ℂ) :
    scorerHi z = (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ) ^ 3 / 3 + z * t) := (rfl)

/-- The Scorer function `Gi = Bi − Hi` (DLMF 9.12.11). -/
def scorerGi (z : ℂ) : ℂ := airyBi z - scorerHi z

/-- The defining expression of `Gi`. -/
theorem _root_.Complex.scorerGi_def (z : ℂ) : scorerGi z = airyBi z - scorerHi z := (rfl)

/-- The real restriction of `Hi`. -/
def _root_.Real.scorerHi (x : ℝ) : ℝ := (TauCeti.scorerHi x).re

/-- The defining expression of the real restriction of `Hi`. -/
theorem _root_.Real.scorerHi_def (x : ℝ) : Real.scorerHi x = (TauCeti.scorerHi x).re := (rfl)

/-- The real restriction of `Gi`. -/
def _root_.Real.scorerGi (x : ℝ) : ℝ := (TauCeti.scorerGi x).re

/-- The defining expression of the real restriction of `Gi`. -/
theorem _root_.Real.scorerGi_def (x : ℝ) : Real.scorerGi x = (TauCeti.scorerGi x).re := (rfl)

/-- `Hi(x)` for real `x` is the cast of the real integral `π⁻¹ ∫₀^∞ exp(−t³/3 + x t) dt`. -/
private theorem scorerHi_ofReal_eq_integral (x : ℝ) :
    scorerHi x = ((π⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 3 / 3 + x * t) : ℝ) : ℂ) := by
  rw [Complex.scorerHi_def, ofReal_mul, ← integral_complex_ofReal, ofReal_inv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast
  ring_nf

/-- The real restriction of `Hi` is the real integral
`Real.scorerHi x = π⁻¹ ∫₀^∞ exp(−t³/3 + x t) dt`. -/
theorem _root_.Real.scorerHi_eq_integral (x : ℝ) :
    Real.scorerHi x = π⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 3 / 3 + x * t) := by
  rw [Real.scorerHi_def, scorerHi_ofReal_eq_integral, ofReal_re]

/-- On the real line `Hi` is real: `Hi(x)` is the cast of its real restriction. -/
@[simp]
theorem _root_.Real.scorerHi_ofReal (x : ℝ) : TauCeti.scorerHi x = Real.scorerHi x := by
  rw [scorerHi_ofReal_eq_integral, Real.scorerHi_eq_integral]

/-! ### Moment integrals -/

/-- The moment integrand of `Hi` is the power-decay kernel with `p = 3`, `q = n` and
`b = 1/3`. -/
private theorem pow_mul_cexp_neg_cube_div_three_add_mul_eq (n : ℕ) (z : ℂ) (t : ℝ) :
    (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t) =
      (t : ℂ) ^ ((n : ℝ) : ℂ) * cexp (z * t - ((1 / 3 * t ^ (3 : ℝ) : ℝ) : ℂ)) := by
  rw [ofReal_natCast, cpow_natCast, Real.rpow_ofNat]
  push_cast
  ring_nf

/-- For every natural number `n` and complex `z`, the moment integrand
`t ↦ tⁿ exp(−t³/3 + z t)` is Bochner integrable on `(0, ∞)`. -/
theorem _root_.Nat.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul (n : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
  refine (integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi (p := 3) (b := 1 / 3) (s := n)
    (by norm_num) (by norm_num) (by simp; linarith [n.cast_nonneg (α := ℝ)]) z).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  have hexp : z * t - (1 / 3 : ℂ) * (t : ℂ) ^ ((3 : ℝ) : ℂ) = -(t : ℂ) ^ 3 / 3 + z * t := by
    rw [show ((3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast]
    ring
  dsimp only
  rw [cpow_natCast, hexp]

/-- The integrand `t ↦ exp(−t³/3 + z t)` of `Hi` is Bochner integrable on `(0, ∞)`. -/
theorem _root_.Complex.integrableOn_cexp_neg_cube_div_three_add_mul (z : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
  simpa only [pow_zero, one_mul] using
    Nat.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul 0 z

/-- The derivative of `w ↦ ∫₀^∞ tⁿ exp(−t³/3 + w t) dt` is obtained by multiplying the integrand
by `t`. -/
theorem _root_.Nat.hasDerivAt_integral_pow_mul_cexp_neg_cube_div_three_add_mul (n : ℕ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + w * t))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) z := by
  have h := hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_rpow (p := 3) (q := n) (b := 1 / 3)
    (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z
  -- The exponent `n + 1` of the derivative kernel is the real number `n + 1`.
  have hcast : ((n : ℝ) : ℂ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simpa only [hcast, pow_mul_cexp_neg_cube_div_three_add_mul_eq] using h

/-! ### Derivatives of `Hi` -/

/-- Every iterated derivative of `Hi` is a moment integral:
`Hi⁽ⁿ⁾(z) = π⁻¹ ∫₀^∞ tⁿ exp(−t³/3 + z t) dt`. -/
theorem _root_.Nat.iterate_deriv_scorerHi (n : ℕ) (z : ℂ) :
    deriv^[n] scorerHi z =
      (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t) := by
  -- The moment integrals form a tower of successive derivatives starting at `Hi`.
  have htower := iteratedDeriv_eq_of_derivative_tower
    (F := fun k w => (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ k * cexp (-(t : ℂ) ^ 3 / 3 + w * t))
    (fun k w => (Nat.hasDerivAt_integral_pow_mul_cexp_neg_cube_div_three_add_mul k w).const_mul
      ((π : ℂ)⁻¹)) n
  simp only [pow_zero, one_mul, ← Complex.scorerHi_def, iteratedDeriv_eq_iterate] at htower
  rw [htower]

/-- The derivative of `Hi` is `Hi′(z) = π⁻¹ ∫₀^∞ t exp(−t³/3 + z t) dt`. -/
theorem _root_.Complex.hasDerivAt_scorerHi (z : ℂ) :
    HasDerivAt scorerHi
      ((π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) z := by
  simpa only [pow_zero, one_mul, zero_add, pow_one, ← Complex.scorerHi_def] using
    (Nat.hasDerivAt_integral_pow_mul_cexp_neg_cube_div_three_add_mul 0 z).const_mul ((π : ℂ)⁻¹)

/-- The Scorer function `Hi` is entire. -/
@[fun_prop]
theorem differentiable_scorerHi : Differentiable ℂ scorerHi :=
  fun z => (Complex.hasDerivAt_scorerHi z).differentiableAt

/-- `Gi` is entire. -/
@[fun_prop]
theorem differentiable_scorerGi : Differentiable ℂ scorerGi := by
  rw [funext Complex.scorerGi_def]
  fun_prop

/-- The real restriction of `Hi` is differentiable. -/
@[fun_prop]
theorem _root_.Real.differentiable_scorerHi : Differentiable ℝ Real.scorerHi := fun x =>
  (TauCeti.differentiable_scorerHi (x : ℂ)).hasDerivAt.real_of_complex.differentiableAt

/-- The real restriction of `Gi` is differentiable. -/
@[fun_prop]
theorem _root_.Real.differentiable_scorerGi : Differentiable ℝ Real.scorerGi := fun x =>
  (TauCeti.differentiable_scorerGi (x : ℂ)).hasDerivAt.real_of_complex.differentiableAt

/-- The kernel identity `∫₀^∞ (t² exp(−t³/3 + z t) − z exp(−t³/3 + z t)) dt = 1`, from
`(t² − z) exp(−t³/3 + z t) = −∂ₜ exp(−t³/3 + z t)`. -/
private theorem integral_sq_mul_cexp_sub_mul_cexp_neg_cube_div_three_add_mul (z : ℂ) :
    ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ 2 * cexp (-(t : ℂ) ^ 3 / 3 + z * t) - z * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) =
      1 := by
  let g : ℝ → ℂ := fun t => -cexp (-(t : ℂ) ^ 3 / 3 + z * t)
  have hcont : Continuous g := by fun_prop
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g
      ((t : ℂ) ^ 2 * cexp (-(t : ℂ) ^ 3 / 3 + z * t) - z * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) t := by
    intro t _
    have harg : HasDerivAt (fun s : ℝ => -(s : ℂ) ^ 3 / 3 + z * s) (-(t : ℂ) ^ 2 + z) t := by
      refine ((((hasDerivAt_pow 3 (t : ℂ)).neg.div_const 3).add
        ((hasDerivAt_id (t : ℂ)).const_mul z)).comp_ofReal).congr_deriv ?_
      push_cast
      ring
    exact harg.cexp.neg.congr_deriv (by ring)
  have hint := (Nat.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul 2 z).sub
    ((Complex.integrableOn_cexp_neg_cube_div_three_add_mul z).const_mul z)
  -- `g` is the negated kernel of `TauCeti.MeasureTheory.Integral.Exp.PowerDecay` with `q = 0`.
  have htend : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_cpow_mul_cexp_mul_sub_mul_rpow_atTop (q := 0) (p := 3) (b := 1 / 3)
      (by norm_num) (by norm_num) z).neg
    rw [neg_zero] at h
    refine h.congr fun t => ?_
    have hk := pow_mul_cexp_neg_cube_div_three_add_mul_eq 0 z t
    rw [pow_zero, one_mul, CharP.cast_eq_zero] at hk
    rw [← hk]
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hderiv hint htend
  simpa [g] using hibp

/-- `Hi` solves the inhomogeneous Airy equation `Hi'' = z Hi + 1/π` (DLMF 9.12.1). -/
theorem scorerHi_ode (z : ℂ) : deriv^[2] scorerHi z = z * scorerHi z + (π : ℂ)⁻¹ := by
  have hk := integral_sq_mul_cexp_sub_mul_cexp_neg_cube_div_three_add_mul z
  rw [integral_sub (Nat.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul 2 z)
    ((Complex.integrableOn_cexp_neg_cube_div_three_add_mul z).const_mul z),
    integral_const_mul] at hk
  rw [Nat.iterate_deriv_scorerHi, Complex.scorerHi_def]
  linear_combination (π : ℂ)⁻¹ * hk

/-- For a cube root of unity `ν`, the rotated function `z ↦ ν Hi(ν z)` solves the inhomogeneous
Airy equation `w'' = z w + 1/π`; with `ν = e^{∓2πi/3}` this is DLMF 9.12.3 for `Hi`. -/
theorem scorerHi_rotation_ode {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun w => ν * scorerHi (ν * w)) z = z * (ν * scorerHi (ν * z)) + (π : ℂ)⁻¹ :=
  airy_inhomogeneous_ode_rotation scorerHi_ode hν z

/-! ### The value at the origin -/

/-- The iterated derivatives of `Hi` at the origin:
`Hi⁽ⁿ⁾(0) = 3^{(n − 2)/3} Γ((n + 1)/3) / π`. -/
theorem _root_.Nat.iterate_deriv_scorerHi_zero (n : ℕ) :
    deriv^[n] scorerHi 0 = (3 : ℂ) ^ (((n : ℂ) - 2) / 3) * Gamma (((n : ℂ) + 1) / 3) / π := by
  have hint :
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + 0 * t) =
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ (n : ℂ) * cexp (-(1 / 3 : ℂ) * (t : ℂ) ^ ((3 : ℝ) : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hexp : -(t : ℂ) ^ 3 / 3 + 0 * t = -(1 / 3 : ℂ) * (t : ℂ) ^ ((3 : ℝ) : ℂ) := by
      rw [show ((3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast]
      ring
    rw [cpow_natCast, hexp]
  have hpow : (1 / 3 : ℂ) ^ (-((n : ℂ) + 1) / 3) * (1 / (3 : ℂ)) =
      (3 : ℂ) ^ (((n : ℂ) - 2) / 3) := by
    have hexp : ((n : ℂ) + 1) / 3 + (-1) = ((n : ℂ) - 2) / 3 := by ring
    rw [neg_div, one_div, ← ofReal_ofNat 3, inv_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      cpow_neg, inv_inv, ← cpow_neg_one, ← cpow_add _ _ (by norm_num), ofReal_ofNat, hexp]
  rw [Nat.iterate_deriv_scorerHi, hint,
    integral_cpow_mul_cexp_neg_mul_cpow_Ioi (p := 3) (b := 1 / 3) (s := n)
      (by norm_num) (by norm_num) (by simp; linarith [n.cast_nonneg (α := ℝ)]),
    ofReal_ofNat, hpow]
  ring

/-- The value `Hi(0) = 3^{−2/3} Γ(1/3) / π`. -/
@[simp]
theorem scorerHi_zero : scorerHi 0 = (3 : ℂ) ^ (-2 / 3 : ℂ) * Gamma (1 / 3) / π := by
  simpa using Nat.iterate_deriv_scorerHi_zero 0

end TauCeti
