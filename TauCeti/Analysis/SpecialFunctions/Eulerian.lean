/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.RingTheory.Polynomial.Eulerian
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Shifted Euler operator on `(1 - z)⁻¹` and nonpositive rational forms

Iterating the shifted Euler differential operator `f ↦ (w ↦ w * deriv f w + c * f w)` on
`w ↦ (1 - w)⁻¹` produces the rational functions
`(shiftedEulerianPolynomial c m).eval z / (1 - z) ^ (m + 1)`.
Because `shiftedEulerianPolynomial c m` evaluates to `m!` at `z = 1` independently of `c`,
removing the pole factor `(1 - z) ^ (m + 1)` yields the nonzero limit `m!` as `z → 1`, so no
totalized iterate is continuous at `1` and the rational identity holds for all `z, c : ℂ` including
at the pole `z = 1`. Moreover, the rational function `(z, c) ↦ P_m(z; c) / (1 - z) ^ (m + 1)` is
jointly analytic on `{p : ℂ × ℂ | p.1 ≠ 1}`.

## Main declarations

* `TauCeti.shiftedEulerOp`, `TauCeti.shiftedEulerOp_apply`: the shifted Euler differential
  operator `f ↦ (w ↦ w * deriv f w + c * f w)`.
* `TauCeti.tendsto_one_sub_pow_mul_iterate_shiftedEulerOp_inv_one_sub_nhdsNE_one`:
  punctured pole limit `(1 - z) ^ (m + 1) * F_m(z) → m!` as `z → 1` (`z ≠ 1`).
* `TauCeti.iterate_shiftedEulerOp_inv_one_sub`: rational formula for all `z, c : ℂ`, including
  the totalized pole `z = 1`.
* `TauCeti.analyticOnNhd_shiftedEulerianPolynomial_div`: joint analyticity of
  `(z, c) ↦ (shiftedEulerianPolynomial c m).eval z / (1 - z) ^ (m + 1)` on `{p | p.1 ≠ 1}`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (2)–(3), p. 50.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, §5, Theorem 5.1.
* The rational-form induction, pole limit, and totalized-pole argument are adapted from
  `TauCeti/Analysis/SpecialFunctions/Polylogarithm/Nonpositive.lean`.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

/-- Shifted Euler differential operator `f ↦ (w ↦ w * deriv f w + c * f w)`. -/
noncomputable def shiftedEulerOp (c : ℂ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  w * deriv f w + c * f w

/-- Pointwise evaluation of `shiftedEulerOp`. -/
@[simp]
theorem shiftedEulerOp_apply (c : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    shiftedEulerOp c f w = w * deriv f w + c * f w := by rfl

/-- Rational formula for the `m`-fold shifted Euler derivative of `(1 - w)⁻¹` away from `z = 1`.
-/
private theorem iterate_shiftedEulerOp_inv_one_sub_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1)
    (c : ℂ) :
    ((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹) z =
      (shiftedEulerianPolynomial c m).eval z / (1 - z) ^ (m + 1) := by
  induction m generalizing z with
  | zero => simp [div_eq_mul_inv]
  | succ m ih =>
    have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hloc : ((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹) =ᶠ[𝓝 z]
        fun w => (shiftedEulerianPolynomial c m).eval w / (1 - w) ^ (m + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw; exact ih hw
    have hd := ((shiftedEulerianPolynomial c m).hasDerivAt z).div
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow (m + 1)) (pow_ne_zero (m + 1) hne)
    rw [Function.iterate_succ_apply', shiftedEulerOp_apply,
      (hd.congr_of_eventuallyEq hloc).deriv, ih hz]
    simp only [shiftedEulerianPolynomial_succ, pow_succ, eval_add, eval_mul, eval_C, eval_X,
      eval_sub, eval_one, Pi.pow_apply, Pi.sub_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    field_simp; ring

/-- Removing the pole `(1 - z) ^ (m + 1)` at `z = 1` of the `m`-th iterated shifted Euler
derivative yields the nonzero residue-like limit `m!` independently of `c`. -/
theorem tendsto_one_sub_pow_mul_iterate_shiftedEulerOp_inv_one_sub_nhdsNE_one (m : ℕ) (c : ℂ) :
    Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) * ((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹) z)
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
  have h : Tendsto (fun z : ℂ => (shiftedEulerianPolynomial c m).eval z)
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
    simpa only [shiftedEulerianPolynomial_eval_one] using
      (shiftedEulerianPolynomial c m).continuous.continuousAt
        |>.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ 1 := by simpa using hz
  have : 1 - z ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [iterate_shiftedEulerOp_inv_one_sub_of_ne_one m hne c]; field_simp

private theorem not_continuousAt_iterate_shiftedEulerOp_inv_one_sub_one (m : ℕ) (c : ℂ) :
    ¬ ContinuousAt (((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹)) 1 := by
  intro hc
  have hcont : ContinuousAt
      (fun z : ℂ => (1 - z) ^ (m + 1) * ((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹) z) 1 :=
    ((continuous_const.sub continuous_id).pow (m + 1)).continuousAt.mul hc
  have hzero : Tendsto
      (fun z : ℂ => (1 - z) ^ (m + 1) * ((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹) z)
      (𝓝[≠] 1) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℂ) ≠ 0)
    (tendsto_nhds_unique hzero
      (tendsto_one_sub_pow_mul_iterate_shiftedEulerOp_inv_one_sub_nhdsNE_one m c)).symm

/-- Closed rational form of the `m`-fold shifted Euler derivative of `(1 - w)⁻¹` for all `z, c : ℂ`,
including at the totalized pole `z = 1` where both sides vanish. -/
theorem iterate_shiftedEulerOp_inv_one_sub (m : ℕ) (z c : ℂ) :
    ((shiftedEulerOp c)^[m]) (fun w => (1 - w)⁻¹) z =
      (shiftedEulerianPolynomial c m).eval z / (1 - z) ^ (m + 1) := by
  by_cases hz : z = 1
  · subst z
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', shiftedEulerOp_apply, deriv_zero_of_not_differentiableAt
        (mt DifferentiableAt.continuousAt
          (not_continuousAt_iterate_shiftedEulerOp_inv_one_sub_one m c)), ih]
      simp
  · exact iterate_shiftedEulerOp_inv_one_sub_of_ne_one m hz c

/-- The rational nonpositive-integer continuation `(z, c) ↦ P_m(z; c) / (1 - z) ^ (m + 1)` is
jointly analytic on `{p : ℂ × ℂ | p.1 ≠ 1}` across all `c ∈ ℂ`. -/
theorem analyticOnNhd_shiftedEulerianPolynomial_div (m : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => (shiftedEulerianPolynomial p.2 m).eval p.1 / (1 - p.1) ^ (m + 1))
      {p : ℂ × ℂ | p.1 ≠ 1} := by
  let F : ℕ → ℂ × ℂ → ℂ := fun k p => ((shiftedEulerOp p.2)^[k]) (fun w => (1 - w)⁻¹) p.1
  have hUo : IsOpen {p : ℂ × ℂ | p.1 ≠ 1} := isOpen_ne.preimage continuous_fst
  suffices hF : AnalyticOnNhd ℂ (F m) {p : ℂ × ℂ | p.1 ≠ 1} by
    exact hF.congr hUo fun p _ => iterate_shiftedEulerOp_inv_one_sub m p.1 p.2
  induction m with
  | zero =>
    exact DifferentiableOn.analyticOnNhd_of_finiteDimensional
      (((differentiableOn_const (1 : ℂ)).sub differentiable_fst.differentiableOn).inv
        fun p hp => sub_ne_zero.mpr (Ne.symm hp)) hUo
  | succ m ih =>
    refine DifferentiableOn.analyticOnNhd_of_finiteDimensional (fun p hp => ?_) hUo
    let L : (ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1, 0)
    refine (((differentiableAt_fst.mul
      (L.differentiableAt.comp p (ih p hp).fderiv.differentiableAt))
      |>.add (differentiableAt_snd.mul (ih p hp).differentiableAt)).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [hUo.mem_nhds hp] with q hq
    have hd : deriv (fun w : ℂ => F m (w, q.2)) q.1 = L (fderiv ℂ (F m) q) := by
      simpa [L, Function.comp_def] using ((ih q hq).differentiableAt.hasFDerivAt.comp_hasDerivAt q.1
        ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv
    have hstep : F (m + 1) q = q.1 * deriv (fun w : ℂ => F m (w, q.2)) q.1 + q.2 * F m q := by
      simpa only [F, shiftedEulerOp_apply] using
        congrFun (Function.iterate_succ_apply' (shiftedEulerOp q.2) m (fun w => (1 - w)⁻¹)) q.1
    rw [hstep, hd]
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]

end TauCeti
