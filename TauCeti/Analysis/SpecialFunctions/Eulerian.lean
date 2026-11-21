/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.RingTheory.Polynomial.Eulerian
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Polynomial

/-!
# Shifted Euler operator on `(1 - z)⁻¹` and nonpositive rational forms

Iterating the shifted Euler differential operator `f ↦ (w ↦ w * deriv f w + c * f w)` on
`w ↦ (1 - w)⁻¹` produces the rational functions `(lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1)`.
Because `lerchNegNatPoly c m` evaluates to `m!` at `z = 1` independently of `c`, removing the pole
factor `(1 - z) ^ (m + 1)` yields the nonzero limit `m!` as `z → 1`, so no totalized iterate is
continuous at `1` and the rational identity holds for all `z, c : ℂ` including at the pole `z = 1`.

## Main declarations

* `TauCeti.iterate_mul_deriv_add_mul_eq_div_of_ne_one`: rational formula for `z ≠ 1`.
* `TauCeti.tendsto_one_sub_pow_mul_iterate_mul_deriv_add_mul_inv_one_sub_nhdsNE_one`:
  punctured pole limit `(1 - z) ^ (m + 1) * F_m(z) → m!` as `z → 1` (`z ≠ 1`).
* `TauCeti.iterate_mul_deriv_add_mul_inv_one_sub`: rational formula for all `z, c : ℂ`, including
  the totalized pole `z = 1`.

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

/-- Rational formula for the `m`-fold shifted Euler derivative of `(1 - w)⁻¹` away from `z = 1`.
-/
theorem iterate_mul_deriv_add_mul_eq_div_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) (c : ℂ) :
    ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z =
      (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1) := by
  induction m generalizing z with
  | zero => simp [div_eq_mul_inv]
  | succ m ih =>
    have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hloc : (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m])
        (fun w => (1 - w)⁻¹)) =ᶠ[𝓝 z]
        fun w => (lerchNegNatPoly c m).eval w / (1 - w) ^ (m + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw; exact ih hw
    have hd := ((lerchNegNatPoly c m).hasDerivAt z).div
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow (m + 1)) (pow_ne_zero (m + 1) hne)
    rw [Function.iterate_succ_apply', (hd.congr_of_eventuallyEq hloc).deriv, ih hz]
    simp [lerchNegNatPoly_succ, pow_succ]
    field_simp; ring

/-- Removing the pole `(1 - z) ^ (m + 1)` at `z = 1` of the `m`-th iterated shifted Euler
derivative yields the nonzero residue-like limit `m!` independently of `c`. -/
theorem tendsto_one_sub_pow_mul_iterate_mul_deriv_add_mul_inv_one_sub_nhdsNE_one (m : ℕ) (c : ℂ) :
    Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) *
        (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z))
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
  have h : Tendsto (fun z : ℂ => (lerchNegNatPoly c m).eval z) (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
    simpa only [lerchNegNatPoly_eval_one] using (lerchNegNatPoly c m).continuous.continuousAt
      |>.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ 1 := by simpa using hz
  have : 1 - z ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [iterate_mul_deriv_add_mul_eq_div_of_ne_one m hne c]; field_simp

private theorem not_continuousAt_iterate_mul_deriv_add_mul_inv_one_sub_one (m : ℕ) (c : ℂ) :
    ¬ ContinuousAt
      (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹)) 1 := by
  intro hc
  have hcont : ContinuousAt (fun z : ℂ => (1 - z) ^ (m + 1) *
      (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z)) 1 :=
    ((continuous_const.sub continuous_id).pow (m + 1)).continuousAt.mul hc
  have hzero : Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) *
      (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z))
      (𝓝[≠] 1) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℂ) ≠ 0)
    (tendsto_nhds_unique hzero
      (tendsto_one_sub_pow_mul_iterate_mul_deriv_add_mul_inv_one_sub_nhdsNE_one m c)).symm

/-- Closed rational form of the `m`-fold shifted Euler derivative of `(1 - w)⁻¹` for all `z, c : ℂ`,
including at the totalized pole `z = 1` where both sides vanish. -/
theorem iterate_mul_deriv_add_mul_inv_one_sub (m : ℕ) (z c : ℂ) :
    ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z =
      (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1) := by
  by_cases hz : z = 1
  · subst z
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', deriv_zero_of_not_differentiableAt
        (mt DifferentiableAt.continuousAt
          (not_continuousAt_iterate_mul_deriv_add_mul_inv_one_sub_one m c)), ih]
      simp
  · exact iterate_mul_deriv_add_mul_eq_div_of_ne_one m hz c

end TauCeti
