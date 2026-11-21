/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.LSeries.Lerch.Series
public import TauCeti.RingTheory.Polynomial.Eulerian

import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Eulerian

/-!
# Lerch PDE and nonpositive-integer values for the Lerch series

For `‖z‖ < 1`, combining the lowering relation `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)` from
`TauCeti/NumberTheory/LSeries/Lerch/Series.lean` with `∂_c Φ(z, s, c) = -s Φ(z, s + 1, c)` on
`Complex.slitPlane` gives the second-order PDE `(z ∂_z + c) ∂_c Φ(z, s, c) = -s Φ(z, s, c)`.

Iterating `z ∂_z + c` on `Φ(z, 0, c) = (1 - z)⁻¹` yields rational values
`Φ(z, -m, c) = (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1)` at nonpositive integers `s = -m`,
where `lerchNegNatPoly 1 m = eulerianPolynomial m` and `(lerchNegNatPoly c m).eval 1 = m!`. These
rational continuations are jointly holomorphic on `{p : ℂ × ℂ | p.1 ≠ 1}` across all `c ∈ ℂ`.

## Main declarations

* `TauCeti.mul_deriv_deriv_lerchSeries_right_add_mul`: the Lerch PDE
  `(z ∂_z + c) ∂_c Φ(z, s, c) = -s Φ(z, s, c)`.
* `TauCeti.lerchSeries_neg_nat`, `TauCeti.lerchSeries_neg_nat_eq_div`,
  `TauCeti.lerchSeries_neg_one`, `TauCeti.analyticOnNhd_lerchNegNatPoly_div`:
  rational nonpositive-integer formulas (using `TauCeti.lerchNegNatPoly` from
  `TauCeti/RingTheory/Polynomial/Eulerian.lean` and the shared shifted Euler-operator lemmas from
  `TauCeti/Analysis/SpecialFunctions/Eulerian.lean`) and joint analyticity on
  `{p : ℂ × ℂ | p.1 ≠ 1}`.

## References

* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. 1, McGraw-Hill, 1953, Chapter 1.11.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, (1.8)–(1.9), Theorem 2.3 (2.3), (2.5), §4 Theorem 4.1, §5 Theorem 5.1
  (5.2)–(5.5).
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti

/-! ### Lerch partial differential equation -/

/-- Coupling the raising derivative in `c` with the lowering operator `z ∂_z + c` yields the
second-order Lerch partial differential equation `(z ∂_z + c) ∂_c Φ(z, s, c) = -s Φ(z, s, c)` on
`‖z‖ < 1` and `c ∈ Complex.slitPlane`. -/
theorem mul_deriv_deriv_lerchSeries_right_add_mul {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    z * deriv (fun w => deriv (fun u => lerchSeries w s u) c) z +
        c * deriv (fun u => lerchSeries z s u) c =
      -s * lerchSeries z s c := by
  have hloc : (fun w => deriv (fun u => lerchSeries w s u) c) =ᶠ[𝓝 z]
      fun w => -s * lerchSeries w (s + 1) c := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
    exact deriv_lerchSeries_right (mem_ball_zero_iff.mp hw) s hc
  rw [hloc.deriv_eq,
    deriv_const_mul _ (hasDerivAt_lerchSeries_left hz (s + 1) c).differentiableAt,
    deriv_lerchSeries_right hz s hc]
  have hlow := mul_deriv_lerchSeries_left_add_mul hz (s + 1) fun n =>
    Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hc (Nat.cast_nonneg n))
  rw [add_sub_cancel_right] at hlow
  linear_combination -s * hlow

/-! ### Nonpositive integer values and numerator polynomials -/

/-- At nonpositive integer orders `s = -(m : ℂ)`, `Φ(z, -m, c)` on `‖z‖ < 1` agrees with `m`-fold
iteration of the shifted Euler operator `f ↦ (w ↦ w * deriv f w + c * f w)` applied to
`w ↦ (1 - w)⁻¹` whenever `(n : ℂ) + c ≠ 0` for all `n : ℕ`. -/
theorem lerchSeries_neg_nat (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-(m : ℂ)) c =
      ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z := by
  induction m generalizing z with
  | zero => simpa using lerchSeries_zero_middle hz c
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hloc : (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m])
        (fun w => (1 - w)⁻¹)) =ᶠ[𝓝 z] fun w => lerchSeries w (-(m : ℂ)) c := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      exact (ih (mem_ball_zero_iff.mp hw)).symm
    have hcast : -(m : ℂ) - 1 = -((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hloc.deriv_eq, ← ih hz, mul_deriv_lerchSeries_left_add_mul hz (-(m : ℂ)) hc, hcast]

/-- Rational formula for `Φ(z, -m, c)` on `‖z‖ < 1` whenever `(n : ℂ) + c ≠ 0` for all `n : ℕ`. -/
theorem lerchSeries_neg_nat_eq_div (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-(m : ℂ)) c = (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1) := by
  rw [lerchSeries_neg_nat m hz hc, iterate_mul_deriv_add_mul_inv_one_sub]

/-- Explicit rational value `Φ(z, -1, c) = c / (1 - z) + z / (1 - z) ^ 2` on `‖z‖ < 1` whenever
`(n : ℂ) + c ≠ 0` for all `n : ℕ`. -/
theorem lerchSeries_neg_one {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ} (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-1) c = c / (1 - z) + z / (1 - z) ^ 2 := by
  have : 1 - z ≠ 0 := sub_ne_zero.mpr fun h1 => by rw [← h1, norm_one] at hz; exact lt_irrefl 1 hz
  calc lerchSeries z (-1) c
      = (lerchNegNatPoly c 1).eval z / (1 - z) ^ 2 := by
          simpa using lerchSeries_neg_nat_eq_div 1 hz hc
    _ = (c * (1 - z) + z) / (1 - z) ^ 2 := by simp [lerchNegNatPoly_one]
    _ = c / (1 - z) + z / (1 - z) ^ 2 := by field_simp

/-- The rational nonpositive-integer continuation `(z, c) ↦ P_m(z; c) / (1 - z) ^ (m + 1)` is
jointly analytic on `{p : ℂ × ℂ | p.1 ≠ 1}` across all `c ∈ ℂ`. -/
theorem analyticOnNhd_lerchNegNatPoly_div (m : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => (lerchNegNatPoly p.2 m).eval p.1 / (1 - p.1) ^ (m + 1))
      {p : ℂ × ℂ | p.1 ≠ 1} := by
  let F : ℕ → ℂ × ℂ → ℂ := fun k p =>
    ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + p.2 * f w)^[k]) (fun w => (1 - w)⁻¹) p.1
  have hUo : IsOpen {p : ℂ × ℂ | p.1 ≠ 1} := isOpen_ne.preimage continuous_fst
  suffices hF : AnalyticOnNhd ℂ (F m) {p : ℂ × ℂ | p.1 ≠ 1} by
    exact hF.congr hUo fun p hp => iterate_mul_deriv_add_mul_eq_div_of_ne_one m hp p.2
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
    dsimp only [F]; rw [Function.iterate_succ_apply', hd]; rfl

-- Normalization witness `Φ(1 / 2, 0, 1) = 2`, contrasting with `Li_0(1 / 2) = 1 = (1 / 2) * 2`.
example : lerchSeries (1 / 2) 0 1 = 2 := by
  rw [lerchSeries_zero_middle (by norm_num) 1]; norm_num

end TauCeti
