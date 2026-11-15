/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.LSeries.Lerch.Series
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import TauCeti.RingTheory.Polynomial.Eulerian
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.Algebra.Polynomial

import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Differential relations, nonpositive-integer values, and polylogarithm comparison for Lerch series

For `‖z‖ < 1`, the Lerch transcendent `Φ(z, s, c) = TauCeti.lerchSeries z s c` satisfies a coupled
pair of first-order differential relations in `z` and `c`:
* the lowering relation `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)` whenever `(n : ℂ) + c ≠ 0` for
  all `n : ℕ`, and
* combined with `∂_c Φ(z, s, c) = -s Φ(z, s + 1, c)` on `c ∈ Complex.slitPlane`, the second-order
  partial differential equation `(z ∂_z + c) ∂_c Φ(z, s, c) = -s Φ(z, s, c)`.

Starting from `Φ(z, 0, c) = (1 - z)⁻¹`, iterating the shifted Euler operator `z ∂_z + c` gives
rational closed forms for `Φ(z, -m, c)` at every nonpositive integer `s = -m`:
`Φ(z, -m, c) = (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1)`, where `lerchNegNatPoly c m`
generalizes `TauCeti.eulerianPolynomial m` (`lerchNegNatPoly 1 m = eulerianPolynomial m`) and
satisfies `(lerchNegNatPoly c m).eval 1 = m!`. Unlike the positive-order series, these rational
continuations are jointly holomorphic on `{p : ℂ × ℂ | p.1 ≠ 1}` across all `c ∈ ℂ` without any
cut in `c`.

At `c = 1`, multiplying by `z` recovers `TauCeti.Polylog.polylog` on the open unit disc in weight
`1` and at all nonpositive integer weights `-(m : ℤ)`.

## Main declarations

* `TauCeti.mul_deriv_lerchSeries_left_add_mul`: `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)`.
* `TauCeti.mul_deriv_deriv_lerchSeries_right_add_mul`: `(z ∂_z + c) ∂_c Φ(z, s, c) = -s Φ(z, s, c)`.
* `TauCeti.lerchNegNatPoly`: polynomial numerators of the rational values at nonpositive integers.
* `TauCeti.lerchSeries_neg_nat`, `TauCeti.lerchSeries_neg_nat_eq_div`,
  `TauCeti.lerchSeries_neg_one`: iterated-operator and rational formulas for `Φ(z, -m, c)`.
* `TauCeti.analyticOnNhd_lerchNegNatPoly_div`: joint analyticity on `{p : ℂ × ℂ | p.1 ≠ 1}`.
* `TauCeti.polylog_one_eq_mul_lerchSeries`, `TauCeti.polylog_neg_nat_eq_mul_lerchSeries`:
  comparison with `TauCeti.Polylog.polylog` on `‖z‖ < 1`.

## References

* [A. Erdélyi et al., *Higher Transcendental Functions*, Vol. 1][erdelyi1953vol1], Chapter 1.11.
* [J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I. Zeta integrals*][lagariasli2012].
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti

/-! ### Lowering differential relation and Lerch PDE -/

/-- Lowering differential relation `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)` on `‖z‖ < 1` whenever
`(n : ℂ) + c ≠ 0` for every `n : ℕ`. -/
theorem mul_deriv_lerchSeries_left_add_mul {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    z * deriv (fun w => lerchSeries w s c) z + c * lerchSeries z s c =
      lerchSeries z (s - 1) c := by
  have hterm (n : ℕ) :
      z * ((n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) =
        z ^ n * Complex.exp (-(s - 1) * Complex.log (n + c)) -
          c * (z ^ n * Complex.exp (-s * Complex.log (n + c))) := by
    have hzn : z * ((n : ℂ) * z ^ (n - 1)) = (n : ℂ) * z ^ n := by
      rcases n with _ | k <;> simp [pow_succ', mul_left_comm]
    have hexp : Complex.exp (-(s - 1) * Complex.log (n + c)) =
        ((n : ℂ) + c) * Complex.exp (-s * Complex.log (n + c)) := by
      rw [show -(s - 1) * Complex.log (n + c) =
        Complex.log (n + c) + (-s * Complex.log (n + c)) by ring,
        Complex.exp_add, Complex.exp_log (hc n)]
    rw [← mul_assoc, hzn, hexp]
    ring
  have hs1 := summable_lerchSeries_term hz (s - 1) c
  have hs2 := (summable_lerchSeries_term hz s c).mul_left c
  rw [deriv_lerchSeries_left hz s c, ← tsum_mul_left, lerchSeries_def z s c, ← tsum_mul_left,
    show (fun n : ℕ => z * ((n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)))) = _
      from funext hterm,
    ← (hs1.sub hs2).tsum_add hs2]
  simp [lerchSeries_def]

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
  calc z * (-s * deriv (fun w => lerchSeries w (s + 1) c) z) +
        c * (-s * lerchSeries z (s + 1) c)
      = -s * (z * deriv (fun w => lerchSeries w (s + 1) c) z + c * lerchSeries z (s + 1) c) := by
          ring
    _ = -s * lerchSeries z s c := by rw [hlow]

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
    rw [hloc.deriv_eq, ← ih hz, mul_deriv_lerchSeries_left_add_mul hz (-(m : ℂ)) hc]
    congr 2
    push_cast
    ring

/-- Shifted Eulerian numerator polynomial `P_m(X; c)` satisfying
`((w ∂_w + c)^[m] (1 - w)⁻¹) = P_m(w; c) / (1 - w) ^ (m + 1)`. At `c = 1` this recovers
`TauCeti.eulerianPolynomial m`. -/
noncomputable def lerchNegNatPoly {R : Type*} [CommRing R] (c : R) : ℕ → R[X]
  | 0 => 1
  | m + 1 => (C c * (1 - X) + C (m + 1 : R) * X) * lerchNegNatPoly c m +
      X * (1 - X) * (lerchNegNatPoly c m).derivative

/-- Base case `lerchNegNatPoly c 0 = 1`. -/
@[simp]
theorem lerchNegNatPoly_zero {R : Type*} [CommRing R] (c : R) :
    lerchNegNatPoly c 0 = 1 := by rfl

/-- Differential recurrence for `lerchNegNatPoly c (m + 1)` induced by `X ∂_X + c`. -/
theorem lerchNegNatPoly_succ {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    lerchNegNatPoly c (m + 1) =
      (C c * (1 - X) + C (m + 1 : R) * X) * lerchNegNatPoly c m +
        X * (1 - X) * (lerchNegNatPoly c m).derivative := by rfl

/-- First numerator polynomial `lerchNegNatPoly c 1 = c (1 - X) + X`. -/
@[simp]
theorem lerchNegNatPoly_one_order {R : Type*} [CommRing R] (c : R) :
    lerchNegNatPoly c 1 = C c * (1 - X) + X := by
  simp [lerchNegNatPoly_succ]

/-- Evaluating `lerchNegNatPoly c m` at `1` gives `m!` independently of the shift `c`. -/
@[simp]
theorem lerchNegNatPoly_eval_one {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    (lerchNegNatPoly c m).eval 1 = (m.factorial : R) := by
  induction m with
  | zero => simp
  | succ m ih => simp [lerchNegNatPoly_succ, ih, Nat.factorial_succ]

/-- At shift `c = 1 : ℤ`, `lerchNegNatPoly` coincides with `TauCeti.eulerianPolynomial`. -/
@[simp]
theorem lerchNegNatPoly_one_int (m : ℕ) :
    lerchNegNatPoly (1 : ℤ) m = eulerianPolynomial m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [lerchNegNatPoly_succ, eulerianPolynomial_succ, ih, map_add, map_one]
    ring

private theorem iterate_mul_deriv_add_mul_eq_div_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) (c : ℂ) :
    ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z =
      (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1) := by
  induction m generalizing z with
  | zero => simp [div_eq_mul_inv]
  | succ m ih =>
    have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hloc : (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m])
        (fun w => (1 - w)⁻¹)) =ᶠ[𝓝 z]
        fun w => (lerchNegNatPoly c m).eval w / (1 - w) ^ (m + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact ih hw
    have hd := ((lerchNegNatPoly c m).hasDerivAt z).div
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow (m + 1))
      (pow_ne_zero _ hne)
    rw [Function.iterate_succ_apply', (hd.congr_of_eventuallyEq hloc).deriv, ih hz]
    dsimp only [id_eq, Pi.sub_apply, Pi.pow_apply]
    simp only [lerchNegNatPoly_succ, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X,
      pow_succ]
    push_cast
    field_simp
    ring

/-- Removing the pole `(1 - z) ^ (m + 1)` at `z = 1` of the `m`-th iterated shifted Euler
derivative yields the nonzero residue-like limit `m!` independently of `c`. -/
theorem tendsto_one_sub_pow_mul_iterate_lerchEuler_nhdsNE_one (m : ℕ) (c : ℂ) :
    Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) *
        (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z))
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
  have hcont : Continuous (fun z : ℂ => (lerchNegNatPoly c m).eval z) :=
    (lerchNegNatPoly c m).continuous
  have h : Tendsto (fun z : ℂ => (lerchNegNatPoly c m).eval z)
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
    simpa only [lerchNegNatPoly_eval_one] using
      hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ 1 := by simpa using hz
  rw [iterate_mul_deriv_add_mul_eq_div_of_ne_one m hne c]
  have : 1 - z ≠ 0 := sub_ne_zero.mpr hne.symm
  field_simp

private theorem not_continuousAt_iterate_lerchEuler_one (m : ℕ) (c : ℂ) :
    ¬ ContinuousAt
      (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹)) 1 := by
  intro hc
  have hzero : Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) *
      (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z))
      (𝓝[≠] 1) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℂ => (1 - z) ^ (m + 1) *
        (((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w + c * f w)^[m]) (fun w => (1 - w)⁻¹) z)) 1 :=
      ((continuous_const.sub continuous_id).pow (m + 1)).continuousAt.mul hc
    simpa using hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  have heq := tendsto_nhds_unique hzero
    (tendsto_one_sub_pow_mul_iterate_lerchEuler_nhdsNE_one m c)
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℂ) ≠ 0) heq.symm

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
        (mt DifferentiableAt.continuousAt (not_continuousAt_iterate_lerchEuler_one m c)), ih]
      simp
  · exact iterate_mul_deriv_add_mul_eq_div_of_ne_one m hz c

/-- Rational formula for `Φ(z, -m, c)` on `‖z‖ < 1` whenever `(n : ℂ) + c ≠ 0` for all `n : ℕ`. -/
theorem lerchSeries_neg_nat_eq_div (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-(m : ℂ)) c = (lerchNegNatPoly c m).eval z / (1 - z) ^ (m + 1) := by
  rw [lerchSeries_neg_nat m hz hc, iterate_mul_deriv_add_mul_inv_one_sub]

/-- Explicit rational value `Φ(z, -1, c) = c / (1 - z) + z / (1 - z) ^ 2` on `‖z‖ < 1` whenever
`(n : ℂ) + c ≠ 0` for all `n : ℕ`. -/
theorem lerchSeries_neg_one {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ} (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-1) c = c / (1 - z) + z / (1 - z) ^ 2 := by
  have h := lerchSeries_neg_nat_eq_div 1 hz hc
  have : 1 - z ≠ 0 := by
    intro h0
    have hz1 : z = 1 := by linear_combination -h0
    rw [hz1, norm_one] at hz
    exact lt_irrefl 1 hz
  simp only [Nat.cast_one, lerchNegNatPoly_one_order, eval_add, eval_mul, eval_sub, eval_one,
    eval_C, eval_X, Nat.reduceAdd] at h
  rw [h]
  field_simp

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
    convert hF using 1
    ext p
    exact (iterate_mul_deriv_add_mul_inv_one_sub m p.1 p.2).symm
  induction m with
  | zero =>
    refine DifferentiableOn.analyticOnNhd_of_finiteDimensional ?_ hUo
    exact ((differentiableOn_const (1 : ℂ)).sub differentiable_fst.differentiableOn).inv
      fun p hp => sub_ne_zero.mpr (Ne.symm hp)
  | succ m ih =>
    refine DifferentiableOn.analyticOnNhd_of_finiteDimensional (fun p hp => ?_) hUo
    let L : (ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1, 0)
    have hdiff : DifferentiableAt ℂ
        (fun q : ℂ × ℂ => q.1 * L (fderiv ℂ (F m) q) + q.2 * F m q) p :=
      (differentiableAt_fst.mul (L.differentiableAt.comp p (ih p hp).fderiv.differentiableAt)).add
        (differentiableAt_snd.mul (ih p hp).differentiableAt)
    refine (hdiff.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hUo.mem_nhds hp] with q hq
    have hd : deriv (fun w : ℂ => F m (w, q.2)) q.1 = L (fderiv ℂ (F m) q) := by
      simpa [L, Function.comp_def] using ((ih q hq).differentiableAt.hasFDerivAt.comp_hasDerivAt q.1
        ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv
    dsimp only [F]
    rw [Function.iterate_succ_apply', hd]

/-! ### Comparison with integer-weight polylogarithms on the open unit disc -/

/-- On the open unit disc `‖z‖ < 1`, `Li_1(z) = z * Φ(z, 1, 1)`. -/
theorem polylog_one_eq_mul_lerchSeries {z : ℂ} (hz : ‖z‖ < 1) :
    Polylog.polylog 1 z = z * lerchSeries z 1 1 := by
  refine (Polylog.hasSum_polylog_one hz).unique ?_
  convert (hasSum_lerchSeries hz 1 1).mul_left z using 2 with k
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [neg_one_mul, Complex.exp_neg, Complex.exp_log hk, pow_succ', div_eq_mul_inv, mul_assoc]

/-- On the open unit disc `‖z‖ < 1`, `Li_{-m}(z) = z * Φ(z, -m, 1)` for every `m : ℕ`. -/
theorem polylog_neg_nat_eq_mul_lerchSeries (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Polylog.polylog (-(m : ℤ)) z = z * lerchSeries z (-(m : ℂ)) 1 := by
  induction m generalizing z with
  | zero => simp [lerchSeries_zero_middle hz 1, div_eq_mul_inv]
  | succ m ih =>
    have hloc : Polylog.polylog (-(m : ℤ)) =ᶠ[𝓝 z]
        fun w => w * lerchSeries w (-(m : ℂ)) 1 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      exact ih (mem_ball_zero_iff.mp hw)
    have hd := (hasDerivAt_id z).mul
      (hasDerivAt_lerchSeries_left hz (-(m : ℂ)) 1).differentiableAt.hasDerivAt
    rw [Polylog.polylog_neg_nat_succ m z, (hd.congr_of_eventuallyEq hloc).deriv]
    have hlow := mul_deriv_lerchSeries_left_add_mul hz (-(m : ℂ)) (c := 1) fun n => by
      exact_mod_cast Nat.succ_ne_zero n
    have hcast : -(m : ℂ) - 1 = -((m + 1 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hlow
    dsimp only [id_eq]
    linear_combination z * hlow

/-- Normalization witness `Φ(1 / 2, 0, 1) = 2`, contrasting with `Li_0(1 / 2) = 1 = (1 / 2) * 2`. -/
theorem lerchSeries_half_zero_one : lerchSeries (1 / 2) 0 1 = 2 := by
  rw [lerchSeries_zero_middle (by norm_num) 1]
  norm_num

end TauCeti
