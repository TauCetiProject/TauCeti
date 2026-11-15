/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Weierstrass primary factors of arbitrary genus

For each natural number `p`, the Weierstrass primary (elementary) factor of genus `p` is
`Complex.elementaryFactor p z = (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))`.
At `p = 0` this is `1 - z`, and at `p = 1` it coincides with `Complex.weierstrassFactorOne`.

Cancelling the first `p` terms of the logarithmic Taylor series of `1 - z` gives the derivative
identity `deriv (elementaryFactor p) z = -z ^ p * exp (∑ k < p, z ^ (k + 1) / (k + 1))`.
Integrating its radial derivative along `[0, 1]` yields Rudin's sharp closed-disc estimate
`‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1)` for all `‖z‖ ≤ 1`, which supplies the summable
compact-set majorants for canonical products of arbitrary (fixed or variable) genus. Away from
`z = 1`, `elementaryFactor p z = exp (log (1 - z) + ∑ k < p, z ^ (k + 1) / (k + 1))`, and on
`‖z‖ < 1` the exponent is bounded via `Complex.norm_log_sub_logTaylor_le` by
`‖z‖ ^ (p + 1) * (1 - ‖z‖)⁻¹ / (p + 1)` (hence by `2 / (p + 1) * ‖z‖ ^ (p + 1)` on `‖z‖ ≤ 1 / 2`).

## Main definitions

* `Complex.elementaryFactor p z`: the genus-`p` Weierstrass primary factor
  `(1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))`.

## Main results

* `Complex.elementaryFactor_zero_left`, `Complex.elementaryFactor_one_left`: specializations at
  genus `0` (`1 - z`) and genus `1` (`Complex.weierstrassFactorOne z`).
* `Complex.elementaryFactor_odd_mul_neg`, `Complex.elementaryFactor_one_mul_neg`: symmetric pairing
  `E_{2q+1}(z) * E_{2q+1}(-z) = E_q(z ^ 2)`, in particular `E₁(z) * E₁(-z) = 1 - z ^ 2`.
* `Complex.hasDerivAt_elementaryFactor`, `Complex.logDeriv_elementaryFactor`: exact derivative and
  rational logarithmic derivative `-z ^ p / (1 - z)`.
* `Complex.analyticOrderAt_elementaryFactor`, `Complex.analyticOrderAt_elementaryFactor_div`:
  `E_p` has a unique simple zero at `1`, and `w ↦ E_p(w / a)` (`a ≠ 0`) has a unique simple zero
  at `a`.
* `Complex.norm_one_sub_elementaryFactor_le`, `Complex.norm_elementaryFactor_sub_one_le`:
  `‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1)` on the closed unit disc `‖z‖ ≤ 1`.
* `Complex.norm_log_one_sub_add_sum_range_le`,
  `Complex.norm_log_one_sub_add_sum_range_le_of_le_half`: Taylor remainder bounds for
  `log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Definition 15.7 and
  Lemma 15.8.
* Z. Yun, W. Zhang, *Shtukas and the Taylor expansion of L-functions*, J. Amer. Math. Soc. **30**
  (2017), Appendix B.1.
-/

public section

open Filter Set Topology
open scoped BigOperators

namespace Complex

/-- The Weierstrass primary (elementary) factor of genus `p`:
`E_p(z) = (1 - z) * exp (∑_{k=0}^{p-1} z ^ (k + 1) / (k + 1))`. -/
noncomputable def elementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))

/-- Defining formula for `Complex.elementaryFactor`. -/
theorem elementaryFactor_def (p : ℕ) (z : ℂ) :
    elementaryFactor p z = (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) :=
  (rfl)

/-- At genus zero, the primary factor is `1 - z`. -/
@[simp]
theorem elementaryFactor_zero_left (z : ℂ) : elementaryFactor 0 z = 1 - z := by
  simp [elementaryFactor]

/-- At genus one, the primary factor agrees with `Complex.weierstrassFactorOne`. -/
@[simp]
theorem elementaryFactor_one_left (z : ℂ) : elementaryFactor 1 z = weierstrassFactorOne z := by
  simp [elementaryFactor, weierstrassFactorOne_def]

/-- Function-level equality between `elementaryFactor 1` and `weierstrassFactorOne`. -/
theorem elementaryFactor_eq_weierstrassFactorOne : elementaryFactor 1 = weierstrassFactorOne :=
  funext elementaryFactor_one_left

/-- Stepping from genus `p` to genus `p + 1` multiplies by `exp (z ^ (p + 1) / (p + 1))`. -/
theorem elementaryFactor_succ (p : ℕ) (z : ℂ) :
    elementaryFactor (p + 1) z = elementaryFactor p z * exp (z ^ (p + 1) / (p + 1)) := by
  rw [elementaryFactor_def, Finset.sum_range_succ, exp_add, ← mul_assoc, ← elementaryFactor_def]

/-- Every primary factor is normalized to `1` at the origin. -/
@[simp]
theorem elementaryFactor_zero (p : ℕ) : elementaryFactor p 0 = 1 := by
  simp [elementaryFactor]

/-- Every primary factor vanishes at `1`. -/
@[simp]
theorem elementaryFactor_one (p : ℕ) : elementaryFactor p 1 = 0 := by
  simp [elementaryFactor]

/-- The only zero of `elementaryFactor p` is `1`. -/
@[simp]
theorem elementaryFactor_eq_zero_iff {p : ℕ} {z : ℂ} :
    elementaryFactor p z = 0 ↔ z = 1 := by
  rw [elementaryFactor_def, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero, eq_comm]

/-- Away from `1`, `elementaryFactor p z` is the exponential of the `p`-th Taylor remainder of
`log (1 - z)`. -/
theorem elementaryFactor_eq_exp_log_add {p : ℕ} {z : ℂ} (hz : z ≠ 1) :
    elementaryFactor p z =
      exp (log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by
  rw [exp_add, exp_log (sub_ne_zero.mpr (Ne.symm hz)), elementaryFactor_def]

/-- Pairing opposite arguments in an odd-genus primary factor cancels the odd-degree exponential
terms and halves the even ones: `E_{2q+1}(z) * E_{2q+1}(-z) = E_q(z ^ 2)`. -/
theorem elementaryFactor_odd_mul_neg (q : ℕ) (z : ℂ) :
    elementaryFactor (2 * q + 1) z * elementaryFactor (2 * q + 1) (-z) =
      elementaryFactor q (z ^ 2) := by
  induction q with
  | zero =>
    simp only [Nat.mul_zero, zero_add, elementaryFactor_zero_left, elementaryFactor_one_left,
      weierstrassFactorOne_def]
    rw [mul_mul_mul_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
    ring
  | succ q ih =>
    have hstep : 2 * (q + 1) + 1 = (2 * q + 1) + 1 + 1 := by omega
    rw [hstep, elementaryFactor_succ (2 * q + 1 + 1) z, elementaryFactor_succ (2 * q + 1) z,
      elementaryFactor_succ (2 * q + 1 + 1) (-z), elementaryFactor_succ (2 * q + 1) (-z)]
    have hodd : (-z) ^ (2 * q + 1 + 1) = z ^ (2 * q + 1 + 1) := by
      have heven : Even (2 * q + 1 + 1) := ⟨q + 1, by omega⟩
      exact heven.neg_pow z
    have hodd2 : (-z) ^ (2 * q + 1 + 1 + 1) = -z ^ (2 * q + 1 + 1 + 1) := by
      have h : Odd (2 * q + 1 + 1 + 1) := ⟨q + 1, by omega⟩
      exact h.neg_pow z
    have heven_term : z ^ (2 * q + 1 + 1) / ((2 * q + 1 : ℕ) + 1 : ℂ) +
        (-z) ^ (2 * q + 1 + 1) / ((2 * q + 1 : ℕ) + 1 : ℂ) =
        (z ^ 2) ^ (q + 1) / ((q : ℂ) + 1) := by
      rw [hodd, ← pow_mul]
      have hq0 : ((q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero q
      have h2q : ((2 * q + 1 : ℕ) + 1 : ℂ) = 2 * ((q : ℂ) + 1) := by push_cast; ring
      rw [h2q, show 2 * (q + 1) = 2 * q + 1 + 1 by omega]
      field_simp
      ring
    have hcancel : z ^ (2 * q + 1 + 1 + 1) / ((2 * q + 1 + 1 : ℕ) + 1 : ℂ) +
        (-z) ^ (2 * q + 1 + 1 + 1) / ((2 * q + 1 + 1 : ℕ) + 1 : ℂ) = 0 := by
      rw [hodd2, neg_div, add_neg_cancel]
    calc
      _ = (elementaryFactor (2 * q + 1) z * elementaryFactor (2 * q + 1) (-z)) *
            (exp (z ^ (2 * q + 1 + 1) / ((2 * q + 1 : ℕ) + 1) +
              (-z) ^ (2 * q + 1 + 1) / ((2 * q + 1 : ℕ) + 1)) *
            exp (z ^ (2 * q + 1 + 1 + 1) / ((2 * q + 1 + 1 : ℕ) + 1) +
              (-z) ^ (2 * q + 1 + 1 + 1) / ((2 * q + 1 + 1 : ℕ) + 1))) := by
          simp only [exp_add]
          ring
      _ = elementaryFactor (q + 1) (z ^ 2) := by
          rw [ih, heven_term, hcancel, exp_zero, mul_one, ← elementaryFactor_succ]

/-- Symmetric genus-one pairing: `E₁(z) * E₁(-z) = 1 - z ^ 2`. -/
theorem elementaryFactor_one_mul_neg (z : ℂ) :
    elementaryFactor 1 z * elementaryFactor 1 (-z) = 1 - z ^ 2 := by
  simpa using elementaryFactor_odd_mul_neg 0 z

private theorem hasDerivAt_sum_pow_div_succ (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ ∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))
      (∑ k ∈ Finset.range p, z ^ k) z := by
  have h := HasDerivAt.fun_sum (u := Finset.range p)
    (A := fun k (w : ℂ) ↦ w ^ (k + 1) / ((k : ℂ) + 1))
    (A' := fun k ↦ (((k + 1 : ℕ) : ℂ) * z ^ k) / ((k : ℂ) + 1))
    fun k _ ↦ by
      simpa [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) z).div_const ((k : ℂ) + 1)
  refine h.congr_deriv (Finset.sum_congr rfl fun k _ ↦ ?_)
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk]

/-- Derivative of `elementaryFactor p`: the polynomial in the exponent cancels the lower terms,
leaving `-z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))`. -/
theorem hasDerivAt_elementaryFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (elementaryFactor p)
      (-z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))) z := by
  have hmul : HasDerivAt (elementaryFactor p)
      ((0 - 1) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) +
        (1 - z) * (exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) *
          ∑ k ∈ Finset.range p, z ^ k)) z :=
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
      (hasDerivAt_sum_pow_div_succ p z).cexp
  refine hmul.congr_deriv ?_
  have hgeom : (1 - z) * ∑ k ∈ Finset.range p, z ^ k = 1 - z ^ p := by
    calc (1 - z) * ∑ k ∈ Finset.range p, z ^ k
        = -((∑ k ∈ Finset.range p, z ^ k) * (z - 1)) := by ring
      _ = -(z ^ p - 1) := by rw [geom_sum_mul]
      _ = 1 - z ^ p := by ring
  calc
    (0 - 1) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) +
        (1 - z) * (exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) *
          ∑ k ∈ Finset.range p, z ^ k)
      = (-1 + (1 - z) * ∑ k ∈ Finset.range p, z ^ k) *
          exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by ring
    _ = -z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by
      rw [hgeom]; ring

/-- Every Weierstrass primary factor is entire. -/
@[fun_prop]
theorem differentiable_elementaryFactor (p : ℕ) : Differentiable ℂ (elementaryFactor p) :=
  fun z ↦ (hasDerivAt_elementaryFactor p z).differentiableAt

/-- Every Weierstrass primary factor is continuous. -/
@[fun_prop]
theorem continuous_elementaryFactor (p : ℕ) : Continuous (elementaryFactor p) :=
  (differentiable_elementaryFactor p).continuous

/-- Every Weierstrass primary factor is analytic at every complex point. -/
@[fun_prop]
theorem analyticAt_elementaryFactor (p : ℕ) (z : ℂ) : AnalyticAt ℂ (elementaryFactor p) z := by
  rw [show elementaryFactor p = fun w : ℂ ↦
    (1 - w) * exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))
    from funext (elementaryFactor_def p)]
  fun_prop

/-- Explicit derivative formula for `elementaryFactor p`. -/
@[simp]
theorem deriv_elementaryFactor (p : ℕ) (z : ℂ) :
    deriv (elementaryFactor p) z =
      -z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) :=
  (hasDerivAt_elementaryFactor p z).deriv

/-- The unique zero of `elementaryFactor p` at `1` is simple. -/
theorem analyticOrderAt_elementaryFactor_one (p : ℕ) :
    analyticOrderAt (elementaryFactor p) 1 = 1 := by
  apply (analyticAt_elementaryFactor p 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (elementaryFactor_one p)
  rw [deriv_elementaryFactor]
  simp [exp_ne_zero]

/-- Analytic order of `elementaryFactor p` at an arbitrary point `z : ℂ`. -/
theorem analyticOrderAt_elementaryFactor (p : ℕ) (z : ℂ) :
    analyticOrderAt (elementaryFactor p) z = if z = 1 then 1 else 0 := by
  split_ifs with hz
  · exact hz ▸ analyticOrderAt_elementaryFactor_one p
  · exact (analyticAt_elementaryFactor p z).analyticOrderAt_eq_zero.mpr
      (mt elementaryFactor_eq_zero_iff.mp hz)

/-- Composing `elementaryFactor p` with a nonzero linear slope preserves its simple root. -/
theorem analyticOrderAt_elementaryFactor_mul (p : ℕ) {c z : ℂ} (h : c * z = 1) :
    analyticOrderAt (fun w ↦ elementaryFactor p (c * w)) z = 1 := by
  have hc : c ≠ 0 := fun hc ↦ by simp [hc] at h
  have hd : HasDerivAt (fun w ↦ c * w) c z := by simpa using (hasDerivAt_id z).const_mul c
  have hg : AnalyticAt ℂ (fun w ↦ c * w) z := by fun_prop
  have heq : (fun w ↦ elementaryFactor p (c * w)) = elementaryFactor p ∘ fun w ↦ c * w := rfl
  rw [heq, analyticOrderAt_comp_of_deriv_ne_zero hg (by rwa [hd.deriv]), h]
  exact analyticOrderAt_elementaryFactor_one p

/-- For a nonzero root location `a`, `w ↦ elementaryFactor p (w / a)` has analytic order `1` at `a`
and `0` everywhere else. -/
theorem analyticOrderAt_elementaryFactor_div (p : ℕ) {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    analyticOrderAt (fun w ↦ elementaryFactor p (w / a)) z = if z = a then 1 else 0 := by
  split_ifs with hz
  · subst z
    have hmul : (fun w ↦ elementaryFactor p (w / a)) = fun w ↦ elementaryFactor p (a⁻¹ * w) := by
      ext w; rw [div_eq_inv_mul]
    rw [hmul]
    exact analyticOrderAt_elementaryFactor_mul p (inv_mul_cancel₀ ha)
  · have hana : AnalyticAt ℂ (fun w ↦ elementaryFactor p (w / a)) z := by fun_prop
    refine hana.analyticOrderAt_eq_zero.mpr ?_
    rw [ne_eq, elementaryFactor_eq_zero_iff, div_eq_one_iff_eq ha]
    exact hz

/-- Rational logarithmic derivative of `elementaryFactor p`: `-z ^ p / (1 - z)` everywhere
(including `z = 1` under total division). -/
theorem logDeriv_elementaryFactor (p : ℕ) (z : ℂ) :
    logDeriv (elementaryFactor p) z = -z ^ p / (1 - z) := by
  rw [logDeriv_apply, deriv_elementaryFactor, elementaryFactor_def]
  exact mul_div_mul_right _ _ (exp_ne_zero _)

private theorem real_hasDerivAt_one_sub_elementaryFactor (p : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ 1 - (1 - s) * Real.exp (∑ k ∈ Finset.range p, s ^ (k + 1) / (k + 1)))
      (t ^ p * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1))) t := by
  have hsum : HasDerivAt (fun s : ℝ ↦ ∑ k ∈ Finset.range p, s ^ (k + 1) / (k + 1))
      (∑ k ∈ Finset.range p, t ^ k) t := by
    have h := HasDerivAt.fun_sum (u := Finset.range p)
      (A := fun k (s : ℝ) ↦ s ^ (k + 1) / ((k : ℝ) + 1))
      (A' := fun k ↦ (((k + 1 : ℕ) : ℝ) * t ^ k) / ((k : ℝ) + 1))
      fun k _ ↦ by
        simpa [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) t).div_const ((k : ℝ) + 1)
    refine h.congr_deriv (Finset.sum_congr rfl fun k _ ↦ ?_)
    have hk : ((k : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    rw [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk]
  have hprod := (hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul hsum.exp)
  refine hprod.congr_deriv ?_
  have hgeom : (1 - t) * ∑ k ∈ Finset.range p, t ^ k = 1 - t ^ p := by
    calc (1 - t) * ∑ k ∈ Finset.range p, t ^ k
        = -((∑ k ∈ Finset.range p, t ^ k) * (t - 1)) := by ring
      _ = -(t ^ p - 1) := by rw [geom_sum_mul]
      _ = 1 - t ^ p := by ring
  calc
    0 - ((0 - 1) * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1)) +
        (1 - t) * (Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1)) *
          ∑ k ∈ Finset.range p, t ^ k))
      = (1 - (1 - t) * ∑ k ∈ Finset.range p, t ^ k) *
          Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1)) := by ring
    _ = t ^ p * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1)) := by
      rw [hgeom]; ring

/-- **Rudin's Lemma 15.8.** For every genus `p : ℕ` and every `z : ℂ` in the closed unit disc
`‖z‖ ≤ 1`, `‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1)`. -/
theorem norm_one_sub_elementaryFactor_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1) := by
  let g : ℝ → ℂ := fun t ↦ 1 - elementaryFactor p (t • z)
  let g' : ℝ → ℂ := fun t ↦
    z * ((t • z) ^ p * exp (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1)))
  let φ' : ℝ → ℝ := fun t ↦ t ^ p * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1))
  have hg_deriv (t : ℝ) : HasDerivAt g (g' t) t := by
    have hF : HasDerivAt (fun w : ℂ ↦ 1 - elementaryFactor p w)
        ((t • z) ^ p * exp (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1))) (t • z) :=
      ((hasDerivAt_const (t • z) (1 : ℂ)).fun_sub
        (hasDerivAt_elementaryFactor p (t • z))).congr_deriv (by ring)
    have hsmul : HasDerivAt (fun s : ℝ ↦ s • z) z t := by
      simpa using (hasDerivAt_id t).smul_const z
    exact (hF.scomp t hsmul).congr_deriv (smul_eq_mul _ _)
  have hg_int : IntervalIntegrable g' MeasureTheory.volume 0 1 :=
    Continuous.intervalIntegrable (by dsimp [g']; fun_prop) 0 1
  have hφ_int : IntervalIntegrable (fun t ↦ ‖z‖ ^ (p + 1) * φ' t) MeasureTheory.volume 0 1 :=
    Continuous.intervalIntegrable (by dsimp [φ']; fun_prop) 0 1
  have hftc_g : ∫ t in (0 : ℝ)..1, g' t = 1 - elementaryFactor p z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hg_deriv t) hg_int]
    simp [g]
  have hftc_φ : ∫ t in (0 : ℝ)..1, ‖z‖ ^ (p + 1) * φ' t = ‖z‖ ^ (p + 1) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ real_hasDerivAt_one_sub_elementaryFactor p t)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp [zero_pow (Nat.succ_ne_zero _)]
  rw [← hftc_g, ← hftc_φ]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hφ_int
  filter_upwards with t ht
  have ht0 : 0 ≤ t := ht.1.le
  have hre : (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1)).re ≤
      ∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1) := by
    rw [re_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    refine (re_le_norm _).trans ?_
    have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have htz : ‖t • z‖ ≤ t := by
      rw [norm_smul, Real.norm_of_nonneg ht0]
      exact mul_le_of_le_one_right ht0 hz
    rw [norm_div, norm_pow]
    have hcast : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      rw [← Nat.cast_add_one, norm_natCast, Nat.cast_add_one]
    rw [hcast]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) htz _) hk_pos.le
  calc
    ‖g' t‖ = ‖z‖ * (‖t • z‖ ^ p * Real.exp
        (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1)).re) := by
      dsimp [g']
      rw [norm_mul, norm_mul, norm_pow, norm_exp]
    _ = ‖z‖ ^ (p + 1) * (t ^ p * Real.exp
        (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1)).re) := by
      rw [norm_smul, Real.norm_of_nonneg ht0, mul_pow, pow_succ]
      ring
    _ ≤ ‖z‖ ^ (p + 1) * φ' t := by
      dsimp [φ']
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (pow_nonneg ht0 p))
        (pow_nonneg (norm_nonneg z) _)

/-- Symmetric form of `norm_one_sub_elementaryFactor_le`: for `‖z‖ ≤ 1`,
`‖elementaryFactor p z - 1‖ ≤ ‖z‖ ^ (p + 1)`. -/
theorem norm_elementaryFactor_sub_one_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖elementaryFactor p z - 1‖ ≤ ‖z‖ ^ (p + 1) := by
  rw [norm_sub_rev]
  exact norm_one_sub_elementaryFactor_le p hz

/-- Relation between `Complex.logTaylor` at `-z` and the polynomial exponent of
`Complex.elementaryFactor`. -/
theorem logTaylor_succ_neg (p : ℕ) (z : ℂ) :
    logTaylor (p + 1) (-z) = -∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1) := by
  induction p with
  | zero => simp [logTaylor_succ, logTaylor_zero]
  | succ p ih =>
    rw [logTaylor_succ, Pi.add_apply, ih, Finset.sum_range_succ, neg_add_rev]
    have hsign : (-1 : ℂ) ^ (p + 1 + 1) * (-z) ^ (p + 1) = -z ^ (p + 1) := by
      rw [neg_eq_neg_one_mul z, mul_pow, ← mul_assoc, ← pow_add]
      have hodd : Odd ((p + 1 + 1) + (p + 1)) := ⟨p + 1, by omega⟩
      rw [hodd.neg_one_pow, neg_one_mul]
    rw [hsign, Nat.cast_add, Nat.cast_one, neg_div]
    ring

/-- On the open unit disc `‖z‖ < 1`, the `p`-th Taylor remainder of `log (1 - z)` is bounded by
`‖z‖ ^ (p + 1) * (1 - ‖z‖)⁻¹ / (p + 1)`. -/
theorem norm_log_one_sub_add_sum_range_le (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)‖ ≤
      ‖z‖ ^ (p + 1) * (1 - ‖z‖)⁻¹ / (p + 1) := by
  have h := norm_log_sub_logTaylor_le p (show ‖-z‖ < 1 by simpa using hz)
  simpa [sub_eq_add_neg, logTaylor_succ_neg] using h

/-- On the closed half-radius disc `‖z‖ ≤ 1 / 2`, the `p`-th Taylor remainder of `log (1 - z)` is
bounded by `2 / (p + 1) * ‖z‖ ^ (p + 1)`. -/
theorem norm_log_one_sub_add_sum_range_le_of_le_half (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)‖ ≤
      2 / (p + 1) * ‖z‖ ^ (p + 1) := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc
    _ ≤ ‖z‖ ^ (p + 1) * (1 - ‖z‖)⁻¹ / (p + 1) := norm_log_one_sub_add_sum_range_le p hz1
    _ ≤ ‖z‖ ^ (p + 1) * 2 / (p + 1) := by gcongr
    _ = 2 / (p + 1) * ‖z‖ ^ (p + 1) := by ring

/-- Uniform genus-independent form of `norm_log_one_sub_add_sum_range_le_of_le_half`: for
`‖z‖ ≤ 1 / 2`, `‖log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)‖ ≤ 2 * ‖z‖ ^ (p + 1)`. -/
theorem norm_log_one_sub_add_sum_range_le_two_mul_pow (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)‖ ≤ 2 * ‖z‖ ^ (p + 1) := by
  refine (norm_log_one_sub_add_sum_range_le_of_le_half p hz).trans ?_
  have hdiv : (2 : ℝ) / ((p : ℝ) + 1) ≤ 2 :=
    div_le_self (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) p])
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg (norm_nonneg z) _)

/-! ### Examples -/

/-- Explicit evaluations of `E_p(-1)` for `p = 0, 1, 2`. -/
example :
    elementaryFactor 0 (-1) = 2 ∧
      elementaryFactor 1 (-1) = 2 * exp (-1) ∧
      elementaryFactor 2 (-1) = 2 * exp (-1 / 2) := by
  refine ⟨by norm_num [elementaryFactor], ?_, ?_⟩
  · simp only [elementaryFactor, Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one]
    norm_num
  · simp only [elementaryFactor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add]
    norm_num

end Complex
