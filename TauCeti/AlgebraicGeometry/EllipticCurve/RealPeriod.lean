/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- Proof-only: `Ψ₂Sq` is a cubic with leading coefficient `4`, so it is positive on a half-line.
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Analysis.Polynomial.Basic
-- Proof-only: the three complex roots of the cubic `Ψ₂Sq` and its discriminant `16 Δ`.
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
-- Proof-only: the tail bound `∫ (1 + |x|)^(-3/2) < ∞`.
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
-- Proof-only: translation and dilation invariance of the Lebesgue integral.
import Mathlib.MeasureTheory.Group.LIntegral
-- Proof-only: `Ψ₂Sq` under a change of variables.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
-- Proof-only: bounds on `1 / √d` and on `∏ᵢ |z - eᵢ|^(-1/2)`, and `∫_{|x| ≤ R} |x - e|^(-1/2) < ∞`
-- for `e ∈ ℂ`.
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The real period of a Weierstrass curve over `ℝ`

Let `W` be a Weierstrass curve over `ℝ` and `ω = dx / (2y + a₁x + a₃)` its invariant differential.
On the curve `(2y + a₁x + a₃)² = Ψ₂Sq(x)`, where

  `Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆`

is Mathlib's `WeierstrassCurve.Ψ₂Sq`. A real point with abscissa `x` exists exactly when
`Ψ₂Sq(x) ≥ 0`, and over each `x` with `Ψ₂Sq(x) > 0` there are two real points, on which
`|ω| = dx / √Ψ₂Sq(x)`. The **real period** of `W` is therefore defined by the explicit integral

  `Ω(W) = 2 ∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)`,

the factor `2` counting the two branches of `y`. It treats curves with one real component
(`Δ < 0`) and with two (`Δ > 0`) uniformly. The integral is a Lebesgue integral of a nonnegative
function, `WeierstrassCurve.realPeriodLIntegral`, with values in `ℝ≥0∞`, and
`WeierstrassCurve.realPeriod` is twice its value as a real number. So that a divergent integral
cannot silently read as `0`, the finiteness is a theorem: for an elliptic curve the integral is
finite and positive.

The singularities of the integrand are the real roots of `Ψ₂Sq`. On an elliptic curve the
discriminant of the cubic `Ψ₂Sq` is `16 Δ ≠ 0`, so its three complex roots `e₁, e₂, e₃` are
distinct, and `|Ψ₂Sq(x)| = 4 |x - e₁| |x - e₂| |x - e₃|`. Near a root only one factor is small,
so the integrand is at most a constant times `|x - Re eᵢ|^(-1/2)`, which is integrable; far from
the roots it is at most a constant times `(1 + |x|)^(-3/2)`, which is integrable at infinity.

Under a change of variables `C = (u, r, s, t)` the invariant differential becomes `u ω`, and
correspondingly `Ω(C • W) = |u| Ω(W)`. In particular the period is unchanged by a change of
variables with `u = ±1`, which is the residual freedom between minimal Weierstrass equations
over `ℤ`. Taking the absolute value `|ω|` is what makes the period independent of the sign of
`u`: the automorphism `[-1]` of the curve pulls `ω` back to `-ω`.

## Main definitions

* `WeierstrassCurve.realPeriodLIntegral`: the integral `∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)` in `ℝ≥0∞`.
* `WeierstrassCurve.realPeriod`: the real period `Ω(W)`, twice the real value of that integral.

## Main results

* `WeierstrassCurve.realPeriodLIntegral_eq_lintegral`: the integrand vanishes off the set
  `Ψ₂Sq(x) > 0`, so the integral may be taken over all of `ℝ`.
* `WeierstrassCurve.realPeriodLIntegral_pos`: the integral is positive, for every curve.
* `WeierstrassCurve.realPeriodLIntegral_lt_top`: the integral is finite on an elliptic curve.
* `WeierstrassCurve.ofReal_realPeriod`: on an elliptic curve, `Ω(W)` is exactly twice the
  integral.
* `WeierstrassCurve.realPeriod_pos`: the real period of an elliptic curve is positive.
* `WeierstrassCurve.realPeriodLIntegral_variableChange` and
  `WeierstrassCurve.realPeriod_variableChange`: `Ω(C • W) = |u| Ω(W)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and Appendix C, §16.
-/

public section

open MeasureTheory Polynomial Set
open scoped ENNReal

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ)

/-- The integral `∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)` of a Weierstrass curve over `ℝ`, where
`Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆` is the square of `2y + a₁x + a₃` on the curve, as a value in
`ℝ≥0∞`. It is finite for an elliptic curve (`WeierstrassCurve.realPeriodLIntegral_lt_top`), and
whenever it is finite it is half the real period `WeierstrassCurve.realPeriod`
(`WeierstrassCurve.ofReal_realPeriod`). -/
noncomputable def realPeriodLIntegral : ℝ≥0∞ :=
  ∫⁻ x in {x | 0 < W.Ψ₂Sq.eval x}, ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹

/-- The **real period** `Ω(W)` of a Weierstrass curve over `ℝ`, defined as twice the real value of
`WeierstrassCurve.realPeriodLIntegral`. When that integral is finite, for instance for an elliptic
curve (`WeierstrassCurve.ofReal_realPeriod`), this is `Ω(W) = 2 ∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)`;
when it diverges, `Ω(W) = 0`. The motivation is that this integral computes `∫ |ω|` over the real
points, `ω = dx / (2y + a₁x + a₃)` being the invariant differential and the factor `2` counting the
two real points over each `x`. -/
noncomputable def realPeriod : ℝ :=
  2 * W.realPeriodLIntegral.toReal

/-- The defining integral of `WeierstrassCurve.realPeriodLIntegral`, over the set where
`Ψ₂Sq > 0`. -/
theorem realPeriodLIntegral_def :
    W.realPeriodLIntegral =
      ∫⁻ x in {x | 0 < W.Ψ₂Sq.eval x}, ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹ :=
  (rfl)

/-- The real period is twice the real value of `WeierstrassCurve.realPeriodLIntegral`. -/
theorem realPeriod_def : W.realPeriod = 2 * W.realPeriodLIntegral.toReal :=
  (rfl)

/-! ### The integrand -/

private theorem measurable_integrand :
    Measurable fun x ↦ ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹ :=
  (W.Ψ₂Sq.continuous.measurable.sqrt.inv).ennreal_ofReal

private theorem support_integrand :
    Function.support (fun x ↦ ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹) = {x | 0 < W.Ψ₂Sq.eval x} := by
  ext x
  simp [ENNReal.ofReal_eq_zero, Real.sqrt_pos]

/-- The integrand of the real period vanishes off the set `Ψ₂Sq(x) > 0`, so the integral may be
taken over all of `ℝ`. -/
theorem realPeriodLIntegral_eq_lintegral :
    W.realPeriodLIntegral = ∫⁻ x, ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹ :=
  setLIntegral_eq_of_support_subset (W.support_integrand ▸ subset_rfl)

/-- The integral of the real period is positive, for every Weierstrass curve over `ℝ`: the cubic
`Ψ₂Sq` has leading coefficient `4`, so it is positive on a half-line. -/
theorem realPeriodLIntegral_pos : 0 < W.realPeriodLIntegral := by
  rw [realPeriodLIntegral_eq_lintegral, lintegral_pos_iff_support W.measurable_integrand,
    support_integrand]
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hdeg : 0 < W.Ψ₂Sq.degree := by
    rw [degree_eq_natDegree (fun h ↦ by simpa [h] using W.leadingCoeff_Ψ₂Sq h4),
      W.natDegree_Ψ₂Sq h4]
    norm_num
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((W.Ψ₂Sq.tendsto_atTop_of_leadingCoeff_nonneg hdeg
      (by rw [W.leadingCoeff_Ψ₂Sq h4]; norm_num)).eventually_gt_atTop 0)
  calc (0 : ℝ≥0∞) < volume (Ioi M) := by simp
    _ ≤ volume {x | 0 < W.Ψ₂Sq.eval x} := measure_mono fun x hx ↦ hM x (le_of_lt hx)

/-! ### Finiteness -/

/-- On an elliptic curve, `|Ψ₂Sq(x)| = 4 |x - e₁| |x - e₂| |x - e₃|` for the three distinct complex
roots `eᵢ` of `Ψ₂Sq`, which are distinct since the discriminant of `Ψ₂Sq` is `16 Δ ≠ 0`. -/
private theorem exists_norm_eval_Ψ₂Sq_eq [W.IsElliptic] :
    ∃ e₁ e₂ e₃ : ℂ, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧ ∀ x : ℝ,
      ‖W.Ψ₂Sq.eval x‖ = 4 * (‖(x : ℂ) - e₁‖ * ‖(x : ℂ) - e₂‖ * ‖(x : ℂ) - e₃‖) := by
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by norm_num [twoTorsionPolynomial]
  obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three (φ := Complex.ofRealHom) ha).mp
    (IsAlgClosed.splits _)
  have hdisc := Cubic.discr_eq_prod_three_roots ha h3
  rw [twoTorsionPolynomial_discr] at hdisc
  have hne : (Complex.ofRealHom (16 * W.Δ)) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (mul_ne_zero (by norm_num) W.isUnit_Δ.ne_zero)
  rw [hdisc] at hne
  have hprod := pow_ne_zero_iff (n := 2) (by norm_num) |>.mp hne
  simp only [mul_ne_zero_iff, sub_ne_zero] at hprod
  obtain ⟨⟨⟨-, h₁₂⟩, h₁₃⟩, h₂₃⟩ := hprod
  refine ⟨e₁, e₂, e₃, h₁₂, h₁₃, h₂₃, fun x ↦ ?_⟩
  have hx := congrArg (Polynomial.eval (x : ℂ)) (Cubic.eq_prod_three_roots ha h3)
  rw [Cubic.map_toPoly, ← Complex.ofRealHom_eq_coe, Polynomial.eval_map_apply,
    Complex.ofRealHom_eq_coe] at hx
  rw [Ψ₂Sq_eq, ← Complex.norm_real, hx]
  simp [twoTorsionPolynomial, mul_assoc]

/-- Near the roots of `Ψ₂Sq`, the integrand of the real period is at most a constant times
`∑ᵢ |x - eᵢ|^(-1/2)`, so its integral over a bounded interval is finite. -/
private theorem setLIntegral_closedBall_lt_top {e₁ e₂ e₃ : ℂ} (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃)
    (h₂₃ : e₂ ≠ e₃)
    (hfac : ∀ x : ℝ, ‖W.Ψ₂Sq.eval x‖ = 4 * (‖(x : ℂ) - e₁‖ * ‖(x : ℂ) - e₂‖ * ‖(x : ℂ) - e₃‖))
    (R : ℝ) :
    ∫⁻ x in Metric.closedBall 0 R, ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹ < ∞ := by
  obtain ⟨K, hK, hle⟩ := ENNReal.exists_enorm_sub_rpow_neg_half_mul_le h₁₂ h₁₃ h₂₃
  have hmeas (e : ℂ) : Measurable fun x : ℝ ↦ ‖(x : ℂ) - e‖ₑ ^ (-2⁻¹ : ℝ) := by fun_prop
  have hfin (e : ℂ) := Complex.setLIntegral_closedBall_enorm_ofReal_sub_rpow_lt_top e
    (s := -2⁻¹) (by norm_num) 0 R
  calc ∫⁻ x in Metric.closedBall 0 R, ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹
      ≤ ∫⁻ x : ℝ in Metric.closedBall 0 R, K * (‖(x : ℂ) - e₁‖ₑ ^ (-2⁻¹ : ℝ) +
          ‖(x : ℂ) - e₂‖ₑ ^ (-2⁻¹ : ℝ) + ‖(x : ℂ) - e₃‖ₑ ^ (-2⁻¹ : ℝ)) := by
        refine lintegral_mono fun x ↦ (ENNReal.ofReal_inv_sqrt_le_enorm_rpow _).trans ?_
        refine (ENNReal.rpow_le_rpow_of_nonpos
          (x := ‖(x : ℂ) - e₁‖ₑ * ‖(x : ℂ) - e₂‖ₑ * ‖(x : ℂ) - e₃‖ₑ) ?_ (by norm_num)).trans ?_
        · have h0 : 0 ≤ ‖(x : ℂ) - e₁‖ * ‖(x : ℂ) - e₂‖ * ‖(x : ℂ) - e₃‖ := by positivity
          simp only [← ofReal_norm]
          rw [hfac, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · rw [ENNReal.mul_rpow_of_ne_top (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
            enorm_ne_top, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
          exact hle x
    _ = K * ((∫⁻ x : ℝ in Metric.closedBall 0 R, ‖(x : ℂ) - e₁‖ₑ ^ (-2⁻¹ : ℝ)) +
          (∫⁻ x : ℝ in Metric.closedBall 0 R, ‖(x : ℂ) - e₂‖ₑ ^ (-2⁻¹ : ℝ)) +
          ∫⁻ x : ℝ in Metric.closedBall 0 R, ‖(x : ℂ) - e₃‖ₑ ^ (-2⁻¹ : ℝ)) := by
        rw [lintegral_const_mul' _ _ hK, lintegral_add_left (f := fun x : ℝ ↦
          ‖(x : ℂ) - e₁‖ₑ ^ (-2⁻¹ : ℝ) + ‖(x : ℂ) - e₂‖ₑ ^ (-2⁻¹ : ℝ)) ((hmeas e₁).add (hmeas e₂)),
          lintegral_add_left (hmeas e₁)]
    _ < ∞ := ENNReal.mul_lt_top hK.lt_top <| ENNReal.add_lt_top.mpr
        ⟨ENNReal.add_lt_top.mpr ⟨hfin e₁, hfin e₂⟩, hfin e₃⟩

/-- Far from the roots of `Ψ₂Sq`, where each `|x - eᵢ|` is at least `(1 + |x|) / 2`, the integrand
of the real period is at most `√2 (1 + |x|)^(-3/2)`, so its integral is finite. -/
private theorem setLIntegral_compl_closedBall_lt_top {e₁ e₂ e₃ : ℂ}
    (hfac : ∀ x : ℝ, ‖W.Ψ₂Sq.eval x‖ = 4 * (‖(x : ℂ) - e₁‖ * ‖(x : ℂ) - e₂‖ * ‖(x : ℂ) - e₃‖)) :
    ∫⁻ x in (Metric.closedBall 0 (2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1))ᶜ,
      ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹ < ∞ := by
  set R := 2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1
  set F : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal √2 * ENNReal.ofReal ((1 + ‖x‖) ^ (-(3 / 2 : ℝ)))
  calc ∫⁻ x in (Metric.closedBall 0 R)ᶜ, ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹
      ≤ ∫⁻ x in (Metric.closedBall 0 R)ᶜ, F x := by
        refine setLIntegral_mono_ae (by fun_prop) (ae_of_all _ fun x hx ↦ ?_)
        refine ENNReal.ofReal_inv_sqrt_le_of_pow_three_le (by positivity) ?_
        simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
        -- each `|x - eᵢ|` is at least `(1 + |x|) / 2`
        have hfar (e : ℂ) (he : 2 * ‖e‖ + 1 ≤ R) : (1 + ‖x‖) / 2 ≤ ‖(x : ℂ) - e‖ := by
          have := norm_sub_norm_le (x : ℂ) e
          rw [Complex.norm_real] at this
          linarith
        have h₁ := hfar e₁ (by linarith [norm_nonneg e₂, norm_nonneg e₃])
        have h₂ := hfar e₂ (by linarith [norm_nonneg e₁, norm_nonneg e₃])
        have h₃ := hfar e₃ (by linarith [norm_nonneg e₁, norm_nonneg e₂])
        have hy : 0 ≤ (1 + ‖x‖) / 2 := by positivity
        rw [← Real.norm_eq_abs, hfac]
        nlinarith [mul_le_mul (mul_le_mul h₁ h₂ hy (hy.trans h₁)) h₃ hy
          (mul_nonneg (hy.trans h₁) (hy.trans h₂))]
    _ ≤ ∫⁻ x, F x := setLIntegral_le_lintegral _ _
    _ < ∞ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (finite_integral_one_add_norm (by norm_num))

/-- **The real period integral of an elliptic curve is finite.** -/
theorem realPeriodLIntegral_lt_top [W.IsElliptic] : W.realPeriodLIntegral < ∞ := by
  obtain ⟨e₁, e₂, e₃, h₁₂, h₁₃, h₂₃, hfac⟩ := W.exists_norm_eval_Ψ₂Sq_eq
  rw [realPeriodLIntegral_eq_lintegral, ← lintegral_add_compl _
    (Metric.isClosed_closedBall (x := (0 : ℝ)) (ε := 2 * (‖e₁‖ + ‖e₂‖ + ‖e₃‖) + 1)).measurableSet]
  exact ENNReal.add_lt_top.mpr ⟨W.setLIntegral_closedBall_lt_top h₁₂ h₁₃ h₂₃ hfac _,
    W.setLIntegral_compl_closedBall_lt_top hfac⟩

/-- On an elliptic curve, the real period is exactly twice the integral
`∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)`. -/
theorem ofReal_realPeriod [W.IsElliptic] :
    ENNReal.ofReal W.realPeriod = 2 * W.realPeriodLIntegral := by
  rw [realPeriod, ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_toReal W.realPeriodLIntegral_lt_top.ne, ENNReal.ofReal_ofNat]

/-- **The real period of an elliptic curve is positive.** -/
theorem realPeriod_pos [W.IsElliptic] : 0 < W.realPeriod :=
  mul_pos two_pos <|
    ENNReal.toReal_pos W.realPeriodLIntegral_pos.ne' W.realPeriodLIntegral_lt_top.ne

/-! ### Changes of variables -/

/-- Under a change of variables `C = (u, r, s, t)` the integral of the real period scales by `|u|`,
as the invariant differential becomes `u ω`. -/
@[simp]
theorem realPeriodLIntegral_variableChange (C : VariableChange ℝ) :
    (C • W).realPeriodLIntegral = ENNReal.ofReal |(C.u : ℝ)| * W.realPeriodLIntegral := by
  have hu : (C.u : ℝ) ≠ 0 := C.u.ne_zero
  have hu2 : (C.u : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  set g : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (√(W.Ψ₂Sq.eval x))⁻¹ with g_def
  -- the integrand of `C • W` at `x` is `|u|³` times that of `W` at `u² x + r`
  have hpt (x : ℝ) : ENNReal.ofReal (√((C • W).Ψ₂Sq.eval x))⁻¹ =
      ENNReal.ofReal (|(C.u : ℝ)| ^ 3) * g ((C.u : ℝ) ^ 2 * (x + C.r / (C.u : ℝ) ^ 2)) := by
    rw [eval_variableChange_Ψ₂Sq, g_def, ← ENNReal.ofReal_mul (by positivity),
      mul_add, mul_div_cancel₀ _ hu2]
    congr 1
    have h6 : ((C.u⁻¹ : ℝˣ) : ℝ) ^ 6 = ((|(C.u : ℝ)| ^ 3)⁻¹) ^ 2 := by
      have habs : |(C.u : ℝ)| ^ 6 = (C.u : ℝ) ^ 6 := (by decide : Even 6).pow_abs _
      rw [Units.val_inv_eq_inv_val, inv_pow, inv_pow, ← pow_mul, habs]
    rw [h6, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_inv, inv_inv]
  -- translation invariance removes the shift by `r / u²`
  have htrans : ∫⁻ x, g ((C.u : ℝ) ^ 2 * (x + C.r / (C.u : ℝ) ^ 2)) =
      ∫⁻ x, g ((C.u : ℝ) ^ 2 * x) :=
    lintegral_add_right_eq_self (fun y ↦ g ((C.u : ℝ) ^ 2 * y)) _
  -- dilation by `u²` scales the integral by `|u²|⁻¹`
  have hdil : ∫⁻ x, g ((C.u : ℝ) ^ 2 * x) = ENNReal.ofReal |((C.u : ℝ) ^ 2)⁻¹| * ∫⁻ x, g x := by
    rw [← (measurableEmbedding_mulLeft₀ hu2).lintegral_map, Real.map_volume_mul_left hu2,
      lintegral_smul_measure, smul_eq_mul]
  rw [realPeriodLIntegral_eq_lintegral, realPeriodLIntegral_eq_lintegral]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htrans, hdil, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [abs_inv, abs_pow]
  field_simp

/-- **The real period scales by `|u|` under a change of variables** `C = (u, r, s, t)`:
`Ω(C • W) = |u| Ω(W)`. In particular it is unchanged when `u = ±1`. -/
@[simp]
theorem realPeriod_variableChange (C : VariableChange ℝ) :
    (C • W).realPeriod = |(C.u : ℝ)| * W.realPeriod := by
  rw [realPeriod, realPeriod, realPeriodLIntegral_variableChange, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

end WeierstrassCurve
