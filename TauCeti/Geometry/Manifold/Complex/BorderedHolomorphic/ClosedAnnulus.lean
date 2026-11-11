/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Topology.Constructions.DoubleAlong.Annulus

/-!
# The closed annulus as a Riemann surface with boundary

For `0 < r₁ < r₂`, the closed annulus `Complex.closedAnnulus r₁ r₂`, the set `r₁ ≤ ‖z‖ ≤ r₂`, is a
Riemann surface with boundary modelled on the closed upper half-plane. Its charts are branches of
the logarithm. For a point `ζ` of the unit circle:

* the inner chart `TauCeti.ClosedAnnulus.innerChart ζ` is `z ↦ I log (z / (r₁ ζ))`, with inverse
  `w ↦ r₁ ζ exp (-I w)`. Its imaginary part is `log (‖z‖ / r₁) ≥ 0`, which vanishes exactly on
  the inner circle `‖z‖ = r₁`;
* the outer chart `TauCeti.ClosedAnnulus.outerChart ζ` is `z ↦ -I log (z / (r₂ ζ))`, with inverse
  `w ↦ r₂ ζ exp (I w)`. Its imaginary part is `log (r₂ / ‖z‖) ≥ 0`, which vanishes exactly on the
  outer circle `‖z‖ = r₂`.

The principal branch of the logarithm is used on the points where `z / ζ` is off the closed
negative real axis. The inner chart is restricted to `‖z‖ < r₂` and the outer chart to
`‖z‖ > r₁`, so that each sees only its own boundary circle. Both charts take values in the open
subset `|re w| < π`, `im w < log (r₂ / r₁)` of the closed upper half-plane. The chart at `z` is
the inner chart if `‖z‖ < r₂` and the outer chart otherwise, centred at `ζ = 1` if `0 ≤ re z` and
at `ζ = -1` otherwise.

Every transition map is `w ↦ d' log (ρ exp (c w) / ρ')` for constants `ρ, ρ', c, d'`, with
the logarithm evaluated on the slit plane. It is therefore holomorphic on its domain, up to the
boundary, and lies in `TauCeti.borderedHolomorphicGroupoid`. Concretely, between charts at the
same circle the transitions are locally translations by real constants, and between an inner and
an outer chart they are locally maps `w ↦ -w + c` with `im c = log (r₂ / r₁)`, defined away from
the boundary.

The manifold interior is the open annulus `r₁ < ‖z‖ < r₂`, and its complement is the pair of
boundary circles `TauCeti.DoubleAlong.annulusBoundary r₁ r₂` along which `TauCeti.DoubleAlong`
doubles the annulus to the torus. The induced complex structure on the interior is the standard
one: the inclusion of the interior into `ℂ` is analytic.

The atlas is put on the subtype `↥(Complex.closedAnnulus r₁ r₂)` itself, which carries no other
charted space structure. The hypotheses `0 < r₁` and `r₁ < r₂` enter as `Fact` instances.

## Main declarations

* `TauCeti.ClosedAnnulus.innerChart` and `TauCeti.ClosedAnnulus.outerChart`: the logarithmic
  charts at the inner and outer boundary circle.
* `TauCeti.ClosedAnnulus.instChartedSpace`: the atlas of logarithmic charts.
* `TauCeti.ClosedAnnulus.instHasGroupoid`: the charts have bordered holomorphic transition maps,
  so the closed annulus is a Riemann surface with boundary.
* `TauCeti.ClosedAnnulus.mem_borderedInterior_iff` and
  `TauCeti.ClosedAnnulus.compl_borderedInterior`: the interior is the open annulus, and its
  complement is the pair of boundary circles `TauCeti.DoubleAlong.annulusBoundary r₁ r₂`.
* `TauCeti.ClosedAnnulus.contMDiff_coe_borderedInterior`: the inclusion of the interior into `ℂ`
  is analytic, so the interior carries the standard complex structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.4, for Riemann surfaces with boundary.
-/

public section

noncomputable section

open Set Complex Filter
open scoped Manifold ContDiff Topology Real

namespace TauCeti

namespace ClosedAnnulus

variable {r₁ r₂ : ℝ}

/-! ### Elementary estimates -/

/-- A point of the closed annulus has norm at least `r₁`. -/
theorem le_norm_coe (z : closedAnnulus r₁ r₂) : r₁ ≤ ‖(z : ℂ)‖ :=
  (mem_closedAnnulus.1 z.2).1

/-- A point of the closed annulus has norm at most `r₂`. -/
theorem norm_coe_le (z : closedAnnulus r₁ r₂) : ‖(z : ℂ)‖ ≤ r₂ :=
  (mem_closedAnnulus.1 z.2).2

/-- The point `w` with its imaginary part capped at `L`. It is used to make the inverse charts
total; it does not change `w` on the chart targets. -/
private def capIm (L : ℝ) (w : ℂ) : ℂ :=
  w.re + (min w.im L : ℝ) * I

private theorem im_capIm (L : ℝ) (w : ℂ) : (capIm L w).im = min w.im L := by
  simp [capIm]

private theorem capIm_of_im_le {L : ℝ} {w : ℂ} (h : w.im ≤ L) : capIm L w = w := by
  apply Complex.ext <;> simp [capIm, h]

private theorem continuous_capIm (L : ℝ) : Continuous (capIm L) := by
  unfold capIm
  fun_prop

private theorem norm_div_ofReal_mul {ρ : ℝ} (hρ : 0 < ρ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : ℂ) :
    ‖z / (ρ * ζ)‖ = ‖z‖ / ρ := by
  rw [norm_div, norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]

private theorem ofReal_mul_ne_zero {ρ : ℝ} (hρ : 0 < ρ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (ρ : ℂ) * ζ ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.2 hρ.ne') (norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero))

private theorem im_I_mul_log (u : ℂ) : (I * log u).im = Real.log ‖u‖ := by
  simp [log_re]

private theorem re_I_mul_log (u : ℂ) : (I * log u).re = -arg u := by
  simp [log_im]

private theorem im_neg_I_mul_log (u : ℂ) : (-I * log u).im = -Real.log ‖u‖ := by
  simp [log_re]

private theorem re_neg_I_mul_log (u : ℂ) : (-I * log u).re = arg u := by
  simp [log_im]

private theorem abs_arg_lt_pi {u : ℂ} (hu : u ∈ slitPlane) : |arg u| < π :=
  abs_lt.2 ⟨neg_pi_lt_arg u, lt_of_le_of_ne (arg_le_pi u) (slitPlane_arg_ne_pi hu)⟩

private theorem exp_mem_slitPlane_of_abs_im_lt {x : ℂ} (hx : |x.im| < π) : exp x ∈ slitPlane := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hx
  rw [exp_mem_slitPlane, (toIocMod_eq_self _).2 ⟨h₁, by linarith [Real.pi_pos]⟩]
  exact h₂.ne

private theorem log_exp_of_abs_im_lt {x : ℂ} (hx : |x.im| < π) : log (exp x) = x :=
  log_exp (abs_lt.1 hx).1 (abs_lt.1 hx).2.le

/-! ### The logarithmic charts -/

section Charts

variable [hr₁ : Fact (0 < r₁)] [hr₁₂ : Fact (r₁ < r₂)]

variable (r₁ r₂) in
include hr₁ hr₁₂ in
private theorem zero_lt_r₂ : 0 < r₂ :=
  hr₁.out.trans hr₁₂.out

private theorem zero_lt_log : 0 < Real.log (r₂ / r₁) :=
  Real.log_pos ((one_lt_div hr₁.out).2 hr₁₂.out)

omit hr₁₂ in
private theorem norm_coe_pos (z : closedAnnulus r₁ r₂) : 0 < ‖(z : ℂ)‖ :=
  hr₁.out.trans_le (le_norm_coe z)

/-- The open set of the closed upper half-plane on which the logarithmic charts take values: the
points with `|re w| < π` and `im w < log (r₂ / r₁)`. -/
def chartTarget (r₁ r₂ : ℝ) : Set ClosedUpperHalfPlane :=
  {w | |(w : ℂ).re| < π ∧ (w : ℂ).im < Real.log (r₂ / r₁)}

omit hr₁ hr₁₂ in
private theorem isOpen_chartTarget : IsOpen (chartTarget r₁ r₂) :=
  ((continuous_abs.comp (continuous_re.comp continuous_subtype_val)).isOpen_preimage _
    isOpen_Iio).inter ((continuous_im.comp continuous_subtype_val).isOpen_preimage _ isOpen_Iio)

/-- The inverse of the inner chart lands in the closed annulus. -/
private theorem mem_closedAnnulus_inner {ζ : ℂ} (hζ : ‖ζ‖ = 1) (w : ClosedUpperHalfPlane) :
    (r₁ : ℂ) * ζ * exp (-I * capIm (Real.log (r₂ / r₁)) w) ∈ closedAnnulus r₁ r₂ := by
  have hL := (zero_lt_log (r₁ := r₁) (r₂ := r₂)).le
  have him : (-I * capIm (Real.log (r₂ / r₁)) w).re = min (w : ℂ).im (Real.log (r₂ / r₁)) := by
    simp [im_capIm]
  rw [mem_closedAnnulus, norm_mul, norm_mul, hζ, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr₁.out.le, norm_exp, him]
  constructor
  · exact le_mul_of_one_le_right hr₁.out.le (Real.one_le_exp (le_min w.2 hL))
  · calc r₁ * Real.exp (min (w : ℂ).im (Real.log (r₂ / r₁)))
        ≤ r₁ * Real.exp (Real.log (r₂ / r₁)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (min_le_right _ _)) hr₁.out.le
      _ = r₂ := by
          rw [Real.exp_log (div_pos (zero_lt_r₂ r₁ r₂) hr₁.out)]
          field_simp [hr₁.out.ne']

/-- The inverse of the outer chart lands in the closed annulus. -/
private theorem mem_closedAnnulus_outer {ζ : ℂ} (hζ : ‖ζ‖ = 1) (w : ClosedUpperHalfPlane) :
    (r₂ : ℂ) * ζ * exp (I * capIm (Real.log (r₂ / r₁)) w) ∈ closedAnnulus r₁ r₂ := by
  have hL := (zero_lt_log (r₁ := r₁) (r₂ := r₂)).le
  have him : (I * capIm (Real.log (r₂ / r₁)) w).re = -min (w : ℂ).im (Real.log (r₂ / r₁)) := by
    simp [im_capIm]
  have hr₂ := zero_lt_r₂ r₁ r₂
  rw [mem_closedAnnulus, norm_mul, norm_mul, hζ, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr₂.le, norm_exp, him]
  constructor
  · calc r₁ = r₂ * Real.exp (-Real.log (r₂ / r₁)) := by
          rw [Real.exp_neg, Real.exp_log (div_pos hr₂ hr₁.out)]
          field_simp [hr₁.out.ne', hr₂.ne']
      _ ≤ r₂ * Real.exp (-min (w : ℂ).im (Real.log (r₂ / r₁))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg (min_le_right _ _))) hr₂.le
  · exact mul_le_of_le_one_right hr₂.le
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (le_min w.2 hL)))

omit hr₁₂ in
/-- The inner chart has nonnegative imaginary part on the closed annulus. -/
private theorem im_inner_nonneg {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : closedAnnulus r₁ r₂) :
    0 ≤ (I * log ((z : ℂ) / (r₁ * ζ))).im := by
  rw [im_I_mul_log, norm_div_ofReal_mul hr₁.out hζ]
  exact Real.log_nonneg ((one_le_div hr₁.out).2 (le_norm_coe z))

/-- The outer chart has nonnegative imaginary part on the closed annulus. -/
private theorem im_outer_nonneg {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : closedAnnulus r₁ r₂) :
    0 ≤ (-I * log ((z : ℂ) / (r₂ * ζ))).im := by
  rw [im_neg_I_mul_log, norm_div_ofReal_mul (zero_lt_r₂ r₁ r₂) hζ, neg_nonneg]
  exact Real.log_nonpos (div_nonneg (norm_nonneg _) (zero_lt_r₂ r₁ r₂).le)
    ((div_le_one (zero_lt_r₂ r₁ r₂)).2 (norm_coe_le z))

omit hr₁₂ in
/-- On the points with `‖z‖ < r₂`, the inner chart has imaginary part below `log (r₂ / r₁)`. -/
private theorem im_inner_lt {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : closedAnnulus r₁ r₂)
    (hz : ‖(z : ℂ)‖ < r₂) : (I * log ((z : ℂ) / (r₁ * ζ))).im < Real.log (r₂ / r₁) := by
  rw [im_I_mul_log, norm_div_ofReal_mul hr₁.out hζ]
  exact Real.log_lt_log (div_pos (norm_coe_pos z) hr₁.out) (div_lt_div_of_pos_right hz hr₁.out)

/-- The inner logarithmic chart attached to a point `ζ` of the unit circle: the map
`z ↦ I log (z / (r₁ ζ))` from the points of the closed annulus with `‖z‖ < r₂` and `z / ζ` off
the closed negative real axis, onto `TauCeti.ClosedAnnulus.chartTarget r₁ r₂`. Its inverse is
`w ↦ r₁ ζ exp (-I w)`. It sends the inner circle `‖z‖ = r₁` to the real axis. -/
def innerChart (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane where
  toFun z := ⟨I * log ((z : ℂ) / (r₁ * ζ)), im_inner_nonneg hζ z⟩
  invFun w := ⟨r₁ * ζ * exp (-I * capIm (Real.log (r₂ / r₁)) w), mem_closedAnnulus_inner hζ w⟩
  source := {z | ‖(z : ℂ)‖ < r₂ ∧ (z : ℂ) / (r₁ * ζ) ∈ slitPlane}
  target := chartTarget r₁ r₂
  map_source' z hz := by
    refine ⟨?_, ?_⟩
    · change |(I * log ((z : ℂ) / (r₁ * ζ))).re| < π
      rw [re_I_mul_log, abs_neg]
      exact abs_arg_lt_pi hz.2
    · exact im_inner_lt hζ z hz.1
  map_target' w hw := by
    have hρ := ofReal_mul_ne_zero hr₁.out hζ
    have hc : capIm (Real.log (r₂ / r₁)) w = w := capIm_of_im_le hw.2.le
    have hre : |(-I * (w : ℂ)).im| < π := by simpa using hw.1
    simp only [mem_ofPred_eq, hc]
    refine ⟨?_, ?_⟩
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr₁.out.le, hζ, mul_one,
        norm_exp]
      calc r₁ * Real.exp (-I * (w : ℂ)).re < r₁ * Real.exp (Real.log (r₂ / r₁)) := by
            refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hr₁.out
            simpa using hw.2
        _ = r₂ := by
            rw [Real.exp_log (div_pos (zero_lt_r₂ r₁ r₂) hr₁.out)]
            field_simp [hr₁.out.ne']
    · rw [mul_div_cancel_left₀ _ hρ]
      exact exp_mem_slitPlane_of_abs_im_lt hre
  left_inv' z hz := by
    have hρ := ofReal_mul_ne_zero hr₁.out hζ
    apply Subtype.ext
    change (r₁ : ℂ) * ζ * exp (-I * capIm (Real.log (r₂ / r₁)) (I * log ((z : ℂ) / (r₁ * ζ)))) = z
    rw [capIm_of_im_le (im_inner_lt hζ z hz.1).le, ← mul_assoc, neg_mul, I_mul_I, neg_neg,
      one_mul, exp_log (slitPlane_ne_zero hz.2), mul_div_cancel₀ _ hρ]
  right_inv' w hw := by
    have hρ := ofReal_mul_ne_zero hr₁.out hζ
    have hc : capIm (Real.log (r₂ / r₁)) w = w := capIm_of_im_le hw.2.le
    have hre : |(-I * (w : ℂ)).im| < π := by simpa using hw.1
    apply Subtype.ext
    change I * log (r₁ * ζ * exp (-I * capIm (Real.log (r₂ / r₁)) w) / (r₁ * ζ)) = w
    rw [hc, mul_div_cancel_left₀ _ hρ, log_exp_of_abs_im_lt hre, ← mul_assoc, mul_neg, I_mul_I,
      neg_neg, one_mul]
  open_source := (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const).inter
    (isOpen_slitPlane.preimage (continuous_subtype_val.div_const _))
  open_target := isOpen_chartTarget
  continuousOn_toFun := by
    refine ((Topology.IsEmbedding.subtypeVal (p := fun w : ℂ ↦ 0 ≤ w.im)).isInducing
      |>.continuousOn_iff).2 fun z hz ↦ ?_
    exact (continuousAt_const.mul (ContinuousAt.comp
      (f := fun x : closedAnnulus r₁ r₂ ↦ (x : ℂ) / (r₁ * ζ)) (continuousAt_clog hz.2)
      (continuous_subtype_val.div_const _).continuousAt)).continuousWithinAt
  continuousOn_invFun := by
    refine Continuous.continuousOn (Topology.IsInducing.subtypeVal.continuous_iff.2 ?_)
    exact continuous_const.mul
      (continuous_const.mul ((continuous_capIm _).comp continuous_subtype_val)).cexp

/-- On the points with `‖z‖ > r₁`, the outer chart has imaginary part below `log (r₂ / r₁)`. -/
private theorem im_outer_lt {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : closedAnnulus r₁ r₂)
    (hz : r₁ < ‖(z : ℂ)‖) : (-I * log ((z : ℂ) / (r₂ * ζ))).im < Real.log (r₂ / r₁) := by
  rw [im_neg_I_mul_log, norm_div_ofReal_mul (zero_lt_r₂ r₁ r₂) hζ, ← Real.log_inv, inv_div]
  exact Real.log_lt_log (div_pos (zero_lt_r₂ r₁ r₂) (norm_coe_pos z))
    (div_lt_div_of_pos_left (zero_lt_r₂ r₁ r₂) hr₁.out hz)

/-- The outer logarithmic chart attached to a point `ζ` of the unit circle: the map
`z ↦ -I log (z / (r₂ ζ))` from the points of the closed annulus with `‖z‖ > r₁` and `z / ζ` off
the closed negative real axis, onto `TauCeti.ClosedAnnulus.chartTarget r₁ r₂`. Its inverse is
`w ↦ r₂ ζ exp (I w)`. It sends the outer circle `‖z‖ = r₂` to the real axis. -/
def outerChart (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane where
  toFun z := ⟨-I * log ((z : ℂ) / (r₂ * ζ)), im_outer_nonneg hζ z⟩
  invFun w := ⟨r₂ * ζ * exp (I * capIm (Real.log (r₂ / r₁)) w), mem_closedAnnulus_outer hζ w⟩
  source := {z | r₁ < ‖(z : ℂ)‖ ∧ (z : ℂ) / (r₂ * ζ) ∈ slitPlane}
  target := chartTarget r₁ r₂
  map_source' z hz := by
    refine ⟨?_, ?_⟩
    · change |(-I * log ((z : ℂ) / (r₂ * ζ))).re| < π
      rw [re_neg_I_mul_log]
      exact abs_arg_lt_pi hz.2
    · exact im_outer_lt hζ z hz.1
  map_target' w hw := by
    have hρ := ofReal_mul_ne_zero (zero_lt_r₂ r₁ r₂) hζ
    have hc : capIm (Real.log (r₂ / r₁)) w = w := capIm_of_im_le hw.2.le
    have hre : |(I * (w : ℂ)).im| < π := by simpa using hw.1
    simp only [mem_ofPred_eq, hc]
    refine ⟨?_, ?_⟩
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (zero_lt_r₂ r₁ r₂).le, hζ,
        mul_one, norm_exp]
      calc r₁ = r₂ * Real.exp (-Real.log (r₂ / r₁)) := by
            rw [Real.exp_neg, Real.exp_log (div_pos (zero_lt_r₂ r₁ r₂) hr₁.out)]
            field_simp [hr₁.out.ne', (zero_lt_r₂ r₁ r₂).ne']
        _ < r₂ * Real.exp (I * (w : ℂ)).re := by
            refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) (zero_lt_r₂ r₁ r₂)
            simpa using hw.2
    · rw [mul_div_cancel_left₀ _ hρ]
      exact exp_mem_slitPlane_of_abs_im_lt hre
  left_inv' z hz := by
    have hρ := ofReal_mul_ne_zero (zero_lt_r₂ r₁ r₂) hζ
    apply Subtype.ext
    change (r₂ : ℂ) * ζ * exp (I * capIm (Real.log (r₂ / r₁)) (-I * log ((z : ℂ) / (r₂ * ζ)))) = z
    rw [capIm_of_im_le (im_outer_lt hζ z hz.1).le, ← mul_assoc, mul_neg, I_mul_I, neg_neg,
      one_mul, exp_log (slitPlane_ne_zero hz.2), mul_div_cancel₀ _ hρ]
  right_inv' w hw := by
    have hρ := ofReal_mul_ne_zero (zero_lt_r₂ r₁ r₂) hζ
    have hc : capIm (Real.log (r₂ / r₁)) w = w := capIm_of_im_le hw.2.le
    have hre : |(I * (w : ℂ)).im| < π := by simpa using hw.1
    apply Subtype.ext
    change -I * log (r₂ * ζ * exp (I * capIm (Real.log (r₂ / r₁)) w) / (r₂ * ζ)) = w
    rw [hc, mul_div_cancel_left₀ _ hρ, log_exp_of_abs_im_lt hre, ← mul_assoc, neg_mul, I_mul_I,
      neg_neg, one_mul]
  open_source := (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).inter
    (isOpen_slitPlane.preimage (continuous_subtype_val.div_const _))
  open_target := isOpen_chartTarget
  continuousOn_toFun := by
    refine ((Topology.IsEmbedding.subtypeVal (p := fun w : ℂ ↦ 0 ≤ w.im)).isInducing
      |>.continuousOn_iff).2 fun z hz ↦ ?_
    exact (continuousAt_const.mul (ContinuousAt.comp
      (f := fun x : closedAnnulus r₁ r₂ ↦ (x : ℂ) / (r₂ * ζ)) (continuousAt_clog hz.2)
      (continuous_subtype_val.div_const _).continuousAt)).continuousWithinAt
  continuousOn_invFun := by
    refine Continuous.continuousOn (Topology.IsInducing.subtypeVal.continuous_iff.2 ?_)
    exact continuous_const.mul
      (continuous_const.mul ((continuous_capIm _).comp continuous_subtype_val)).cexp

variable {ζ : ℂ} {hζ : ‖ζ‖ = 1}

/-- The inner chart is `z ↦ I log (z / (r₁ ζ))`. -/
@[simp]
theorem coe_innerChart_apply (z : closedAnnulus r₁ r₂) :
    (innerChart ζ hζ z : ℂ) = I * log ((z : ℂ) / (r₁ * ζ)) := by
  rw [innerChart]; rfl

/-- The outer chart is `z ↦ -I log (z / (r₂ ζ))`. -/
@[simp]
theorem coe_outerChart_apply (z : closedAnnulus r₁ r₂) :
    (outerChart ζ hζ z : ℂ) = -I * log ((z : ℂ) / (r₂ * ζ)) := by
  rw [outerChart]; rfl

/-- The inner chart is defined on the points with `‖z‖ < r₂` and `z / (r₁ ζ)` in the slit
plane. -/
@[simp]
theorem innerChart_source : (innerChart (r₁ := r₁) (r₂ := r₂) ζ hζ).source =
    {z : closedAnnulus r₁ r₂ | ‖(z : ℂ)‖ < r₂ ∧ (z : ℂ) / (r₁ * ζ) ∈ slitPlane} := by
  rw [innerChart]

/-- The outer chart is defined on the points with `‖z‖ > r₁` and `z / (r₂ ζ)` in the slit
plane. -/
@[simp]
theorem outerChart_source : (outerChart (r₁ := r₁) (r₂ := r₂) ζ hζ).source =
    {z : closedAnnulus r₁ r₂ | r₁ < ‖(z : ℂ)‖ ∧ (z : ℂ) / (r₂ * ζ) ∈ slitPlane} := by
  rw [outerChart]

/-- The inner chart takes values in `TauCeti.ClosedAnnulus.chartTarget r₁ r₂`. -/
@[simp]
theorem innerChart_target :
    (innerChart (r₁ := r₁) (r₂ := r₂) ζ hζ).target = chartTarget r₁ r₂ := by
  rw [innerChart]

/-- The outer chart takes values in `TauCeti.ClosedAnnulus.chartTarget r₁ r₂`. -/
@[simp]
theorem outerChart_target :
    (outerChart (r₁ := r₁) (r₂ := r₂) ζ hζ).target = chartTarget r₁ r₂ := by
  rw [outerChart]

/-- On its target, the inverse of the inner chart is `w ↦ r₁ ζ exp (-I w)`. -/
theorem coe_innerChart_symm_apply {w : ClosedUpperHalfPlane} (hw : w ∈ chartTarget r₁ r₂) :
    ((innerChart (r₁ := r₁) (r₂ := r₂) ζ hζ).symm w : ℂ) = r₁ * ζ * exp (-I * w) := by
  change (r₁ : ℂ) * ζ * exp (-I * capIm (Real.log (r₂ / r₁)) w) = _
  rw [capIm_of_im_le hw.2.le]

/-- On its target, the inverse of the outer chart is `w ↦ r₂ ζ exp (I w)`. -/
theorem coe_outerChart_symm_apply {w : ClosedUpperHalfPlane} (hw : w ∈ chartTarget r₁ r₂) :
    ((outerChart (r₁ := r₁) (r₂ := r₂) ζ hζ).symm w : ℂ) = r₂ * ζ * exp (I * w) := by
  change (r₂ : ℂ) * ζ * exp (I * capIm (Real.log (r₂ / r₁)) w) = _
  rw [capIm_of_im_le hw.2.le]

/-- The imaginary part of the inner chart is `log (‖z‖ / r₁)`. -/
theorem im_innerChart_apply (z : closedAnnulus r₁ r₂) :
    (innerChart ζ hζ z : ℂ).im = Real.log (‖(z : ℂ)‖ / r₁) := by
  rw [coe_innerChart_apply, im_I_mul_log, norm_div_ofReal_mul hr₁.out hζ]

/-- The imaginary part of the outer chart is `log (r₂ / ‖z‖)`. -/
theorem im_outerChart_apply (z : closedAnnulus r₁ r₂) :
    (outerChart ζ hζ z : ℂ).im = Real.log (r₂ / ‖(z : ℂ)‖) := by
  rw [coe_outerChart_apply, im_neg_I_mul_log, norm_div_ofReal_mul (zero_lt_r₂ r₁ r₂) hζ,
    ← Real.log_inv, inv_div]

/-! ### The atlas -/

omit hr₁ hr₁₂ in
/-- The direction of the preferred chart at `z`: `1` if `0 ≤ re z`, and `-1` otherwise. -/
def chartDirection (z : closedAnnulus r₁ r₂) : ℂ :=
  if 0 ≤ (z : ℂ).re then 1 else -1

omit hr₁ hr₁₂ in
/-- The direction of the preferred chart lies on the unit circle. -/
theorem norm_chartDirection (z : closedAnnulus r₁ r₂) : ‖chartDirection z‖ = 1 := by
  unfold chartDirection
  split_ifs <;> simp

omit hr₁₂ in
/-- For `ρ > 0`, the point `z / (ρ ζ)` lies in the slit plane when `ζ` is the direction of the
preferred chart at `z`. -/
private theorem div_mem_slitPlane {ρ : ℝ} (hρ : 0 < ρ) (z : closedAnnulus r₁ r₂) :
    (z : ℂ) / (ρ * chartDirection z) ∈ slitPlane := by
  have hz : (z : ℂ) ≠ 0 := norm_ne_zero_iff.1 (norm_coe_pos z).ne'
  unfold chartDirection
  split_ifs with h
  · rw [mul_one, mem_slitPlane_iff, div_ofReal_re, div_ofReal_im]
    rcases h.lt_or_eq with h | h
    · exact Or.inl (div_pos h hρ)
    · refine Or.inr (div_ne_zero (fun him ↦ hz (Complex.ext ?_ ?_)) hρ.ne')
      · simpa using h.symm
      · simpa using him
  · rw [mul_neg_one, div_neg, mem_slitPlane_iff, neg_re, div_ofReal_re]
    exact Or.inl (neg_pos.2 (div_neg_of_neg_of_pos (not_le.1 h) hρ))

/-- The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` is a charted space modelled on the closed upper
half-plane. The atlas consists of the inner and outer logarithmic charts. The chart at `z` is the
inner chart if `‖z‖ < r₂` and the outer chart otherwise, with direction
`TauCeti.ClosedAnnulus.chartDirection z`. -/
instance instChartedSpace : ChartedSpace ClosedUpperHalfPlane (closedAnnulus r₁ r₂) where
  atlas := {e | ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = innerChart ζ hζ ∨ e = outerChart ζ hζ}
  chartAt z := if ‖(z : ℂ)‖ < r₂ then innerChart (chartDirection z) (norm_chartDirection z)
    else outerChart (chartDirection z) (norm_chartDirection z)
  mem_chart_source z := by
    split_ifs with h
    · exact ⟨h, div_mem_slitPlane hr₁.out z⟩
    · exact ⟨hr₁₂.out.trans_le (not_lt.1 h), div_mem_slitPlane (zero_lt_r₂ r₁ r₂) z⟩
  chart_mem_atlas z := by
    split_ifs
    · exact ⟨_, _, Or.inl rfl⟩
    · exact ⟨_, _, Or.inr rfl⟩

/-- The chart at `z` is the inner chart if `‖z‖ < r₂` and the outer chart otherwise. -/
theorem chartAt_eq (z : closedAnnulus r₁ r₂) :
    chartAt ClosedUpperHalfPlane z =
      if ‖(z : ℂ)‖ < r₂ then innerChart (chartDirection z) (norm_chartDirection z)
      else outerChart (chartDirection z) (norm_chartDirection z) :=
  rfl

/-- The charts of the atlas are the inner and outer logarithmic charts. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane} :
    e ∈ atlas ClosedUpperHalfPlane (closedAnnulus r₁ r₂) ↔
      ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = innerChart ζ hζ ∨ e = outerChart ζ hζ :=
  Iff.rfl

/-! ### Transition maps -/

/-- A chart of the closed annulus whose inverse is `w ↦ ρ exp (c w)` on its target and which is
`z ↦ d log (z / ρ)` on its source, with `z / ρ` in the slit plane. -/
private def IsLogChart (e : OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane) :
    Prop :=
  ∃ ρ c d : ℂ, (∀ w ∈ e.target, ((e.symm w : closedAnnulus r₁ r₂) : ℂ) = ρ * exp (c * w)) ∧
    ∀ z ∈ e.source, (z : ℂ) / ρ ∈ slitPlane ∧ (e z : ℂ) = d * log ((z : ℂ) / ρ)

private theorem isLogChart_of_mem_atlas
    {e : OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane}
    (he : e ∈ atlas ClosedUpperHalfPlane (closedAnnulus r₁ r₂)) : IsLogChart e := by
  obtain ⟨ζ, hζ, rfl | rfl⟩ := he
  · exact ⟨r₁ * ζ, -I, I, fun w hw ↦ coe_innerChart_symm_apply hw, fun z hz ↦ ⟨hz.2, rfl⟩⟩
  · exact ⟨r₂ * ζ, I, -I, fun w hw ↦ coe_outerChart_symm_apply hw, fun z hz ↦ ⟨hz.2, rfl⟩⟩

end Charts

/-- A partial homeomorphism of the closed upper half-plane which, on its source and on its
target, is given in the ambient coordinate by functions that are complex analytic at each point,
belongs to the bordered holomorphic groupoid. -/
private theorem mem_borderedHolomorphicGroupoid_of_contDiffAt
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane} {F G : ℂ → ℂ}
    (hF : ∀ w ∈ e.source, ContDiffAt ℂ ∞ F w ∧ (e w : ℂ) = F w)
    (hG : ∀ w ∈ e.target, ContDiffAt ℂ ∞ G w ∧ (e.symm w : ℂ) = G w) :
    e ∈ borderedHolomorphicGroupoid := by
  have key : ∀ {k : ClosedUpperHalfPlane → ClosedUpperHalfPlane} {s : Set ClosedUpperHalfPlane}
      {K : ℂ → ℂ}, (∀ w ∈ s, ContDiffAt ℂ ∞ K w ∧ (k w : ℂ) = K w) →
        ContDiffOn ℝ ∞ (closedUpperHalfPlaneModel ∘ k ∘ closedUpperHalfPlaneModel.symm)
          (closedUpperHalfPlaneModel.symm ⁻¹' s ∩ range closedUpperHalfPlaneModel) ∧
        DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ k ∘ closedUpperHalfPlaneModel.symm)
          (closedUpperHalfPlaneModel.symm ⁻¹' s ∩ {z | 0 < z.im}) := by
    intro k s K hk
    have heq : ∀ {z : ℂ}, 0 ≤ z.im → closedUpperHalfPlaneModel.symm z ∈ s →
        (closedUpperHalfPlaneModel ∘ k ∘ closedUpperHalfPlaneModel.symm) z = K z := by
      intro z hz hs
      simpa [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz] using (hk _ hs).2
    have hat : ∀ {z : ℂ}, 0 ≤ z.im → closedUpperHalfPlaneModel.symm z ∈ s →
        ContDiffAt ℂ ∞ K z := by
      intro z hz hs
      simpa [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz] using (hk _ hs).1
    refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · have him : 0 ≤ z.im := by simpa using hz.2
      exact ((hat him hz.1).restrict_scalars ℝ).contDiffWithinAt.congr
        (fun y hy ↦ heq (by simpa using hy.2) hy.1) (heq him hz.1)
    · exact ((hat hz.2.le hz.1).differentiableAt (by simp)).differentiableWithinAt.congr
        (fun y hy ↦ heq hy.2.le hy.1) (heq hz.2.le hz.1)
  exact mem_borderedHolomorphicGroupoid_iff.2
    ⟨⟨(key hF).1, (key hG).1⟩, (key hF).2, (key hG).2⟩

section Transitions

variable [hr₁ : Fact (0 < r₁)] [hr₁₂ : Fact (r₁ < r₂)]

omit hr₁ hr₁₂ in
/-- The transition map from a log chart `e` to a log chart `e'` is
`w ↦ d' log (ρ exp (c w) / ρ')`, analytic at each point of its source. -/
private theorem transition_contDiffAt
    {e e' : OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane} {ρ c ρ' d' : ℂ}
    (he : ∀ w ∈ e.target, ((e.symm w : closedAnnulus r₁ r₂) : ℂ) = ρ * exp (c * w))
    (he' : ∀ z ∈ e'.source, (z : ℂ) / ρ' ∈ slitPlane ∧ (e' z : ℂ) = d' * log ((z : ℂ) / ρ'))
    (w : ClosedUpperHalfPlane) (hw : w ∈ (e.symm ≫ₕ e').source) :
    ContDiffAt ℂ ∞ (fun v ↦ d' * log (ρ * exp (c * v) / ρ')) w ∧
      ((e.symm ≫ₕ e') w : ℂ) = d' * log (ρ * exp (c * w) / ρ') := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
  have h' := he' _ hw.2
  rw [he w hw.1] at h'
  refine ⟨?_, ?_⟩
  · exact contDiffAt_const.mul ((contDiffAt_log h'.1).comp (w : ℂ)
      (f := fun v ↦ ρ * exp (c * v) / ρ')
      ((contDiffAt_const.mul (contDiffAt_const.mul contDiffAt_id).cexp).div_const _))
  · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, (he' _ hw.2).2, he w hw.1]

omit hr₁ hr₁₂ in
private theorem symm_trans_mem_borderedHolomorphicGroupoid
    {e e' : OpenPartialHomeomorph (closedAnnulus r₁ r₂) ClosedUpperHalfPlane}
    (he : IsLogChart e) (he' : IsLogChart e') :
    e.symm ≫ₕ e' ∈ borderedHolomorphicGroupoid := by
  obtain ⟨ρ, c, d, hes, hee⟩ := he
  obtain ⟨ρ', c', d', hes', hee'⟩ := he'
  have hsymm : (e.symm ≫ₕ e').symm = e'.symm ≫ₕ e := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  refine mem_borderedHolomorphicGroupoid_of_contDiffAt
    (G := fun v ↦ d * log (ρ' * exp (c' * v) / ρ))
    (transition_contDiffAt hes hee') fun w hw ↦ ?_
  rw [← OpenPartialHomeomorph.symm_source, hsymm] at hw
  rw [hsymm]
  exact transition_contDiffAt hes' hee w hw

/-- The closed annulus, with its logarithmic charts, is a Riemann surface with boundary. -/
instance instHasGroupoid : HasGroupoid (closedAnnulus r₁ r₂) borderedHolomorphicGroupoid where
  compatible he he' :=
    symm_trans_mem_borderedHolomorphicGroupoid (isLogChart_of_mem_atlas he)
      (isLogChart_of_mem_atlas he')

/-! ### Interior and boundary -/

/-- The interior of the closed annulus is the open annulus `r₁ < ‖z‖ < r₂`. -/
theorem mem_borderedInterior_iff {z : closedAnnulus r₁ r₂} :
    z ∈ borderedInterior (closedAnnulus r₁ r₂) ↔ r₁ < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < r₂ := by
  rw [mem_borderedInterior_iff_im_chartAt_pos, chartAt_eq]
  split_ifs with h
  · rw [im_innerChart_apply, Real.log_pos_iff (div_nonneg (norm_nonneg _) hr₁.out.le),
      one_lt_div hr₁.out]
    exact ⟨fun h' ↦ ⟨h', h⟩, And.left⟩
  · have hz : ‖(z : ℂ)‖ = r₂ := le_antisymm (norm_coe_le z) (not_lt.1 h)
    rw [im_outerChart_apply, hz, div_self (zero_lt_r₂ r₁ r₂).ne', Real.log_one]
    exact ⟨fun h' ↦ (lt_irrefl _ h').elim, fun h' ↦ (lt_irrefl _ h'.2).elim⟩

/-- The interior of the closed annulus is the open annulus `r₁ < ‖z‖ < r₂`. -/
theorem coe_borderedInterior :
    (borderedInterior (closedAnnulus r₁ r₂) : Set ↥(closedAnnulus r₁ r₂)) =
      {z : closedAnnulus r₁ r₂ | r₁ < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < r₂} :=
  Set.ext fun _ ↦ mem_borderedInterior_iff

/-- The complement of the interior of the closed annulus is its pair of boundary circles, the
boundary along which `TauCeti.DoubleAlong` doubles the annulus to the torus. -/
theorem compl_borderedInterior :
    (borderedInterior (closedAnnulus r₁ r₂) : Set ↥(closedAnnulus r₁ r₂))ᶜ =
      DoubleAlong.annulusBoundary r₁ r₂ := by
  ext z
  rw [mem_compl_iff, SetLike.mem_coe, mem_borderedInterior_iff, DoubleAlong.mem_annulusBoundary,
    not_and_or, not_lt, not_lt]
  constructor
  · rintro (h | h)
    · exact Or.inl (le_antisymm h (le_norm_coe z))
    · exact Or.inr (le_antisymm (norm_coe_le z) h)
  · rintro (h | h)
    · exact Or.inl h.le
    · exact Or.inr h.ge

/-- The inclusion of the interior of the closed annulus into `ℂ` is analytic for the complex
structure induced by the logarithmic charts. So the induced complex structure on the open annulus
is the standard one. -/
theorem contMDiff_coe_borderedInterior :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : borderedInterior (closedAnnulus r₁ r₂) ↦ ((z : closedAnnulus r₁ r₂) : ℂ)) := by
  intro x
  refine contMDiffAt_iff.2 ⟨(continuous_subtype_val.comp continuous_subtype_val).continuousAt, ?_⟩
  simp only [mfld_simps]
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ρ, c, -, hsymm, -⟩ :=
    isLogChart_of_mem_atlas (chart_mem_atlas ClosedUpperHalfPlane (x : closedAnnulus r₁ r₂))
  have hw := mem_chart_target ℂ x
  have hev : (fun v ↦ (((chartAt ℂ x).symm v : closedAnnulus r₁ r₂) : ℂ)) =ᶠ[𝓝 (chartAt ℂ x x)]
      fun v ↦ ρ * exp (c * v) := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hw] with v hv
    rw [chartAt_borderedInterior_symm_apply x hv]
    rw [chartAt_borderedInterior_target] at hv
    rw [hsymm _ hv.1, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hv.2.le]
  exact (contDiffAt_const.mul (contDiffAt_const.mul contDiffAt_id).cexp).congr_of_eventuallyEq hev

end Transitions

end ClosedAnnulus

end TauCeti
