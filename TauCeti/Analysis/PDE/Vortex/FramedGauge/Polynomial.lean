/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Moduli
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
public import TauCeti.RingTheory.Polynomial.SymmetricPower
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The end-normalizing gauge of a monic polynomial

Taubes's plane vortex with zero divisor `D ∈ Sym ℂ m` has section `exp(u) P`, where `u` is real
and `P = Wᵐ + c_(m-1) Wᵐ⁻¹ + ⋯ + c₀` is the monic polynomial with root multiset `D`. Its lower
coefficients `c = (c₀, …, c_(m-1))` are the symmetric coordinates of `D`
(`Sym.coeffHomeomorph`). When `c_(m-1) ≠ 0`, the phase `P / |P|` of the section tends to the
winding phase `(z / |z|)ᵐ` only like `1 / |z|`, so the vortex itself need not lie in the affine
Sobolev space `A_m^k = x_m + H^k` (`TauCeti.Vortex.framedFieldSpace`), and a framed gauge must
normalize its phase near infinity. This file constructs one such gauge for every coefficient
tuple, depending smoothly on the coefficients, and normalizing on a common exterior over each
compact window of coefficients or divisors.

For `z ≠ 0` write `P_c(z) = zᵐ (1 + q_c(z))` with `q_c(z) = ∑ᵢ cᵢ zⁱ / zᵐ`. If
`‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 1` then `‖q_c(z)‖ < 1`, by the Cauchy–Schwarz inequality, so
`1 + q_c(z)` lies in the slit plane and has a smooth argument. The **polynomial gauge**
(`TauCeti.Vortex.polynomialGauge`) is

`g_c(z) = exp (-i χ(‖z‖² - m ∑ᵢ ‖cᵢ‖² - 1) arg (1 + q_c(z)))`,

with the smooth transition `χ` vanishing on `(-∞, 0]` and equal to one on `[1, ∞)`. Thus:

* `g_c(z)` is jointly smooth in the coefficients and the point
  (`TauCeti.Vortex.contDiff_polynomialGauge`), and for each `c` it is a smooth framed gauge
  (`TauCeti.Vortex.polynomialGauge_mem_framedGaugeGroup`).
* `g_c = 1` on the disc `‖z‖² ≤ m ∑ᵢ ‖cᵢ‖² + 1` (`TauCeti.Vortex.polynomialGauge_eq_one`).
* Outside the slightly larger disc `‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 2`, it turns the phase of `P_c` into the
  winding phase: `g_c(z) P_c(z) = |P_c(z)| (z / |z|)ᵐ`
  (`TauCeti.Vortex.polynomialGauge_mul_eval`). Where `‖z‖² > m ∑ᵢ ‖cᵢ‖² + 2`, its logarithmic
  derivative is `m dθ - d arg P_c`, that is
  `Im (g⁻¹ dg)(v) = m Im (v / z) - Im (P_c'(z) v / P_c(z))`
  (`TauCeti.Vortex.gaugeForm_polynomialGauge_apply`).
* The radius depends on `c` only through `∑ᵢ ‖cᵢ‖²`, so one radius serves a bounded set of
  coefficients (`TauCeti.Vortex.exists_forall_polynomialGauge_mul_eval`) and a compact set of
  divisors (`TauCeti.Vortex.exists_forall_polynomialGauge_coeffEquiv_mul_eval`).
* The construction is compatible with rotations of the plane: rotating `P_c` by a unit `u`
  rotates the gauge, `g_(c^u)(z) = g_c(u z)` where `c^u` are the coefficients of
  `u⁻ᵐ P_c(u z)` (`TauCeti.Vortex.polynomialGauge_rotateCoeff`), so the rotation `R_u` of the
  plane carries `g_c · x` to `g_(c^u) · R_u x`
  (`TauCeti.Vortex.rotateField_gaugeTransform_polynomialGauge`). The polynomial with rotated
  coefficients is `P_c` with roots scaled by `u⁻¹` (`TauCeti.Vortex.monicOfCoeff_rotateCoeff`),
  and the rotations compose (`TauCeti.Vortex.rotateCoeff_one`,
  `TauCeti.Vortex.rotateCoeff_mul`). In the elementary symmetric chart the rotated coefficients
  are the divisor multiplied by `u⁻¹` (`TauCeti.Vortex.coeffEquiv_symm_rotateCoeff`). The gauge of
  `Wᵐ` is trivial (`TauCeti.Vortex.polynomialGauge_zero`).
* Translations of the plane act on the coefficients too, by
  `TauCeti.Polynomial.translateCoeff a c`, the coefficients of `P_c(z + a)`: the divisor moves by
  `-a` (`Sym.coeffEquiv_symm_translateCoeff`). The polynomial gauge is not
  translation-equivariant, since translations do not preserve the winding phase; the laws of the
  normalized vortices under both symmetries are in `TauCeti.Analysis.PDE.Vortex.Divisor.Symmetry`.

Applied to a field whose section is a nonnegative multiple `ρ P_c` of the polynomial, such as
the reconstructed field `TauCeti.Vortex.amplitudeField u P_c` of Taubes's existence proof, the
gauge makes the section `|α|` times the winding phase outside a radius that is uniform over a
bounded set of coefficients
(`TauCeti.Vortex.exists_forall_sectionValue_gaugeTransform_polynomialGauge`). A smooth framed
vortex whose section is a real multiple of `P_c` has a positive multiple near infinity, so the
gauged field lies in every `A_m^s`, with every derivative of `g_c · x - x_ref` decaying like
`exp (-c |z|)` for each `c < 1 / 2`
(`TauCeti.Vortex.gaugeTransform_polynomialGauge_mem_framedFieldSpace`). This is an explicit,
coefficient-smooth choice of the normalizing gauge in
`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`, which is only shown to exist
for each vortex separately; both follow from
`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_of_eventually_sectionValue_eq`.

The translation gauge `TauCeti.Vortex.translationGauge m a` normalizes the phase of the single
polynomial `(W + a)ᵐ`, with a cutoff adapted to `‖a‖`; the polynomial gauge does this for every
monic polynomial of degree `m` at once, smoothly in its coefficients.

## Main definitions

* `TauCeti.Vortex.polynomialGauge c`: the end-normalizing gauge of the monic polynomial with
  lower coefficients `c`.
* `TauCeti.Vortex.rotateCoeff u c`: the coefficients of `u⁻ᵐ P_c(u z)`.

## Main results

* `TauCeti.Vortex.contDiff_polynomialGauge`: the gauge is smooth in `(c, z)`.
* `TauCeti.Vortex.polynomialGauge_mem_framedGaugeGroup`: each `g_c` is a smooth framed gauge.
* `TauCeti.Vortex.polynomialGauge_mul_eval`: `g_c(z) P_c(z) = |P_c(z)| (z / |z|)ᵐ` outside a disc.
* `TauCeti.Vortex.exists_forall_polynomialGauge_coeffEquiv_mul_eval`: one radius for a compact
  window of divisors.
* `TauCeti.Vortex.gaugeTransform_polynomialGauge_mem_framedFieldSpace`: the gauged vortex lies in
  every `A_m^s`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology Asymptotics
open TauCeti.Polynomial
open scoped ContDiff _root_.Polynomial

variable {m : ℕ}

/-! ### The tail of a monic polynomial -/

/-- The tail `q_c(z) = ∑ᵢ cᵢ zⁱ / zᵐ`, so that `P_c(z) = zᵐ (1 + q_c(z))` for `z ≠ 0`. -/
private def tail (c : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin m, c i * z ^ (i : ℕ) / z ^ m

/-- The argument of the cutoff of the polynomial gauge. -/
private def cutoffArg (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  ‖z‖ ^ 2 - m * ∑ i, ‖c i‖ ^ 2 - 1

private theorem eval_monicOfCoeff_eq_mul_tail (c : Fin m → ℂ) {z : ℂ} (hz : z ≠ 0) :
    (monicOfCoeff c).eval z = z ^ m * (1 + tail c z) := by
  have hzm : z ^ m ≠ 0 := pow_ne_zero m hz
  rw [eval_monicOfCoeff, tail, mul_add, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by field_simp

/-- For `‖z‖ ≥ 1`, the tail is bounded by `∑ᵢ ‖cᵢ‖ / ‖z‖`. -/
private theorem norm_tail_le (c : Fin m → ℂ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖tail c z‖ ≤ (∑ i, ‖c i‖) / ‖z‖ := by
  have hz0 : 0 < ‖z‖ := one_pos.trans_le hz
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_div, norm_mul, norm_pow, norm_pow,
    div_le_div_iff₀ (pow_pos hz0 m) hz0, mul_assoc, ← pow_succ]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz i.isLt) (norm_nonneg _)

/-- Where the cutoff of the polynomial gauge can be nonzero, `z ≠ 0` and the tail has norm less
than one. -/
private theorem ne_zero_and_norm_tail_lt_one {c : Fin m → ℂ} {z : ℂ}
    (hz : 0 ≤ cutoffArg c z) : z ≠ 0 ∧ ‖tail c z‖ < 1 := by
  have hS : 0 ≤ (m : ℝ) * ∑ i, ‖c i‖ ^ 2 := by positivity
  have hz2 : (m : ℝ) * ∑ i, ‖c i‖ ^ 2 + 1 ≤ ‖z‖ ^ 2 := by
    unfold cutoffArg at hz
    linarith
  have hz1 : 1 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have hz0 : 0 < ‖z‖ := one_pos.trans_le hz1
  -- By the Cauchy–Schwarz inequality, `(∑ᵢ ‖cᵢ‖)² ≤ m ∑ᵢ ‖cᵢ‖² < ‖z‖²`.
  have hcs : (∑ i, ‖c i‖) ^ 2 ≤ m * ∑ i, ‖c i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ ‖c i‖)
  have hsum : ∑ i, ‖c i‖ < ‖z‖ := lt_of_pow_lt_pow_left₀ 2 hz0.le (hcs.trans_lt (by linarith))
  exact ⟨norm_pos_iff.1 hz0, (norm_tail_le c hz1).trans_lt ((div_lt_one hz0).2 hsum)⟩

private theorem one_add_tail_mem_slitPlane {c : Fin m → ℂ} {z : ℂ} (hz : 0 ≤ cutoffArg c z) :
    1 + tail c z ∈ slitPlane :=
  mem_slitPlane_of_norm_lt_one (ne_zero_and_norm_tail_lt_one hz).2

/-! ### The polynomial gauge -/

/-- The phase of the polynomial gauge: `-arg (1 + q_c(z))` where `‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 2`, cut off
smoothly to zero where `‖z‖² ≤ m ∑ᵢ ‖cᵢ‖² + 1`. -/
private def polynomialPhase (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  -(Real.smoothTransition (cutoffArg c z) * arg (1 + tail c z))

/-- **The polynomial gauge** of the monic polynomial `P_c = Wᵐ + ∑ᵢ cᵢ Wⁱ` with lower coefficients
`c`: the circle-valued gauge `exp (-i χ arg (P_c(z) / zᵐ))`, where the cutoff `χ` vanishes where
`‖z‖² ≤ m ∑ᵢ ‖cᵢ‖² + 1` and equals one where `‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 2`. It is a smooth framed gauge
(`polynomialGauge_mem_framedGaugeGroup`), smooth in `c` as well (`contDiff_polynomialGauge`), and
outside a disc it makes the phase of `P_c` the winding phase (`polynomialGauge_mul_eval`). Its
value at every point is stated in public terms by `polynomialGauge_apply`. -/
def polynomialGauge (c : Fin m → ℂ) (z : ℂ) : Circle :=
  Circle.exp (polynomialPhase c z)

private theorem contDiff_cutoffArg :
    ContDiff ℝ ∞ (fun p : (Fin m → ℂ) × ℂ ↦ cutoffArg p.1 p.2) := by
  have hc (i : Fin m) : ContDiff ℝ ∞ (fun p : (Fin m → ℂ) × ℂ ↦ ‖p.1 i‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_pi.1 contDiff_fst i)
  exact (((contDiff_norm_sq ℝ).comp contDiff_snd).sub
    (contDiff_const.mul (ContDiff.sum fun i _ ↦ hc i))).sub contDiff_const

private theorem isOpen_cutoffArg_lt :
    IsOpen {p : (Fin m → ℂ) × ℂ | cutoffArg p.1 p.2 < 0} :=
  isOpen_lt contDiff_cutoffArg.continuous continuous_const

/-- The tail is complex-smooth in the coefficients and the point, away from `z = 0`. -/
private theorem contDiffAt_tail {p : (Fin m → ℂ) × ℂ} (hp : p.2 ≠ 0) :
    ContDiffAt ℂ ∞ (fun q : (Fin m → ℂ) × ℂ ↦ tail q.1 q.2) p := by
  unfold tail
  refine ContDiffAt.sum fun i _ ↦ ?_
  exact (((contDiff_pi.1 contDiff_fst i).mul
    (contDiff_snd.pow _)).contDiffAt).div (contDiff_snd.pow m).contDiffAt (pow_ne_zero m hp)

/-- The phase of the polynomial gauge is smooth in the coefficients and the point. -/
private theorem contDiff_polynomialPhase :
    ContDiff ℝ ∞ (fun p : (Fin m → ℂ) × ℂ ↦ polynomialPhase p.1 p.2) := by
  refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
  rcases lt_or_ge (cutoffArg p.1 p.2) 0 with hp | hp
  · -- Near `p` the cutoff vanishes.
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [isOpen_cutoffArg_lt.mem_nhds hp] with q hq
    simp [polynomialPhase, Real.smoothTransition.zero_of_nonpos (le_of_lt hq)]
  · have hp0 := (ne_zero_and_norm_tail_lt_one hp).1
    have harg := (contDiffAt_arg (one_add_tail_mem_slitPlane hp)).comp p
      (((contDiffAt_const (c := (1 : ℂ))).add (contDiffAt_tail hp0)).restrict_scalars ℝ)
    exact ((Real.smoothTransition.contDiff.comp contDiff_cutoffArg).contDiffAt.mul harg).neg

/-- **The polynomial gauge is jointly smooth** in the coefficients and the point. -/
theorem contDiff_polynomialGauge :
    ContDiff ℝ ∞ (fun p : (Fin m → ℂ) × ℂ ↦ (polynomialGauge p.1 p.2 : ℂ)) := by
  simpa only [polynomialGauge, Circle.coe_exp, Function.comp_def, ofRealCLM_apply] using
    ((ofRealCLM.contDiff.comp contDiff_polynomialPhase).mul (contDiff_const (c := I))).cexp

private theorem contDiff_polynomialPhase_right (c : Fin m → ℂ) :
    ContDiff ℝ ∞ (polynomialPhase c) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ ↦ ((c, z) : (Fin m → ℂ) × ℂ)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using contDiff_polynomialPhase.comp h

/-- The tail of a monic polynomial tends to zero at infinity. -/
private theorem tendsto_tail (c : Fin m → ℂ) :
    Tendsto (tail c) (cocompact ℂ) (𝓝 0) := by
  have hdiv : Tendsto (fun z : ℂ ↦ (∑ i, ‖c i‖) / ‖z‖) (cocompact ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
  refine squeeze_zero_norm' ?_ hdiv
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop 1] with z hz
  exact norm_tail_le c hz

/-- The phase of the polynomial gauge tends to zero at infinity. -/
private theorem tendsto_polynomialPhase (c : Fin m → ℂ) :
    Tendsto (polynomialPhase c) (cocompact ℂ) (𝓝 0) := by
  have harg : Tendsto (fun z : ℂ ↦ arg (1 + tail c z)) (cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ ↦ 1 + tail c z) (cocompact ℂ) (𝓝 1) := by
      simpa only [add_zero] using (tendsto_tail c).const_add 1
    simpa only [Function.comp_def, arg_one] using
      (continuousAt_arg one_mem_slitPlane).tendsto.comp h1
  refine squeeze_zero_norm (fun z ↦ ?_) (by simpa using harg.norm)
  have h₀ := Real.smoothTransition.nonneg (cutoffArg c z)
  have h₁ := Real.smoothTransition.le_one (cutoffArg c z)
  rw [polynomialPhase, norm_neg, norm_mul, Real.norm_of_nonneg h₀]
  exact mul_le_of_le_one_left (norm_nonneg _) h₁

/-- **The polynomial gauge is a smooth framed gauge.** -/
theorem polynomialGauge_mem_framedGaugeGroup (c : Fin m → ℂ) :
    polynomialGauge c ∈ framedGaugeGroup :=
  exp_mem_framedGaugeGroup (contDiff_polynomialPhase_right c) (tendsto_polynomialPhase c)

/-- The polynomial gauge is differentiable in the point. -/
theorem differentiable_polynomialGauge (c : Fin m → ℂ) :
    Differentiable ℝ fun z ↦ (polynomialGauge c z : ℂ) :=
  differentiable_of_mem_framedGaugeGroup (polynomialGauge_mem_framedGaugeGroup c)

/-- The polynomial gauge is trivial where `‖z‖² ≤ m ∑ᵢ ‖cᵢ‖² + 1`. -/
theorem polynomialGauge_eq_one {c : Fin m → ℂ} {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ m * ∑ i, ‖c i‖ ^ 2 + 1) : polynomialGauge c z = 1 := by
  have h : cutoffArg c z ≤ 0 := by
    unfold cutoffArg
    linarith
  simp [polynomialGauge, polynomialPhase, Real.smoothTransition.zero_of_nonpos h]

/-- The polynomial gauge of `Wᵐ` is trivial. -/
@[simp]
theorem polynomialGauge_zero : polynomialGauge (0 : Fin m → ℂ) = 1 := by
  funext z
  simp [polynomialGauge, polynomialPhase, tail]

/-- **The polynomial gauge at every point**:
`g_c(z) = exp (-i χ(‖z‖² - m ∑ᵢ ‖cᵢ‖² - 1) arg (P_c(z) / zᵐ))`, with the smooth transition `χ`. -/
theorem polynomialGauge_apply (c : Fin m → ℂ) (z : ℂ) :
    polynomialGauge c z =
      Circle.exp (-(Real.smoothTransition (‖z‖ ^ 2 - m * ∑ i, ‖c i‖ ^ 2 - 1) *
        arg ((monicOfCoeff c).eval z / z ^ m))) := by
  rw [polynomialGauge, polynomialPhase, cutoffArg]
  rcases eq_or_ne z 0 with rfl | hz
  · have hS : 0 ≤ (m : ℝ) * ∑ i, ‖c i‖ ^ 2 := by positivity
    rw [Real.smoothTransition.zero_of_nonpos (by rw [norm_zero]; nlinarith), zero_mul, zero_mul]
  · rw [eval_monicOfCoeff_eq_mul_tail c hz, mul_div_cancel_left₀ _ (pow_ne_zero m hz)]

/-- Where `‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 2`, the cutoff of the polynomial phase is inactive. -/
private theorem polynomialPhase_eq {c : Fin m → ℂ} {z : ℂ}
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 ≤ ‖z‖ ^ 2) :
    polynomialPhase c z = -arg (1 + tail c z) := by
  rw [polynomialPhase, Real.smoothTransition.one_of_one_le (by unfold cutoffArg; linarith),
    one_mul]

private theorem zero_le_cutoffArg {c : Fin m → ℂ} {z : ℂ}
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 ≤ ‖z‖ ^ 2) : 0 ≤ cutoffArg c z := by
  unfold cutoffArg
  linarith

/-- **The polynomial gauge outside a disc.** Where `‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 2`, the polynomial gauge
turns the phase of `P_c` into the winding phase: `g_c(z) P_c(z) = |P_c(z)| (z / |z|)ᵐ`. -/
theorem polynomialGauge_mul_eval {c : Fin m → ℂ} {z : ℂ}
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 ≤ ‖z‖ ^ 2) :
    (polynomialGauge c z : ℂ) * (monicOfCoeff c).eval z =
      ‖(monicOfCoeff c).eval z‖ * windingPhase m z := by
  have h0 := zero_le_cutoffArg hz
  have hz0 := (ne_zero_and_norm_tail_lt_one h0).1
  have hw0 : 1 + tail c z ≠ 0 := slitPlane_ne_zero (one_add_tail_mem_slitPlane h0)
  set w := 1 + tail c z with hw
  have hnz : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)
  have hg : (polynomialGauge c z : ℂ) = ‖w‖ / w := by
    rw [polynomialGauge, Circle.coe_exp, polynomialPhase_eq hz, ← hw, ofReal_neg, neg_mul,
      exp_neg, exp_arg_mul_I hw0, inv_div]
  rw [hg, eval_monicOfCoeff_eq_mul_tail c hz0, ← hw, coe_windingPhase m hz0]
  simp only [norm_mul, norm_pow, ofReal_mul, ofReal_pow, div_pow]
  field_simp

/-- Where `‖z‖² > m ∑ᵢ ‖cᵢ‖² + 2`, the phase of the polynomial gauge is `-arg (P_c / Wᵐ)` near `z`,
so its derivative is `v ↦ -Im ((P_c'(z) / P_c(z) - m / z) v)`. -/
private theorem hasFDerivAt_polynomialPhase {c : Fin m → ℂ} {z : ℂ}
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) :
    HasFDerivAt (polynomialPhase c)
      (-(imCLM ∘L ((ContinuousLinearMap.toSpanSingleton ℂ
        ((monicOfCoeff c).derivative.eval z / (monicOfCoeff c).eval z - m / z)).restrictScalars
          ℝ))) z := by
  have h0 := zero_le_cutoffArg hz.le
  have hz0 := (ne_zero_and_norm_tail_lt_one h0).1
  have hzm : z ^ m ≠ 0 := pow_ne_zero m hz0
  set P := monicOfCoeff c with hP
  have hfz : P.eval z / z ^ m = 1 + tail c z := by
    rw [eval_monicOfCoeff_eq_mul_tail c hz0, mul_div_cancel_left₀ _ hzm]
  have hPz : P.eval z ≠ 0 := by
    rw [eval_monicOfCoeff_eq_mul_tail c hz0]
    exact mul_ne_zero hzm (slitPlane_ne_zero (one_add_tail_mem_slitPlane h0))
  -- The logarithmic derivative of `P / Wᵐ` is `P' / P - m / z`.
  have hlog : (P.derivative.eval z * z ^ m - P.eval z * (m * z ^ (m - 1))) / (z ^ m) ^ 2 /
      (P.eval z / z ^ m) = P.derivative.eval z / P.eval z - m / z := by
    rcases m with _ | m
    · simp
    · rw [Nat.add_sub_cancel]
      field_simp
      ring
  have harg := ((P.hasDerivAt z).fun_div (hasDerivAt_pow m z) hzm).hasFDerivAt_arg
    (hfz ▸ one_add_tail_mem_slitPlane h0)
  rw [hlog] at harg
  -- Near `z`, the phase is `-arg (P / Wᵐ)`.
  have hopen : IsOpen {w : ℂ | m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖w‖ ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  refine harg.neg.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hw0 := (ne_zero_and_norm_tail_lt_one (zero_le_cutoffArg hw.le)).1
  rw [polynomialPhase_eq hw.le, Pi.neg_apply, hP, eval_monicOfCoeff_eq_mul_tail c hw0,
    mul_div_cancel_left₀ _ (pow_ne_zero m hw0)]

/-- **The logarithmic derivative of the polynomial gauge.** Where `‖z‖² > m ∑ᵢ ‖cᵢ‖² + 2`, the
real one-form `Im (g⁻¹ dg)` of the polynomial gauge is `m dθ - d arg P_c`:
`v ↦ m Im (v / z) - Im (P_c'(z) v / P_c(z))`. -/
theorem gaugeForm_polynomialGauge_apply {c : Fin m → ℂ} {z : ℂ}
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) (v : ℂ) :
    gaugeForm (polynomialGauge c) z v =
      m * (v / z).im -
        ((monicOfCoeff c).derivative.eval z * v / (monicOfCoeff c).eval z).im := by
  have hg : polynomialGauge c = fun w ↦ Circle.exp (polynomialPhase c w) := rfl
  rw [hg, gaugeForm_exp ((contDiff_polynomialPhase_right c).differentiable (by simp) z),
    (hasFDerivAt_polynomialPhase hz).fderiv]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    imCLM_apply, smul_eq_mul]
  rw [mul_sub, sub_im, neg_sub]
  congr 1
  · rw [mul_div_assoc', mul_comm v, mul_div_assoc]
    exact_mod_cast im_ofReal_mul (m : ℝ) (v / z)
  · ring_nf

/-! ### Uniform radii over windows -/

/-- **A common radius over a bounded window of coefficients.** For a bounded set `K` of
coefficient tuples there is one radius `R` beyond which every polynomial gauge `g_c`, `c ∈ K`,
turns the phase of `P_c` into the winding phase. -/
theorem exists_forall_polynomialGauge_mul_eval {K : Set (Fin m → ℂ)}
    (hK : Bornology.IsBounded K) :
    ∃ R, ∀ c ∈ K, ∀ z : ℂ, R ≤ ‖z‖ →
      (polynomialGauge c z : ℂ) * (monicOfCoeff c).eval z =
        ‖(monicOfCoeff c).eval z‖ * windingPhase m z := by
  obtain ⟨ρ, hρ⟩ := hK.exists_norm_le
  refine ⟨m * max ρ 0 + 2, fun c hc z hz ↦ polynomialGauge_mul_eval ?_⟩
  set r := max ρ 0
  have hr : 0 ≤ r := le_max_right ρ 0
  have hcr (i : Fin m) : ‖c i‖ ≤ r :=
    (norm_le_pi_norm c i).trans ((hρ c hc).trans (le_max_left _ _))
  have hsum : ∑ i, ‖c i‖ ^ 2 ≤ m * r ^ 2 := by
    calc ∑ i, ‖c i‖ ^ 2 ≤ ∑ _i : Fin m, r ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hcr i) 2
      _ = m * r ^ 2 := by simp
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hz' : 0 ≤ m * r + 2 := by positivity
  have hsq : (m * r + 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hz' hz 2
  nlinarith [mul_le_mul_of_nonneg_left hsum hm]

/-- **A common radius over a compact window of divisors.** For a compact set `K` of effective
divisors of degree `m`, read in the symmetric coordinates `Sym.coeffEquiv`, there is one radius
beyond which the polynomial gauge of each `D ∈ K` turns the phase of `∏_{a ∈ D} (z - a)` into the
winding phase. -/
theorem exists_forall_polynomialGauge_coeffEquiv_mul_eval {K : Set (Sym ℂ m)}
    (hK : IsCompact K) :
    ∃ R, ∀ D ∈ K, ∀ z : ℂ, R ≤ ‖z‖ →
      (polynomialGauge (Sym.coeffEquiv ℂ m D) z : ℂ) * (Sym.toMonic D : ℂ[X]).eval z =
        ‖(Sym.toMonic D : ℂ[X]).eval z‖ * windingPhase m z := by
  have hK' : IsCompact (Sym.coeffEquiv ℂ m '' K) := by
    simpa only [Sym.coeffHomeomorph_apply] using
      hK.image (Sym.coeffHomeomorph ℂ m).continuous
  obtain ⟨R, hR⟩ := exists_forall_polynomialGauge_mul_eval hK'.isBounded
  refine ⟨R, fun D hD z hz ↦ ?_⟩
  rw [Sym.toMonic_eq_monicOfCoeff_coeffEquiv]
  exact hR _ ⟨D, hD, rfl⟩ z hz

/-! ### Rotations -/

/-- The coefficients of `u⁻ᵐ P_c(u z)`: the `i`-th coefficient is divided by `u^(m - i)`. -/
def rotateCoeff (u : Circle) (c : Fin m → ℂ) (i : Fin m) : ℂ :=
  c i / (u : ℂ) ^ (m - i)

/-- The `i`-th rotated coefficient is `cᵢ / u^(m - i)`. -/
@[simp]
theorem rotateCoeff_apply (u : Circle) (c : Fin m → ℂ) (i : Fin m) :
    rotateCoeff u c i = c i / (u : ℂ) ^ (m - i) := (rfl)

/-- The identity rotation fixes the coefficients. -/
@[simp]
theorem rotateCoeff_one (c : Fin m → ℂ) : rotateCoeff 1 c = c := by
  funext i
  simp

/-- Rotation fixes the coefficients of `Wᵐ`. -/
@[simp]
theorem rotateCoeff_zero (u : Circle) : rotateCoeff u (0 : Fin m → ℂ) = 0 := by
  funext i
  simp

/-- Rotating by `u * v` is rotating by `u` and then by `v`. -/
theorem rotateCoeff_mul (u v : Circle) (c : Fin m → ℂ) :
    rotateCoeff (u * v) c = rotateCoeff v (rotateCoeff u c) := by
  funext i
  have hu := Circle.coe_ne_zero u
  have hv := Circle.coe_ne_zero v
  simp only [rotateCoeff_apply, Circle.coe_mul, mul_pow]
  field_simp

/-- The polynomial with rotated coefficients is `P_c` with its roots scaled by `u⁻¹`. -/
theorem monicOfCoeff_rotateCoeff (u : Circle) (c : Fin m → ℂ) :
    monicOfCoeff (rotateCoeff u c) = (monicOfCoeff c).scaleRoots (u : ℂ)⁻¹ := by
  refine Eq.trans ?_ (monicOfCoeff_coeff
    ((Polynomial.monic_scaleRoots_iff _).2 (monic_monicOfCoeff c))
    (by rw [Polynomial.natDegree_scaleRoots, natDegree_monicOfCoeff]))
  congr 1
  funext i
  rw [Polynomial.coeff_scaleRoots, coeff_monicOfCoeff, natDegree_monicOfCoeff, rotateCoeff_apply,
    inv_pow, div_eq_mul_inv]

/-- The polynomial with rotated coefficients is the rotated polynomial: `P_(c^u)(z) =
u⁻ᵐ P_c(u z)`. -/
theorem eval_monicOfCoeff_rotateCoeff (u : Circle) (c : Fin m → ℂ) (z : ℂ) :
    (monicOfCoeff (rotateCoeff u c)).eval z =
      (monicOfCoeff c).eval ((u : ℂ) * z) / (u : ℂ) ^ m := by
  have hz : (u : ℂ)⁻¹ * ((u : ℂ) * z) = z := by
    rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero u), one_mul]
  have h := Polynomial.scaleRoots_eval_mul (monicOfCoeff c) ((u : ℂ) * z) (u : ℂ)⁻¹
  rwa [hz, natDegree_monicOfCoeff, ← monicOfCoeff_rotateCoeff, inv_pow, ← div_eq_inv_mul] at h

open _root_.Polynomial in
/-- The polynomial with rotated coefficients is the rotated polynomial with the leading
coefficient restored by the constant `u⁻ᵐ`: `P_(c^u) = u⁻ᵐ P_c(u ·)`. -/
theorem monicOfCoeff_rotateCoeff_eq_C_mul_comp (u : Circle) (c : Fin m → ℂ) :
    monicOfCoeff (rotateCoeff u c) =
      C ((u⁻¹ ^ m : Circle) : ℂ) * (monicOfCoeff c).comp (C (u : ℂ) * X) := by
  refine Polynomial.funext fun z ↦ ?_
  rw [eval_monicOfCoeff_rotateCoeff]
  simp [div_eq_inv_mul]

open _root_.Polynomial in
/-- In the elementary symmetric chart, rotating the coefficients rotates the divisor: the zeros
of `P_(c^u) = u⁻ᵐ P_c(u ·)` are those of `P_c` multiplied by `u⁻¹`. -/
theorem coeffEquiv_symm_rotateCoeff (u : Circle) (c : Fin m → ℂ) :
    (Sym.coeffEquiv ℂ m).symm (rotateCoeff u c) =
      ((Sym.coeffEquiv ℂ m).symm c).map ((u : ℂ)⁻¹ * ·) := by
  apply Sym.coe_injective
  rw [Sym.coeffEquiv_symm_apply, Sym.coe_map, Sym.coeffEquiv_symm_apply,
    monicOfCoeff_rotateCoeff, roots_scaleRoots _ (Circle.coe_ne_zero u).isUnit.inv]

/-- **Rotation law of the polynomial gauge.** The gauge of the rotated polynomial
`u⁻ᵐ P_c(u z)` is the rotated gauge: `g_(c^u)(z) = g_c(u z)`. -/
theorem polynomialGauge_rotateCoeff (u : Circle) (c : Fin m → ℂ) (z : ℂ) :
    polynomialGauge (rotateCoeff u c) z = polynomialGauge c ((u : ℂ) * z) := by
  have hu : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  have harg : cutoffArg (rotateCoeff u c) z = cutoffArg c ((u : ℂ) * z) := by
    simp [cutoffArg, hu]
  have htail : tail (rotateCoeff u c) z = tail c ((u : ℂ) * z) := by
    rcases eq_or_ne z 0 with rfl | hz
    · rcases m with _ | m <;> simp [tail]
    have huz : (u : ℂ) * z ≠ 0 := mul_ne_zero (Circle.coe_ne_zero u) hz
    have h := eval_monicOfCoeff_rotateCoeff u c z
    rw [eval_monicOfCoeff_eq_mul_tail _ hz, eval_monicOfCoeff_eq_mul_tail c huz] at h
    have hum : (u : ℂ) ^ m ≠ 0 := pow_ne_zero m (Circle.coe_ne_zero u)
    rw [eq_div_iff hum] at h
    refine mul_left_cancel₀ (mul_ne_zero hum (pow_ne_zero m hz)) ?_
    linear_combination h
  simp only [polynomialGauge, polynomialPhase, harg, htail]

/-- **Rotation law of the gauged fields.** Rotating the plane intertwines the polynomial gauge
of `c` with that of the rotated coefficients: `R_u (g_c · x) = g_(c^u) · R_u x`. -/
theorem rotateField_gaugeTransform_polynomialGauge (u : Circle) (c : Fin m → ℂ)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateField u (gaugeTransform (polynomialGauge c) x) =
      gaugeTransform (polynomialGauge (rotateCoeff u c)) (rotateField u x) := by
  rw [rotateField_gaugeTransform]
  congr 1
  funext w
  exact (polynomialGauge_rotateCoeff u c w).symm

/-! ### Normalizing fields whose section is a multiple of `P_c` -/

/-- If the section of `x` at `z` is `ρ P_c(z)` with `ρ ≥ 0`, and `g_c(z)` turns the phase of
`P_c(z)` into the winding phase, then the section of `g_c · x` at `z` is its modulus times the
winding phase. -/
private theorem sectionValue_gaugeTransform_eq_of_mul_eval {c : Fin m → ℂ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsec : sectionValue x z = ρ * (monicOfCoeff c).eval z)
    (h : (polynomialGauge c z : ℂ) * (monicOfCoeff c).eval z =
      ‖(monicOfCoeff c).eval z‖ * windingPhase m z) :
    sectionValue (gaugeTransform (polynomialGauge c) x) z =
      ‖sectionValue (gaugeTransform (polynomialGauge c) x) z‖ * windingPhase m z := by
  rw [sectionValue_gaugeTransform, hsec, mul_left_comm, h]
  simp only [norm_mul, Circle.norm_coe, norm_real, Real.norm_of_nonneg hρ, ofReal_mul,
    ofReal_one, norm_norm]
  ring

/-- **The gauged section outside a disc.** If the section of `x` at `z` is a nonnegative multiple
`ρ P_c(z)` of the polynomial `P_c`, and `‖z‖² ≥ m ∑ᵢ ‖cᵢ‖² + 2`, then the section of the gauged
field `g_c · x` at `z` is its modulus times the winding phase. -/
theorem sectionValue_gaugeTransform_polynomialGauge {c : Fin m → ℂ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsec : sectionValue x z = ρ * (monicOfCoeff c).eval z)
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 ≤ ‖z‖ ^ 2) :
    sectionValue (gaugeTransform (polynomialGauge c) x) z =
      ‖sectionValue (gaugeTransform (polynomialGauge c) x) z‖ * windingPhase m z :=
  sectionValue_gaugeTransform_eq_of_mul_eval hρ hsec (polynomialGauge_mul_eval hz)

/-- **A common normalization radius over a bounded window.** For a bounded set `K` of coefficient
tuples there is one radius `R` such that, for every `c ∈ K`, every field `x` and every point `z`
with `‖z‖ ≥ R` at which the section of `x` is a nonnegative multiple of `P_c(z)`, the section of
`g_c · x` at `z` is its modulus times the winding phase. -/
theorem exists_forall_sectionValue_gaugeTransform_polynomialGauge {K : Set (Fin m → ℂ)}
    (hK : Bornology.IsBounded K) :
    ∃ R, ∀ c ∈ K, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) (ρ : ℝ), R ≤ ‖z‖ → 0 ≤ ρ →
      sectionValue x z = ρ * (monicOfCoeff c).eval z →
        sectionValue (gaugeTransform (polynomialGauge c) x) z =
          ‖sectionValue (gaugeTransform (polynomialGauge c) x) z‖ * windingPhase m z := by
  obtain ⟨R, hR⟩ := exists_forall_polynomialGauge_mul_eval hK
  exact ⟨R, fun c hc x z ρ hz hρ hsec ↦
    sectionValue_gaugeTransform_eq_of_mul_eval hρ hsec (hR c hc z hz)⟩

/-- A framed degree-`m` field whose section is a real multiple `ρ P_c` of the monic polynomial
`P_c` has `ρ ≥ 0` near infinity: there `P_c(z) (z / |z|)⁻ᵐ` is `|z|ᵐ` times a number of positive
real part, while the framed section tends to `1`. -/
private theorem eventually_nonneg_of_tendsto_sectionValue {c : Fin m → ℂ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {ρ : ℂ → ℝ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hsec : ∀ z, sectionValue x z = ρ z * (monicOfCoeff c).eval z) :
    ∀ᶠ z in cocompact ℂ, 0 ≤ ρ z := by
  have hre : Tendsto (fun z ↦ (sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹).re) (cocompact ℂ)
      (𝓝 1) := by
    simpa only [Function.comp_def, one_re] using (continuous_re.tendsto 1).comp hframe
  filter_upwards [tendsto_normSq_cocompact_atTop.eventually_ge_atTop (m * ∑ i, ‖c i‖ ^ 2 + 1),
    hre.eventually (lt_mem_nhds one_pos)] with z hz h1
  rw [normSq_eq_norm_sq] at hz
  obtain ⟨hz0, htail⟩ := ne_zero_and_norm_tail_lt_one (c := c) (z := z)
    (by unfold cutoffArg; linarith)
  have hnz : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)
  have hq : sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹ =
      ((ρ z * ‖z‖ ^ m : ℝ) : ℂ) * (1 + tail c z) := by
    have hzm : (‖z‖ : ℂ) ^ m ≠ 0 := pow_ne_zero m hnz
    rw [hsec, eval_monicOfCoeff_eq_mul_tail c hz0, div_pow, inv_div]
    push_cast
    field_simp
  rw [hq, re_ofReal_mul] at h1
  have hre1 : 0 < (1 + tail c z).re := by
    have := abs_re_le_norm (tail c z)
    rw [add_re, one_re]
    linarith [neg_abs_le (tail c z).re]
  exact (pos_of_mul_pos_left ((pos_iff_pos_of_mul_pos h1).2 hre1)
    (pow_nonneg (norm_nonneg z) m)).le

/-- **Normalized vortices in the affine Sobolev spaces.** Let `x` be a smooth framed degree-`m`
vortex whose section is a real multiple of the monic polynomial `P_c`, for instance the
reconstructed field `amplitudeField u P_c` of Taubes's existence proof. Then the polynomial gauge
carries `x` to a field `g_c · x` lying in the affine Sobolev space `A_m^s` for every real `s`, and
every derivative of `g_c · x - x_ref` is `O(exp (-c' |z|))` at infinity for every `c' < 1 / 2`. -/
theorem gaugeTransform_polynomialGauge_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    {c : Fin m → ℂ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {ρ : ℂ → ℝ} (hsec : ∀ z, sectionValue x z = ρ z * (monicOfCoeff c).eval z) :
    (∀ s : ℝ, gaugeTransform (polynomialGauge c) x ∈ framedFieldSpace f m s) ∧
      ∀ c' < 1 / 2, ∀ n : ℕ,
        iteratedFDeriv ℝ n (gaugeTransform (polynomialGauge c) x - referenceField f m)
          =O[cocompact ℂ] fun z ↦ Real.exp (-(c' * ‖z‖)) := by
  refine gaugeTransform_mem_framedFieldSpace_of_eventually_sectionValue_eq f
    (polynomialGauge_mem_framedGaugeGroup c) hx hsol hframe ?_
  filter_upwards [tendsto_normSq_cocompact_atTop.eventually_ge_atTop (m * ∑ i, ‖c i‖ ^ 2 + 2),
    eventually_nonneg_of_tendsto_sectionValue hframe hsec] with z hz hρ
  exact sectionValue_gaugeTransform_polynomialGauge hρ (hsec z) (normSq_eq_norm_sq z ▸ hz)

end TauCeti.Vortex
