/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Complex.UpperLogContinuity
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Contour.ArcFTC
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Log
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Fundamental theorem of calculus for a logarithmic-derivative integrand

For a function `f : ℝ → ℂ` continuous on `[a, b]`, differentiable off a countable set `P`, and
staying in `Complex.slitPlane` on `[a, b]`, the principal `Complex.log ∘ f` is a single-valued
antiderivative of the logarithmic-derivative integrand `f' t / f t`, so

`∫ t in a..b, f' t / f t = Complex.log (f b) - Complex.log (f a)`.

Specializing to `f t = (γ t - w) / (γ a - w)` for a curve `γ` avoiding `w` gives the contour form
used downstream, `∫ t in a..b, γ' t / (γ t - w) = Complex.log ((γ b - w) / (γ a - w))`, where the
normalization by `γ a - w` is what keeps the ratio in the slit plane and makes the value at the
basepoint `a` equal to `Complex.log 1 = 0`. The exceptional set `P` accommodates the finitely many
breakpoints of a piecewise-`C¹` contour, and the oriented interval `[a, b]` needs no `a ≤ b`
assumption.

The same principle holds along a curve. For an absolutely continuous curve `γ` and a function `h`
that is analytic along it with values in `Complex.slitPlane`, `Complex.log ∘ h` is a single-valued
primitive of `logDeriv h` near the curve, so the argument-principle integral
`∫ t in a..b, deriv γ t • logDeriv h (γ t)` vanishes when `γ` is closed. This is the counterpart
along a curve of `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`, which is stated for
circles. It rests on the fundamental theorem of calculus along an absolutely continuous contour
(`AbsolutelyContinuousOnInterval.integral_deriv_smul_deriv_comp_eq_zero_of_closed`), not on the
countable exceptional set above.

That same integrand is what the winding number of the *image* curve computes: if `h` is analytic
and zero-free along `γ`, then `h ∘ γ` misses the origin and its index integral
`(2πi)⁻¹ ∮_{h ∘ γ} dw / w` is, after the substitution `w = h z`, exactly
`(2πi)⁻¹ ∫_a^b γ' • (logDeriv h ∘ γ)`. Formally the substitution is the chain rule
`(h ∘ γ)' = γ' · h'(γ)`, available wherever `γ` is differentiable and so almost everywhere, which
is all an integral sees. This bridge is what turns every logarithmic-derivative integral identity —
the argument principle above all — into a statement about how often an image curve winds.

## Main results

* `TauCeti.Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg`
  and `intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_neg_sub_log_neg_of_im_nonpos` —
  the boundary-tolerant comparison FTCs: the logarithmic integral of `g` is integrable and
  evaluates to an endpoint-log difference through a comparison `h` that is continuous on the
  closed interval, differentiable on the open one off a countable set, has integrable logarithmic
  integrand, is confined to a closed half-plane, is nonvanishing at the two endpoints and
  slit-plane-valued strictly between them, and agrees with `g` both on the open interval and at
  each endpoint — so endpoint values may sit on the negative-real boundary.
* `intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane` (in
  `TauCeti.Contour`, unqualified here only to stay inside the line limit)
  — the third member of that family, for a comparison confined to the slit plane on the whole
  closed interval rather than held off the cut by a half-plane condition. Its conclusion could be
  reached inline from `integral_deriv_div_eq_log_sub_log` plus `IntervalIntegrable.congr_uIoo` and
  `intervalIntegral.integral_congr_uIoo`, but that transport is performed at nine call sites
  across the winding developments, so it is factored here.
* the `_of_le` forms of the slit-plane and upper comparisons — the ordered-interval versions
  callers usually have: `a ≤ b`, hypotheses read on `Set.Icc a b` and `Set.Ioo a b` rather than
  through `min` and `max`, and integrability derived from a continuous derivative.
* `TauCeti.Contour.integral_index_eq_log_sub_log` — the winding-integral integrand
  `(γ t - s)⁻¹ * deriv γ t` of a curve agreeing with a slit-plane comparison curve integrates to a
  difference of principal logarithms.
* `TauCeti.Contour.integral_deriv_div_eq_log_sub_log` — the slit-plane logarithmic-derivative FTC in
  general `f' / f` form.
* `AbsolutelyContinuousOnInterval.integral_inv_sub_mul_deriv_eq_log` — the contour form along an
  absolutely continuous slit-plane arc, with the winding integrand `(γ t - w)⁻¹ * deriv γ t`: the
  per-segment step for evaluating the winding-number integral as a sum of `Complex.log` argument
  increments.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_smul_logDeriv` — interval-integrability
  of the argument-principle integrand `deriv γ • (logDeriv h ∘ γ)` along an absolutely continuous
  curve on which `h` is analytic and zero-free.
* `AbsolutelyContinuousOnInterval.integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane` — that
  integral vanishes along a closed absolutely continuous curve on which `h` is analytic and
  slit-plane-valued.
* `AbsolutelyContinuousOnInterval.windingNumber_comp_eq_integral_logDeriv` — the bridge to the
  image curve: for `h` analytic and zero-free along an absolutely continuous curve `γ`, the winding
  number of `h ∘ γ` about the origin is `(2πi)⁻¹ ∫_a^b γ' • (logDeriv h ∘ γ)`.

## Provenance

Adapted from `segment_log_FTC` in `WindingInteger.lean` of the AINTLIB `LeanModularForms`
development, split from the argument-lift PR (#759) as an independent contour prerequisite.
The boundary-tolerant comparison forms port the corner FTC pieces of AINTLIB's
valence-formula winding-weight development
(`ForMathlib/ValenceFormula/WindingWeights/I.lean`, `Rho.lean`, `RhoPlusOne.lean`)
onto the current Mathlib pin.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **Logarithmic-derivative FTC on the slit plane.** For `f` continuous on `[a, b]`, differentiable
off a countable set `P`, taking values in `Complex.slitPlane` throughout `[a, b]`, and with `f' / f`
interval-integrable, the integral of `f' t / f t` over `a..b` telescopes through the single-valued
branch `Complex.log ∘ f`:
`∫ t in a..b, f' t / f t = Complex.log (f b) - Complex.log (f a)`. -/
theorem integral_deriv_div_eq_log_sub_log {f f' : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hP : P.Countable) (hf_cont : ContinuousOn f (uIcc a b))
    (hf_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, HasDerivAt f (f' t) t)
    (h_slit : ∀ t ∈ uIcc a b, f t ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ f' t / f t) volume a b) :
    ∫ t in a..b, f' t / f t = Complex.log (f b) - Complex.log (f a) :=
  integral_eq_of_hasDerivAt_off_countable (fun t ↦ Complex.log (f t)) (fun t ↦ f' t / f t) hP
    (hf_cont.clog h_slit)
    (fun t ht ↦ (hf_diff t ht).clog_real (h_slit t (Ioo_subset_Icc_self ht.1))) h_int

/-- **FTC for the winding integrand on a slit-plane arc.** For an absolutely continuous curve `γ`
on the oriented interval with endpoints `a`, `b` whose normalized ratio `(γ t - w) / (γ a - w)`
stays in `Complex.slitPlane` throughout `[[a, b]]`, the winding integrand
`(γ t - w)⁻¹ * deriv γ t` integrates to the principal logarithm of the endpoint ratio,
`Complex.log ((γ b - w) / (γ a - w))`. This is the per-segment step for evaluating the winding
number integral as a sum of `Complex.log` argument increments. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_inv_sub_mul_deriv_eq_log
    {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (h_slit : ∀ t ∈ uIcc a b, (γ t - w) / (γ a - w) ∈ slitPlane) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t = Complex.log ((γ b - w) / (γ a - w)) := by
  have hc : γ a - w ≠ 0 := fun h0 ↦
    zero_notMem_slitPlane (by simpa [h0] using h_slit a left_mem_uIcc)
  have hconst (c : ℂ) : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  -- The curve `γ - w` against the constant curve `γ a - w`, whose logarithmic derivative is `0`.
  have h := (hγ.fun_sub (hconst w)).integral_deriv_div_sub_integral_deriv_div_eq_log_div_sub_log_div
    (hconst (γ a - w)) h_slit
  rw [div_self hc, Complex.log_one, sub_zero] at h
  simpa only [deriv_sub_const, deriv_const, zero_div, intervalIntegral.integral_zero, sub_zero,
    div_eq_inv_mul, mul_zero] using h

/-- The argument-principle integrand `deriv γ • (logDeriv h ∘ γ)` is interval-integrable along an
absolutely continuous curve `γ` on which `h` is analytic and zero-free. This supplies the
integrability hypothesis of the logarithmic-derivative contour results. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_smul_logDeriv
    {γ : ℝ → ℂ} {h : ℂ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t)) (hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0) :
    IntervalIntegrable (fun t ↦ deriv γ t • logDeriv h (γ t)) volume a b :=
  hγ.intervalIntegrable_deriv_of_finiteDimensional.smul_continuousOn fun t ht ↦
    ((hh t ht).logDeriv (hne t ht)).continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)

/-- **A slit-plane-valued function has a single-valued logarithm along a closed curve.** If `h` is
analytic along a closed absolutely continuous curve `γ` and takes its values there in
`Complex.slitPlane`, then the contour integral of `logDeriv h` along `γ` vanishes.

This is the counterpart along a curve of `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`,
which is stated for circles. Nothing is required of `h` off the curve — in the Rouché application
`h = g / f` has both zeros and poles inside. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane
    {γ : ℝ → ℂ} {h : ℂ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t))
    (hslit : ∀ t ∈ uIcc a b, h (γ t) ∈ slitPlane) :
    ∫ t in a..b, deriv γ t • logDeriv h (γ t) = 0 := by
  -- `Complex.log ∘ h` is a primitive of `logDeriv h` on the open set where `h` is analytic and
  -- slit-plane-valued, which contains the curve.
  have hU : IsOpen ({z | AnalyticAt ℂ h z} ∩ h ⁻¹' slitPlane) :=
    (AnalyticOnNhd.continuousOn fun _ hz ↦ hz).isOpen_inter_preimage (isOpen_analyticAt ℂ h)
      isOpen_slitPlane
  have hG : ∀ z ∈ {z | AnalyticAt ℂ h z} ∩ h ⁻¹' slitPlane,
      HasDerivAt (fun z ↦ Complex.log (h z)) (logDeriv h z) z := fun z hz ↦ by
    simpa [logDeriv_apply] using hz.1.differentiableAt.hasDerivAt.clog hz.2
  rw [← hγ.integral_deriv_smul_deriv_comp_eq_zero_of_closed hU
    (fun z hz ↦ (hG z hz).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ ⟨hh t ht, hslit t ht⟩) hclosed]
  exact integral_congr fun t ht ↦ by rw [(hG (γ t) ⟨hh t ht, hslit t ht⟩).deriv]

/-- **The winding number of the image curve is the logarithmic-derivative integral.** If `h` is
analytic and zero-free along an absolutely continuous curve `γ`, the composite `h ∘ γ` avoids the
origin and

`n_0(h ∘ γ) = (2πi)⁻¹ ∫_a^b γ' t · (logDeriv h) (γ t)`.

This is the substitution `w = h z` in the index integral `(2πi)⁻¹ ∮_{h ∘ γ} dw / w`.

The analyticity hypothesis is local: `AnalyticAt ℂ h (γ t)` asks only for *some* neighbourhood of
each point of the curve on which `h` is analytic, never for one ambient open set carrying the whole
curve, and imposes no condition beyond those neighbourhoods. So the lemma applies verbatim to a
function with zeros and poles inside the region the curve encloses; that is what the argument
principle then counts. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_comp_eq_integral_logDeriv
    {γ : ℝ → ℂ} {h : ℂ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t)) (hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0) :
    windingNumber (h ∘ γ) a b 0
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, deriv γ t • logDeriv h (γ t) := by
  have hcont : ContinuousOn (h ∘ γ) (uIcc a b) := fun t ht =>
    (hh t ht).continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)
  -- The chain rule identifies the two integrands wherever `γ` is differentiable, so almost
  -- everywhere.
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      deriv γ t • logDeriv h (γ t) = ((h ∘ γ) t - 0)⁻¹ * deriv (h ∘ γ) t := by
    filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
    have htu := uIoc_subset_uIcc hmem
    have hd := ((hh t htu).differentiableAt.hasDerivAt.scomp t (ht htu).hasDerivAt).deriv
    simp only [Function.comp_apply, sub_zero, logDeriv_apply, smul_eq_mul, hd]
    ring
  have hint := hγ.intervalIntegrable_deriv_smul_logDeriv hh hne
  rw [windingNumber_eq_integral_of_avoidance hcont
      (fun t ht => hne t ht) (hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae))]
  exact congrArg _ (intervalIntegral.integral_congr_ae hae).symm

section BoundaryTolerant

open MeasureTheory

variable {g h : ℝ → ℂ} {a b : ℝ}

/-- Interior agreement transports the logarithmic integrand to the open interval. -/
private lemma eqOn_uIoo_deriv_div (heq : Set.EqOn g h (Set.Ioo (min a b) (max a b))) :
    Set.EqOn (fun t ↦ deriv g t / g t) (fun t ↦ deriv h t / h t) (Set.uIoo a b) := by
  intro t ht
  rw [← Set.Ioo_min_max] at ht
  simp only [heq ht, heq.deriv isOpen_Ioo ht]

/-- The shared comparison core: once the branch `Complex.log ∘ h` of the comparison function
is continuous up to the endpoints and differentiates to the logarithmic integrand off a
countable set, the logarithmic FTC transports to `g` across the interior agreement. -/
private lemma comparison_core {P : Set ℝ} (hP : P.Countable)
    (hlog_cont : ContinuousOn (fun t ↦ Complex.log (h t)) (Set.uIcc a b))
    (hlog_diff : ∀ t ∈ Set.Ioo (min a b) (max a b) \ P,
      HasDerivAt (fun t ↦ Complex.log (h t)) (deriv h t / h t) t)
    (hh_int : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b)
    (heq : Set.EqOn g h (Set.Ioo (min a b) (max a b)))
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  refine ⟨hh_int.congr_uIoo fun t ht ↦ (eqOn_uIoo_deriv_div heq ht).symm, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t :=
        intervalIntegral.integral_congr_uIoo (eqOn_uIoo_deriv_div heq)
    _ = Complex.log (h b) - Complex.log (h a) :=
        integral_eq_of_hasDerivAt_off_countable _ _ hP hlog_cont hlog_diff hh_int
    _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]

/-- Endpoint nonvanishing and interior slit-plane confinement keep the comparison function
zero-free on the whole closed interval. -/
private lemma ne_zero_on_uIcc (ha_ne : h a ≠ 0) (hb_ne : h b ≠ 0)
    (hh_slit : ∀ t ∈ Set.Ioo (min a b) (max a b), h t ∈ Complex.slitPlane) :
    ∀ t ∈ Set.uIcc a b, h t ≠ 0 := by
  intro t ht
  rw [← Set.Icc_min_max] at ht
  rcases eq_or_lt_of_le ht.1 with heq1 | hlt1
  · rcases min_choice a b with hm | hm <;> rw [← heq1, hm]
    exacts [ha_ne, hb_ne]
  rcases eq_or_lt_of_le ht.2 with heq2 | hlt2
  · rcases max_choice a b with hm | hm <;> rw [heq2, hm]
    exacts [ha_ne, hb_ne]
  exact Complex.slitPlane_ne_zero (hh_slit t ⟨hlt1, hlt2⟩)

/-- **The boundary-tolerant logarithmic FTC, upper form**: for a comparison function `h`
continuous on the closed interval, confined to the closed upper half-plane, nonvanishing at the
endpoints, slit-plane-valued strictly between them, differentiable there off a countable set, and
with integrable logarithmic integrand, and for a `g` agreeing with `h` on the open interval and
at both endpoints, the logarithmic integral of `g` is integrable and evaluates to the difference
of its endpoint logarithms — even when the endpoint values sit on the slit-plane boundary.

The conclusion is about `g`, which is otherwise unconstrained: it is the agreement with `h`, at
the endpoints as well as inside, that carries the regularity across. -/
theorem intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg {P : Set ℝ}
    (hP : P.Countable) (hh_cont : ContinuousOn h (Set.uIcc a b))
    (hh_diff : ∀ t ∈ Set.Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ h t)
    (hh_int : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b)
    (hh_im_nn : ∀ t ∈ Set.uIcc a b, 0 ≤ (h t).im)
    (ha_ne : h a ≠ 0) (hb_ne : h b ≠ 0)
    (hh_slit : ∀ t ∈ Set.Ioo (min a b) (max a b), h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Set.Ioo (min a b) (max a b)))
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  comparison_core hP
    (TauCeti.continuousOn_log_im_nonneg_ne_zero.comp hh_cont fun t ht ↦
      ⟨hh_im_nn t ht, ne_zero_on_uIcc ha_ne hb_ne hh_slit t ht⟩)
    (fun t ht ↦ (hh_diff t ht).hasDerivAt.clog_real (hh_slit t ht.1))
    hh_int heq heq_a heq_b

/-- **The boundary-tolerant logarithmic FTC, lower form**: for a comparison function `h`
continuous on the closed interval, differentiable on the open one off a countable set, with
integrable logarithmic integrand, confined to the closed lower half-plane, nonvanishing at the
endpoints and whose negation is slit-plane-valued strictly between them, and for a `g` agreeing
with `h` on the open interval and at both endpoints, the logarithmic integral of `g` is
integrable and evaluates to the difference of the endpoint logarithms of the negations. -/
theorem intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_neg_sub_log_neg_of_im_nonpos
    {P : Set ℝ} (hP : P.Countable) (hh_cont : ContinuousOn h (Set.uIcc a b))
    (hh_diff : ∀ t ∈ Set.Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ h t)
    (hh_int : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b)
    (hh_im_np : ∀ t ∈ Set.uIcc a b, (h t).im ≤ 0)
    (ha_ne : h a ≠ 0) (hb_ne : h b ≠ 0)
    (hh_slit_neg : ∀ t ∈ Set.Ioo (min a b) (max a b), -(h t) ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Set.Ioo (min a b) (max a b)))
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (-(g b)) - Complex.log (-(g a)) := by
  have hderiv_neg : ∀ k : ℝ → ℂ, (fun t ↦ deriv (-k) t / (-k) t) = fun t ↦ deriv k t / k t :=
    fun k ↦ funext fun t ↦ by rw [deriv.neg, Pi.neg_apply, neg_div_neg_eq]
  have hkey := intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg
    (g := -g) (h := -h) hP hh_cont.neg (fun t ht ↦ (hh_diff t ht).neg)
    (by rw [hderiv_neg h]; exact hh_int)
    (fun t ht ↦ by simpa using hh_im_np t ht)
    (neg_ne_zero.mpr ha_ne) (neg_ne_zero.mpr hb_ne)
    (fun t ht ↦ by simpa using hh_slit_neg t ht)
    (fun t ht ↦ by simp only [Pi.neg_apply, heq ht])
    (by simp only [Pi.neg_apply, heq_a]) (by simp only [Pi.neg_apply, heq_b])
  rwa [hderiv_neg g] at hkey

/-- **The comparison logarithmic FTC on the slit plane**: for a comparison function `h` that
stays in the slit plane on the whole oriented closed interval — endpoints included — is
continuous there, is differentiable strictly inside off a countable exceptional set `P`, and
has interval-integrable logarithmic derivative, and for a `g` agreeing with `h` on the open
interval and at both endpoints, the logarithmic integral of `g` is integrable and evaluates
to the difference of its endpoint logarithms.

Integrability of `deriv h / h` is assumed rather than derived: callers that have a continuous
derivative and nonvanishing `h` get it from `ContinuousOn.div` plus
`ContinuousOn.intervalIntegrable`.

This is the sibling of the two half-plane forms above: there the comparison may touch the
branch cut at an endpoint and is held off it by a half-plane condition, whereas here it is
slit-plane-valued throughout and no half-plane hypothesis is needed. -/
theorem intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane
    {P : Set ℝ} (hP : P.Countable) (hh_cont : ContinuousOn h (Set.uIcc a b))
    (hh_diff : ∀ t ∈ Set.Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ h t)
    (hh_int : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b)
    (hh_slit : ∀ t ∈ Set.uIcc a b, h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Set.Ioo (min a b) (max a b)))
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  comparison_core hP (hh_cont.clog fun t ht ↦ hh_slit t ht)
    (fun t ht ↦ (hh_diff t ht).hasDerivAt.clog_real
      (hh_slit t (Set.Ioo_subset_Icc_self ht.1)))
    hh_int heq heq_a heq_b

/-- **The comparison logarithmic FTC on the slit plane, ordered-interval form.** The form
callers actually have to hand: an oriented interval `a ≤ b`, a comparison function `h`
continuous with continuous derivative on `Icc a b`, slit-plane-valued there and
differentiable strictly inside, and a `g` agreeing with `h` on `Ioo a b` and at both
endpoints.

Integrability of `deriv h / h` is derived rather than assumed — slit-plane confinement
already forces `h` to be nonvanishing — and the interval hypotheses read on `Set.Icc a b`
and `Set.Ioo a b` instead of through `min` and `max`. Everything else is
`intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane`, which
remains the general statement to reach for when the interval is unoriented, the
exceptional set is nonempty, or integrability comes from somewhere other than a continuous
derivative. -/
theorem intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
    (hab : a ≤ b) (hh_cont : ContinuousOn h (Set.Icc a b))
    (hh_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Set.Icc a b))
    (hh_slit : ∀ t ∈ Set.Icc a b, h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Set.Ioo a b)) (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hu : Set.uIcc a b = Set.Icc a b := uIcc_of_le hab
  have ho : Set.Ioo (min a b) (max a b) = Set.Ioo a b := by
    rw [min_eq_left hab, max_eq_right hab]
  have hne : ∀ t ∈ Set.Icc a b, h t ≠ 0 := fun t ht ↦ Complex.slitPlane_ne_zero (hh_slit t ht)
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane
    countable_empty (hu ▸ hh_cont) (fun t ht ↦ hh_diff t (ho ▸ ht.1))
    ((hh_deriv_cont.div hh_cont hne).mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
    (fun t ht ↦ hh_slit t (hu ▸ ht)) (fun t ht ↦ heq (ho ▸ ht)) heq_a heq_b

/-- **The boundary-tolerant logarithmic FTC on an ordered interval, upper form.** The form
callers usually have: an oriented interval `a ≤ b`, a comparison function `h` continuous with
continuous derivative and nonvanishing on `Icc a b`, confined to the closed upper half-plane
there and slit-plane-valued strictly inside, and a `g` agreeing with `h` on `Ioo a b` and at
both endpoints.

Integrability of `deriv h / h` is derived from the continuous derivative and the
nonvanishing rather than assumed, and the interval hypotheses read on `Set.Icc a b` and
`Set.Ioo a b` instead of through `min` and `max`. Everything else is
`intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg`, which
stays the statement to reach for on an unoriented interval or a nonempty exceptional set. -/
theorem intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg_of_le
    (hab : a ≤ b) (hh_cont : ContinuousOn h (Set.Icc a b))
    (hh_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Set.Icc a b))
    (hh_ne : ∀ t ∈ Set.Icc a b, h t ≠ 0)
    (hh_im_nn : ∀ t ∈ Set.Icc a b, 0 ≤ (h t).im)
    (hh_slit : ∀ t ∈ Set.Ioo a b, h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Set.Ioo a b)) (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hu : Set.uIcc a b = Set.Icc a b := uIcc_of_le hab
  have ho : Set.Ioo (min a b) (max a b) = Set.Ioo a b := by
    rw [min_eq_left hab, max_eq_right hab]
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg
    countable_empty (hu ▸ hh_cont) (fun t ht ↦ hh_diff t (ho ▸ ht.1))
    ((hh_deriv_cont.div hh_cont hh_ne).mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
    (fun t ht ↦ hh_im_nn t (hu ▸ ht))
    (hh_ne a (left_mem_Icc.mpr hab)) (hh_ne b (right_mem_Icc.mpr hab))
    (fun t ht ↦ hh_slit t (ho ▸ ht)) (fun t ht ↦ heq (ho ▸ ht)) heq_a heq_b

end BoundaryTolerant

/-- **Slit-plane evaluation of an index integral.** If `γ` agrees on the open interval and at both
endpoints with a comparison curve `h` whose difference `h · - s` stays in `Complex.slitPlane`, the
index integral of `γ` about `s` telescopes through the principal branch of the logarithm.

The comparison shape is what makes this usable at a corner: a piecewise curve need not be
differentiable at a junction, but it may agree with a smooth piece on each side of it. -/
theorem integral_index_eq_log_sub_log {γ h : ℝ → ℂ} {a b : ℝ} {s : ℂ} (hab : a ≤ b)
    (hcont : ContinuousOn h (Icc a b)) (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hderiv : ContinuousOn (deriv h) (Icc a b))
    (hslit : ∀ t ∈ Icc a b, h t - s ∈ slitPlane)
    (heq : EqOn γ h (Ioo a b)) (ha : γ a = h a) (hb : γ b = h b) :
    (∫ t in a..b, (γ t - s)⁻¹ * deriv γ t)
      = Complex.log (γ b - s) - Complex.log (γ a - s) := by
  have hd : (deriv fun t => h t - s) = deriv h := funext fun t => deriv_sub_const s
  have hkey :=
    intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
      (g := fun t => γ t - s) (h := fun t => h t - s) hab (hcont.sub continuousOn_const)
      (fun t ht => (hdiff t ht).sub_const s) (by rw [hd]; exact hderiv) hslit
      (fun t ht => by simp only [heq ht]) (by simp only [ha]) (by simp only [hb])
  simpa only [deriv_sub_const, div_eq_inv_mul] using hkey.2

end TauCeti.Contour
