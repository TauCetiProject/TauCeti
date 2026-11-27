/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integrability of real powers: `Lᵖ` near the origin, shifted powers, `|x| ^ p` and `|sin x| ^ p`

On an interval `(0, c)`, the power `t ↦ t ^ s` is in `Lᵖ` for a finite exponent `p` exactly when
`-1 < s p` (`TauCeti.memLp_rpow_restrict_Ioo_iff`), the `Lᵖ` form of Mathlib's
`intervalIntegral.integrableOn_Ioo_rpow_iff`; so `t ↦ t ^ (-a)` is in `Lᵖ` when `a p < 1`
(`TauCeti.memLp_rpow_neg_restrict_Ioo`). For `a = 1 / 2` this shows that the derivative
`(2 √t)⁻¹` of `t ↦ √t` is in `Lᵖ(0, c)` for `p < 2`. More generally, the `i`-th derivative of
`t ↦ t ^ s` is `s (s - 1) ⋯ (s - i + 1) t ^ (s - i)`, so it is in `Lᵖ(0, c)` exactly when this
coefficient vanishes or `-1 < (s - i) p`
(`TauCeti.memLp_iteratedFDeriv_rpow_const_restrict_Ioo_iff`). Translating `(0, b - a)` to
`(a, b)` also gives the shifted integrability criterion
`TauCeti.integrableOn_Ioo_sub_rpow_iff`: for `a < b`, `t ↦ (t - a) ^ s` is integrable on `(a, b)`
if and only if `-1 < s`. On an upper ray `(a, ∞)`,
`a > 0`, a power `t ^ p` with `p < -1` stays integrable after multiplication by the fractional part
`{t} ∈ [0, 1)` (`TauCeti.integrableOn_rpow_mul_fract`).

At infinity, the inverse natural power `t ↦ t⁻¹ ^ k` is integrable on `(c, ∞)` for `0 < c` and
`2 ≤ k` (`TauCeti.integrableOn_Ioi_inv_pow`), the natural-power form of Mathlib's
`integrableOn_Ioi_rpow_of_lt`.

On bounded intervals, the even power `x ↦ |x| ^ p` is interval integrable for every `p > -1`
(`TauCeti.intervalIntegrable_abs_rpow`), the two-sided form of Mathlib's
`intervalIntegral.intervalIntegrable_rpow'`. So is `x ↦ |sin x| ^ p`
(`TauCeti.intervalIntegrable_abs_sin_rpow`), whose singularities at the zeros `kπ` of the sine
are of this type by Jordan's inequality. For `p ≤ 0`, the latter dominates, up to a constant
factor, the powers `|z - w| ^ p` of the distance from a point `z` running along a circle about `c`
to a fixed point `w` (`TauCeti.norm_circleMap_sub_rpow_le`).
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti

/-- On `(0, c)`, the power `t ↦ t ^ s` is in `Lᵖ` for a finite exponent `p` if and only if
`-1 < s p`. For `p = 0` both sides hold. -/
theorem memLp_rpow_restrict_Ioo_iff {s c : ℝ} {p : ENNReal} (hc : 0 < c) (hp : p ≠ ⊤) :
    MemLp (fun t : ℝ => t ^ s) p (volume.restrict (Ioo 0 c)) ↔ -1 < s * p.toReal := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ s) (volume.restrict (Ioo 0 c)) :=
    (by fun_prop : Measurable fun t : ℝ => t ^ s).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using memLp_zero_iff_aestronglyMeasurable.2 hmeas
  rw [← integrable_norm_rpow_iff hmeas hp0 hp, ← intervalIntegral.integrableOn_Ioo_rpow_iff hc]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioo
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _), ← Real.rpow_mul ht.1.le]

/-- On `(0, b)`, the `i`-th derivative `s (s - 1) ⋯ (s - i + 1) x ^ (s - i)` of `x ^ s` lies in
`Lᵖ` for a finite exponent `p` exactly when its coefficient vanishes or `-1 < (s - i) p`. -/
theorem memLp_iteratedFDeriv_rpow_const_restrict_Ioo_iff {s b : ℝ} {p : ENNReal} (hb : 0 < b)
    (hp : p ≠ ⊤) (i : ℕ) :
    MemLp (iteratedFDeriv ℝ i fun x : ℝ => x ^ s) p (volume.restrict (Ioo 0 b)) ↔
      (descPochhammer ℝ i).eval s = 0 ∨ -1 < (s - i) * p.toReal := by
  set c := (descPochhammer ℝ i).eval s
  have hsmooth : ContDiffOn ℝ i (fun x : ℝ => x ^ s) (Ioo 0 b) := fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne hx.1.ne').contDiffWithinAt
  -- The `i`-th derivative has the norm of `c x ^ (s - i)` (`Real.iter_deriv_rpow_const`).
  rw [memLp_congr_norm (g := fun x : ℝ => c * x ^ (s - i))
    ((ContinuousOn.continuousOn_iteratedFDeriv hsmooth isOpen_Ioo le_rfl).aestronglyMeasurable
      measurableSet_Ioo)
    ((by fun_prop : Measurable fun x : ℝ => c * x ^ (s - i)).aestronglyMeasurable)
    (.of_forall fun x => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_rpow_const])]
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  · rw [← memLp_rpow_restrict_Ioo_iff hb hp]
    simp only [hc, false_or]
    exact ⟨fun h => by simpa [hc] using h.const_mul c⁻¹, fun h => h.const_mul c⟩

/-- On `(0, c)`, the power `t ↦ t ^ (-a)` is in `Lᵖ` for every finite exponent `p` with
`a p < 1`. -/
theorem memLp_rpow_neg_restrict_Ioo {a c : ℝ} {p : ENNReal} (hc : 0 < c) (hp : p ≠ ⊤)
    (hap : a * p.toReal < 1) : MemLp (fun t : ℝ => t ^ (-a)) p (volume.restrict (Ioo 0 c)) :=
  (memLp_rpow_restrict_Ioo_iff hc hp).2 (by linarith [neg_mul a p.toReal])

/-- On `(a, b)` with `a < b`, the shifted power `t ↦ (t - a) ^ s` is integrable if and only if
`-1 < s`. -/
theorem integrableOn_Ioo_sub_rpow_iff {a b s : ℝ} (hab : a < b) :
    IntegrableOn (fun t : ℝ ↦ (t - a) ^ s) (Ioo a b) ↔ -1 < s := by
  have heq : (fun x : ℝ ↦ x + a) '' Ioo 0 (b - a) = Ioo a b := by
    rw [image_add_const_Ioo, zero_add, sub_add_cancel]
  rw [← heq, (measurePreserving_add_right volume a).integrableOn_image
    (measurableEmbedding_addRight a)]
  simpa [Function.comp_def, add_sub_cancel_right] using
    intervalIntegral.integrableOn_Ioo_rpow_iff (sub_pos.mpr hab)

/-- On `(c, ∞)` with `0 < c`, the inverse power `t ↦ t⁻¹ ^ k` is integrable for `2 ≤ k`. -/
theorem integrableOn_Ioi_inv_pow {k : ℕ} {c : ℝ} (hk : 2 ≤ k) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t⁻¹ ^ k) (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -(k : ℝ)) ?_ hc).congr_fun (fun t ht => ?_)
    measurableSet_Ioi
  · have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  · simp only [Real.rpow_neg (hc.trans ht).le, Real.rpow_natCast, inv_pow]

/-- The fractional part `{t} ∈ [0, 1)` weighted by `t^p` is integrable on `(a, ∞)` for `a > 0`
and `p < -1`. -/
theorem integrableOn_rpow_mul_fract {p a : ℝ} (hp : p < -1) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ t ^ p * Int.fract t) (Ioi a) :=
  (integrableOn_Ioi_rpow_of_lt hp ha).mul_bdd measurable_fract.aestronglyMeasurable
    (ae_of_all _ fun t ↦ by
      rw [Real.norm_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le)

/-- For `p > -1`, the power `x ↦ |x| ^ p` is interval integrable on every bounded interval. -/
theorem intervalIntegrable_abs_rpow {p : ℝ} (hp : -1 < p) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ |x| ^ p) volume a b := by
  -- On `[0, c]` the function is `x ↦ x ^ p` away from `0`; it is even, so `[c, 0]` follows.
  have hpos (c : ℝ) (hc : 0 ≤ c) : IntervalIntegrable (fun x : ℝ ↦ |x| ^ p) volume 0 c :=
    (intervalIntegral.intervalIntegrable_rpow' hp).congr fun x hx ↦ by
      rw [uIoc_of_le hc] at hx
      simp only [abs_of_pos hx.1]
  have h (c : ℝ) : IntervalIntegrable (fun x : ℝ ↦ |x| ^ p) volume 0 c := by
    rcases le_total 0 c with hc | hc
    · exact hpos c hc
    · rw [IntervalIntegrable.iff_comp_neg]
      simpa only [abs_neg, neg_zero] using hpos (-c) (neg_nonneg.2 hc)
  exact (h a).symm.trans (h b)

/-- For `p > -1`, the power `x ↦ |sin x| ^ p` is interval integrable on every bounded interval,
although it is unbounded near the zeros of the sine when `p < 0`. -/
theorem intervalIntegrable_abs_sin_rpow {p : ℝ} (hp : -1 < p) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ |Real.sin x| ^ p) volume a b := by
  rcases le_or_gt 0 p with hp0 | hp0
  · exact (Real.continuous_sin.abs.rpow_const fun _ ↦ Or.inr hp0).intervalIntegrable a b
  -- The function has period `π`; on `[-π/2, π/2]` Jordan's inequality `|sin x| ≥ 2|x|/π`
  -- dominates it by a multiple of `|x| ^ p`.
  have hper : Function.Periodic (fun x : ℝ ↦ |Real.sin x| ^ p) π := fun x ↦ by
    simp only [Real.sin_add_pi, abs_neg]
  refine hper.intervalIntegrable Real.pi_ne_zero (t := -(π / 2)) ?_ a b
  have hle : -(π / 2) ≤ -(π / 2) + π := by linarith [Real.pi_pos]
  refine (((intervalIntegrable_abs_rpow hp _ _).const_mul ((2 / π) ^ p))).mono_fun'
    ((by fun_prop : Measurable fun x : ℝ ↦ |Real.sin x| ^ p).aestronglyMeasurable) ?_
  rw [uIoc_of_le hle]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with x hx hx0
  have hxπ : |x| ≤ π / 2 := abs_le.2 ⟨hx.1.le, by linarith [hx.2]⟩
  have hpos : 0 < 2 / π * |x| := by positivity
  rw [Real.norm_of_nonneg (by positivity), ← Real.mul_rpow (by positivity) (abs_nonneg x)]
  exact Real.rpow_le_rpow_of_nonpos hpos (Real.mul_abs_le_abs_sin hxπ) hp0.le

end TauCeti
