/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Supplements to the fundamental theorem of calculus

Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` evaluates `∫ x in a..b, f x` as
`F b - F a` for an antiderivative `F` that is continuous on `[a, b]`, provided `f` is interval
integrable. When `f` is nonnegative on `(a, b)` the integrability is automatic
(`intervalIntegral.integrableOn_deriv_of_nonneg`), which matters for integrands that are unbounded
at an endpoint, such as `1 / √(x - a)`. This file records the combined statement.

In the converse direction, FTC-1 recovers the derivative of a `T`-periodic function `x` from the
integral equation `x(t) - x(0) = ∫₀ᵗ Y` over a single period `[0, T]`, when `Y` is continuous and
`T`-periodic: FTC-1 gives the derivative within `[0, T]`, and periodicity extends it to all of `ℝ`
(`TauCeti.hasDerivAt_of_periodic_of_hasDerivWithinAt`).

It also records the slope form of FTC-1 at a point of right continuity: the right integral
averages `(t - a)⁻¹ • ∫ u in a..t, g u` tend to `g a` as `t → a⁺`.

It also records that the integral of `B (f x) (f' x)` for a continuous bilinear map `B` is
unchanged by subtracting a constant `m` from `f` when `B m (f a) = B m (f b)`, because
`∫ B m f' = B m (f b - f a)`. This holds along a loop (`f a = f b`) for every `m`, and along an
arc with endpoints in a subspace isotropic for `B` for every `m` in that subspace.

Finally, the primitive `u ↦ ∫ t in a..u, f t` of a function continuous on `[a, b]` has derivative
`f x` at every point `x` of the open interval `(a, b)`, and so does any function which agrees with
a constant plus this primitive on `(a, b)`.
Within `[a, b]`, the primitive `σ ↦ ∫ r in t₀..σ, A r` of a function `A` continuous on `[a, b]`,
based at any `t₀ ∈ [a, b]`, has derivative `A τ` within `[a, b]` at every `τ ∈ [a, b]`.

## Main declarations

* `TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg`
* `TauCeti.intervalIntegral.tendsto_sub_inv_smul_integral_nhdsGT`
* `TauCeti.intervalIntegral.hasDerivWithinAt_integral`
* `ContinuousOn.integral_hasDerivAt_of_mem_Ioo`
* `ContinuousOn.hasDerivAt_of_eq_add_integral`
* `TauCeti.hasDerivAt_of_periodic_of_sub_eq_integral`
* `ContinuousLinearMap.intervalIntegral_apply_apply_eq_sub_const`
-/

public section

open MeasureTheory Set
open scoped Interval Topology

namespace TauCeti

namespace intervalIntegral

/-- **FTC-2 for a nonnegative derivative.** If `F` is continuous on `[a, b]` and has derivative
`f x ≥ 0` at every `x ∈ (a, b)`, then `∫ x in a..b, f x = F b - F a`; the integrability of `f`
is a consequence rather than a hypothesis. -/
theorem integral_eq_sub_of_hasDerivAt_of_le_of_nonneg {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Ioo a b, 0 ≤ f x) : ∫ x in a..b, f x = F b - F a :=
  _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF hd hf))

/-- **Right integral averages at a point of right continuity.** If `g` is strongly measurable
near `a` from the right and continuous at `a` from the right, then the integral averages
`(t - a)⁻¹ • ∫ u in a..t, g u` tend to `g a` as `t → a⁺`. This is the slope form of FTC-1
(`intervalIntegral.integral_hasDerivWithinAt_right`). -/
theorem tendsto_sub_inv_smul_integral_nhdsGT {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} {a : ℝ}
    (hmeas : StronglyMeasurableAtFilter g (𝓝[>] a) volume)
    (hg : ContinuousWithinAt g (Ioi a) a) :
    Filter.Tendsto (fun t ↦ (t - a)⁻¹ • ∫ u in a..t, g u) (𝓝[>] a) (𝓝 (g a)) := by
  have h : HasDerivWithinAt (fun t ↦ ∫ u in a..t, g u) (g a) (Ioi a) a :=
    (_root_.intervalIntegral.integral_hasDerivWithinAt_right IntervalIntegrable.refl hmeas
      hg).Ioi_of_Ici
  refine ((hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)).mp h).congr fun t ↦ ?_
  rw [slope_def_module, _root_.intervalIntegral.integral_same, sub_zero]

/-- **The fundamental theorem of calculus within a compact interval** `[a, b]` containing the
base point `t₀`: for `A` continuous on `[a, b]`, the primitive `σ ↦ ∫_{t₀}^σ A r dr` has
derivative `A τ` within `[a, b]` at every `τ ∈ [a, b]`. -/
theorem hasDerivWithinAt_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {A : ℝ → X} {a b t₀ τ : ℝ} (hA : ContinuousOn A (Icc a b))
    (ht₀ : t₀ ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    HasDerivWithinAt (fun σ ↦ ∫ r in t₀..σ, A r) (A τ) (Icc a b) τ := by
  have : Fact (τ ∈ Icc a b) := ⟨hτ⟩
  exact _root_.intervalIntegral.integral_hasDerivWithinAt_right
    (hA.mono (uIcc_subset_Icc ht₀ hτ)).intervalIntegrable
    (hA.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc τ) (hA τ hτ)

end intervalIntegral

/-- **FTC-1 on an open interval.** If `f` is continuous on `[a, b]`, then its primitive
`u ↦ ∫ t in a..u, f t` has derivative `f x` at every interior point `x ∈ (a, b)`. -/
theorem _root_.ContinuousOn.integral_hasDerivAt_of_mem_Ioo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b x : ℝ} (hf : ContinuousOn f (Icc a b))
    (hx : x ∈ Ioo a b) : HasDerivAt (fun u ↦ ∫ t in a..u, f t) (f x) x :=
  _root_.intervalIntegral.integral_hasDerivAt_right
    ((hf.mono (by simpa [uIcc_of_le hx.1.le] using Icc_subset_Icc_right hx.2.le)
      ).intervalIntegrable)
    ((hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
    ((hf.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hx))

/-- If `g` is continuous on `[a, b]` and `f t = f a + ∫ s in a..t, g s` for `t ∈ (a, b)`, then `f`
has derivative `g x` at every `x ∈ (a, b)`. -/
theorem _root_.ContinuousOn.hasDerivAt_of_eq_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {a b x : ℝ} (hg : ContinuousOn g (Icc a b))
    (hx : x ∈ Ioo a b) (heq : ∀ t ∈ Ioo a b, f t = f a + ∫ s in a..t, g s) :
    HasDerivAt f (g x) x :=
  ((hg.integral_hasDerivAt_of_mem_Ioo hx).const_add (f a)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) heq)

/-- **Periodic solutions of an integral equation.** Let `x` and a continuous `Y` be `T`-periodic,
with `T > 0`. If `x t - x 0 = ∫₀ᵗ Y` for every `t ∈ [0, T]`, then `x` has derivative `Y t` at every
`t`. -/
theorem hasDerivAt_of_periodic_of_sub_eq_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {x Y : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hxper : Function.Periodic x T) (hY : Continuous Y) (hYper : Function.Periodic Y T)
    (hint : ∀ t ∈ Icc 0 T, x t - x 0 = ∫ τ in 0..t, Y τ) (t : ℝ) : HasDerivAt x (Y t) t := by
  refine hasDerivAt_of_periodic_of_hasDerivWithinAt hT hxper hYper 0 (fun s hs ↦ ?_) t
  rw [zero_add] at hs ⊢
  -- On `[0, T]`, `x` agrees with `x 0 + ∫₀ᵗ Y`, which has derivative `Y` by FTC-1.
  exact ((_root_.intervalIntegral.integral_hasDerivAt_right (hY.intervalIntegrable 0 s)
    (hY.stronglyMeasurableAtFilter _ _) hY.continuousAt).const_add (x 0)).hasDerivWithinAt
    |>.congr_of_mem (fun r hr ↦ by rw [← hint r hr, add_sub_cancel]) hs

end TauCeti

namespace ContinuousLinearMap

/-- For `f` continuous on `[a, b]` with derivative `f'` in the interior, subtracting a constant `m`
from the first argument does not change the integral of `B (f x) (f' x)` when
`B m (f a) = B m (f b)`, since `∫ B m f' = B m (f b) - B m (f a)`. This holds for every `m` along
a loop, `f a = f b`. -/
theorem intervalIntegral_apply_apply_eq_sub_const {V G : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : V →L[ℝ] V →L[ℝ] G) {a b : ℝ}
    {f f' : ℝ → V}
    (hfc : ContinuousOn f [[a, b]])
    (hf : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x) {m : V}
    (hm : B m (f a) = B m (f b)) (hf'ii : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, B (f x) (f' x) = ∫ x in a..b, B (f x - m) (f' x) := by
  have hBm : IntervalIntegrable (fun x => B m (f' x)) volume a b :=
    ⟨(B m).integrable_comp hf'ii.1, (B m).integrable_comp hf'ii.2⟩
  -- Without completeness of `G` every integral in `G` vanishes.
  by_cases hG : CompleteSpace G
  swap
  · simp [intervalIntegral, integral_of_not_completeSpace hG]
  have hmean : ∫ x in a..b, B m (f' x) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right ((B m).continuous.comp_continuousOn hfc)
      (fun x hx => ((B m).hasFDerivAt.comp_hasDerivAt x (hf x hx)).hasDerivWithinAt) hBm]
    simp [hm]
  by_cases hint : IntervalIntegrable (fun x => B (f x - m) (f' x)) volume a b
  · rw [← add_zero (∫ x in a..b, B (f x - m) (f' x)), ← hmean,
      ← intervalIntegral.integral_add hint hBm]
    simp [map_sub]
  · -- if `B (f x - m) (f' x)` is not integrable then neither is `B (f x) (f' x)`, as `B m (f' x)`
    -- is, and both integrals vanish
    have hfint : ¬ IntervalIntegrable (fun x => B (f x) (f' x)) volume a b := fun h =>
      hint (by simpa [map_sub] using h.sub hBm)
    rw [intervalIntegral.integral_undef hint, intervalIntegral.integral_undef hfint]

end ContinuousLinearMap
