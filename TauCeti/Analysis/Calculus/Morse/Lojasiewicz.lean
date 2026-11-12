/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.Morse.Convergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite length of gradient trajectories under a Łojasiewicz inequality

Let `γ` be a negative gradient trajectory of `f : E → ℝ` in a real Hilbert space, so that
`γ' = -∇f(γ)`, and suppose that along `γ` the values of `f` stay above `b` and satisfy the
**Łojasiewicz gradient inequality**

`‖∇f(γ(t))‖ ≥ c (f(γ(t)) - b) ^ θ`,  with `c > 0` and `θ < 1`.

Then `γ` has **finite length**: with `K = c (1 - θ)`,

`∫_{t₀}^{t₁} ‖∇f(γ(t))‖ dt ≤ ((f(γ(t₀)) - b) ^ (1 - θ) - (f(γ(t₁)) - b) ^ (1 - θ)) / K`,

and on a forward half-line `∫_{t₀}^∞ ‖∇f(γ(t))‖ dt ≤ (f(γ(t₀)) - b) ^ (1 - θ) / K`. Consequently
the values `f(γ(t))` decrease to `b`, the trajectory converges to a single point `p`, and its tail
obeys the explicit bound `‖γ(t) - p‖ ≤ (f(γ(t)) - b) ^ (1 - θ) / K`. When `∇ f` is continuous at
`p`, the limit is a critical point (`IsIntegralCurveOn.gradient_eq_zero_of_tendsto`). Unlike the
convergence theorem of `TauCeti.Analysis.Calculus.Morse.Convergence`, nothing is assumed about the
critical locus: the gradient inequality excludes a trajectory spiralling towards a continuum of
critical points, the phenomenon that a merely smooth `f` permits. The exponent `θ` is not assumed
to be `1 / 2`, so degenerate critical points such as that of `x ↦ x⁴`, for which
`|∇f| = 4 |f| ^ (3 / 4)`, are covered.

## The argument

Write `e(t) = f(γ(t)) - b ≥ 0` and `g(t) = ‖∇f(γ(t))‖`, so that `e' = -g²` and `c e ^ θ ≤ g`.
The **Łojasiewicz potential** `Φ(t) = -e(t) ^ (1 - θ) / K` has right derivative
`e ^ (-θ) g² / c`, which is at least `g`: where `e > 0` this is the chain rule together with the
gradient inequality, and once `e` vanishes it stays zero, since `e` is antitone and nonnegative,
so that both `Φ` and `g` vanish from then on. A function whose right derivative dominates `g` grows
at least by the integral of `g`, and dominates the displacement of any curve with speed at most
`g`. These two scalar statements
(`TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz` and
`TauCeti.norm_sub_le_rpow_sub_rpow_of_lojasiewicz`) use nothing about gradients or about the
norm in which `g` is measured. For a gradient trajectory of a Riemannian metric read in a chart,
`g` is the metric norm of the gradient, and the displacement bound applies to the curve divided by
a constant comparing the chart norm with the metric.

## Main results

* `TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz`: the scalar finite-length bound.
* `TauCeti.norm_sub_le_rpow_sub_rpow_of_lojasiewicz`: the scalar displacement bound for a curve
  whose speed is at most `g`.
* `IsIntegralCurveOn.integral_norm_gradient_le_of_lojasiewicz`,
  `IsIntegralCurveOn.norm_sub_le_of_lojasiewicz`: the length and displacement bounds for a
  negative gradient trajectory on a compact time interval.
* `IsIntegralCurveOn.integrableOn_norm_gradient_Ioi_of_lojasiewicz`,
  `IsIntegralCurveOn.integral_Ioi_norm_gradient_le_of_lojasiewicz`: a forward trajectory has
  finite length, bounded by `(f(γ(t₀)) - b) ^ (1 - θ) / (c (1 - θ))`.
* `IsIntegralCurveOn.tendsto_comp_atTop_of_lojasiewicz`: the values of `f` along it tend to `b`.
* `IsIntegralCurveOn.exists_tendsto_atTop_of_lojasiewicz`: it converges to a single point, with
  the tail bound `‖γ(t) - p‖ ≤ (f(γ(t)) - b) ^ (1 - θ) / (c (1 - θ))`.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, CNRS, Paris, 1963, 87–89.
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, arXiv:math/0410568, proof of Theorem 1.1.
-/

public section

open Filter MeasureTheory Set
open scoped Gradient Interval Topology

namespace TauCeti

/-! ### The scalar argument -/

section Scalar

variable {e g : ℝ → ℝ} {a b c θ : ℝ}

/-- A nonnegative function with derivative `-g²` on `[a, b]` is antitone there. -/
private theorem antitoneOn_of_hasDerivWithinAt_neg_sq
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t) :
    AntitoneOn e (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun t ht ↦ (he t ht).continuousWithinAt)
    (fun t ht ↦ (he t (interior_subset ht)).mono interior_subset)
    (fun _ _ ↦ neg_nonpos.mpr (sq_nonneg _))

/-- Where a nonnegative function with derivative `-g²` on `[a, b]` vanishes, before the end of the
interval, so does `g`: the function stays zero from then on. -/
private theorem sq_eq_zero_of_hasDerivWithinAt_neg_sq
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) {t : ℝ} (ht : t ∈ Ico a b) (hzero : e t = 0) :
    g t ^ 2 = 0 ∧ e =ᶠ[𝓝[≥] t] fun _ ↦ 0 := by
  have hmem : Ico t b ∈ 𝓝[≥] t := Ico_mem_nhdsGE ht.2
  have hsub : Ico t b ⊆ Icc a b := fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.le⟩
  have heq : e =ᶠ[𝓝[≥] t] fun _ ↦ 0 := by
    filter_upwards [hmem] with u hu
    exact le_antisymm (hzero ▸ antitoneOn_of_hasDerivWithinAt_neg_sq he
      (Ico_subset_Icc_self ht) (hsub hu) hu.1) (he₀ u (hsub hu))
  refine ⟨?_, heq⟩
  have hd₁ := (he t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (mem_of_superset hmem hsub)
  have hd₂ : HasDerivWithinAt e 0 (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq heq hzero
  exact neg_eq_zero.mp ((uniqueDiffWithinAt_Ici t).eq_deriv _ hd₁ hd₂)

/-- The right derivative of the **Łojasiewicz potential** `-e ^ (1 - θ) / (c (1 - θ))`. -/
private theorem hasDerivWithinAt_lojasiewiczPotential (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun u ↦ -e u ^ (1 - θ) / (c * (1 - θ))) (e t ^ (-θ) * g t ^ 2 / c)
      (Ici t) t := by
  have hp : (1 - θ) ≠ 0 := (sub_pos.mpr hθ).ne'
  rcases (he₀ t (Ico_subset_Icc_self ht)).lt_or_eq with hpos | hzero
  · have hd := (he t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ico_mem_nhdsGE ht.2) fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.le⟩)
    convert ((hd.rpow_const (p := 1 - θ) (Or.inl hpos.ne')).neg.div_const (c * (1 - θ)))
      using 1
    rw [show (1 : ℝ) - θ - 1 = -θ by ring]
    field_simp
  · obtain ⟨hg, heq⟩ := sq_eq_zero_of_hasDerivWithinAt_neg_sq he he₀ ht hzero.symm
    rw [hg, mul_zero, zero_div]
    refine (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [heq] with u hu
      simp [hu, Real.zero_rpow hp]
    · simp [← hzero, Real.zero_rpow hp]

/-- The right derivative of the Łojasiewicz potential dominates `g`. -/
private theorem le_lojasiewiczPotential_deriv (hc : 0 < c)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) (hL : ∀ t ∈ Ico a b, c * e t ^ θ ≤ g t) {t : ℝ}
    (ht : t ∈ Ico a b) :
    g t ≤ e t ^ (-θ) * g t ^ 2 / c := by
  rcases (he₀ t (Ico_subset_Icc_self ht)).lt_or_eq with hpos | hzero
  · have hpow : 0 < e t ^ θ := Real.rpow_pos_of_pos hpos θ
    have hg : 0 < g t := (mul_pos hc hpow).trans_le (hL t ht)
    rw [Real.rpow_neg hpos.le, le_div_iff₀ hc, inv_mul_eq_div, le_div_iff₀ hpow]
    nlinarith [mul_le_mul_of_nonneg_left (hL t ht) hg.le]
  · have hg := (sq_eq_zero_of_hasDerivWithinAt_neg_sq he he₀ ht hzero.symm).1
    rw [hg, pow_eq_zero_iff two_ne_zero |>.mp hg]
    simp

/-- The Łojasiewicz potential is continuous on `[a, b]`. -/
private theorem continuousOn_lojasiewiczPotential (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t) :
    ContinuousOn (fun u ↦ -e u ^ (1 - θ) / (c * (1 - θ))) (Icc a b) :=
  ((ContinuousOn.rpow_const (fun t ht ↦ (he t ht).continuousWithinAt)
    fun _ _ ↦ Or.inr (sub_pos.mpr hθ).le).neg).div_const _

/-- **The scalar Łojasiewicz finite-length bound.** Let `e ≥ 0` have derivative `-g²` on
`[a, b]`, and suppose `c e ^ θ ≤ g` with `c > 0` and `θ < 1`. Then
`∫_a^b g ≤ (e(a) ^ (1 - θ) - e(b) ^ (1 - θ)) / (c (1 - θ))`.

For a negative gradient trajectory, `e` is the excess of `f` over a critical value and `g` the norm
of the gradient. No integrability of `g` is assumed: when `g` is not integrable its integral is
`0`, and the right side is nonnegative. -/
theorem integral_le_rpow_sub_rpow_of_lojasiewicz (hab : a ≤ b) (hc : 0 < c) (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) (hL : ∀ t ∈ Ico a b, c * e t ^ θ ≤ g t) :
    ∫ t in a..b, g t ≤ (e a ^ (1 - θ) - e b ^ (1 - θ)) / (c * (1 - θ)) := by
  by_cases hint : IntegrableOn g (Icc a b)
  · calc ∫ t in a..b, g t
        ≤ -e b ^ (1 - θ) / (c * (1 - θ)) - -e a ^ (1 - θ) / (c * (1 - θ)) :=
          intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
            (continuousOn_lojasiewiczPotential hθ he)
            (fun t ht ↦ (hasDerivWithinAt_lojasiewiczPotential hθ he he₀
              (Ioo_subset_Ico_self ht)).mono Ioi_subset_Ici_self) hint
            fun t ht ↦ le_lojasiewiczPotential_deriv hc he he₀ hL (Ioo_subset_Ico_self ht)
      _ = (e a ^ (1 - θ) - e b ^ (1 - θ)) / (c * (1 - θ)) := by ring
  · rw [intervalIntegral.integral_undef fun h ↦ hint
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp h)]
    refine div_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow (he₀ b (right_mem_Icc.mpr hab))
      (antitoneOn_of_hasDerivWithinAt_neg_sq he (left_mem_Icc.mpr hab)
        (right_mem_Icc.mpr hab) hab) (sub_pos.mpr hθ).le))
      (mul_pos hc (sub_pos.mpr hθ)).le

/-- **The scalar Łojasiewicz displacement bound.** Let `e ≥ 0` have derivative `-g²` on `[a, b]`,
and suppose `c e ^ θ ≤ g` with `c > 0` and `θ < 1`. A curve `x` whose velocity has norm at most
`g` moves by at most `(e(a) ^ (1 - θ) - e(b) ^ (1 - θ)) / (c (1 - θ))` during `[a, b]`. -/
theorem norm_sub_le_rpow_sub_rpow_of_lojasiewicz {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {x x' : ℝ → F} (hab : a ≤ b) (hc : 0 < c) (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) (hL : ∀ t ∈ Ico a b, c * e t ^ θ ≤ g t)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (x' t) (Icc a b) t)
    (hx' : ∀ t ∈ Ico a b, ‖x' t‖ ≤ g t) :
    ‖x b - x a‖ ≤ (e a ^ (1 - θ) - e b ^ (1 - θ)) / (c * (1 - θ)) := by
  set Φ : ℝ → ℝ := fun u ↦ -e u ^ (1 - θ) / (c * (1 - θ)) with hΦ
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun u ↦ x u - x a) (f' := x') (B := fun u ↦ Φ u - Φ a)
    (B' := fun t ↦ e t ^ (-θ) * g t ^ 2 / c)
    (ContinuousOn.sub (fun t ht ↦ (hx t ht).continuousWithinAt) continuousOn_const)
    (fun t ht ↦ ((hx t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ico_mem_nhdsGE ht.2) fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.le⟩)).sub_const
        (x a))
    (by simp) ((continuousOn_lojasiewiczPotential hθ he).sub continuousOn_const)
    (fun t ht ↦ (hasDerivWithinAt_lojasiewiczPotential hθ he he₀ ht).sub_const (Φ a))
    (fun t ht ↦ (hx' t ht).trans (le_lojasiewiczPotential_deriv hc he he₀ hL ht))
    (right_mem_Icc.mpr hab)
  refine key.trans (le_of_eq ?_)
  simp only [hΦ]
  ring

end Scalar

end TauCeti

/-! ### Negative gradient trajectories -/

namespace IsIntegralCurveOn

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {t₀ t₁ b c θ : ℝ}

/-- **Finite length of a gradient trajectory on a compact time interval.** If along a negative
gradient trajectory `f` stays above `b` and `‖∇f‖ ≥ c (f - b) ^ θ` with `c > 0` and `θ < 1`,
then its length during `[t₀, t₁]` is at most
`((f(γ(t₀)) - b) ^ (1 - θ) - (f(γ(t₁)) - b) ^ (1 - θ)) / (c (1 - θ))`. -/
theorem integral_norm_gradient_le_of_lojasiewicz (ht : t₀ ≤ t₁)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Icc t₀ t₁))
    (hf : ∀ t ∈ Icc t₀ t₁, DifferentiableAt ℝ f (γ t)) (hc : 0 < c) (hθ : θ < 1)
    (hb : ∀ t ∈ Icc t₀ t₁, b ≤ f (γ t))
    (hL : ∀ t ∈ Ico t₀ t₁, c * (f (γ t) - b) ^ θ ≤ ‖∇ f (γ t)‖) :
    ∫ t in t₀..t₁, ‖∇ f (γ t)‖ ≤
      ((f (γ t₀) - b) ^ (1 - θ) - (f (γ t₁) - b) ^ (1 - θ)) / (c * (1 - θ)) :=
  integral_le_rpow_sub_rpow_of_lojasiewicz ht hc hθ
    (fun t ht ↦ (hγ.hasDerivWithinAt_comp_neg_gradient ht (hf t ht)).sub_const b)
    (fun t ht ↦ sub_nonneg.mpr (hb t ht)) hL

/-- **Displacement of a gradient trajectory on a compact time interval.** Under the hypotheses of
`IsIntegralCurveOn.integral_norm_gradient_le_of_lojasiewicz`, the trajectory moves by at most
`((f(γ(t₀)) - b) ^ (1 - θ) - (f(γ(t₁)) - b) ^ (1 - θ)) / (c (1 - θ))` during `[t₀, t₁]`. -/
theorem norm_sub_le_of_lojasiewicz (ht : t₀ ≤ t₁)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Icc t₀ t₁))
    (hf : ∀ t ∈ Icc t₀ t₁, DifferentiableAt ℝ f (γ t)) (hc : 0 < c) (hθ : θ < 1)
    (hb : ∀ t ∈ Icc t₀ t₁, b ≤ f (γ t))
    (hL : ∀ t ∈ Ico t₀ t₁, c * (f (γ t) - b) ^ θ ≤ ‖∇ f (γ t)‖) :
    ‖γ t₁ - γ t₀‖ ≤
      ((f (γ t₀) - b) ^ (1 - θ) - (f (γ t₁) - b) ^ (1 - θ)) / (c * (1 - θ)) :=
  norm_sub_le_rpow_sub_rpow_of_lojasiewicz ht hc hθ
    (fun t ht ↦ (hγ.hasDerivWithinAt_comp_neg_gradient ht (hf t ht)).sub_const b)
    (fun t ht ↦ sub_nonneg.mpr (hb t ht)) hL hγ fun _ _ ↦ (norm_neg _).le

section Forward

variable (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici t₀))
  (hf : ∀ t ∈ Ici t₀, DifferentiableAt ℝ f (γ t)) (hc : 0 < c) (hθ : θ < 1)
  (hb : ∀ t ∈ Ici t₀, b ≤ f (γ t))
  (hL : ∀ t ∈ Ici t₀, c * (f (γ t) - b) ^ θ ≤ ‖∇ f (γ t)‖)
include hγ hf hc hθ hb hL

/-- The length bound on `[t, u] ⊆ [t₀, ∞)`, after discarding the nonnegative final term. -/
private theorem integral_norm_gradient_le_of_lojasiewicz_of_le {t u : ℝ} (ht : t₀ ≤ t)
    (htu : t ≤ u) :
    ∫ s in t..u, ‖∇ f (γ s)‖ ≤ (f (γ t) - b) ^ (1 - θ) / (c * (1 - θ)) := by
  have hsub : Icc t u ⊆ Ici t₀ := fun s hs ↦ mem_Ici.mpr (ht.trans hs.1)
  refine (integral_norm_gradient_le_of_lojasiewicz htu (hγ.mono hsub) (fun s hs ↦ hf s (hsub hs))
    hc hθ (fun s hs ↦ hb s (hsub hs)) fun s hs ↦ hL s (hsub (Ico_subset_Icc_self hs))).trans ?_
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.mpr (hb u (ht.trans htu))) _)

/-- The displacement bound on `[t, u] ⊆ [t₀, ∞)`, after discarding the nonnegative final term. -/
private theorem norm_sub_le_of_lojasiewicz_of_le {t u : ℝ} (ht : t₀ ≤ t) (htu : t ≤ u) :
    ‖γ u - γ t‖ ≤ (f (γ t) - b) ^ (1 - θ) / (c * (1 - θ)) := by
  have hsub : Icc t u ⊆ Ici t₀ := fun s hs ↦ mem_Ici.mpr (ht.trans hs.1)
  refine (norm_sub_le_of_lojasiewicz htu (hγ.mono hsub) (fun s hs ↦ hf s (hsub hs))
    hc hθ (fun s hs ↦ hb s (hsub hs)) fun s hs ↦ hL s (hsub (Ico_subset_Icc_self hs))).trans ?_
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.mpr (hb u (ht.trans htu))) _)

/-- **A forward gradient trajectory satisfying a Łojasiewicz inequality has finite length**: its
speed `‖∇f(γ(t))‖` is integrable on `(t₀, ∞)`. -/
theorem integrableOn_norm_gradient_Ioi_of_lojasiewicz :
    IntegrableOn (fun t ↦ ‖∇ f (γ t)‖) (Ioi t₀) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
    ((f (γ t₀) - b) ^ (1 - θ) / (c * (1 - θ))) t₀ (fun T ↦ ?_) tendsto_id ?_
  · rcases le_total T t₀ with hT | hT
    · simp [Ioc_eq_empty (not_lt.mpr hT)]
    · have hsub : Icc t₀ T ⊆ Ici t₀ := Icc_subset_Ici_self
      rw [← uIcc_of_le hT] at hsub
      exact (intervalIntegrable_norm_gradient t₀ T (hγ.mono hsub) fun s hs ↦ hf s (hsub hs)).1
  · filter_upwards [eventually_ge_atTop t₀] with T hT
    simpa only [norm_norm, id] using
      integral_norm_gradient_le_of_lojasiewicz_of_le hγ hf hc hθ hb hL le_rfl hT

/-- **The Łojasiewicz length bound on a half-line.** A forward negative gradient trajectory along
which `f ≥ b` and `‖∇f‖ ≥ c (f - b) ^ θ`, with `c > 0` and `θ < 1`, has length at most
`(f(γ(t₀)) - b) ^ (1 - θ) / (c (1 - θ))`. -/
theorem integral_Ioi_norm_gradient_le_of_lojasiewicz :
    ∫ t in Ioi t₀, ‖∇ f (γ t)‖ ≤ (f (γ t₀) - b) ^ (1 - θ) / (c * (1 - θ)) :=
  le_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi t₀
      (integrableOn_norm_gradient_Ioi_of_lojasiewicz hγ hf hc hθ hb hL) tendsto_id)
    (by
      filter_upwards [eventually_ge_atTop t₀] with T hT
      exact integral_norm_gradient_le_of_lojasiewicz_of_le hγ hf hc hθ hb hL le_rfl hT)

omit hθ in
/-- **The values of `f` along the trajectory tend to `b`.** While `f(γ(t)) ≥ b + ε`, the gradient
inequality keeps the speed above a positive constant, so `f` would drop without bound. Here the
exponent `θ` may be arbitrary. -/
theorem tendsto_comp_atTop_of_lojasiewicz :
    Tendsto (fun t ↦ f (γ t)) atTop (𝓝 b) := by
  have hanti : AntitoneOn (fun t ↦ f (γ t)) (Ici t₀) :=
    hγ.antitoneOn_comp_neg_gradient (convex_Ici t₀) hf
  refine tendsto_order.mpr ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · filter_upwards [eventually_ge_atTop t₀] with t ht
    exact ha.trans_le (hb t ht)
  -- It suffices to find one time at which `f(γ(T)) < a`, by monotonicity.
  suffices h : ∃ T ∈ Ici t₀, f (γ T) < a by
    obtain ⟨T, hT, hlt⟩ := h
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hanti hT (mem_Ici.mpr ((mem_Ici.mp hT).trans ht)) ht).trans_lt hlt
  by_contra! hge
  set ε := a - b
  have hεpos : 0 < ε := sub_pos.mpr ha
  set e₀ := f (γ t₀) - b
  have hεe₀ : ε ≤ e₀ := by linarith [hge t₀ (mem_Ici.mpr le_rfl)]
  -- On `[ε, e₀]` the power `x ^ θ` is bounded below by a positive constant `m`.
  set m := min (ε ^ θ) (e₀ ^ θ)
  have hmpos : 0 < m :=
    lt_min (Real.rpow_pos_of_pos hεpos θ) (Real.rpow_pos_of_pos (hεpos.trans_le hεe₀) θ)
  have hspeed : ∀ t ∈ Ici t₀, c * m ≤ ‖∇ f (γ t)‖ := by
    intro t ht
    have hlo : ε ≤ f (γ t) - b := by linarith [hge t ht]
    have hhi : f (γ t) - b ≤ e₀ := by linarith [hanti (mem_Ici.mpr le_rfl) ht (mem_Ici.mp ht)]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hc.le) (hL t ht)
    rcases le_total 0 θ with hθ₀ | hθ₀
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow hεpos.le hlo hθ₀)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hεpos.trans_le hlo) hhi hθ₀)
  set κ := c * m
  have hκpos : 0 < κ := mul_pos hc hmpos
  set T := t₀ + e₀ / κ ^ 2 + 1 with hT
  have hT₀ : t₀ ≤ T := by
    have : 0 ≤ e₀ / κ ^ 2 := div_nonneg (hεpos.le.trans hεe₀) (sq_nonneg _)
    linarith
  have hdrop := mul_sq_le_sub_of_le_norm_gradient hT₀ hγ Icc_subset_Ici_self
    (fun t ht ↦ hf t ht.1) hκpos.le fun t ht ↦ hspeed t ht.1
  have hlow := hb T hT₀
  have hkey : (T - t₀) * κ ^ 2 = e₀ + κ ^ 2 := by
    rw [hT]
    field_simp
    ring
  nlinarith [sq_pos_of_pos hκpos]

/-- **A forward gradient trajectory satisfying a Łojasiewicz inequality converges to a single
point**, and its tail obeys `‖γ(t) - p‖ ≤ (f(γ(t)) - b) ^ (1 - θ) / (c (1 - θ))` for every
`t ≥ t₀`. The limit is a critical point of `f` wherever the gradient is continuous at it, by
`IsIntegralCurveOn.gradient_eq_zero_of_tendsto`. -/
theorem exists_tendsto_atTop_of_lojasiewicz :
    ∃ p, Tendsto γ atTop (𝓝 p) ∧
      ∀ t ∈ Ici t₀, ‖γ t - p‖ ≤ (f (γ t) - b) ^ (1 - θ) / (c * (1 - θ)) := by
  have hp : (1 - θ) ≠ 0 := (sub_pos.mpr hθ).ne'
  -- The tail bound tends to `0`, since `f(γ(t)) → b`.
  have hbound : Tendsto (fun t ↦ (f (γ t) - b) ^ (1 - θ) / (c * (1 - θ))) atTop (𝓝 0) := by
    have h₀ : Tendsto (fun t ↦ f (γ t) - b) atTop (𝓝 0) := by
      simpa using (tendsto_comp_atTop_of_lojasiewicz hγ hf hc hb hL).sub_const b
    have h := ((Real.continuousAt_rpow_const 0 (1 - θ) (Or.inr (sub_pos.mpr hθ).le)).tendsto.comp
      h₀).div_const (c * (1 - θ))
    simpa [Function.comp_def, Real.zero_rpow hp] using h
  have hcauchy : CauchySeq γ := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN, hN₀⟩ :=
      ((hbound.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop t₀)).exists
    exact ⟨N, fun n hn ↦ (dist_eq_norm _ _).trans_lt
      ((norm_sub_le_of_lojasiewicz_of_le hγ hf hc hθ hb hL hN₀ hn).trans_lt hN)⟩
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨p, hp, fun t ht ↦ ?_⟩
  rw [norm_sub_rev]
  refine le_of_tendsto ((hp.sub_const (γ t)).norm) ?_
  filter_upwards [eventually_ge_atTop t] with u hu
  exact norm_sub_le_of_lojasiewicz_of_le hγ hf hc hθ hb hL ht hu

end Forward

end IsIntegralCurveOn
