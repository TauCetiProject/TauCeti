/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import TauCeti.Analysis.GradientFlow.Slope
public import TauCeti.Data.EReal.Operations
public import TauCeti.MeasureTheory.Function.MetricDerivative

/-!
# Strong upper gradients

A function `g : X → [0, ∞]` is a *strong upper gradient* of an energy `φ : X → EReal` on a metric
space if along every absolutely continuous curve `γ` the energy varies by at most the integral of
`g` against the metric speed:

`|φ (γ b) - φ (γ a)| ≤ ∫_a^b g (γ r) |γ'|(r) dr`.

Upper gradients replace the norm of the gradient in the theory of gradient flows in metric spaces
of Ambrosio–Gigli–Savaré: curves of maximal slope and the energy-dissipation inequality are stated
with respect to an upper gradient, and the descending slope `TauCeti.descendingSlope` is the
canonical candidate.

## Main definitions

* `TauCeti.IsStrongUpperGradient φ g`: `g` is a strong upper gradient of `φ`.

## Main results

* the **chain rule inequality** `|(f ∘ γ)'(t)| ≤ |∂f|(γ t) |γ'|(t)` at every time where `f ∘ γ` is
  differentiable and the right-hand side is not of the form `0 · ∞`, comparing the derivative of a
  real function along a curve with its descending slope and the metric derivative of the curve
  (`HasDerivAt.enorm_le_descendingSlope_mul_metricDerivative`);
* the descending slope of a locally Lipschitz function is a strong upper gradient
  (`LocallyLipschitz.isStrongUpperGradient_descendingSlope`);
* for a real function with strong upper gradient `g`, the bound
  `|f (γ a) - f (γ b)| ≤ ∫ g (γ r) |γ'|(r) dr` (`TauCeti.IsStrongUpperGradient.edist_le_lintegral`),
  so that along an absolutely continuous curve on which `g (γ r) |γ'|(r)` is integrable the function
  is absolutely continuous
  (`TauCeti.IsStrongUpperGradient.absolutelyContinuousOnInterval_comp`).

## Implementation notes

Since `φ` takes values in `EReal`, the absolute value of a difference is replaced by the two
one-sided inequalities `φ (γ a) ≤ φ (γ b) + ∫ ...` and `φ (γ b) ≤ φ (γ a) + ∫ ...`; the definition
states the first for every absolutely continuous curve on `[a, b]`, and the second follows by
exchanging `a` and `b`. When the integral is finite this is exactly the two-sided bound, and it
forces `φ (γ a) = ⊤` exactly when `φ (γ b) = ⊤`.

The integral is the lower Lebesgue integral `lintegral`, which is defined for every function.
Ambrosio–Gigli–Savaré require `g ∘ γ` to be Borel so that the integral makes sense; for a Borel
`g` the two definitions agree, since `γ` is continuous.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 1, Section 1.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- `g` is a *strong upper gradient* of the energy `φ` if for every curve `γ` absolutely continuous
on `[a, b]`, `φ (γ a) ≤ φ (γ b) + ∫⁻ r in Ι a b, g (γ r) * |γ'|(r)`. Exchanging `a` and `b` gives
the reverse inequality, so for a finite integral this is the bound
`|φ (γ b) - φ (γ a)| ≤ ∫ g (γ r) |γ'|(r) dr`. -/
def IsStrongUpperGradient (φ : X → EReal) (g : X → ℝ≥0∞) : Prop :=
  ∀ ⦃γ : ℝ → X⦄ ⦃a b : ℝ⦄, AbsolutelyContinuousOnInterval γ a b →
    φ (γ a) ≤ φ (γ b) + ∫⁻ r in Ι a b, g (γ r) * metricDerivative γ r

variable {φ : X → EReal} {g g' : X → ℝ≥0∞}

/-- The defining property of a strong upper gradient. -/
theorem isStrongUpperGradient_iff :
    IsStrongUpperGradient φ g ↔ ∀ ⦃γ : ℝ → X⦄ ⦃a b : ℝ⦄, AbsolutelyContinuousOnInterval γ a b →
      φ (γ a) ≤ φ (γ b) + ∫⁻ r in Ι a b, g (γ r) * metricDerivative γ r :=
  Iff.rfl

/-- Along a curve `γ` absolutely continuous on `[a, b]`, an energy with strong upper gradient `g`
satisfies `φ (γ a) ≤ φ (γ b) + ∫⁻ r in Ι a b, g (γ r) * |γ'|(r)`. -/
theorem IsStrongUpperGradient.le_add_lintegral (hg : IsStrongUpperGradient φ g) {γ : ℝ → X}
    {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    φ (γ a) ≤ φ (γ b) + ∫⁻ r in Ι a b, g (γ r) * metricDerivative γ r :=
  hg hγ

/-- A function above a strong upper gradient is a strong upper gradient. -/
theorem IsStrongUpperGradient.mono (hg : IsStrongUpperGradient φ g) (hgg' : ∀ x, g x ≤ g' x) :
    IsStrongUpperGradient φ g' := fun _ _ _ hγ ↦
  (hg hγ).trans <| add_le_add_right (EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
    lintegral_mono fun _ ↦ mul_le_mul_left (hgg' _) _) _

/-- For a real function `f` with strong upper gradient `g` and a curve `γ` absolutely continuous on
`[a, b]`, `|f (γ a) - f (γ b)| ≤ ∫⁻ r in Ι a b, g (γ r) * |γ'|(r)`. -/
theorem IsStrongUpperGradient.edist_le_lintegral {f : X → ℝ}
    (hg : IsStrongUpperGradient (fun x ↦ (f x : EReal)) g) {γ : ℝ → X} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    edist (f (γ a)) (f (γ b)) ≤ ∫⁻ r in Ι a b, g (γ r) * metricDerivative γ r := by
  rcases eq_or_ne (∫⁻ r in Ι a b, g (γ r) * metricDerivative γ r) ∞ with hI | hI
  · exact hI ▸ le_top
  have h₁ := (EReal.coe_le_coe_add_coe_ennreal_iff hI).1 (hg hγ)
  have h₂ := hg hγ.symm
  rw [uIoc_comm, EReal.coe_le_coe_add_coe_ennreal_iff hI] at h₂
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_toReal hI]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)

/-- Along an absolutely continuous curve `γ` on `[a, b]` with
`∫⁻ r in Ι a b, g (γ r) * |γ'|(r) < ∞`, a real function with strong upper gradient `g` is absolutely
continuous on `[a, b]`. -/
theorem IsStrongUpperGradient.absolutelyContinuousOnInterval_comp {f : X → ℝ}
    (hg : IsStrongUpperGradient (fun x ↦ (f x : EReal)) g) {γ : ℝ → X} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hfin : ∫⁻ r in Ι a b, g (γ r) * metricDerivative γ r ≠ ∞) :
    AbsolutelyContinuousOnInterval (fun r ↦ f (γ r)) a b :=
  absolutelyContinuousOnInterval_of_edist_le_lintegral hfin fun _ hs _ hu ↦
    hg.edist_le_lintegral (hγ.mono (uIcc_subset_uIcc hs hu))

end PseudoMetricSpace

section EMetricSpace

variable {X : Type*} [EMetricSpace X]

/-- If `γ` is continuous at `t`, the rates of decrease of `f` from `γ t` to `γ u` have upper limit
at most the descending slope of `f` at `γ t` as `u → t`. -/
private lemma limsup_ofReal_sub_div_edist_le_descendingSlope {f : X → ℝ} {γ : ℝ → X} {t : ℝ}
    (hγ : ContinuousAt γ t) :
    limsup (fun u ↦ ENNReal.ofReal (f (γ t) - f (γ u)) / edist (γ t) (γ u)) (𝓝[≠] t) ≤
      descendingSlope (fun x ↦ (f x : EReal)) (γ t) := by
  set Q : X → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (f (γ t) - f y) / edist (γ t) y
  -- Unlike the slope, `γ u` may equal `γ t`, where the rate `Q (γ t) = 0 / 0` vanishes.
  calc limsup (fun u ↦ Q (γ u)) (𝓝[≠] t) = limsup Q (map γ (𝓝[≠] t)) := limsup_comp Q γ _
    _ ≤ limsup Q (𝓝 (γ t)) := limsup_le_limsup_of_le (hγ.tendsto.mono_left nhdsWithin_le_nhds)
    _ = max (limsup Q (𝓝[≠] (γ t))) (limsup Q (pure (γ t))) := by
      rw [← nhdsNE_sup_pure, limsup_sup_filter]
    _ ≤ _ := max_le (descendingSlope_coe f (γ t)).ge <|
      limsup_le_of_le (h := eventually_pure.2 (by simp [Q]))

/-- **Chain rule inequality** for the descending slope: if `f ∘ γ` has derivative `D` at `t`, then
`|D| ≤ |∂f|(γ t) * |γ'|(t)`. The hypotheses `h₀` and `htop` exclude the products `0 * ∞` and
`∞ * 0`, for which the inequality can fail. -/
theorem _root_.HasDerivAt.enorm_le_descendingSlope_mul_metricDerivative {f : X → ℝ} {γ : ℝ → X}
    {t D : ℝ} (hD : HasDerivAt (fun r ↦ f (γ r)) D t)
    (h₀ : descendingSlope (fun x ↦ (f x : EReal)) (γ t) ≠ 0 ∨ metricDerivative γ t ≠ ∞)
    (htop : descendingSlope (fun x ↦ (f x : EReal)) (γ t) ≠ ∞ ∨ metricDerivative γ t ≠ 0) :
    ‖D‖ₑ ≤ descendingSlope (fun x ↦ (f x : EReal)) (γ t) * metricDerivative γ t := by
  set S := descendingSlope (fun x ↦ (f x : EReal)) (γ t)
  by_cases hM : metricDerivative γ t = ∞
  · rw [hM, ENNReal.mul_top (h₀.resolve_right (not_not.2 hM))]
    exact le_top
  by_cases hS : S = ∞
  · rw [hS, ENNReal.top_mul (htop.resolve_left (not_not.2 hS))]
    exact le_top
  -- The rate of decrease of `f ∘ γ` between `t` and `u` is the rate of decrease of `f` between
  -- `γ t` and `γ u` times the difference quotient of `γ`.
  have hγ := continuousAt_of_metricDerivative_ne_top hM
  have hQ := limsup_ofReal_sub_div_edist_le_descendingSlope (f := f) hγ
  calc ‖D‖ₑ = limsup (fun u ↦ ENNReal.ofReal (f (γ t) - f (γ u)) / edist t u) (𝓝[≠] t) :=
        hD.descendingSlope_eq.symm.trans (descendingSlope_coe _ t)
    _ ≤ limsup ((fun u ↦ ENNReal.ofReal (f (γ t) - f (γ u)) / edist (γ t) (γ u)) *
          fun u ↦ edist (γ u) (γ t) / edist u t) (𝓝[≠] t) := by
        -- Near `t`, the distance from `γ t` to `γ u` is finite and can be cancelled.
        refine limsup_le_limsup ?_
        filter_upwards [nhdsWithin_le_nhds (hγ.eventually (Metric.eball_mem_nhds (γ t) one_pos))]
          with u hu₁
        by_cases hu : γ u = γ t
        · simp [hu]
        have h0 : edist (γ t) (γ u) ≠ 0 := (edist_pos.2 (Ne.symm hu)).ne'
        have htop : edist (γ t) (γ u) ≠ ∞ :=
          (edist_comm (γ t) (γ u) ▸ hu₁.trans ENNReal.one_lt_top).ne
        simp only [Pi.mul_apply, edist_comm (γ u), edist_comm u, div_eq_mul_inv, mul_assoc]
        rw [← mul_assoc _ (edist (γ t) (γ u)), ENNReal.inv_mul_cancel h0 htop, one_mul]
    _ ≤ S * metricDerivative γ t := by
        rw [metricDerivative_def] at hM ⊢
        exact (ENNReal.limsup_mul_le' (Or.inr hM) (Or.inl (ne_top_of_le_ne_top hS hQ))).trans
          (mul_le_mul_left hQ _)

end EMetricSpace

section MetricSpace

variable {X : Type*} [MetricSpace X]

/-- The descending slope of a locally Lipschitz function is a strong upper gradient: along every
absolutely continuous curve `γ` on `[a, b]`,
`|f (γ b) - f (γ a)| ≤ ∫ |∂f|(γ r) |γ'|(r) dr`. -/
theorem _root_.LocallyLipschitz.isStrongUpperGradient_descendingSlope {f : X → ℝ}
    (hf : LocallyLipschitz f) :
    IsStrongUpperGradient (fun x ↦ (f x : EReal)) (descendingSlope fun x ↦ (f x : EReal)) := by
  intro γ a b hγ
  set I := ∫⁻ r in Ι a b, descendingSlope (fun x ↦ (f x : EReal)) (γ r) * metricDerivative γ r
  -- `f ∘ γ` is absolutely continuous, since `f` is Lipschitz on the compact image of `[a, b]`.
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn')
  have hfγ : AbsolutelyContinuousOnInterval (fun r ↦ f (γ r)) a b :=
    hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ
  -- Almost everywhere the derivative of `f ∘ γ` is bounded by the chain rule inequality.
  have hderiv : ∀ᵐ r ∂volume.restrict (Ι a b), ‖deriv (fun r ↦ f (γ r)) r‖ₑ ≤
      descendingSlope (fun x ↦ (f x : EReal)) (γ r) * metricDerivative γ r := by
    filter_upwards [ae_lt_top' hγ.aemeasurable_metricDerivative
      hγ.lintegral_metricDerivative_lt_top.ne,
      ae_restrict_of_ae hfγ.ae_differentiableAt,
      ae_restrict_mem measurableSet_uIoc] with r hr hdiff hab
    obtain ⟨K', s, hs, hK'⟩ := hf (γ r)
    exact (hdiff (uIoc_subset_uIcc hab)).hasDerivAt.enorm_le_descendingSlope_mul_metricDerivative
      (Or.inr hr.ne) (Or.inl ((hK'.descendingSlope_le hs).trans_lt ENNReal.coe_lt_top).ne)
  have hle : ENNReal.ofReal (f (γ a) - f (γ b)) ≤ I :=
    calc ENNReal.ofReal (f (γ a) - f (γ b)) ≤ ENNReal.ofReal |f (γ a) - f (γ b)| :=
          ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ = ‖∫ r in Ι b a, deriv (fun r ↦ f (γ r)) r‖ₑ := by
          rw [← hfγ.symm.integral_deriv_eq_sub, intervalIntegral.abs_integral_eq_abs_integral_uIoc,
            Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ r in Ι b a, ‖deriv (fun r ↦ f (γ r)) r‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ I := by
          rw [uIoc_comm]
          exact lintegral_mono_ae hderiv
  rcases eq_or_ne I ∞ with hI | hI
  · rw [hI, EReal.coe_ennreal_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  · rw [EReal.coe_le_coe_add_coe_ennreal_iff hI]
    linarith [(ENNReal.ofReal_le_iff_le_toReal hI).1 hle]

end MetricSpace

end TauCeti
