/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.EvolutionSpace.PositivePart
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Order

/-!
# The weak maximum principle for evolution equations in a Gelfand triple over `L²`

Let `ι : V →L[ℝ] L²(ν)` be a continuous linear map from a real Banach space into a real `L²`
space, so that `V ↪ L²(ν) ↪ V*` through `ι.gelfandDual`, and let `P : V → V` be a positive part on
`V` compatible with that of `L²(ν)`: continuous, with `‖P v‖ ≤ ‖v‖` and `ι (P v) = (ι v)⁺`. Let
`A(t) : V → V*` be bounded operators with `A(t)(v)(P v) ≥ -β ‖ι (P v)‖²_{L²}` for some constant
`β` and almost every `t`.

A function `u ∈ L²(a, b; V)` whose image in `V*` has a weak derivative `u' ∈ L²(a, b; V*)` is a
weak subsolution of `u' + A(t) u = f` when `u'(t)(v) + A(t)(u(t))(v) ≤ f(t)(v)` for every `v` with
`ι v ≥ 0`, for almost every `t`, and a weak supersolution when the reverse inequality holds. The
**weak maximum principle** (`TauCeti.HasWeakLineDerivOn.nonpos_of_gelfandDual`) says that a weak
subsolution with `f = 0` whose continuous `L²(ν)`-valued representative `w` satisfies `w(a) ≤ 0`
has `w(t) ≤ 0` for every `t ∈ [a, b]`. The **weak comparison principle**
(`TauCeti.HasWeakLineDerivOn.le_of_gelfandDual`) says that a weak subsolution and a weak
supersolution of the same equation with ordered initial values stay ordered.

The model is `V = H¹₀(Ω)` with `P` the positive part and `A(t)` the operator of the energy form of
a parabolic operator in divergence form; see
`TauCeti.PDE.nonpos_of_hasWeakLineDerivOn_gelfandDual_energyFormH1`.

## The argument

Test the inequality with the positive part `v = P (u(t))`. The chain rule for the positive part
(`TauCeti.HasWeakLineDerivOn.norm_posPart_sq_of_gelfandDual`) gives
`d/dt ‖(ι u(t))⁺‖² = 2 u'(t)(P u(t)) ≤ -2 A(t)(u(t))(P u(t)) ≤ 2 β ‖(ι u(t))⁺‖²`, where `β ≥ 0`
may be assumed. Hence `‖w(t)⁺‖² ≤ 2 β ∫ₐᵗ ‖w⁺‖²`, and Grönwall's inequality with `w(a)⁺ = 0`
forces `w(t)⁺ = 0`. Comparison follows by applying the maximum principle to the difference.

## References

* G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific, 1996,
  Chapter VI, for weak solutions of parabolic equations and their maximum principle.
-/

public section

noncomputable section

open MeasureTheory Set Filter

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {ι : V →L[ℝ] Lp ℝ 2 ν} {P : V → V} {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b β : ℝ}

/-- **The weak maximum principle in a Gelfand triple over `L²`.** Let `ι : V →L[ℝ] L²(ν)`, and let
`P : V → V` be continuous with `‖P v‖ ≤ ‖v‖` and `ι (P v) = (ι v)⁺`. Let `A(t)` satisfy
`-β ‖ι (P v)‖² ≤ A(t)(v)(P v)` for almost every `t ∈ (a, b)`. Let `u ∈ L²(a, b; V)`
be such that `t ↦ ι.gelfandDual (ι (u t))` has weak derivative `u' ∈ L²(a, b; V*)`, and let `u` be
a weak subsolution of `u' + A(t) u = 0`: `u'(t)(v) + A(t)(u t)(v) ≤ 0` whenever `ι v ≥ 0`, for
almost every `t`. If `w` is continuous on `[a, b]`, equal to `ι ∘ u` almost everywhere on
`(a, b)`, and `w a ≤ 0`, then `w t ≤ 0` for every `t ∈ [a, b]`. -/
theorem HasWeakLineDerivOn.nonpos_of_gelfandDual (hP : Continuous P) (hPb : ∀ v, ‖P v‖ ≤ ‖v‖)
    (hιP : ∀ v, ι (P v) = Lp.posPart (ι v)) {u : ℝ → V} {u' : ℝ → StrongDual ℝ V}
    {w : ℝ → Lp ℝ 2 ν}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, -β * ‖ι (P v)‖ ^ 2 ≤ A t v (P v))
    (hsub : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v → u' t v + A t (u t) v ≤ 0)
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a ≤ 0) {t : ℝ} (ht : t ∈ Icc a b) :
    w t ≤ 0 := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 (ht.1.trans ht.2)
  -- `t ↦ ‖u(t)⁺‖²` has weak derivative `2 u'(P u)`, which is integrable.
  have hd := h.norm_posPart_sq_of_gelfandDual hP hPb hιP hu hu'
  have hPu : MemLp (fun r ↦ P (u r)) 2 (volume.restrict (Ioo a b)) :=
    hu.mono (hP.comp_aestronglyMeasurable hu.aestronglyMeasurable)
      (Eventually.of_forall fun r ↦ hPb (u r))
  have hint : IntegrableOn (fun r ↦ 2 * u' r (P (u r))) (Ioo a b) :=
    (memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1 hu'
      hPu)).const_mul 2
  -- The function `y s = ‖(w s)⁺‖²` is continuous and vanishes at `a`.
  set y : ℝ → ℝ := fun s ↦ ‖Lp.posPart (w s)‖ ^ 2
  have hy : ContinuousOn y (Icc a b) := ((Lp.continuous_posPart.comp_continuousOn hw).norm).pow 2
  have hyae : (fun s ↦ ‖Lp.posPart (ι (u s))‖ ^ 2) =ᵐ[volume.restrict (Ioo a b)] y :=
    hae.fun_comp fun f ↦ ‖Lp.posPart f‖ ^ 2
  have hy₀ : y a = 0 := by simp [y, Lp.posPart_eq_zero_iff.2 h₀]
  -- Testing with `P u`: `2 u'(P u) ≤ -2 A(u)(P u) ≤ 2 β ‖ι (P u)‖² ≤ 2 β⁺ y`.
  have hpt : ∀ᵐ r ∂volume.restrict (Ioo a b), 2 * u' r (P (u r)) ≤ 2 * max β 0 * y r := by
    filter_upwards [hsub, hA, hae] with r hsubr hAr haer
    have hv := hsubr (P (u r)) (by rw [hιP]; exact Lp.posPart_nonneg _)
    have hAv := hAr (u r)
    rw [hιP, haer] at hAv
    have hβy : β * y r ≤ max β 0 * y r :=
      mul_le_mul_of_nonneg_right (le_max_left β 0) (by positivity)
    simp only [y] at hβy ⊢
    linarith
  -- Hence `y s ≤ 2 β⁺ ∫ₐˢ y`, and Grönwall's inequality forces `y = 0`.
  have hbound : ∀ s ∈ Icc a b, y s ≤ 0 + 2 * max β 0 * ∫ r in a..s, y r := by
    intro s hs
    have hid := hd.integral_eq_sub hint hy hyae ha hs
    have hsub' : Ioo a s ⊆ Ioo a b := Ioo_subset_Ioo_right hs.2
    have hmono : ∫ r in a..s, 2 * u' r (P (u r)) ≤ ∫ r in a..s, 2 * max β 0 * y r := by
      rw [intervalIntegral.integral_of_le hs.1, intervalIntegral.integral_of_le hs.1,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_mono_ae_restrict (hint.mono_set hsub')
        ((hy.integrableOn_Icc.mono_set (Ioo_subset_Icc_self.trans
          (Icc_subset_Icc_right hs.2))).const_mul _)
        (ae_restrict_of_ae_restrict_of_subset hsub' hpt)
    have hc := intervalIntegral.integral_const_mul (μ := volume) (a := a) (b := s)
      (2 * max β 0) y
    linarith
  have hyt := le_mul_exp_of_le_add_mul_integral hy
    (mul_nonneg zero_le_two (le_max_right β 0)) hbound t ht
  rw [zero_mul] at hyt
  have hpos : Lp.posPart (w t) = 0 := by
    have : ‖Lp.posPart (w t)‖ ^ 2 = 0 := le_antisymm hyt (by positivity)
    simpa using this
  exact Lp.posPart_eq_zero_iff.1 hpos

/-- **The weak comparison principle in a Gelfand triple over `L²`.** Under the hypotheses on
`ι`, `P` and `A` of `TauCeti.HasWeakLineDerivOn.nonpos_of_gelfandDual`, let `u₁` be a weak
subsolution and `u₂` a weak supersolution of `u' + A(t) u = f`: for almost every `t` and every `v`
with `ι v ≥ 0`, `u₁'(t)(v) + A(t)(u₁ t)(v) ≤ f(t)(v) ≤ u₂'(t)(v) + A(t)(u₂ t)(v)`. If their
continuous representatives satisfy `w₁ a ≤ w₂ a`, then `w₁ t ≤ w₂ t` for every `t ∈ [a, b]`. -/
theorem HasWeakLineDerivOn.le_of_gelfandDual (hP : Continuous P) (hPb : ∀ v, ‖P v‖ ≤ ‖v‖)
    (hιP : ∀ v, ι (P v) = Lp.posPart (ι v)) {f : ℝ → StrongDual ℝ V} {u₁ u₂ : ℝ → V}
    {u₁' u₂' : ℝ → StrongDual ℝ V} {w₁ w₂ : ℝ → Lp ℝ 2 ν}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo a b))) (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo a b)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo a b))) (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo a b)))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, -β * ‖ι (P v)‖ ^ 2 ≤ A t v (P v))
    (hsub : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v → u₁' t v + A t (u₁ t) v ≤ f t v)
    (hsup : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v → f t v ≤ u₂' t v + A t (u₂ t) v)
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hae₁ : (fun t ↦ ι (u₁ t)) =ᵐ[volume.restrict (Ioo a b)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc a b)) (hae₂ : (fun t ↦ ι (u₂ t)) =ᵐ[volume.restrict (Ioo a b)] w₂)
    (h₀ : w₁ a ≤ w₂ a) {t : ℝ} (ht : t ∈ Icc a b) :
    w₁ t ≤ w₂ t := by
  -- `u₁ - u₂` is a weak subsolution of the homogeneous equation with nonpositive initial value.
  have hd : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι ((u₁ - u₂) t))) (u₁' - u₂') 1 := by
    have e : (fun t ↦ ι.gelfandDual (ι ((u₁ - u₂) t))) =
        (fun t ↦ ι.gelfandDual (ι (u₁ t))) - fun t ↦ ι.gelfandDual (ι (u₂ t)) := by
      ext1 t
      simp only [Pi.sub_apply, map_sub]
    rw [e]
    exact h₁.sub h₂
  have hdsub : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v →
      (u₁' - u₂') t v + A t ((u₁ - u₂) t) v ≤ 0 := by
    filter_upwards [hsub, hsup] with r h₁r h₂r v hv
    simp only [Pi.sub_apply, map_sub, sub_apply]
    linarith [h₁r v hv, h₂r v hv]
  have hdae : (fun t ↦ ι ((u₁ - u₂) t)) =ᵐ[volume.restrict (Ioo a b)] w₁ - w₂ := by
    filter_upwards [hae₁, hae₂] with r e₁ e₂
    rw [Pi.sub_apply, map_sub, e₁, e₂, Pi.sub_apply]
  exact sub_nonpos.1 (hd.nonpos_of_gelfandDual hP hPb hιP (hu₁.sub hu₂) (hu₁'.sub hu₂') hA
    hdsub (hw₁.sub hw₂) hdae (sub_nonpos.2 h₀) ht)

end TauCeti
