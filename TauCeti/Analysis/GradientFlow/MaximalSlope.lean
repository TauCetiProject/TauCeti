/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.GradientFlow.UpperGradient
public import TauCeti.MeasureTheory.Function.CurveAction

/-!
# Curves of maximal slope

Let `φ : X → EReal` be an energy on a metric space with an upper gradient `g : X → [0, ∞]`, and let
`p, q` be conjugate exponents. Along every absolutely continuous curve `u`, the energy can drop by
at most the *dissipation*

`(1/p) ∫_s^t |u'|(r) ^ p dr + (1/q) ∫_s^t g (u r) ^ q dr`,

since `g` controls the rate of change of `φ ∘ u` by `g (u r) |u'|(r)`, and Young's inequality
bounds this product by the integrand above. A *`p`-curve of maximal slope* is a curve along which
the energy drops by at least the dissipation: the energy-dissipation inequality

`φ (u t) + (1/p) ∫_s^t |u'| ^ p + (1/q) ∫_s^t g (u r) ^ q ≤ φ (u s)`

holds for all `s ≤ t`. These curves are the metric replacement for the solutions of the gradient
flow `u' = -∇φ(u)` of a smooth energy on a Hilbert space, which are curves of maximal slope for the
descending slope (`TauCeti.isCurveOfMaximalSlope_of_hasGradientAt`).

When `g` is a strong upper gradient the two bounds meet. Along a curve of maximal slope the
energy identity holds: the energy drops by exactly the dissipation. Where the energy is finite,
the metric speed and the upper gradient are moreover related by `|u'| ^ p = g (u) ^ q` almost
everywhere, and the energy drop is the `p`-action. Conversely, the energy-dissipation inequality
between the endpoints of a compact interval already makes a curve of maximal slope on the whole
interval.

## Main definitions

* `TauCeti.dissipation p q g u s t`: the dissipation `(1/p) A_p + (1/q) ∫ g (u r) ^ q` of the
  curve `u` between `s` and `t`, where `A_p = TauCeti.curveAction p u s t`.
* `TauCeti.IsCurveOfMaximalSlope p q φ g u I`: `u` is a `p`-curve of maximal slope for `φ` with
  respect to `g` on the set of times `I`.

## Main results

* `TauCeti.IsStrongUpperGradient.le_add_dissipation`: along every absolutely continuous curve the
  energy drops by at most the dissipation.
* `TauCeti.IsCurveOfMaximalSlope.apply_eq_add_dissipation`: the **energy identity**
  `φ (u s) = φ (u t) + dissipation p q g u s t` for `s ≤ t`.
* `TauCeti.IsCurveOfMaximalSlope.ae_metricDerivative_rpow_eq`: `|u'| ^ p = g (u) ^ q` almost
  everywhere, and `TauCeti.IsCurveOfMaximalSlope.apply_eq_add_curveAction`: the energy drop is the
  `p`-action.
* `TauCeti.isCurveOfMaximalSlope_Icc_iff`: on `[a, b]` it suffices to check the
  energy-dissipation inequality between `a` and `b`.
* `TauCeti.isCurveOfMaximalSlope_of_hasGradientAt`: on a Hilbert space, a `C¹` solution of
  `u' = -∇f(u)` is a `2`-curve of maximal slope for the descending slope of `f`;
  `TauCeti.isCurveOfMaximalSlope_exp_neg_smul` is the flow `t ↦ e⁻ᵗ x` of `‖x‖² / 2`.

## Implementation notes

Ambrosio–Gigli–Savaré define a curve of maximal slope on an open interval as a locally absolutely
continuous curve such that `φ ∘ u` agrees almost everywhere with a nonincreasing function `ψ`
satisfying `ψ' ≤ -(1/p) |u'| ^ p - (1/q) g (u) ^ q` almost everywhere. Here the integrated
energy-dissipation inequality is required of `φ ∘ u` itself, on every pair of times of an
arbitrary set `I` (so `I` may be closed, open or unbounded), together with absolute continuity of
`u` between them. Ruling out a modification of `φ ∘ u` on a null set is a genuine restriction
only for weak upper gradients: for a strong upper gradient, Ambrosio–Gigli–Savaré show that
`φ ∘ u` is locally absolutely continuous along their curves of maximal slope.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 1, Section 1.3.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {p q : ℝ} {g : X → ℝ≥0∞} {u : ℝ → X}

/-- The *dissipation* of a curve `u` between `s` and `t` for exponents `p, q` and an upper gradient
`g`: `(1/p) ∫ |u'|(r) ^ p dr + (1/q) ∫ g (u r) ^ q dr` over the interval between `s` and `t`, with
the first term the `p`-action `TauCeti.curveAction p u s t`. -/
def dissipation (p q : ℝ) (g : X → ℝ≥0∞) (u : ℝ → X) (s t : ℝ) : ℝ≥0∞ :=
  curveAction p u s t / ENNReal.ofReal p + (∫⁻ r in Ι s t, g (u r) ^ q) / ENNReal.ofReal q

/-- The defining formula of the dissipation. -/
theorem dissipation_def (p q : ℝ) (g : X → ℝ≥0∞) (u : ℝ → X) (s t : ℝ) :
    dissipation p q g u s t =
      curveAction p u s t / ENNReal.ofReal p + (∫⁻ r in Ι s t, g (u r) ^ q) / ENNReal.ofReal q :=
  (rfl)

/-- The dissipation does not depend on the orientation of the interval. -/
theorem dissipation_comm (p q : ℝ) (g : X → ℝ≥0∞) (u : ℝ → X) (s t : ℝ) :
    dissipation p q g u s t = dissipation p q g u t s := by
  rw [dissipation_def, dissipation_def, curveAction_comm, uIoc_comm]

/-- The dissipation over a degenerate interval vanishes. -/
@[simp]
theorem dissipation_self (p q : ℝ) (g : X → ℝ≥0∞) (u : ℝ → X) (s : ℝ) :
    dissipation p q g u s s = 0 := by
  simp [dissipation_def]

/-- The dissipation is additive over adjacent intervals. -/
theorem dissipation_add (p q : ℝ) (g : X → ℝ≥0∞) (u : ℝ → X) {a b c : ℝ} (hb : b ∈ uIcc a c) :
    dissipation p q g u a b + dissipation p q g u b c = dissipation p q g u a c := by
  have hg : (∫⁻ r in Ι a b, g (u r) ^ q) + ∫⁻ r in Ι b c, g (u r) ^ q =
      ∫⁻ r in Ι a c, g (u r) ^ q := by
    rw [← uIoc_union_uIoc hb, lintegral_union measurableSet_uIoc]
    rcases mem_uIcc.1 hb with ⟨hab, hbc⟩ | ⟨hcb, hba⟩
    · rw [uIoc_of_le hab, uIoc_of_le hbc]
      exact Ioc_disjoint_Ioc_of_le le_rfl
    · rw [uIoc_of_ge hba, uIoc_of_ge hcb]
      exact (Ioc_disjoint_Ioc_of_le le_rfl).symm
  rw [dissipation_def, dissipation_def, dissipation_def, ← curveAction_add p u hb, ← hg,
    ENNReal.add_div, ENNReal.add_div]
  ring

end PseudoEMetricSpace

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ} {φ : X → EReal} {g : X → ℝ≥0∞}
  {u : ℝ → X} {I J : Set ℝ} {s t a b : ℝ}

/-- Along a curve absolutely continuous on `[s, t]`, the dissipation is the integral of
`|u'| ^ p / p + g (u) ^ q / q`. -/
theorem _root_.AbsolutelyContinuousOnInterval.dissipation_eq_lintegral
    (hpq : p.HolderConjugate q) (hu : AbsolutelyContinuousOnInterval u s t) :
    dissipation p q g u s t = ∫⁻ r in Ι s t,
      (metricDerivative u r ^ p / ENNReal.ofReal p + g (u r) ^ q / ENNReal.ofReal q) := by
  have hm : AEMeasurable (fun r ↦ metricDerivative u r ^ p) (volume.restrict (Ι s t)) :=
    hu.aemeasurable_metricDerivative.pow_const p
  simp_rw [div_eq_mul_inv]
  rw [lintegral_add_left' (hm.mul_const _), lintegral_mul_const'' _ hm,
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hpq.symm.pos).ne'),
    dissipation_def, curveAction_def, div_eq_mul_inv, div_eq_mul_inv]

/-- **Young's inequality along a curve**: the integral of `g (u r) |u'|(r)` is at most the
dissipation. -/
theorem _root_.AbsolutelyContinuousOnInterval.lintegral_mul_metricDerivative_le_dissipation
    (hpq : p.HolderConjugate q) (hu : AbsolutelyContinuousOnInterval u s t) :
    ∫⁻ r in Ι s t, g (u r) * metricDerivative u r ≤ dissipation p q g u s t := by
  rw [hu.dissipation_eq_lintegral hpq]
  exact lintegral_mono fun r ↦ (mul_comm _ _).trans_le (ENNReal.young_inequality _ _ hpq)

/-- Along an absolutely continuous curve, an energy with strong upper gradient `g` drops by at most
the dissipation: `φ (u s) ≤ φ (u t) + dissipation p q g u s t`. -/
theorem IsStrongUpperGradient.le_add_dissipation (hg : IsStrongUpperGradient φ g)
    (hpq : p.HolderConjugate q) (hu : AbsolutelyContinuousOnInterval u s t) :
    φ (u s) ≤ φ (u t) + dissipation p q g u s t :=
  (hg.le_add_lintegral hu).trans <| add_le_add_right
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hu.lintegral_mul_metricDerivative_le_dissipation hpq))
    _

/-- `u` is a *`p`-curve of maximal slope* for the energy `φ` with respect to the upper gradient `g`
on the set of times `I` if for all `s ≤ t` in `I` the curve is absolutely continuous on `[s, t]`
and satisfies the energy-dissipation inequality
`φ (u t) + (1/p) ∫_s^t |u'| ^ p + (1/q) ∫_s^t g (u r) ^ q ≤ φ (u s)`. Here `q` is meant to be the
conjugate exponent of `p`. -/
def IsCurveOfMaximalSlope (p q : ℝ) (φ : X → EReal) (g : X → ℝ≥0∞) (u : ℝ → X) (I : Set ℝ) :
    Prop :=
  ∀ ⦃s⦄, s ∈ I → ∀ ⦃t⦄, t ∈ I → s ≤ t →
    AbsolutelyContinuousOnInterval u s t ∧ φ (u t) + dissipation p q g u s t ≤ φ (u s)

/-- The defining property of a curve of maximal slope. -/
theorem isCurveOfMaximalSlope_iff : IsCurveOfMaximalSlope p q φ g u I ↔
    ∀ ⦃s⦄, s ∈ I → ∀ ⦃t⦄, t ∈ I → s ≤ t →
      AbsolutelyContinuousOnInterval u s t ∧ φ (u t) + dissipation p q g u s t ≤ φ (u s) :=
  Iff.rfl

namespace IsCurveOfMaximalSlope

/-- A curve of maximal slope is absolutely continuous between any two of its times. -/
theorem absolutelyContinuousOnInterval (h : IsCurveOfMaximalSlope p q φ g u I) (hs : s ∈ I)
    (ht : t ∈ I) : AbsolutelyContinuousOnInterval u s t := by
  rcases le_total s t with hst | hts
  · exact (h hs ht hst).1
  · exact (h ht hs hts).1.symm

/-- The **energy-dissipation inequality** along a curve of maximal slope. -/
theorem apply_add_dissipation_le (h : IsCurveOfMaximalSlope p q φ g u I) (hs : s ∈ I) (ht : t ∈ I)
    (hst : s ≤ t) : φ (u t) + dissipation p q g u s t ≤ φ (u s) :=
  (h hs ht hst).2

/-- A curve of maximal slope on `I` is a curve of maximal slope on every subset of `I`. -/
theorem mono (h : IsCurveOfMaximalSlope p q φ g u I) (hJI : J ⊆ I) :
    IsCurveOfMaximalSlope p q φ g u J := fun _ hs _ ht hst ↦ h (hJI hs) (hJI ht) hst

/-- The energy is nonincreasing along a curve of maximal slope. -/
theorem antitoneOn (h : IsCurveOfMaximalSlope p q φ g u I) : AntitoneOn (fun t ↦ φ (u t)) I :=
  fun _ hs _ ht hst ↦ le_trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
    (h.apply_add_dissipation_le hs ht hst)

/-- The **energy identity**: if `g` is a strong upper gradient, the energy drops along a curve of
maximal slope by exactly the dissipation, `φ (u s) = φ (u t) + dissipation p q g u s t`. -/
theorem apply_eq_add_dissipation (h : IsCurveOfMaximalSlope p q φ g u I)
    (hg : IsStrongUpperGradient φ g) (hpq : p.HolderConjugate q) (hs : s ∈ I) (ht : t ∈ I)
    (hst : s ≤ t) : φ (u s) = φ (u t) + dissipation p q g u s t :=
  le_antisymm (hg.le_add_dissipation hpq (h hs ht hst).1) (h.apply_add_dissipation_le hs ht hst)

/-- Along a curve of maximal slope for a strong upper gradient `g` and an energy finite at `u s`
and `u t`, the metric speed and the upper gradient satisfy `|u'| ^ p = g (u) ^ q` almost everywhere
between `s` and `t`. -/
theorem ae_metricDerivative_rpow_eq (h : IsCurveOfMaximalSlope p q φ g u I)
    (hg : IsStrongUpperGradient φ g) (hpq : p.HolderConjugate q) (hs : s ∈ I) (ht : t ∈ I)
    (hst : s ≤ t) (hφs : φ (u s) ≠ ⊤) (hφt : φ (u t) ≠ ⊥)
    (hgu : AEMeasurable (fun r ↦ g (u r)) (volume.restrict (Ι s t))) :
    ∀ᵐ r ∂volume.restrict (Ι s t), metricDerivative u r ^ p = g (u r) ^ q := by
  have hu := (h hs ht hst).1
  have heq := h.apply_eq_add_dissipation hg hpq hs ht hst
  set D := dissipation p q g u s t
  set F := ∫⁻ r in Ι s t, g (u r) * metricDerivative u r
  -- The energy at `u t` and the dissipation are finite.
  have hφt' : φ (u t) ≠ ⊤ := fun h' ↦ hφs <| by
    rw [heq, h', EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
  have hD : D ≠ ∞ := fun h' ↦ hφs <| by
    rw [heq, h', EReal.coe_ennreal_top, EReal.add_top_of_ne_bot hφt]
  have hFD : F ≤ D := hu.lintegral_mul_metricDerivative_le_dissipation hpq
  have hF : F ≠ ∞ := ne_top_of_le_ne_top hD hFD
  -- The upper-gradient bound forces the integral of `g (u r) |u'|(r)` to be the dissipation.
  have hDF : D ≤ F := by
    have h₁ : φ (u s) ≤ φ (u t) + F := hg.le_add_lintegral hu
    lift φ (u t) to ℝ using ⟨hφt', hφt⟩ with y
    rw [heq, ← EReal.coe_ennreal_toReal hD, ← EReal.coe_ennreal_toReal hF, ← EReal.coe_add,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at h₁
    exact (ENNReal.toReal_le_toReal hD hF).1 (by linarith)
  -- Hence Young's inequality is an equality almost everywhere.
  have hm : AEMeasurable (fun r ↦ metricDerivative u r ^ p / ENNReal.ofReal p +
      g (u r) ^ q / ENNReal.ofReal q) (volume.restrict (Ι s t)) :=
    (hu.aemeasurable_metricDerivative.pow_const p).div_const _ |>.add
      ((hgu.pow_const q).div_const _)
  have hY := ae_eq_of_ae_le_of_lintegral_le
    (ae_of_all _ fun r ↦ (mul_comm _ _).trans_le (ENNReal.young_inequality (metricDerivative u r)
      (g (u r)) hpq)) hF hm (by rwa [← hu.dissipation_eq_lintegral hpq])
  -- Off a null set the speed and the upper gradient are finite.
  have hDq : (∫⁻ r in Ι s t, g (u r) ^ q) ≠ ∞ := fun htop ↦ hD <| top_le_iff.1 <| by
    rw [← ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, ← htop]
    exact le_add_self
  filter_upwards [hY, ae_lt_top' hu.aemeasurable_metricDerivative
      hu.lintegral_metricDerivative_lt_top.ne, ae_lt_top' (hgu.pow_const q) hDq]
    with r hr hmr hgr
  have hgr' : g (u r) ≠ ∞ := fun h' ↦ by
    simp [h', ENNReal.top_rpow_of_pos hpq.symm.pos] at hgr
  rcases (ENNReal.young_inequality_eq_iff _ _ hpq).1 ((mul_comm _ _).trans hr) with
    ⟨h', -⟩ | ⟨-, h'⟩ | h'
  · exact absurd h' hmr.ne
  · exact absurd h' hgr'
  · exact h'

/-- The **energy identity** in terms of the action: along a curve of maximal slope for a strong
upper gradient, the energy drops by exactly the `p`-action, `φ (u s) = φ (u t) + A_p(u)`. -/
theorem apply_eq_add_curveAction (h : IsCurveOfMaximalSlope p q φ g u I)
    (hg : IsStrongUpperGradient φ g) (hpq : p.HolderConjugate q) (hs : s ∈ I) (ht : t ∈ I)
    (hst : s ≤ t) (hφs : φ (u s) ≠ ⊤) (hφt : φ (u t) ≠ ⊥)
    (hgu : AEMeasurable (fun r ↦ g (u r)) (volume.restrict (Ι s t))) :
    φ (u s) = φ (u t) + curveAction p u s t := by
  have hA : curveAction p u s t = ∫⁻ r in Ι s t, g (u r) ^ q :=
    (curveAction_def p u s t).trans <|
      lintegral_congr_ae (h.ae_metricDerivative_rpow_eq hg hpq hs ht hst hφs hφt hgu)
  rw [h.apply_eq_add_dissipation hg hpq hs ht hst, dissipation_def, ← hA, div_eq_mul_inv,
    div_eq_mul_inv, ← mul_add, hpq.inv_add_inv_ennreal, mul_one]

/-- The **energy identity** in terms of the upper gradient: along a curve of maximal slope for a
strong upper gradient, `φ (u s) = φ (u t) + ∫_s^t g (u r) ^ q dr`. -/
theorem apply_eq_add_lintegral_rpow (h : IsCurveOfMaximalSlope p q φ g u I)
    (hg : IsStrongUpperGradient φ g) (hpq : p.HolderConjugate q) (hs : s ∈ I) (ht : t ∈ I)
    (hst : s ≤ t) (hφs : φ (u s) ≠ ⊤) (hφt : φ (u t) ≠ ⊥)
    (hgu : AEMeasurable (fun r ↦ g (u r)) (volume.restrict (Ι s t))) :
    φ (u s) = φ (u t) + ∫⁻ r in Ι s t, g (u r) ^ q := by
  rw [h.apply_eq_add_curveAction hg hpq hs ht hst hφs hφt hgu, curveAction_def,
    lintegral_congr_ae (h.ae_metricDerivative_rpow_eq hg hpq hs ht hst hφs hφt hgu)]

end IsCurveOfMaximalSlope

/-- For a strong upper gradient `g`, a curve absolutely continuous on `[a, b]` is a curve of
maximal slope on `[a, b]` as soon as the energy-dissipation inequality holds between `a` and `b`,
provided `φ (u a) < ∞` and `φ (u b) > -∞`. -/
theorem isCurveOfMaximalSlope_Icc_iff (hg : IsStrongUpperGradient φ g)
    (hpq : p.HolderConjugate q) (hab : a ≤ b) (hu : AbsolutelyContinuousOnInterval u a b)
    (ha : φ (u a) ≠ ⊤) (hb : φ (u b) ≠ ⊥) :
    IsCurveOfMaximalSlope p q φ g u (Icc a b) ↔
      φ (u b) + dissipation p q g u a b ≤ φ (u a) := by
  refine ⟨fun h ↦ h.apply_add_dissipation_le ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab,
    fun h s hs t ht hst ↦ ?_⟩
  have hsub : ∀ ⦃x y⦄, x ∈ Icc a b → y ∈ Icc a b → AbsolutelyContinuousOnInterval u x y :=
    fun x y hx hy ↦ hu.mono (uIcc_subset_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy))
  refine ⟨hsub hs ht, ?_⟩
  -- The energy-dissipation inequality is trivial if `φ (u s) = ⊤` or `φ (u t) = ⊥`.
  rcases eq_or_ne (φ (u s)) ⊤ with hs' | hs'
  · exact hs' ▸ le_top
  rcases eq_or_ne (φ (u t)) ⊥ with ht' | ht'
  · rw [ht', EReal.bot_add]
    exact bot_le
  -- The upper-gradient bounds on `[a, s]` and `[t, b]`.
  have h₁ := hg.le_add_dissipation hpq (hsub ⟨le_rfl, hab⟩ hs)
  have h₃ := hg.le_add_dissipation hpq (hsub ht ⟨hab, le_rfl⟩)
  have hD : dissipation p q g u a s + dissipation p q g u s t + dissipation p q g u t b =
      dissipation p q g u a b := by
    rw [dissipation_add p q g u (mem_uIcc_of_le hs.1 hst),
      dissipation_add p q g u (mem_uIcc_of_le (hs.1.trans hst) ht.2)]
  -- All energies involved and the dissipations are finite.
  have hDab : dissipation p q g u a b ≠ ∞ := by
    intro h'
    rw [h', EReal.coe_ennreal_top, EReal.add_top_of_ne_bot hb, top_le_iff] at h
    exact ha h
  have hDas : dissipation p q g u a s ≠ ∞ :=
    ne_top_of_le_ne_top hDab (hD ▸ le_self_add.trans le_self_add)
  have hDst : dissipation p q g u s t ≠ ∞ :=
    ne_top_of_le_ne_top hDab (hD ▸ le_add_self.trans le_self_add)
  have hDtb : dissipation p q g u t b ≠ ∞ := ne_top_of_le_ne_top hDab (hD ▸ le_add_self)
  have hsum : (dissipation p q g u a s).toReal + (dissipation p q g u s t).toReal +
      (dissipation p q g u t b).toReal = (dissipation p q g u a b).toReal := by
    rw [← hD, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hDas, hDst⟩) hDtb,
      ENNReal.toReal_add hDas hDst]
  have ha' : φ (u a) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.add_ne_bot_iff.2 ⟨hb, EReal.coe_ennreal_ne_bot _⟩) h
  have hb' : φ (u b) ≠ ⊤ :=
    ne_top_of_le_ne_top ha ((le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)).trans h)
  rw [← EReal.coe_ennreal_toReal hDab] at h
  rw [← EReal.coe_ennreal_toReal hDas] at h₁
  rw [← EReal.coe_ennreal_toReal hDtb] at h₃
  rw [← EReal.coe_ennreal_toReal hDst]
  lift φ (u a) to ℝ using ⟨ha, ha'⟩ with ra
  lift φ (u b) to ℝ using ⟨hb', hb⟩ with rb
  have hs'' : φ (u s) ≠ ⊥ := fun h' ↦ by
    rw [h', EReal.bot_add, le_bot_iff] at h₁
    exact EReal.coe_ne_bot _ h₁
  have ht'' : φ (u t) ≠ ⊤ := ne_top_of_le_ne_top (EReal.add_ne_top (EReal.coe_ne_top _)
    (EReal.coe_ne_top _)) h₃
  lift φ (u s) to ℝ using ⟨hs', hs''⟩ with rs
  lift φ (u t) to ℝ using ⟨ht'', ht'⟩ with rt
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h h₁ h₃ ⊢
  linarith

end PseudoMetricSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On a Hilbert space, a solution `u' = -∇f(u)` of the gradient flow of `f` with continuous
velocity is a `2`-curve of maximal slope for `f` with respect to its descending slope: along it the
energy drops at rate `‖∇f(u)‖² = (1/2) |u'| ^ 2 + (1/2) |∂f| (u) ^ 2`. -/
theorem isCurveOfMaximalSlope_of_hasGradientAt {f : E → ℝ} {u G : ℝ → E} {I : Set ℝ}
    [I.OrdConnected] (hf : ∀ t ∈ I, HasGradientAt f (G t) (u t))
    (hu : ∀ t ∈ I, HasDerivAt u (-G t) t) (hG : ContinuousOn G I) :
    IsCurveOfMaximalSlope 2 2 (fun x ↦ (f x : EReal)) (descendingSlope fun x ↦ (f x : EReal)) u
      I := by
  intro s hs t ht hst
  have hsub : uIcc s t ⊆ I := uIcc_of_le hst ▸ Set.OrdConnected.out ‹_› hs ht
  -- The curve is Lipschitz on `[s, t]`, since its velocity is bounded there.
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn (hG.mono hsub)
  have hAC : AbsolutelyContinuousOnInterval u s t :=
    LipschitzOnWith.absolutelyContinuousOnInterval (K := C.toNNReal) <|
      (convex_uIcc s t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun r hr ↦ (hu r (hsub hr)).hasDerivWithinAt) fun r hr ↦ by
          rw [nnnorm_neg, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
          exact (hC r hr).trans (le_max_left _ _)
  refine ⟨hAC, ?_⟩
  -- The energy decreases at rate `‖G‖²`.
  have hderiv : ∀ r ∈ uIcc s t, HasDerivAt (fun r ↦ f (u r)) (-‖G r‖ ^ 2) r := fun r hr ↦ by
    refine ((hf r (hsub hr)).hasFDerivAt.comp_hasDerivAt r (hu r (hsub hr))).congr_deriv ?_
    simp [InnerProductSpace.toDual_apply_apply]
  have hcont : ContinuousOn (fun r ↦ ‖G r‖ ^ 2) (uIcc s t) := ((hG.mono hsub).norm.pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.neg.intervalIntegrable
  rw [intervalIntegral.integral_neg] at hFTC
  -- The dissipation is `∫ ‖G‖²`.
  have hdiss : dissipation 2 2 (descendingSlope fun x ↦ (f x : EReal)) u s t =
      ENNReal.ofReal (∫ r in s..t, ‖G r‖ ^ 2) := by
    have hint : IntegrableOn (fun r ↦ ‖G r‖ ^ 2) (Ioc s t) :=
      (hcont.integrableOn_compact isCompact_uIcc).mono_set (uIcc_of_le hst ▸ Ioc_subset_Icc_self)
    rw [hAC.dissipation_eq_lintegral Real.HolderConjugate.two_two,
      intervalIntegral.integral_of_le hst, ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun _ ↦ by positivity), ← uIoc_of_le hst]
    refine setLIntegral_congr_fun measurableSet_uIoc fun r hr ↦ ?_
    have hr' := hsub (uIoc_subset_uIcc hr)
    rw [(hu r hr').metricDerivative_eq, (hf r hr').hasFDerivAt.descendingSlope_eq,
      LinearIsometryEquiv.enorm_map, enorm_neg, div_eq_mul_inv, ← mul_add,
      Real.HolderConjugate.two_two.inv_add_inv_ennreal, mul_one, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
    norm_cast
  have hnonneg : 0 ≤ ∫ r in s..t, ‖G r‖ ^ 2 :=
    intervalIntegral.integral_nonneg hst fun _ _ ↦ by positivity
  rw [hdiss, EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- The flow `t ↦ e⁻ᵗ x` of the energy `‖x‖² / 2` on a Hilbert space is a `2`-curve of maximal
slope for the descending slope of the energy. -/
theorem isCurveOfMaximalSlope_exp_neg_smul (x : E) :
    IsCurveOfMaximalSlope 2 2 (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal))
      (descendingSlope fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) (fun t ↦ Real.exp (-t) • x) univ := by
  refine isCurveOfMaximalSlope_of_hasGradientAt (G := fun t ↦ Real.exp (-t) • x)
    (fun t _ ↦ ?_) (fun t _ ↦ ?_) (by fun_prop)
  · rw [hasGradientAt_iff_hasFDerivAt]
    convert (hasStrictFDerivAt_norm_sq (Real.exp (-t) • x)).hasFDerivAt.mul_const (2⁻¹ : ℝ)
      using 1
    · ext y
      simp [div_eq_mul_inv]
    · ext v
      simp [InnerProductSpace.toDual_apply_apply]
  · simpa using ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const x

end InnerProductSpace

end TauCeti
