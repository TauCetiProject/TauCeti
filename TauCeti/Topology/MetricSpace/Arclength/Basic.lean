/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import TauCeti.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Arclength factorization of rectifiable metric curves

A continuous curve of bounded variation on a compact real interval factors through cumulative
variation. The resulting curve is 1-Lipschitz on its length interval and has variation equal to
the parameter difference on every subinterval. The construction collapses constant pieces;
it does not require an inverse to cumulative variation. It also applies to constant curves,
whose length interval is a singleton.
For curves injective on the interior of their parameter interval, cumulative variation induces
an increasing homeomorphism between the original parameter interval and the length interval.
This includes injective arcs and simple closed curves.
On its length interval, the factor is Mathlib's `naturalParameterization`.

We use Mathlib's `variationOnFromTo`, its continuity criterion, and the exact variation formula
for composition with a monotone map. Length is always `eVariationOn`; its conversion to a real
parameter is justified by the bounded-variation hypothesis.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows*, second edition, §1.1
  (arclength parametrization of metric curves).
-/

public section

open Set
open scoped ENNReal

/-- The natural parameterization of a curve of locally bounded variation on `s` recovers the
curve at the cumulative variation of each point of `s`. -/
theorem LocallyBoundedVariationOn.naturalParameterization_variationOnFromTo {α E : Type*}
    [LinearOrder α] [TopologicalSpace E] [WeakEMetricSpace E] {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    naturalParameterization f s a (variationOnFromTo f s a b) = f b :=
  edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf ha hb)

/-- The natural parameterization of a curve of locally bounded variation has the same trace
when restricted to the set of cumulative variations from a base point. -/
@[simp]
theorem LocallyBoundedVariationOn.image_naturalParameterization {α E : Type*}
    [LinearOrder α] [TopologicalSpace E] [WeakEMetricSpace E] {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (ha : a ∈ s) :
    naturalParameterization f s a '' (variationOnFromTo f s a '' s) = f '' s := by
  rw [image_image]
  exact image_congr fun x hx ↦ hf.naturalParameterization_variationOnFromTo ha hx

/-- The natural parameterization of a curve of locally bounded variation on `s` starts, at
parameter `0`, at the value of the curve at the base point. -/
theorem LocallyBoundedVariationOn.naturalParameterization_zero {α E : Type*}
    [LinearOrder α] [TopologicalSpace E] [WeakEMetricSpace E] {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (ha : a ∈ s) :
    naturalParameterization f s a 0 = f a := by
  simpa only [variationOnFromTo.self] using hf.naturalParameterization_variationOnFromTo ha ha

namespace BoundedVariationOn

variable {X : Type*} [MetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- The natural parameterization of a curve of bounded variation on `[a, b]` ends, at the length
`L` of the curve, at `γ b`. -/
theorem naturalParameterization_toReal_eVariationOn (hγ : BoundedVariationOn γ (Icc a b))
    (hab : a ≤ b) :
    naturalParameterization γ (Icc a b) a (eVariationOn γ (Icc a b)).toReal = γ b := by
  simpa only [variationOnFromTo.eq_of_le _ _ hab, inter_self] using
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab)
      (right_mem_Icc.2 hab)

/-- If a curve has equal endpoint values `γ a = γ b` on `[a, b]`, then its natural
parameterization takes equal values at `0` and at the length of the curve. -/
theorem naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn
    (hclosed : γ a = γ b) :
    naturalParameterization γ (Icc a b) a 0 =
      naturalParameterization γ (Icc a b) a (eVariationOn γ (Icc a b)).toReal := by
  by_cases hγ : BoundedVariationOn γ (Icc a b)
  · by_cases hab : a ≤ b
    · exact (hγ.locallyBoundedVariationOn.naturalParameterization_zero
        (left_mem_Icc.mpr hab)).trans
        (hclosed.trans (hγ.naturalParameterization_toReal_eVariationOn hab).symm)
    · simp [Icc_eq_empty hab]
  · simp [not_not.mp hγ]

/-- Cumulative variation maps the parameter interval of a continuous rectifiable curve onto its
length interval. -/
theorem image_variationOnFromTo_Icc (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) :
    variationOnFromTo γ (Icc a b) a '' Icc a b = Icc 0 (eVariationOn γ (Icc a b)).toReal := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  rw [ContinuousOn.image_Icc_of_monotoneOn hab
      (fun t ht ↦ (hγ.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hcont t ht))
      (variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn ha),
    variationOnFromTo.self, variationOnFromTo.eq_of_le _ _ hab, inter_self]

/-- A continuous rectifiable curve factors through a 1-Lipschitz curve on its length interval.
The factor has exactly the parameter difference as variation on every subinterval, including
when the original curve has pauses or zero length. Values of the factor outside its length
interval are unspecified. -/
theorem exists_arclength_factorization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) :
    ∃ g : ℝ → X,
      LipschitzOnWith 1 g (Icc 0 (eVariationOn γ (Icc a b)).toReal) ∧
      EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b) ∧
      ∀ u ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal,
        ∀ v ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal, u ≤ v →
          eVariationOn g (Icc u v) = ENNReal.ofReal (v - u) := by
  rcases lt_or_ge b a with hba | hab
  · have h0 : eVariationOn γ (Icc a b) = 0 := by simp [Icc_eq_empty hba.not_ge]
    refine ⟨fun _ ↦ γ 0, ?_, fun t ht ↦ ?_, fun u hu v hv _ ↦ ?_⟩
    · exact (LipschitzWith.const _).weaken zero_le_one |>.lipschitzOnWith
    · simp [Icc_eq_empty hba.not_ge] at ht
    · rw [h0, ENNReal.toReal_zero, Icc_self, mem_singleton_iff] at hu hv
      subst hu hv
      simp
  let s := variationOnFromTo γ (Icc a b) a
  let L := (eVariationOn γ (Icc a b)).toReal
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hs : ContinuousOn s (Icc a b) := fun t ht ↦
    (hγ.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hcont t ht)
  have hm : MonotoneOn s (Icc a b) :=
    variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn ha
  have himage : s '' Icc a b = Icc 0 L := hγ.image_variationOnFromTo_Icc hcont hab
  -- The general variation factorization collapses each constant fibre.
  obtain ⟨g, hg, hfactor⟩ :=
    hγ.locallyBoundedVariationOn.exists_lipschitzOnWith_comp_variationOnFromTo_eqOn ha
  rw [himage] at hg
  -- A monotone right inverse is used only to compare variation on subintervals.
  let ψ := s.invFunOn (Icc a b)
  have hsurj : SurjOn s (Icc a b) (Icc 0 L) := by
    rw [SurjOn, himage]
  have hψs : MapsTo ψ (Icc 0 L) (Icc a b) := hsurj.mapsTo_invFunOn
  have hsψ : RightInvOn ψ s (Icc 0 L) := hsurj.rightInvOn_invFunOn
  have hψmono : MonotoneOn ψ (Icc 0 L) :=
    Function.monotoneOn_of_rightInvOn_of_mapsTo hm hsψ hψs
  refine ⟨g, hg, hfactor, ?_⟩
  intro u hu v hv huv
  have hpu := hψs hu
  have hpv := hψs hv
  have hp := hψmono hu hv huv
  have hsub : Icc (ψ u) (ψ v) ⊆ Icc a b := Icc_subset_Icc hpu.1 hpv.2
  have hsmall : s '' Icc (ψ u) (ψ v) = Icc u v := by
    rw [(hs.mono hsub).image_Icc_of_monotoneOn hp (hm.mono hsub), hsψ hu, hsψ hv]
  have hvar : eVariationOn γ (Icc (ψ u) (ψ v)) = eVariationOn g (Icc u v) := by
    rw [← hsmall, ← eVariationOn.comp_eq_of_monotoneOn g s (hm.mono hsub)]
    exact (eVariationOn.eq_of_eqOn (hfactor.mono hsub)).symm
  have hdiff : v - u = (eVariationOn γ (Icc (ψ u) (ψ v))).toReal := by
    calc
      v - u = s (ψ v) - s (ψ u) := by rw [hsψ hu, hsψ hv]
      _ = variationOnFromTo γ (Icc a b) (ψ u) (ψ v) :=
        variationOnFromTo.sub_right hγ.locallyBoundedVariationOn ha hpv hpu
      _ = (eVariationOn γ (Icc (ψ u) (ψ v))).toReal := by
        rw [variationOnFromTo.eq_of_le _ _ hp, inter_eq_right.mpr hsub]
  rw [hdiff, ENNReal.ofReal_toReal (hγ.mono hsub), hvar]

/-- The arclength factor of a continuous rectifiable curve is unique on its length interval:
a curve `g` with `g ∘ variationOnFromTo γ (Icc a b) a = γ` on `[a, b]` agrees there with the
natural parameterization. -/
theorem eqOn_naturalParameterization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) {g : ℝ → X}
    (hg : EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b)) :
    EqOn g (naturalParameterization γ (Icc a b) a) (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
  rw [← hγ.image_variationOnFromTo_Icc hcont hab]
  rintro _ ⟨t, ht, rfl⟩
  exact (hg ht).trans <| .symm <|
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht

/-- The natural parameterization of a continuous rectifiable curve traces, on its length
interval, the same set as the curve on its parameter interval. -/
theorem image_naturalParameterization_Icc (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) :
    naturalParameterization γ (Icc a b) a '' Icc 0 (eVariationOn γ (Icc a b)).toReal =
      γ '' Icc a b := by
  rw [← hγ.image_variationOnFromTo_Icc hcont hab]
  exact hγ.locallyBoundedVariationOn.image_naturalParameterization (left_mem_Icc.2 hab)

/-- The natural parameterization of a continuous rectifiable curve has unit speed on its length
interval. -/
theorem hasUnitSpeedOn_naturalParameterization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) :
    HasUnitSpeedOn (naturalParameterization γ (Icc a b) a)
      (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
  rcases lt_or_ge b a with hba | hab
  · have h0 : eVariationOn γ (Icc a b) = 0 := by simp [Icc_eq_empty hba.not_ge]
    rw [h0, ENNReal.toReal_zero]
    intro x hx y hy
    rw [Icc_self, mem_singleton_iff] at hx hy
    subst hx hy
    simp
  rw [← hγ.image_variationOnFromTo_Icc hcont hab]
  exact has_unit_speed_naturalParameterization γ hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab)

/-- The natural parameterization of a continuous rectifiable curve has, on its length interval,
the same length as the curve. -/
theorem eVariationOn_naturalParameterization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) :
    eVariationOn (naturalParameterization γ (Icc a b) a)
      (Icc 0 (eVariationOn γ (Icc a b)).toReal) = eVariationOn γ (Icc a b) := by
  have h := hγ.hasUnitSpeedOn_naturalParameterization hcont
    (left_mem_Icc.2 ENNReal.toReal_nonneg) (right_mem_Icc.2 ENNReal.toReal_nonneg)
  rwa [inter_self, NNReal.coe_one, one_mul, sub_zero, ENNReal.ofReal_toReal hγ] at h

/-- For a continuous rectifiable curve injective on the interior of its parameter interval,
cumulative variation is an increasing homeomorphism onto the length interval. The endpoint
values may coincide, and the singleton interval case is included. -/
theorem exists_arclength_homeomorph (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) (hab : a ≤ b) :
    ∃ e : Icc a b ≃ₜ Icc 0 (eVariationOn γ (Icc a b)).toReal,
      StrictMono e ∧ ∀ t, (e t : ℝ) = variationOnFromTo γ (Icc a b) a t := by
  let s := variationOnFromTo γ (Icc a b) a
  let L := (eVariationOn γ (Icc a b)).toReal
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hm : StrictMonoOn s (Icc a b) :=
    hγ.locallyBoundedVariationOn.strictMonoOn_variationOnFromTo_of_injOn_Ioo ha hinj
  have himage : s '' Icc a b = Icc 0 L := hγ.image_variationOnFromTo_Icc hcont hab
  let S : Icc a b → Icc 0 L := fun t ↦ ⟨s t, himage ▸ mem_image_of_mem s t.property⟩
  have hS : StrictMono S := fun t u htu ↦ hm t.property u.property htu
  have hsurj : Function.Surjective S := by
    intro u
    obtain ⟨t, ht, htu⟩ := (himage.symm ▸ u.property : (u : ℝ) ∈ s '' Icc a b)
    exact ⟨⟨t, ht⟩, Subtype.ext htu⟩
  let e := hS.orderIsoOfSurjective S hsurj
  refine ⟨e.toHomeomorph, e.strictMono, ?_⟩
  intro t
  rw [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]

/-- A rectifiable curve injective on the open interval `(a, b)` with `a < b` has strictly positive
total variation. -/
theorem toReal_eVariationOn_pos_of_injOn_Ioo (hγ : BoundedVariationOn γ (Icc a b))
    (hab : a < b) (hinj : InjOn γ (Ioo a b)) :
    0 < (eVariationOn γ (Icc a b)).toReal := by
  have hm := hγ.locallyBoundedVariationOn.strictMonoOn_variationOnFromTo_of_injOn_Ioo
    (left_mem_Icc.mpr hab.le) hinj
  simpa only [variationOnFromTo.self, variationOnFromTo.eq_of_le _ _ hab.le, inter_self] using
    hm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab

/-- Composing a continuous rectifiable curve with an increasing continuous map onto `[a, b]`
leaves its natural parameterization unchanged on the length interval. -/
theorem eqOn_naturalParameterization_comp_of_monotoneOn (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) {c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d)
    (hφ : ContinuousOn φ (Icc c d)) (hφm : MonotoneOn φ (Icc c d))
    (hφc : φ c = a) (hφd : φ d = b) :
    EqOn (naturalParameterization (γ ∘ φ) (Icc c d) c) (naturalParameterization γ (Icc a b) a)
      (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
  have hab : a ≤ b := hφc ▸ hφd ▸ hφm (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have himage : φ '' Icc c d = Icc a b := by
    rw [hφ.image_Icc_of_monotoneOn hcd hφm, hφc, hφd]
  have hL : eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ hφm, himage]
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) := by rwa [BoundedVariationOn, hL]
  have hcontφ : ContinuousOn (γ ∘ φ) (Icc c d) :=
    hcont.comp hφ (himage ▸ mapsTo_image φ (Icc c d))
  rw [← hL]
  refine (hγφ.eqOn_naturalParameterization hcontφ hcd fun t ht ↦ ?_).symm
  have hφt : φ t ∈ Icc a b := himage ▸ mem_image_of_mem φ ht
  rw [Function.comp_apply,
    variationOnFromTo.comp_eq_of_monotoneOn γ φ hφm (left_mem_Icc.2 hcd) ht, himage, hφc,
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) hφt,
    Function.comp_apply]

/-- Composing a continuous rectifiable curve with a decreasing continuous map onto `[a, b]`
reverses its natural parameterization on the length interval. -/
theorem eqOn_naturalParameterization_comp_of_antitoneOn (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) {c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d)
    (hφ : ContinuousOn φ (Icc c d)) (hφm : AntitoneOn φ (Icc c d))
    (hφc : φ c = b) (hφd : φ d = a) :
    EqOn (naturalParameterization (γ ∘ φ) (Icc c d) c)
      (fun u ↦ naturalParameterization γ (Icc a b) a ((eVariationOn γ (Icc a b)).toReal - u))
      (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
  have hab : a ≤ b := hφc ▸ hφd ▸ hφm (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have himage : φ '' Icc c d = Icc a b := by
    rw [hφ.image_Icc_of_antitoneOn hcd hφm, hφc, hφd]
  have hL : eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
    rw [eVariationOn.comp_eq_of_antitoneOn _ _ hφm, himage]
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) := by rwa [BoundedVariationOn, hL]
  have hcontφ : ContinuousOn (γ ∘ φ) (Icc c d) :=
    hcont.comp hφ (himage ▸ mapsTo_image φ (Icc c d))
  rw [← hL]
  refine (hγφ.eqOn_naturalParameterization hcontφ hcd fun t ht ↦ ?_).symm
  have hφt : φ t ∈ Icc a b := himage ▸ mem_image_of_mem φ ht
  have hvar : variationOnFromTo (γ ∘ φ) (Icc c d) c t =
      (eVariationOn γ (Icc a b)).toReal - variationOnFromTo γ (Icc a b) a (φ t) := by
    rw [variationOnFromTo.comp_eq_of_antitoneOn γ φ hφm (left_mem_Icc.2 hcd) ht, himage, hφc,
      ← variationOnFromTo.sub_right hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab)
        (right_mem_Icc.2 hab) hφt, variationOnFromTo.eq_of_le _ _ hab, inter_self]
  rw [Function.comp_apply, hL, hvar, sub_sub_cancel]
  exact hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo
    (left_mem_Icc.2 hab) hφt

end BoundedVariationOn

namespace MonotoneOn

/-- If `γ = g ∘ s` on `[a, b]` with `s` monotone, then the values of `γ` on the intervals where
`s` is constant form a countable set: each such interval contains a rational parameter. For
example, the values a curve takes while its cumulative arclength pauses form a countable set. -/
theorem countable_setOf_eq_comp {X : Type*} {γ g : ℝ → X} {s : ℝ → ℝ} {a b : ℝ}
    (hm : MonotoneOn s (Icc a b)) (hfac : EqOn (g ∘ s) γ (Icc a b)) :
    {y | ∃ t ∈ Icc a b, ∃ t' ∈ Icc a b, t < t' ∧ s t = s t' ∧ γ t = y}.Countable := by
  refine (countable_range fun q : ℚ ↦ γ q).mono ?_
  rintro _ ⟨t, ht, t', ht', htt', hst, rfl⟩
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn htt'
  have hqI : (q : ℝ) ∈ Icc a b := ⟨ht.1.trans hq.le, hq'.le.trans ht'.2⟩
  have hsq : s q = s t := le_antisymm (hst ▸ hm hqI ht' hq'.le) (hm ht hqI hq.le)
  exact ⟨q, (hfac hqI).symm.trans ((congrArg g hsq).trans (hfac ht))⟩

end MonotoneOn
