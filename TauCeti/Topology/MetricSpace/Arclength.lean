/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
For injective arcs, cumulative variation induces an increasing homeomorphism between the
original parameter interval and the length interval.

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

namespace BoundedVariationOn

variable {X : Type*} [MetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- A continuous rectifiable curve factors through a 1-Lipschitz curve on its length interval.
The factor has exactly the parameter difference as variation on every subinterval, including
when the original curve has pauses or zero length. Values of the factor outside its length
interval are unspecified. -/
theorem exists_arclength_factorization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) :
    ∃ g : ℝ → X,
      LipschitzOnWith 1 g (Icc 0 (eVariationOn γ (Icc a b)).toReal) ∧
      EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b) ∧
      ∀ u ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal,
        ∀ v ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal, u ≤ v →
          eVariationOn g (Icc u v) = ENNReal.ofReal (v - u) := by
  let s := variationOnFromTo γ (Icc a b) a
  let L := (eVariationOn γ (Icc a b)).toReal
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hs : ContinuousOn s (Icc a b) := fun t ht ↦
    (hγ.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hcont t ht)
  have hm : MonotoneOn s (Icc a b) :=
    variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn ha
  have hsa : s a = 0 := variationOnFromTo.self _ _ _
  have hsb : s b = L := by
    simp only [s, variationOnFromTo.eq_of_le _ _ hab, inter_self, L]
  have himage : s '' Icc a b = Icc 0 L := by
    rw [hs.image_Icc_of_monotoneOn hab hm, hsa, hsb]
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

/-- For an injective continuous rectifiable arc, cumulative variation is an increasing
homeomorphism onto the length interval. The singleton interval case is included. -/
theorem exists_arclength_homeomorph (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) (hab : a ≤ b) :
    ∃ e : Icc a b ≃ₜ Icc 0 (eVariationOn γ (Icc a b)).toReal,
      StrictMono e ∧ ∀ t, (e t : ℝ) = variationOnFromTo γ (Icc a b) a t := by
  let s := variationOnFromTo γ (Icc a b) a
  let L := (eVariationOn γ (Icc a b)).toReal
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hs : ContinuousOn s (Icc a b) := fun t ht ↦
    (hγ.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hcont t ht)
  have hm : StrictMonoOn s (Icc a b) :=
    hγ.locallyBoundedVariationOn.strictMonoOn_variationOnFromTo ha hinj
  have hsa : s a = 0 := variationOnFromTo.self _ _ _
  have hsb : s b = L := by
    simp only [s, variationOnFromTo.eq_of_le _ _ hab, inter_self, L]
  have himage : s '' Icc a b = Icc 0 L := by
    rw [hs.image_Icc_of_monotoneOn hab hm.monotoneOn, hsa, hsb]
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

end BoundedVariationOn
