/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UrysohnsLemma

/-!
# Pointwise uniqueness of continuous disintegrations

An integration formula determines fibre measures only almost everywhere in the base. If the
base measure is sigma-finite and positive on every nonempty open set, continuity of the fibre
integrals against compactly supported continuous tests upgrades uniqueness to every parameter.
The fibres are represented as regular measures on a fixed locally compact Hausdorff space;
their total mass need not be finite.

`TauCeti.eq_of_continuous_lintegral_of_disintegration` applies to two families satisfying the
same integration formula along an arbitrary map. Finiteness of the test integrals already makes a
fibre finite on compact sets (`TauCeti.isFiniteMeasureOnCompacts_of_lintegral_lt_top`), hence
regular on a σ-compact metrizable space. No geometric structure on this map is needed
for uniqueness. Regularity already ensures that the compactly supported test integrals are
finite, so no separate finiteness assumption is required.

## Provenance

`TauCeti.eq_of_continuous_lintegral_of_disintegration` is adapted from
`New.Floors.Place.IsDisintegration.unique` (file
`src/Lib/General/Measure/QuadricDisintegration.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
The generalisation from Hermitian quadrics over a place to arbitrary maps and regular fibre
measures is new here; the bespoke disintegration structure is replaced by explicit hypotheses.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill (1987), Theorem 2.14:
  uniqueness of a regular measure from its integrals against compactly supported continuous
  functions, used here through Mathlib's Riesz–Markov–Kakutani theorem.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal CompactlySupported

namespace TauCeti

/-- Two continuous families of regular measures satisfying the same disintegration formula
along `π` agree at every parameter. Continuity means that the lower integrals of every
nonnegative compactly supported continuous function depend continuously on the parameter.

The base measure is sigma-finite and positive on nonempty open sets. The fibre measures may
have infinite total mass. No measurability or continuity assumption on `π` is needed beyond
the two stated integration identities. -/
theorem eq_of_continuous_lintegral_of_disintegration
    {X B : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace B] [MeasurableSpace B]
    [OpensMeasurableSpace B] {μ : Measure X} {ν : Measure B} [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {π : X → B} {l l' : B → Measure X}
    [∀ b, (l b).Regular] [∀ b, (l' b).Regular]
    (hl : ∀ f : C_c(X, ℝ≥0), Continuous (fun b ↦ ∫⁻ x, f x ∂l b))
    (hl' : ∀ f : C_c(X, ℝ≥0), Continuous (fun b ↦ ∫⁻ x, f x ∂l' b))
    (hμ : ∀ F : B × X → ℝ≥0∞, Measurable F →
      ∫⁻ x, F (π x, x) ∂μ = ∫⁻ b, ∫⁻ x, F (b, x) ∂l b ∂ν)
    (hμ' : ∀ F : B × X → ℝ≥0∞, Measurable F →
      ∫⁻ x, F (π x, x) ∂μ = ∫⁻ b, ∫⁻ x, F (b, x) ∂l' b ∂ν) :
    l = l' := by
  classical
  funext b
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦ ?_
  have hsets (s : Set B) (hs : MeasurableSet s) (_ : ν s < ∞) :
      ∫⁻ β in s, ∫⁻ x, f x ∂l β ∂ν = ∫⁻ β in s, ∫⁻ x, f x ∂l' β ∂ν := by
    let F : B × X → ℝ≥0∞ := fun p ↦ s.indicator 1 p.1 * (f p.2 : ℝ≥0∞)
    have hF : Measurable F := by fun_prop
    have hboth := (hμ F hF).symm.trans (hμ' F hF)
    have hlin (m : B → Measure X) :
        ∫⁻ β, ∫⁻ x, F (β, x) ∂m β ∂ν = ∫⁻ β in s, ∫⁻ x, f x ∂m β ∂ν := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro β
      by_cases hβ : β ∈ s <;> simp [F, hβ]
    exact (hlin l).symm.trans (hboth.trans (hlin l'))
  have hae := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (hl f).measurable (hl' f).measurable hsets
  have heq := congrFun (Measure.eq_of_ae_eq hae (hl f) (hl' f)) b
  have h_toReal (m : Measure X) :
      ∫ x, (f x : ℝ) ∂m = (∫⁻ x, f x ∂m).toReal :=
    (f.toBoundedContinuousFunction.toReal_lintegral_coe_eq_integral m).symm
  rw [h_toReal, h_toReal, heq]

/-- A measure on a locally compact Hausdorff space whose lower integrals of nonnegative compactly
supported continuous functions are all finite is finite on compact sets: by Urysohn's lemma, the
indicator of a compact set lies below such a function. -/
theorem isFiniteMeasureOnCompacts_of_lintegral_lt_top {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    (h : ∀ f : C_c(X, ℝ≥0), ∫⁻ x, f x ∂μ < ∞) : IsFiniteMeasureOnCompacts μ := by
  refine ⟨fun K hK ↦ ?_⟩
  obtain ⟨f, hfK, hfc, -, -⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (Set.subset_univ K)
  have hf : HasCompactSupport f :=
    .intro' hfc (isClosed_tsupport f) fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx
  let g : C_c(X, ℝ≥0) :=
    ⟨⟨fun x ↦ (f x).toNNReal, continuous_real_toNNReal.comp f.continuous⟩,
      hf.comp_left Real.toNNReal_zero⟩
  calc μ K = ∫⁻ _ in K, 1 ∂μ := (setLIntegral_one K).symm
    _ ≤ ∫⁻ x in K, g x ∂μ := setLIntegral_mono' hK.isClosed.measurableSet fun x hx ↦ by
        simp [g, hfK hx]
    _ ≤ ∫⁻ x, g x ∂μ := setLIntegral_le_lintegral K _
    _ < ∞ := h g

end TauCeti
