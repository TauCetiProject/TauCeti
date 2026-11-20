/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Almost invariant functions descend along quotient coverings

Let `q : E → X` be a quotient covering map for an action of a countable group `G`
(`IsQuotientCoveringMap q G`), for instance the orbit projection of a free properly discontinuous
action, with `E` Lindelöf, and let `μ` be a measure on `E` for which every `g • ·` is
quasi-measure-preserving. A function on `E` is the pullback `h ∘ q` of a function on `X` exactly
when it is invariant under `G`. This file proves the almost-everywhere version: an almost
everywhere strongly measurable `f` with `f (g • x) = f x` for almost every `x`, for each `g`,
agrees almost everywhere with `h ∘ q` for a strongly measurable `h` on `X`
(`IsQuotientCoveringMap.exists_stronglyMeasurable_ae_eq_comp`).

The points where a strongly measurable representative `f₀` of `f` fails to be invariant form a
null set `Z`, and so does its saturation `q⁻¹ (q Z)`, the union of the translates of `Z`. Off the
saturation `f₀` is invariant, so it is constant on the fibres of `q` there, and redefining it to
be constant on the saturation gives an everywhere invariant function, which factors through `q`.
The factor is strongly measurable because `q` is a surjective local homeomorphism out of a
Lindelöf space (`IsLocalHomeomorph.stronglyMeasurable_comp_iff`).

This is the measure-theoretic step behind identifying the `Lᵖ` functions on the base of a finite
Riemannian covering with the invariant `Lᵖ` functions upstairs.
-/

public section

open Function MeasureTheory Set TopologicalSpace

namespace IsQuotientCoveringMap

variable {E X G F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [LindelofSpace E] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [Group G] [MulAction G E] [Countable G] [TopologicalSpace F] [MetrizableSpace F]
  {q : E → X} {μ : Measure E}

/-- **Almost invariant functions descend along a quotient covering.** If `q` is a quotient
covering map for an action of a countable group `G` by quasi-measure-preserving maps, then an
almost everywhere strongly measurable function `f` on `E` with `f (g • x) = f x` for almost every
`x`, for each `g`, agrees almost everywhere with `h ∘ q` for a strongly measurable `h` on `X`. -/
theorem exists_stronglyMeasurable_ae_eq_comp (hq : IsQuotientCoveringMap q G)
    (hμ : ∀ g : G, QuasiMeasurePreserving (g • · : E → E) μ μ) {f : E → F}
    (hf : AEStronglyMeasurable f μ) (hinv : ∀ g : G, (fun x ↦ f (g • x)) =ᵐ[μ] f) :
    ∃ h : X → F, StronglyMeasurable h ∧ f =ᵐ[μ] h ∘ q := by
  classical
  rcases isEmpty_or_nonempty E with hE | ⟨⟨x₀⟩⟩
  · have : IsEmpty X := ⟨fun y ↦ isEmptyElim (hq.surjective y).choose⟩
    exact ⟨isEmptyElim, .of_subsingleton_dom, .of_forall isEmptyElim⟩
  set f₀ := hf.mk f
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  -- The points where `f₀` is not invariant form a measurable null set `Z`.
  set Z : Set E := ⋃ g : G, {x | f₀ (g • x) ≠ f₀ x}
  have hZ : MeasurableSet Z := .iUnion fun g ↦
    ((hf₀.comp_measurable (hq.continuous_const_smul g).measurable).measurableSet_eq_fun hf₀).compl
  have hZ0 : μ Z = 0 := measure_iUnion_null fun g ↦ ae_iff.1 <|
    ((hμ g).ae_eq_comp hf.ae_eq_mk).symm.trans ((hinv g).trans hf.ae_eq_mk)
  -- So is its saturation `S`, which is the union of the translates of `Z`.
  set S : Set E := q ⁻¹' (q '' Z)
  have hS : MeasurableSet S :=
    hq.continuous.measurable (hq.isLocalHomeomorph.measurableSet_image hZ)
  have hS0 : μ S = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_)
      (measure_iUnion_null fun g ↦ (hμ g).preimage_null hZ0)
    obtain ⟨z, hz, hzx⟩ := hx
    obtain ⟨g, rfl⟩ := hq.apply_eq_iff_mem_orbit.1 hzx
    exact mem_iUnion.2 ⟨g, hz⟩
  -- Off `S` the representative `f₀` is constant on the fibres of `q`; on `S` use a constant.
  set h : X → F := (q '' Z).piecewise (fun _ ↦ f₀ x₀) fun y ↦ f₀ (surjInv hq.surjective y)
  have hcomp : h ∘ q = S.piecewise (fun _ ↦ f₀ x₀) f₀ := by
    ext x
    by_cases hx : x ∈ S
    · simp only [comp_apply, h, piecewise_eq_of_mem _ _ _ hx]
      exact piecewise_eq_of_mem _ _ _ (mem_preimage.1 hx)
    · simp only [comp_apply, h, piecewise_eq_of_notMem _ _ _ hx]
      rw [piecewise_eq_of_notMem _ _ _ fun hy ↦ hx (mem_preimage.2 hy)]
      obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.1 (surjInv_eq hq.surjective (q x))
      have hxZ : x ∉ Z := fun hxZ ↦ hx (mem_preimage.2 (mem_image_of_mem q hxZ))
      simp only [Z, mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hxZ
      rw [← hg, hxZ g]
  refine ⟨h, (hq.isLocalHomeomorph.stronglyMeasurable_comp_iff hq.surjective).1 ?_, ?_⟩
  · rw [hcomp]
    exact StronglyMeasurable.piecewise hS stronglyMeasurable_const hf₀
  · rw [hcomp]
    filter_upwards [hf.ae_eq_mk, measure_eq_zero_iff_ae_notMem.1 hS0] with x hx hxS
    rw [hx, piecewise_eq_of_notMem _ _ _ hxS]

end IsQuotientCoveringMap
