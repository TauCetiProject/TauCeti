/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Connected.Clopen

/-!
# Uniqueness of integral curves on intervals with endpoints

Integral curves of a C¹ vector field on a preconnected real parameter set agree everywhere
if they agree once and the first curve stays in the manifold interior, including when the
initial time is an endpoint. The local comparison
uses one-sided derivatives and Grönwall's inequality in a fixed chart. It does not require
an extension of either curve beyond its parameter set.

This extends the open-interval uniqueness API to closed and half-open intervals. In
particular it applies to velocity lifts of geodesic segments.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 9.
* Mathlib's `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` supplies the local-coordinate and
  connectedness proof architecture; `ODE_solution_unique_of_mem_Icc_right` and its left
  counterpart supply the one-sided comparison.
-/

public noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Topology NNReal

namespace IsMIntegralCurveOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x} {γ δ : ℝ → M}
  {s : Set ℝ} {a b t₀ : ℝ}

/-- Integral curves in a common chart, with a Lipschitz coordinate vector field, agree on a
closed interval if they agree at one parameter. No manifold boundary assumption is needed. -/
theorem eqOn_Icc_of_lipschitzOnWith_extChartAt {x : M} {z : Set E} {K : ℝ≥0}
    (hγ : IsMIntegralCurveOn γ v (Icc a b))
    (hδ : IsMIntegralCurveOn δ v (Icc a b))
    (hγsrc : ∀ t ∈ Icc a b, γ t ∈ (extChartAt I x).source)
    (hδsrc : ∀ t ∈ Icc a b, δ t ∈ (extChartAt I x).source)
    (hγz : ∀ t ∈ Icc a b, extChartAt I x (γ t) ∈ z)
    (hδz : ∀ t ∈ Icc a b, extChartAt I x (δ t) ∈ z)
    (hv : LipschitzOnWith K (fun y ↦ tangentCoordChange I ((extChartAt I x).symm y)
      x ((extChartAt I x).symm y) (v ((extChartAt I x).symm y))) z)
    (ht : t₀ ∈ Icc a b) (heq : γ t₀ = δ t₀) : EqOn γ δ (Icc a b) := by
  let φ := extChartAt I x
  let w : E → E := fun y ↦ tangentCoordChange I (φ.symm y) x (φ.symm y) (v (φ.symm y))
  have hd {c : ℝ → M} (hc : IsMIntegralCurveOn c v (Icc a b))
      (hcs : ∀ t ∈ Icc a b, c t ∈ φ.source) (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (φ ∘ c) (w (φ (c r))) (Icc a b) r := by
    dsimp only [w]
    rw [φ.left_inv (hcs r hr)]
    exact (hc r hr).hasDerivWithinAt_extChartAt_comp (hcs r hr)
  have hcoord : EqOn (φ ∘ γ) (φ ∘ δ) (Icc a b) := by
    intro r hr
    rcases le_total t₀ r with htr | hrt
    · have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht.1
      exact ODE_solution_unique_of_mem_Icc_right (fun _ _ ↦ hv)
        (fun u hu ↦ (hd hγ hγsrc u (hsub hu)).continuousWithinAt.mono hsub)
        (fun u hu ↦ (hd hγ hγsrc u ⟨ht.1.trans hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1.trans hu.1, hu.2⟩))
        (fun u hu ↦ hγz u ⟨ht.1.trans hu.1, hu.2.le⟩)
        (fun u hu ↦ (hd hδ hδsrc u (hsub hu)).continuousWithinAt.mono hsub)
        (fun u hu ↦ (hd hδ hδsrc u ⟨ht.1.trans hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1.trans hu.1, hu.2⟩))
        (fun u hu ↦ hδz u ⟨ht.1.trans hu.1, hu.2.le⟩) (congrArg φ heq) ⟨htr, hr.2⟩
    · have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht.2
      exact ODE_solution_unique_of_mem_Icc_left (fun _ _ ↦ hv)
        (fun u hu ↦ (hd hγ hγsrc u (hsub hu)).continuousWithinAt.mono hsub)
        (fun u hu ↦ (hd hγ hγsrc u ⟨hu.1.le, hu.2.trans ht.2⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨hu.1, hu.2.trans ht.2⟩))
        (fun u hu ↦ hγz u ⟨hu.1.le, hu.2.trans ht.2⟩)
        (fun u hu ↦ (hd hδ hδsrc u (hsub hu)).continuousWithinAt.mono hsub)
        (fun u hu ↦ (hd hδ hδsrc u ⟨hu.1.le, hu.2.trans ht.2⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨hu.1, hu.2.trans ht.2⟩))
        (fun u hu ↦ hδz u ⟨hu.1.le, hu.2.trans ht.2⟩) (congrArg φ heq) ⟨hr.1, hrt⟩
  exact fun r hr ↦ φ.injOn (hγsrc r hr) (hδsrc r hr) (hcoord hr)

/-- Two integral curves that agree at a parameter agree near it within a preconnected
parameter set. The common value is an interior point, and the vector field is C¹ there. -/
theorem eventuallyEq_of_isPreconnected
    (hγ : IsMIntegralCurveOn γ v s) (hδ : IsMIntegralCurveOn δ v s)
    (hs : IsPreconnected s) (ht : t₀ ∈ s)
    (hinterior : I.IsInteriorPoint (γ t₀))
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (heq : γ t₀ = δ t₀) : γ =ᶠ[𝓝[s] t₀] δ := by
  let φ := extChartAt I (γ t₀)
  let w : E → E := fun y ↦ tangentCoordChange I (φ.symm y) (γ t₀) (φ.symm y) (v (φ.symm y))
  obtain ⟨_, hv⟩ := contMDiffAt_iff.mp hv
  obtain ⟨K, z, hz, hlip⟩ : ∃ K, ∃ z ∈ 𝓝 (φ (γ t₀)), LipschitzOnWith K w z :=
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint hinterior)).snd.exists_lipschitzOnWith
  have hsrcγ : ∀ᶠ r in 𝓝[s] t₀, γ r ∈ φ.source :=
    (hγ.continuousWithinAt ht).preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)
  have hδt : δ t₀ ∈ φ.source := by
    rw [← heq]
    exact mem_extChartAt_source (I := I) _
  have hsrcδ : ∀ᶠ r in 𝓝[s] t₀, δ r ∈ φ.source :=
    (hδ.continuousWithinAt ht).preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (γ t₀)).mem_nhds hδt)
  have hzγ : ∀ᶠ r in 𝓝[s] t₀, φ (γ r) ∈ z :=
    ((continuousAt_extChartAt _).comp_continuousWithinAt (hγ.continuousWithinAt ht)).eventually hz
  have hzδ₀ : z ∈ 𝓝 (φ (δ t₀)) := by rw [← heq]; exact hz
  have hzδ : ∀ᶠ r in 𝓝[s] t₀, φ (δ r) ∈ z :=
    ((continuousAt_extChartAt' hδt).comp_continuousWithinAt
      (hδ.continuousWithinAt ht)).eventually hzδ₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hsrcγ.and (hsrcδ.and (hzγ.and hzδ)))
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hε),
    self_mem_nhdsWithin] with r hr hrs
  have hsub : uIcc t₀ r ⊆ Metric.ball t₀ ε ∩ s :=
    ((convex_ball t₀ ε).ordConnected.inter hs.ordConnected).uIcc_subset
      ⟨Metric.mem_ball_self hε, ht⟩ ⟨hr, hrs⟩
  have hlocal : ∀ u ∈ uIcc t₀ r,
      γ u ∈ φ.source ∧ δ u ∈ φ.source ∧ φ (γ u) ∈ z ∧ φ (δ u) ∈ z :=
    fun u hu ↦ hball (hsub hu)
  exact (hγ.mono (fun u hu ↦ (hsub hu).2)).eqOn_Icc_of_lipschitzOnWith_extChartAt
    (hδ.mono (fun u hu ↦ (hsub hu).2)) (fun u hu ↦ (hlocal u hu).1)
    (fun u hu ↦ (hlocal u hu).2.1) (fun u hu ↦ (hlocal u hu).2.2.1)
    (fun u hu ↦ (hlocal u hu).2.2.2) hlip
    ⟨min_le_left _ _, le_max_left _ _⟩ heq right_mem_uIcc

/-- Integral curves of a C¹ vector field on a preconnected real parameter set are determined
by their value at any one parameter, including an endpoint, provided the first curve
stays in the manifold interior. -/
theorem eqOn_of_isPreconnected [T2Space M]
    (hγ : IsMIntegralCurveOn γ v s) (hδ : IsMIntegralCurveOn δ v s)
    (hs : IsPreconnected s) (ht : t₀ ∈ s)
    (hinterior : ∀ t ∈ s, I.IsInteriorPoint (γ t))
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (heq : γ t₀ = δ t₀) : EqOn γ δ s := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hcγ : Continuous (fun t : s ↦ γ t) := hγ.continuousOn.domRestrict
  have hcδ : Continuous (fun t : s ↦ δ t) := hδ.continuousOn.domRestrict
  have hopen : IsOpen {t : s | γ t = δ t} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht'
    have he := hγ.eventuallyEq_of_isPreconnected hδ hs t.property
      (hinterior t t.property) hv.contMDiffAt ht'
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.preimage_mem_comap he
  have hall := IsClopen.eq_univ (s := {t : s | γ t = δ t})
    ⟨isClosed_eq hcγ hcδ, hopen⟩ ⟨⟨t₀, ht⟩, heq⟩
  intro t ht'
  exact Set.eq_univ_iff_forall.mp hall ⟨t, ht'⟩

end IsMIntegralCurveOn
