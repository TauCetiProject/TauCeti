/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.InitialCondition
public import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Smooth dependence of integral curves on their initial point

A smooth vector field on a finite-dimensional boundaryless manifold admits, near every point, a
family of local integral curves that depends smoothly on both the initial point and time.  This is
the manifold form of smooth dependence for ordinary differential equations: express the field in
one extended chart, apply the model-space local-flow theorem, and return through the inverse chart.
The resulting family inherits the flow law whenever its first time lies in the common local
domain.

The family is only asserted as a germ near the chosen point and time zero.  This is the natural
local statement: outside that germ both the chart and the model-space extension carry arbitrary
values.  Uniqueness of integral curves can subsequently identify overlapping germs and assemble
the maximal flow.

## Main result

* `TauCeti.Manifold.exists_contMDiffAt_localFlow`: a smooth vector field has a jointly smooth
  family of local integral curves through all nearby initial points, satisfying the flow law.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, Chapter 9.
* [Winston Yin, mathlib4#26394: *Existence of local flows on
  manifolds*](https://github.com/leanprover-community/mathlib4/pull/26394), for the passage
  between a model-space flow and manifold integral curves.
-/

public section

open Bundle Filter Function Manifold Set Topology
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Smooth dependence of integral curves on their initial point.**

If a tangent vector field is smooth on a neighbourhood of `a`, then there is a family `Φ x t`
which is jointly smooth at `(a, 0)`, starts at `x` for every `x` in a neighbourhood of `a`, and is
an integral curve of the field on one common open time neighbourhood.  Its values outside that
common domain provide only a total extension of the local flow.
-/
theorem exists_contMDiffAt_localFlow [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] (v : (x : M) → TangentSpace I x) (a : M) {V : Set M}
    (hv : ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) V)
    (hV : V ∈ nhds a) :
    ∃ U ∈ nhds a, ∃ s ∈ nhds (0 : ℝ), IsOpen s ∧ ∃ Φ : M → ℝ → M,
      CMDiffAt ∞ (fun p : M × ℝ ↦ Φ p.1 p.2) (a, 0) ∧
        ∀ x ∈ U, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v s ∧
          ∀ t ∈ s, ∀ u, Φ x (t + u) = Φ (Φ x t) u := by
  let e := trivializationAt E (TangentSpace I) a
  let w : E → E := fun z ↦
    (e (⟨(extChartAt I a).symm z, v ((extChartAt I a).symm z)⟩ : TangentBundle I M)).2
  let W := interior (extChartAt I a).target ∩ (extChartAt I a).symm ⁻¹' V
  have hws : ContDiffOn ℝ ∞ w W := by
    have hsection : ContMDiffOn (modelWithCornersSelf ℝ E) I.tangent ∞
        ((fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) ∘ (extChartAt I a).symm)
        W := hv.comp
      ((contMDiffOn_extChartAt_symm a).mono (inter_subset_left.trans interior_subset))
      (fun _ hz ↦ hz.2)
    have hmap : MapsTo
        ((fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) ∘ (extChartAt I a).symm)
        W e.source := by
      intro z hz
      rw [TangentBundle.trivializationAt_source]
      -- Membership in this preimage reduces definitionally by projecting the displayed
      -- tangent-bundle point to its base point; there is no separate projection lemma to apply.
      change (extChartAt I a).symm z ∈ (chartAt H a).source
      simpa only [extChartAt_source] using
        (extChartAt I a).map_target (interior_subset hz.1)
    have hcoord := ((e.contMDiffOn_iff hmap).mp hsection).2
    simpa only [w, Function.comp_apply] using hcoord.contDiffOn
  have haTarget : extChartAt I a a ∈ (extChartAt I a).target := mem_extChartAt_target a
  have hsymmV : (extChartAt I a).symm ⁻¹' V ∈ nhds (extChartAt I a a) := by
    apply (continuousAt_extChartAt_symm'' haTarget).preimage_mem_nhds
    simpa only [(extChartAt I a).left_inv (mem_extChartAt_source a)] using hV
  have hatarget : W ∈ nhds (extChartAt I a a) := inter_mem
    (isOpen_interior.mem_nhds
      (I.isInteriorPoint_iff.mp (BoundarylessManifold.isInteriorPoint (I := I)))) hsymmV
  have hws' : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) w
      W := by simpa using hws
  obtain ⟨φ, hφ, hφ0, hφadd, hφderiv⟩ :=
    ODE.exists_contDiffAt_localFlow (n := (⊤ : ℕ∞)) w hws' hatarget
  let Φ : M → ℝ → M := fun x t ↦
    (extChartAt I a).symm (φ (extChartAt I a x) t)
  have hΦsmooth : CMDiffAt ∞ (fun p : M × ℝ ↦ Φ p.1 p.2) (a, 0) := by
    have hchart : CMDiffAt ∞ (fun p : M × ℝ ↦ extChartAt I a p.1) (a, 0) :=
      contMDiffAt_extChartAt.comp (a, 0) contMDiffAt_fst
    have hcoord : ContMDiffAt (I.prod (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)) ∞
        (fun p : M × ℝ ↦ (extChartAt I a p.1, p.2)) (a, 0) :=
      hchart.prodMk contMDiffAt_snd
    have hφ' : ContDiffAt ℝ ∞ (fun p : E × ℝ ↦ φ p.1 p.2)
        (extChartAt I a a, 0) := by simpa using hφ
    have hφM := hφ'.contMDiffAt
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hφM
    have hinner : CMDiffAt ∞
        (fun p : M × ℝ ↦ φ (extChartAt I a p.1) p.2) (a, 0) := by
      have h := hφM.comp (a, 0) hcoord
      simpa only [Function.comp_def] using h
    have hinv : CMDiffAt ∞ (extChartAt I a).symm (extChartAt I a a) := by
      rw [← contMDiffWithinAt_univ, ← I.range_eq_univ]
      exact contMDiffWithinAt_extChartAt_symm_range_self a
    have hvalue : φ (extChartAt I a a) 0 = extChartAt I a a := hφ0 _
    have hcomp := hinv.comp_of_eq hinner hvalue
    simpa only [Φ, Function.comp_def] using hcomp
  have htarget : ∀ᶠ p in nhds ((extChartAt I a a, 0) : E × ℝ),
      φ p.1 p.2 ∈ interior (extChartAt I a).target := by
    have hmem : extChartAt I a a ∈ interior (extChartAt I a).target :=
      I.isInteriorPoint_iff.mp (BoundarylessManifold.isInteriorPoint (I := I))
    apply hφ.continuousAt.eventually
    apply isOpen_interior.mem_nhds
    simpa only [hφ0] using hmem
  rw [nhds_prod_eq, eventually_prod_iff] at hφderiv htarget
  obtain ⟨u₁, hu₁, t₁, ht₁, hderiv⟩ := hφderiv
  obtain ⟨u₂, hu₂, t₂, ht₂, hmem⟩ := htarget
  let U := (extChartAt I a) ⁻¹' {z | u₁ z ∧ u₂ z} ∩ (extChartAt I a).source
  have hU : U ∈ nhds a := inter_mem
    ((continuousAt_extChartAt a).preimage_mem_nhds (inter_mem hu₁ hu₂))
    (extChartAt_source_mem_nhds (I := I) a)
  obtain ⟨s, hst, hsopen, hs0⟩ := mem_nhds_iff.mp (inter_mem ht₁ ht₂)
  refine ⟨U, hU, s, hsopen.mem_nhds hs0, hsopen, Φ, hΦsmooth, ?_⟩
  intro x hx
  have hxcoord : u₁ (extChartAt I a x) ∧ u₂ (extChartAt I a x) := hx.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [Φ, hφ0]
    exact (extChartAt I a).left_inv hx.2
  · intro t ht
    have hcurve : IsMIntegralCurveAt (Φ x) v t := by
      apply IsMIntegralCurveAt.of_extChartAt_symm
      · filter_upwards [hsopen.mem_nhds ht] with r hr
        exact hmem hxcoord.2 (hst hr).2
      · filter_upwards [hsopen.mem_nhds ht] with r hr
        have hw_eq (z : E) : w z =
            tangentCoordChange I ((extChartAt I a).symm z) a ((extChartAt I a).symm z)
              (v ((extChartAt I a).symm z)) := rfl
        simpa only [hw_eq] using hderiv hxcoord.1 (hst hr).1
    exact hcurve.self_of_nhds.hasMFDerivWithinAt
  · intro t ht u
    have hφtarget : φ (extChartAt I a x) t ∈ (extChartAt I a).target :=
      interior_subset (hmem hxcoord.2 (hst ht).2)
    simp only [Φ]
    rw [(extChartAt I a).right_inv hφtarget, hφadd]

end TauCeti.Manifold

end
