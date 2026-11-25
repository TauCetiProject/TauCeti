/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Topology.Connected.Clopen

/-!
# Uniqueness of integral curves on intervals with endpoints

Integral curves of a vector field on a preconnected real parameter set agree everywhere
if they agree once and the vector field is C¹ along the first curve, including when the
initial time is an endpoint. The local comparison uses one-sided derivatives and Grönwall's
inequality in a fixed chart. It does not require an extension of either curve beyond its
parameter set, nor regularity of the vector field away from the first curve.

The curves may meet the boundary of the manifold. In a chart the coordinate field is C¹
within the range of the model, which is convex, so it is Lipschitz on a neighbourhood relative
to that range, and the chart coordinates of both curves stay in the range. Thus uniqueness
holds at boundary points, where Mathlib's `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` asks for
interior points. In particular two forward integral curves starting at the same boundary
point agree, which is what is needed to glue local flows of an inward-pointing vector field.

This extends the open-interval uniqueness API to closed and half-open intervals. In
particular it applies to velocity lifts of geodesic segments.

Run backwards from a common end point (`IsMIntegralCurveOn.apply_sub_min_eq_of_apply_eq`),
uniqueness also separates forward integral curves that start on the boundary and enter the
interior at once: two such curves meet only at equal times, and then they start at the same
point (`IsMIntegralCurveOn.eq_and_apply_zero_eq_of_apply_eq`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 9.
* Mathlib's `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` supplies the local-coordinate and
  connectedness proof architecture. Mathlib's closed-interval comparisons supply the fixed-chart
  result, and `ContDiffWithinAt.exists_lipschitzOnWith` the Lipschitz bound within the range of
  the model.
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
parameter set, as soon as the vector field is C¹ at their common value. That value may lie on
the boundary of the manifold: uniqueness, unlike existence, needs no interior assumption. -/
theorem eventuallyEq_of_isPreconnected
    (hγ : IsMIntegralCurveOn γ v s) (hδ : IsMIntegralCurveOn δ v s)
    (hs : IsPreconnected s) (ht : t₀ ∈ s)
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (heq : γ t₀ = δ t₀) : γ =ᶠ[𝓝[s] t₀] δ := by
  let φ := extChartAt I (γ t₀)
  let w : E → E := fun y ↦ tangentCoordChange I (φ.symm y) (γ t₀) (φ.symm y) (v (φ.symm y))
  obtain ⟨_, hv⟩ := contMDiffAt_iff.mp hv
  -- The coordinate field is C¹ within the convex range of the model, so it is Lipschitz on a
  -- neighbourhood of the common value relative to that range.
  obtain ⟨K, z, hz, hlip⟩ : ∃ K, ∃ z ∈ 𝓝[range I] (φ (γ t₀)), LipschitzOnWith K w z :=
    hv.snd.exists_lipschitzOnWith I.convex_range
  -- Chart coordinates of a curve through the common value stay in the range of the model, so
  -- they eventually lie in `z`.
  have hnear {c : ℝ → M} (hc : IsMIntegralCurveOn c v s) (hc₀ : c t₀ = γ t₀) :
      ∀ᶠ r in 𝓝[s] t₀, c r ∈ φ.source ∧ φ (c r) ∈ z := by
    have hcont : Tendsto c (𝓝[s] t₀) (𝓝 (γ t₀)) := hc₀ ▸ (hc.continuousWithinAt ht).tendsto
    have hsrc : ∀ᶠ r in 𝓝[s] t₀, c r ∈ φ.source := hcont (extChartAt_source_mem_nhds _)
    have hφc : Tendsto (φ ∘ c) (𝓝[s] t₀) (𝓝[range I] (φ (γ t₀))) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuousAt_extChartAt (γ t₀)).tendsto.comp hcont,
        hsrc.mono fun r hr ↦ extChartAt_target_subset_range _ (φ.map_source hr)⟩
    exact hsrc.and (hφc hz)
  obtain ⟨ε, hε, hgood⟩ := Metric.mem_nhdsWithin_iff.mp ((hnear hγ rfl).and (hnear hδ heq.symm))
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hε), self_mem_nhdsWithin]
    with t htε hts
  -- On the interval between `t₀` and `t` both curves stay where the Lipschitz bound applies.
  have hsub : uIcc t₀ t ⊆ Metric.ball t₀ ε ∩ s :=
    ((convex_ball t₀ ε).ordConnected.inter hs.ordConnected).uIcc_subset
      ⟨Metric.mem_ball_self hε, ht⟩ ⟨htε, hts⟩
  have hsubs : uIcc t₀ t ⊆ s := fun r hr ↦ (hsub hr).2
  exact (hγ.mono hsubs).eqOn_Icc_of_lipschitzOnWith_extChartAt (hδ.mono hsubs)
    (fun r hr ↦ (hgood (hsub hr)).1.1) (fun r hr ↦ (hgood (hsub hr)).2.1)
    (fun r hr ↦ (hgood (hsub hr)).1.2) (fun r hr ↦ (hgood (hsub hr)).2.2) hlip
    left_mem_uIcc heq right_mem_uIcc

/-- Integral curves of a vector field on a preconnected real parameter set are determined
by their value at any one parameter, including an endpoint, provided the vector field is C¹
at each point of the first curve. The curves may meet the boundary of the manifold. -/
theorem eqOn_of_isPreconnected [T2Space M]
    (hγ : IsMIntegralCurveOn γ v s) (hδ : IsMIntegralCurveOn δ v s)
    (hs : IsPreconnected s) (ht : t₀ ∈ s)
    (hv : ∀ t ∈ s, CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t))
    (heq : γ t₀ = δ t₀) : EqOn γ δ s := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hcγ : Continuous (fun t : s ↦ γ t) := hγ.continuousOn.domRestrict
  have hcδ : Continuous (fun t : s ↦ δ t) := hδ.continuousOn.domRestrict
  have hopen : IsOpen {t : s | γ t = δ t} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht'
    have he := hγ.eventuallyEq_of_isPreconnected hδ hs t.property
      (hv t t.property) ht'
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.preimage_mem_comap he
  have hall := IsClopen.eq_univ (s := {t : s | γ t = δ t})
    ⟨isClosed_eq hcγ hcδ, hopen⟩ ⟨⟨t₀, ht⟩, heq⟩
  intro t ht'
  exact Set.eq_univ_iff_forall.mp hall ⟨t, ht'⟩

/-- Integral curves on `[0, a]` and `[0, b]` with a common end point `γ a = δ b` agree after
running back for the same time `min a b`. The vector field is C¹ along the first curve. -/
theorem apply_sub_min_eq_of_apply_eq [T2Space M]
    (hγ : IsMIntegralCurveOn γ v (Icc 0 a)) (hδ : IsMIntegralCurveOn δ v (Icc 0 b))
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : ∀ t ∈ Icc 0 a, CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t))
    (h : γ a = δ b) : γ (a - min a b) = δ (b - min a b) := by
  -- Shift both curves so that they are defined on `[0, min a b]` and meet at its right end.
  have hm : 0 ≤ min a b := le_min ha hb
  have hγ' : IsMIntegralCurveOn (γ ∘ (· + (a - min a b))) v (Icc 0 (min a b)) :=
    (hγ.comp_add _).mono fun t ht ↦ ⟨by linarith [ht.1, min_le_left a b], by linarith [ht.2]⟩
  have hδ' : IsMIntegralCurveOn (δ ∘ (· + (b - min a b))) v (Icc 0 (min a b)) :=
    (hδ.comp_add _).mono fun t ht ↦ ⟨by linarith [ht.1, min_le_right a b], by linarith [ht.2]⟩
  have heq := hγ'.eqOn_of_isPreconnected hδ' isPreconnected_Icc (right_mem_Icc.2 hm)
    (fun t ht ↦ hv _ ⟨by linarith [ht.1, min_le_left a b], by linarith [ht.2]⟩)
    (by simpa only [comp_apply, add_sub_cancel] using h) (left_mem_Icc.2 hm)
  simpa only [comp_apply, zero_add] using heq

/-- **Forward integral curves from the boundary meet only at equal times and from the same
start.** Let `γ` and `δ` be integral curves of `v` on `[0, a]` and `[0, b]`, with `a, b ≥ 0`,
starting on the boundary of `M` and lying in its interior at every positive time. If `γ a = δ b`,
then `a = b` and the two curves start at the same point. The vector field is C¹ along the first
curve. -/
theorem eq_and_apply_zero_eq_of_apply_eq [T2Space M]
    (hγ : IsMIntegralCurveOn γ v (Icc 0 a)) (hδ : IsMIntegralCurveOn δ v (Icc 0 b))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ0 : γ 0 ∈ I.boundary M) (hδ0 : δ 0 ∈ I.boundary M)
    (hγi : ∀ t ∈ Ioc 0 a, γ t ∈ I.interior M) (hδi : ∀ t ∈ Ioc 0 b, δ t ∈ I.interior M)
    (hv : ∀ t ∈ Icc 0 a, CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t))
    (h : γ a = δ b) : a = b ∧ γ 0 = δ 0 := by
  -- Running back for the time `min a b` reaches the starting point of the shorter curve, on the
  -- boundary, and a point of the longer curve, in the interior unless the times agree.
  have key := apply_sub_min_eq_of_apply_eq hγ hδ ha hb hv h
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [min_eq_left hab.le, sub_self] at key
    exact absurd key (I.disjoint_interior_boundary.ne_of_mem
      (hδi _ ⟨sub_pos.2 hab, sub_le_self _ ha⟩) hγ0).symm
  · simpa using key
  · rw [min_eq_right hba.le, sub_self] at key
    exact absurd key (I.disjoint_interior_boundary.ne_of_mem
      (hγi _ ⟨sub_pos.2 hba, sub_le_self _ hb⟩) hδ0)

end IsMIntegralCurveOn
