/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Analytic.IsolatedZeros
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity

/-!
# The local fibre count of a holomorphic map between Riemann surfaces

`TauCeti.localDegree` counts, on a disc in the complex plane, the orders of vanishing of `f - w`
as `w` ranges over the values close to `f z₀`; it is the analytic form of the statement that a
nonconstant holomorphic function maps a small disc onto a disc around the image of its centre,
counted with multiplicity. This file transports that count to a map `f : X → Y` between Riemann
surfaces, where the count is read as a sum of `TauCeti.RiemannSurface.localMultiplicity` over a
fibre of `f` restricted to a chart neighbourhood of the point. It is the counting consequence of
the local normal form `z ↦ z ^ m` of a nonconstant holomorphic map, obtained as a count rather
than as a conjugacy.

A degree read as a sum of local multiplicities over a whole fibre rests on the local statement
recorded here: close to a point where the multiplicity of `f` is positive, every nearby fibre is
finite, nonempty, and carries exactly the multiplicity of the base point, and the neighbourhood of
the point on which it is counted may be taken inside any prescribed neighbourhood. Nonconstancy of
`f` near `x` is therefore spelled as the hypothesis `¬ EventuallyConst f (𝓝 x)`, which says that
`localMultiplicity f x` is positive, so the count is a positive integer.

## Main declarations

* `TauCeti.RiemannSurface.exists_nhds_localMultiplicity_fiber_sum`: the local fibre count.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §10.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §3.
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] {f : X → Y} {x : X} {e : OpenPartialHomeomorph X ℂ}
  {e' : OpenPartialHomeomorph Y ℂ}

/-! ### The local fibre count -/

/-- A small disc about the chart coordinate of `x` on which the chart representative is analytic,
stays inside the chart sources, and has `e x` as an isolated zero. -/
private theorem exists_radius_of_notEventuallyConst
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (hx : x ∈ e.source) (hfx : f x ∈ e'.source)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) :
    ∃ r > 0,
      (∀ z ∈ Metric.closedBall (e x) r, e.symm z ∈ e.source) ∧
      (∀ z ∈ Metric.closedBall (e x) r, f (e.symm z) ∈ e'.source) ∧
      (∀ z ∈ Metric.closedBall (e x) r, z ≠ e x → f (e.symm z) ≠ f x) ∧
      AnalyticOnNhd ℂ (fun z ↦ e' (f (e.symm z))) (Metric.closedBall (e x) r) := by
  set F : ℂ → ℂ := fun z ↦ e' (f (e.symm z))
  have hFa : AnalyticAt ℂ F (e x) := analyticAt_chart_comp_comp_symm he he' hx hfx hf
  have hF0 : F (e x) = e' (f x) := by simp only [F, e.left_inv hx]
  have hcont : Tendsto (fun z ↦ f (e.symm z)) (𝓝 (e x)) (𝓝 (f x)) :=
    hf.self_of_nhds.continuousAt.tendsto.comp (e.tendsto_symm hx)
  have hZ1 : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ e.source :=
    (e.tendsto_symm hx).eventually (e.open_source.mem_nhds hx)
  have hZ2 : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ e'.source :=
    hcont.eventually (e'.open_source.mem_nhds hfx)
  -- Nonconstancy of `f` near `x` says that the representative `F` is not constant near `e x`.
  have hneF : ¬ EventuallyConst F (𝓝 (e x)) := by
    intro h
    obtain ⟨c, hc⟩ := h.eventuallyEq_const
    have hc0 : c = e' (f x) := by
      have hcz := hc.self_of_nhds
      simp only [F, e.left_inv hx] at hcz
      exact hcz.symm
    refine hne ((EventuallyConst.const (f x)).congr ?_)
    have hP2 : ∀ᶠ z in 𝓝 x, f (e.symm (e z)) ∈ e'.source := by
      exact (Filter.eventually_map (m := e) (f := 𝓝 x)
        (P := fun z => f (e.symm z) ∈ e'.source)).mp
          (Filter.Eventually.filter_mono (e.continuousAt hx).tendsto hZ2)
    have hP3 : ∀ᶠ z in 𝓝 x, F (e z) = c := by
      exact (Filter.eventually_map (m := e) (f := 𝓝 x) (P := fun z => F z = c)).mp
          (Filter.Eventually.filter_mono (e.continuousAt hx).tendsto hc.eventually)
    filter_upwards [e.open_source.mem_nhds hx, hP2, hP3] with x' hxsrc hz2 hz3
    have h3 : e' (f (e.symm (e x'))) = c := by simpa only [F] using hz3
    simpa only [e.left_inv hxsrc] using (e'.injOn hz2 hfx (h3.trans hc0)).symm
  -- By the principle of isolated zeros, the analytic function `F` agrees with the constant
  -- `F (e x)` at a nearby point only at `e x` itself, since it does not agree with it eventually.
  have hiso : ∀ᶠ z in 𝓝 (e x), z ≠ e x → F z ≠ F (e x) := by
    have h : ∀ᶠ z in 𝓝[≠] (e x), F z ≠ F (e x) :=
      (hFa.eventually_eq_or_eventually_ne analyticAt_const).resolve_left
        (fun heq => hneF (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨F (e x), heq⟩))
    simpa only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff, not_not] using h
  -- Shrinking the radius, the representative is analytic, its inverse chart is defined, its image
  -- stays in the target chart, and the zero `e x` of `F - F (e x)` is isolated there too.
  obtain ⟨ε₁, hε₁, hA₁⟩ := Metric.eventually_nhds_iff.mp hFa.eventually_analyticAt
  have hZ3 : ∀ᶠ z in 𝓝 (e x), F z = e' (f x) → z = e x :=
    hiso.mono fun z hz => fun hcon => by
      by_contra hne
      exact hz hne (hcon.trans hF0.symm)
  obtain ⟨ε₂, hε₂, hall'⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Eventually.and hZ1 hZ2)
  obtain ⟨ε₃, hε₃, hall''⟩ := Metric.eventually_nhds_iff.mp hZ3
  have hρ1 : min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2)) ≤ ε₁ / 2 := min_le_left _ _
  have hρ2 : min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2)) ≤ ε₂ / 2 :=
    le_trans (min_le_right (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2))) (min_le_left _ _)
  have hρ3 : min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2)) ≤ ε₃ / 2 :=
    le_trans (min_le_right (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2))) (min_le_right _ _)
  have hdist1 : ∀ z ∈ Metric.closedBall (e x) (min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2))),
      dist z (e x) < ε₁ := fun _ hz => by
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (lt_of_le_of_lt hρ1 (by linarith))
  have hdist2 : ∀ z ∈ Metric.closedBall (e x) (min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2))),
      dist z (e x) < ε₂ := fun _ hz => by
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (lt_of_le_of_lt hρ2 (by linarith))
  have hdist3 : ∀ z ∈ Metric.closedBall (e x) (min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2))),
      dist z (e x) < ε₃ := fun _ hz => by
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (lt_of_le_of_lt hρ3 (by linarith))
  refine ⟨min (ε₁ / 2) (min (ε₂ / 2) (ε₃ / 2)),
    lt_min (by linarith) (lt_min (by linarith) (by linarith)),
    fun z hz => (hall' (hdist2 z hz)).1,
    fun z hz => (hall' (hdist2 z hz)).2,
    fun z hz hzne hcon => ?_,
    fun z hz => ?_⟩
  · exact hzne (hall'' (hdist3 z hz) (by simp only [F, hcon]))
  · exact hA₁ (hdist1 z hz)

/-- The chart form of `TauCeti.RiemannSurface.exists_nhds_localMultiplicity_fiber_sum`, read in
arbitrary charts `e` at `x` and `e'` at `f x` of the maximal atlases, with the neighbourhood `U`
produced inside the neighbourhood `Ω₀` of `x` on which `f` is differentiable. The public statement
instantiates the charts with the preferred charts and `Ω₀` with the prescribed neighbourhood. -/
private theorem exists_nhds_localMultiplicity_fiber_sum_of_charts
    [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (hx : x ∈ e.source) (hfx : f x ∈ e'.source) {Ω₀ : Set X} (hΩ₀mem : Ω₀ ∈ 𝓝 x)
    (hΩ₀ : ∀ y ∈ Ω₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) :
    ∃ U ∈ 𝓝 x, U ⊆ Ω₀ ∧ ∃ V ∈ 𝓝 (f x),
      f ⁻¹' {f x} ∩ U = {x} ∧
      ∀ y' ∈ V,
        (f ⁻¹' {y'} ∩ U) ≠ ∅ ∧
        (f ⁻¹' {y'} ∩ U).Finite ∧
        (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ U, localMultiplicity f x') = localMultiplicity f x := by
  classical
  -- Transport of the planar count `TauCeti.localDegree` to Riemann surfaces. In charts `e` at `x`
  -- and `e'` at `f x` the representative `F = e' ∘ f ∘ e.symm` is analytic at `e x`, and the
  -- local multiplicity of `f` at `x` is the order of vanishing of `F - F (e x)` there
  -- (`localMultiplicity_eq_analyticOrderNatAt`); applying the same identity at each `x'` of the
  -- chart ball makes the summand of the planar count at `z` equal to
  -- `localMultiplicity f (e.symm z)`. The zeros of `F - w` in a closed disc are finite
  -- (`finite_setOf_mem_and_eq_zero_of_isCompact`), and reindexing the count along `e.symm` turns
  -- it into a sum over the fibre of `y' = e'.symm w` inside the chart neighbourhood. Finally
  -- `¬ EventuallyConst f (𝓝 x)` says the count is positive by `localMultiplicity_pos_iff`, so
  -- each such fibre is nonempty.
  -- The neighbourhood on which `f` is differentiable, taken open.
  have hΩopen : IsOpen (interior Ω₀) := isOpen_interior
  have hΩmem : interior Ω₀ ∈ 𝓝 x :=
    hΩopen.mem_nhds (mem_interior_iff_mem_nhds.2
      (Filter.eventually_of_mem hΩ₀mem fun y hy => hy))
  have hΩpt : ∀ y ∈ interior Ω₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    fun y hy => hΩ₀ y ((interior_subset : interior Ω₀ ⊆ Ω₀) hy)
  have hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    Filter.eventually_of_mem hΩmem fun y hy => hΩpt y hy
  -- A chart ball on which the chart representative is analytic and has no other zero over
  -- `e' (f x)`, shrunk so that its inverse image lies in the neighbourhood above.
  obtain ⟨r₀, hr₀, hsrc₀, hfimg₀, hisol₀, hA₀⟩ :=
    exists_radius_of_notEventuallyConst he he' hx hfx hf hne
  have hpre : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ interior Ω₀ ∧ z ∈ e.target := by
    filter_upwards [(e.tendsto_symm hx).eventually
        (Filter.eventually_of_mem hΩmem fun y hy => hy),
      Filter.eventually_of_mem (e.open_target.mem_nhds (e.map_source hx)) fun z hz => hz] with
      z hz₁ hz₂
    exact ⟨hz₁, hz₂⟩
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff_ball.mp hpre
  set r := min r₀ ρ
  have hr : 0 < r := lt_min hr₀ hρ
  have hle : r ≤ r₀ := min_le_left r₀ ρ
  have hleq : r ≤ ρ := min_le_right r₀ ρ
  have hdist : ∀ z ∈ Metric.closedBall (e x) r, z ∈ Metric.closedBall (e x) r₀ := by
    intro z hz
    have hlt : dist z (e x) ≤ r := Metric.mem_closedBall.1 hz
    have hlt' : dist z (e x) ≤ r₀ := hlt.trans hle
    exact Metric.mem_closedBall.2 hlt'
  have hsrc : ∀ z ∈ Metric.closedBall (e x) r, e.symm z ∈ e.source :=
    fun z hz => hsrc₀ z (hdist z hz)
  have hfimg : ∀ z ∈ Metric.closedBall (e x) r, f (e.symm z) ∈ e'.source :=
    fun z hz => hfimg₀ z (hdist z hz)
  have hisol : ∀ z ∈ Metric.closedBall (e x) r, z ≠ e x → f (e.symm z) ≠ f x :=
    fun z hz => hisol₀ z (hdist z hz)
  have hA : AnalyticOnNhd ℂ (fun z ↦ e' (f (e.symm z))) (Metric.closedBall (e x) r) :=
    fun z hz => hA₀ z (hdist z hz)
  have hcoord : ∀ z ∈ Metric.ball (e x) r, e.symm z ∈ interior Ω₀ ∧ z ∈ e.target := by
    intro z hz
    exact hρ' z (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) hleq))
  -- The differential condition holds eventually at every point of the chart neighbourhood.
  have hmd : ∀ x' ∈ e.symm '' Metric.ball (e x) r,
      ∀ᶠ y in 𝓝 x', MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y := by
    intro x' hx'
    have hx'Ω : x' ∈ interior Ω₀ := by
      obtain ⟨z, hz, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'
      exact (hcoord z hz).1
    exact Filter.eventually_of_mem (hΩopen.mem_nhds hx'Ω) fun y hy => hΩpt y hy
  -- Isolation of `x`, in the coordinates of the two charts.
  have hisol' : ∀ z ∈ Metric.closedBall (e x) r, z ≠ e x →
      e' (f (e.symm z)) ≠ e' (f (e.symm (e x))) := by
    intro z hz hzne hcon
    rw [e.left_inv hx] at hcon
    exact hisol z hz hzne (e'.injOn (hfimg z hz) hfx hcon)
  obtain ⟨δ, hδ, hcount⟩ := TauCeti.localDegree hr hA hisol'
  rw [e.left_inv hx] at hcount
  have hm : localMultiplicity f x
      = analyticOrderNatAt (fun z ↦ e' (f (e.symm z)) - e' (f x)) (e x) :=
    localMultiplicity_eq_analyticOrderNatAt he he' hx hfx hf
  -- The chart ball is a neighbourhood of `x`.
  have hU : e.symm '' Metric.ball (e x) r ∈ 𝓝 x :=
    (e.isOpen_image_symm_of_subset_target Metric.isOpen_ball
      fun z hz => (hcoord z hz).2).mem_nhds ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩
  have hV : (e' : Y → ℂ) ⁻¹' Metric.ball (e' (f x)) δ ∩ e'.source ∈ 𝓝 (f x) := by
    refine inter_mem ?_ (e'.open_source.mem_nhds hfx)
    exact (e'.continuousAt hfx).preimage_mem_nhds (Metric.ball_mem_nhds (e' (f x)) hδ)
  have hcenter : f ⁻¹' {f x} ∩ e.symm '' Metric.ball (e x) r = {x} := by
    ext b
    constructor
    · rintro ⟨hbf, hbU⟩
      have hbf' : f b = f x := by simpa using Set.mem_preimage.1 hbf
      obtain ⟨z, hz, rfl⟩ := (Set.mem_image e.symm _ _).1 hbU
      by_cases hze : z = e x
      · rw [hze]
        exact e.left_inv hx
      · exact ((hisol z (Metric.ball_subset_closedBall hz) hze) hbf').elim
    · intro hb
      refine ⟨?_, ?_⟩
      · rw [hb]
        simp
      · rw [hb]
        exact (Set.mem_image e.symm _ _).2 ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩
  refine ⟨e.symm '' Metric.ball (e x) r, hU, ?_,
    (e' : Y → ℂ) ⁻¹' Metric.ball (e' (f x)) δ ∩ e'.source, hV, hcenter, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact interior_subset (hcoord z hz).1
  intro y' hy'
  by_cases hcentral : y' = f x
  · -- The central fibre inside the chart neighbourhood is the singleton `{x}`.
    subst hcentral
    refine ⟨?_, ?_, ?_⟩
    · rw [hcenter]
      exact Set.singleton_ne_empty x
    · rw [hcenter]
      exact Set.finite_singleton x
    · rw [hcenter, finsum_mem_eq_finite_toFinset_sum _ (Set.finite_singleton x)]
      simp
  · have hy'ne : y' ≠ f x := hcentral
    obtain ⟨hwy, hy'dom⟩ := hy'
    have hw : dist (e' y') (e' (f x)) < δ := Metric.mem_ball.1 (Set.mem_preimage.1 hwy)
    have hne' : e' (f x) ≠ e' y' := by
      intro hcon
      exact hy'ne (e'.injOn hfx hy'dom hcon).symm
    -- The zeros of the recentred representative in the closed chart ball form a finite set.
    have hZfin : {z ∈ Metric.closedBall (e x) r | e' (f (e.symm z)) = e' y'}.Finite := by
      have han : AnalyticOnNhd ℂ (fun z : ℂ ↦ e' (f (e.symm z)) - e' y')
          (Metric.closedBall (e x) r) := hA.sub analyticOnNhd_const
      have hz0 : e' (f (e.symm (e x))) - e' y' ≠ 0 := by
        rw [e.left_inv hx]
        exact sub_ne_zero.mpr hne'
      have hfin := finite_setOf_mem_and_eq_zero_of_isCompact
        (g := fun z : ℂ ↦ e' (f (e.symm z)) - e' y') (U := Metric.closedBall (e x) r)
        (K := Metric.closedBall (e x) r) han ((convex_closedBall _ _).isPreconnected)
        (Metric.mem_closedBall_self (le_of_lt hr)) hz0 (isCompact_closedBall _ _) subset_rfl
      refine hfin.subset fun z hz => ?_
      have hz : z ∈ Metric.closedBall (e x) r ∧ e' (f (e.symm z)) = e' y' := by
        simpa only [Set.mem_ofPred_eq] using hz
      exact ⟨hz.1, sub_eq_zero.mpr hz.2⟩
    -- The zeros of the recentred representative inside the open chart ball.
    set Sb : Finset ℂ := hZfin.toFinset.filter (fun z => dist z (e x) < r)
    have hSbin : ∀ z ∈ Sb, z ∈ Metric.ball (e x) r ∧ e' (f (e.symm z)) = e' y' := by
      intro z hz
      obtain ⟨hz', hz''⟩ := Finset.mem_filter.mp hz
      have hz' : z ∈ Metric.closedBall (e x) r ∧ e' (f (e.symm z)) = e' y' :=
        Set.mem_ofPred_eq.mp (hZfin.mem_toFinset.1 hz')
      exact ⟨Metric.mem_ball.mpr hz'', hz'.2⟩
    -- Wherever the recentred representative has a positive order of vanishing inside the chart
    -- ball, it vanishes, so it is a zero counted by `Sb`.
    have hsub : (Metric.ball (e x) r ∩ Function.support
        (fun z : ℂ ↦ analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z)) ⊆ ↑Sb := by
      intro z hz
      have hz0 : (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z = 0 := by
        refine apply_eq_zero_of_analyticOrderNatAt_ne_zero
          (f := fun ζ ↦ e' (f (e.symm ζ)) - e' y') (z₀ := z) ?_
        exact Function.mem_support.1 hz.2
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨hZfin.mem_toFinset.2 ⟨Metric.ball_subset_closedBall hz.1, sub_eq_zero.mp hz0⟩, hz.1⟩)
    have hsum : (∑ᶠ z ∈ Metric.ball (e x) r,
          analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z)
        = ∑ z ∈ Sb, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z :=
      finsum_mem_eq_sum_of_subset _ hsub fun z hz => (hSbin z hz).1
    -- At each point of the fibre, the summand of the planar count is the local multiplicity.
    have hval : ∀ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r,
        localMultiplicity f x' = analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') (e x') := by
      intro x' hx'
      obtain ⟨hxf, hx'U⟩ := hx'
      obtain ⟨w, hw, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'U
      have hx'src : e.symm w ∈ e.source := hsrc w (Metric.ball_subset_closedBall hw)
      have hfz : f (e.symm w) ∈ e'.source := hfimg w (Metric.ball_subset_closedBall hw)
      have h1 := localMultiplicity_eq_analyticOrderNatAt he he' hx'src hfz (hmd _ hx'U)
      rw [congrArg e' hxf] at h1
      exact h1
    -- The chart ball carries the fibre of `y'` over `Sb`, in the coordinates of `e`.
    have hbij :
        (f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r).BijOn (fun x' : X => e x') Sb := by
      refine ⟨?_, e.injOn.mono fun x' hx' => ?_, ?_⟩
      · intro x' hx'
        obtain ⟨hxf, hx'U⟩ := hx'
        obtain ⟨w, hw, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'U
        -- The preimage of `x'` is the chart coordinate `w`, so it is enough to exhibit `w` in
        -- `Sb` explicitly and to read back the chart equation `e (e.symm w) = w` there.
        have hwSb : w ∈ ↑Sb := Finset.mem_coe.2 (Finset.mem_filter.2
          ⟨hZfin.mem_toFinset.2
            ⟨Metric.ball_subset_closedBall (Metric.mem_ball.2 hw), congrArg e' hxf⟩,
            Metric.mem_ball.2 hw⟩)
        simp only [e.right_inv ((hcoord w hw).2)]
        exact hwSb
      · obtain ⟨w, hw, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'.2
        exact hsrc w (Metric.ball_subset_closedBall hw)
      · intro z hz
        obtain ⟨hzball, hzf⟩ := hSbin z hz
        have hfz : f (e.symm z) ∈ e'.source := hfimg z (Metric.ball_subset_closedBall hzball)
        refine ⟨e.symm z, ⟨?_, (Set.mem_image e.symm _ _).2 ⟨z, hzball, rfl⟩⟩, ?_⟩
        · rw [Set.mem_preimage]
          exact e'.injOn hfz hy'dom hzf
        · exact e.right_inv ((hcoord z hzball).2)
    have hSbF : (↑Sb : Set ℂ).Finite := Finset.finite_toSet _
    have hconv : hSbF.toFinset = Sb := by
      ext z
      simp only [Set.Finite.mem_toFinset, Finset.mem_coe]
    have hsum2 :
        (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r, localMultiplicity f x')
          = ∑ z ∈ Sb, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z := by
      calc (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r, localMultiplicity f x')
          = ∑ᶠ z ∈ (↑Sb : Set ℂ),
              analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z :=
            finsum_mem_eq_of_bijOn _ hbij hval
        _ = ∑ z ∈ Sb, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z :=
            finsum_mem_eq_finite_toFinset_sum _ hSbF |>.trans (by rw [hconv])
    have hcount' : (∑ z ∈ Sb, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z)
        = localMultiplicity f x := by
      rw [← hsum, hm]
      exact hcount (e' y') (by simpa only [dist_eq_norm] using hw)
    refine ⟨?_, hbij.finite_iff_finite.mpr hSbF, hsum2.trans hcount'⟩
    · -- The count is positive, so `Sb` is nonempty, and the surjectivity of `hbij` exhibits a
      -- point of the fibre of `y'` inside the chart ball.
      have hpos : 0 < localMultiplicity f x := (localMultiplicity_pos_iff hf).mpr hne
      have hSbne : Sb.Nonempty := by
        by_contra hc
        have hzero : (∑ z ∈ Sb,
            analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z) = 0 := by
          rw [Finset.not_nonempty_iff_eq_empty.1 hc, Finset.sum_empty]
        rw [hzero] at hcount'
        exact hpos.ne' hcount'.symm
      obtain ⟨z, hz⟩ := hSbne
      obtain ⟨x', hx', -⟩ :
          ∃ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r, e x' = z :=
        hbij.2.2 (Finset.mem_coe.2 hz)
      exact Set.nonempty_iff_ne_empty.1 ⟨x', hx'⟩

/-- **The local fibre count.** Let `f : X → Y` be differentiable at every point of a neighbourhood
of `x` and not constant near `x`, and let `W` be any neighbourhood of `x`. There are
neighbourhoods `U ⊆ W` of `x` and `V` of `f x` such that `x` is the only preimage of `f x` inside
`U`, and for every `y' ∈ V` the fibre of `y'` meets `U`, is finite there, and the sum of the local
multiplicities over it is exactly `localMultiplicity f x`.

This is the counting consequence of the local normal form `z ↦ z ^ m` of a nonconstant
holomorphic map, read without choosing a conjugacy: the multiplicity of `f` at `x` is the number
of preimages of a nearby value, counted with multiplicities. That `U` can be taken inside any
prescribed neighbourhood is what makes the counts at the finitely many points of a fibre combine
into a count over the whole fibre. -/
theorem exists_nhds_localMultiplicity_fiber_sum
    [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
    (hDiff : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ U ∈ 𝓝 x, U ⊆ W ∧ ∃ V ∈ 𝓝 (f x),
      f ⁻¹' {f x} ∩ U = {x} ∧
      ∀ y' ∈ V,
        (f ⁻¹' {y'} ∩ U) ≠ ∅ ∧
        (f ⁻¹' {y'} ∩ U).Finite ∧
        (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ U, localMultiplicity f x') = localMultiplicity f x := by
  obtain ⟨U, hU, hUW, h⟩ := exists_nhds_localMultiplicity_fiber_sum_of_charts
    (e := chartAt ℂ x) (e' := chartAt ℂ (f x))
    (he := chart_mem_maximalAtlas x) (he' := chart_mem_maximalAtlas (f x))
    (hx := mem_chart_source ℂ x) (hfx := mem_chart_source ℂ (f x))
    (hΩ₀mem := inter_mem hDiff hW) (hΩ₀ := fun _ hy => hy.1) (hne := hne)
  exact ⟨U, hU, hUW.trans inter_subset_right, h⟩

end TauCeti.RiemannSurface

end
