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

omit [ChartedSpace ℂ X] [ChartedSpace ℂ Y] in
/-- If `f` is not eventually constant near `x`, then its chart representative `e' ∘ f ∘ e.symm` is
not eventually constant near `e x`, provided `f ∘ e.symm` maps a neighbourhood of `e x` into the
source of `e'`. -/
theorem not_eventuallyConst_chart_comp_symm (hx : x ∈ e.source) (hfx : f x ∈ e'.source)
    (hZ2 : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ e'.source)
    (hne : ¬ EventuallyConst f (𝓝 x)) :
    ¬ EventuallyConst (fun z ↦ e' (f (e.symm z))) (𝓝 (e x)) := by
  set F : ℂ → ℂ := fun z ↦ e' (f (e.symm z))
  intro h
  obtain ⟨c, hc⟩ := h.eventuallyEq_const
  have hc0 : c = e' (f x) := by
    have hcz := hc.self_of_nhds
    simp only [F, e.left_inv hx] at hcz
    exact hcz.symm
  refine hne ((EventuallyConst.const (f x)).congr ?_)
  have hP2 : ∀ᶠ z in 𝓝 x, f (e.symm (e z)) ∈ e'.source :=
    (Filter.eventually_map (m := e) (f := 𝓝 x)
      (P := fun z => f (e.symm z) ∈ e'.source)).mp
        (Filter.Eventually.filter_mono (e.continuousAt hx).tendsto hZ2)
  have hP3 : ∀ᶠ z in 𝓝 x, F (e z) = c :=
    (Filter.eventually_map (m := e) (f := 𝓝 x) (P := fun z => F z = c)).mp
      (Filter.Eventually.filter_mono (e.continuousAt hx).tendsto hc.eventually)
  filter_upwards [e.open_source.mem_nhds hx, hP2, hP3] with x' hxsrc hz2 hz3
  have h3 : e' (f (e.symm (e x'))) = c := by simpa only [F] using hz3
  simpa only [e.left_inv hxsrc] using (e'.injOn hz2 hfx (h3.trans hc0)).symm

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
  have hneF : ¬ EventuallyConst F (𝓝 (e x)) :=
    not_eventuallyConst_chart_comp_symm hx hfx hZ2 hne
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

/-- A closed chart ball about `e x` on which the chart representative of `f` is analytic, the
inverse chart and `f` land in the chart sources, `e x` is the only point over `f x`, and whose open
ball maps under `e.symm` into the open set `Ω` of differentiability, where `f` is differentiable
near every point. -/
private theorem exists_closedBall_chart_representative
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (hx : x ∈ e.source) (hfx : f x ∈ e'.source) {Ω : Set X} (hΩ : IsOpen Ω) (hxΩ : x ∈ Ω)
    (hΩf : ∀ y ∈ Ω, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) :
    ∃ r > 0,
      (∀ z ∈ Metric.closedBall (e x) r, e.symm z ∈ e.source) ∧
      (∀ z ∈ Metric.closedBall (e x) r, f (e.symm z) ∈ e'.source) ∧
      (∀ z ∈ Metric.closedBall (e x) r, z ≠ e x → f (e.symm z) ≠ f x) ∧
      AnalyticOnNhd ℂ (fun z ↦ e' (f (e.symm z))) (Metric.closedBall (e x) r) ∧
      (∀ z ∈ Metric.ball (e x) r, e.symm z ∈ Ω ∧ z ∈ e.target) ∧
      (∀ z ∈ Metric.ball (e x) r, ∀ᶠ y in 𝓝 (e.symm z), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) := by
  have hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    Filter.eventually_of_mem (hΩ.mem_nhds hxΩ) hΩf
  obtain ⟨r₀, hr₀, hsrc₀, hfimg₀, hisol₀, hA₀⟩ :=
    exists_radius_of_notEventuallyConst he he' hx hfx hf hne
  have hpre : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ Ω ∧ z ∈ e.target := by
    filter_upwards [(e.tendsto_symm hx).eventually (hΩ.mem_nhds hxΩ),
      e.open_target.mem_nhds (e.map_source hx)] with z hz₁ hz₂
    exact ⟨hz₁, hz₂⟩
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff_ball.mp hpre
  have hdist : ∀ z ∈ Metric.closedBall (e x) (min r₀ ρ), z ∈ Metric.closedBall (e x) r₀ :=
    fun z hz => Metric.closedBall_subset_closedBall (min_le_left _ _) hz
  have hcoord : ∀ z ∈ Metric.ball (e x) (min r₀ ρ), e.symm z ∈ Ω ∧ z ∈ e.target :=
    fun z hz => hρ' z (Metric.ball_subset_ball (min_le_right _ _) hz)
  exact ⟨min r₀ ρ, lt_min hr₀ hρ, fun z hz => hsrc₀ z (hdist z hz),
    fun z hz => hfimg₀ z (hdist z hz), fun z hz => hisol₀ z (hdist z hz),
    fun z hz => hA₀ z (hdist z hz), hcoord,
    fun z hz => Filter.eventually_of_mem (hΩ.mem_nhds (hcoord z hz).1) hΩf⟩

/-- If `g` is analytic on a closed disc and does not vanish at its centre, then it has finitely many
zeros in the open disc, and the sum over the open disc of the orders of vanishing of `g` is the
sum of those orders over the finite set `S` of zeros. -/
theorem exists_finset_finsum_ball_analyticOrderNatAt_eq_sum {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (Metric.closedBall c r)) (hgc : g c ≠ 0) :
    ∃ S : Finset ℂ, (∀ z, z ∈ S ↔ z ∈ Metric.ball c r ∧ g z = 0) ∧
      (∑ᶠ z ∈ Metric.ball c r, analyticOrderNatAt g z) = ∑ z ∈ S, analyticOrderNatAt g z := by
  classical
  have hfin : {z | z ∈ Metric.ball c r ∧ g z = 0}.Finite :=
    (hg.finite_setOf_mem_and_eq_zero_of_isCompact (convex_closedBall _ _).isPreconnected
      (Metric.mem_closedBall_self hr.le) hgc (isCompact_closedBall _ _) subset_rfl).subset
      fun z hz => ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩
  refine ⟨hfin.toFinset, fun z => by simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq],
    finsum_mem_eq_sum_of_subset _ (fun z hz => ?_) fun z hz => ?_⟩
  · exact (hfin.mem_toFinset (a := z)).2
      ⟨hz.1, apply_eq_zero_of_analyticOrderNatAt_ne_zero (Function.mem_support.1 hz.2)⟩
  · exact (Finset.mem_coe.1 hz |> hfin.mem_toFinset.1).1

/-- The fibre of `f` over `y'` inside a chart ball is carried by the chart `e` onto the set `S` of
zeros of the recentred representative `e' ∘ f ∘ e.symm - e' y'`, and the sum of the local
multiplicities of `f` over the fibre is the sum over `S` of the orders of vanishing. -/
private theorem fiber_sum_eq_sum_of_zeros [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    {r : ℝ} {y' : Y} (hy' : y' ∈ e'.source)
    (hsrc : ∀ z ∈ Metric.closedBall (e x) r, e.symm z ∈ e.source)
    (hfimg : ∀ z ∈ Metric.closedBall (e x) r, f (e.symm z) ∈ e'.source)
    (hcoord : ∀ z ∈ Metric.ball (e x) r, z ∈ e.target)
    (hmd : ∀ z ∈ Metric.ball (e x) r,
      ∀ᶠ y in 𝓝 (e.symm z), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    {S : Finset ℂ}
    (hS : ∀ z, z ∈ S ↔ z ∈ Metric.ball (e x) r ∧ e' (f (e.symm z)) = e' y') :
    (f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r).BijOn (fun x' : X => e x') S ∧
      (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r, localMultiplicity f x') =
        ∑ z ∈ S, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z := by
  -- At each point of the fibre, the summand of the planar count is the local multiplicity.
  have hval : ∀ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r,
      localMultiplicity f x' = analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') (e x') := by
    intro x' hx'
    obtain ⟨hxf, hx'U⟩ := hx'
    obtain ⟨w, hw, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'U
    have h1 := localMultiplicity_eq_analyticOrderNatAt he he'
      (hsrc w (Metric.ball_subset_closedBall hw)) (hfimg w (Metric.ball_subset_closedBall hw))
      (hmd w hw)
    rw [congrArg e' hxf] at h1
    exact h1
  have hbij : (f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r).BijOn (fun x' : X => e x') S := by
    refine ⟨?_, e.injOn.mono fun x' hx' => ?_, ?_⟩
    · intro x' hx'
      obtain ⟨hxf, hx'U⟩ := hx'
      obtain ⟨w, hw, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'U
      simp only [e.right_inv (hcoord w hw), Finset.mem_coe]
      exact (hS w).2 ⟨hw, congrArg e' hxf⟩
    · obtain ⟨w, hw, rfl⟩ := (Set.mem_image e.symm _ _).1 hx'.2
      exact hsrc w (Metric.ball_subset_closedBall hw)
    · intro z hz
      obtain ⟨hzball, hzf⟩ := (hS z).1 hz
      refine ⟨e.symm z, ⟨?_, (Set.mem_image e.symm _ _).2 ⟨z, hzball, rfl⟩⟩, ?_⟩
      · exact e'.injOn (hfimg z (Metric.ball_subset_closedBall hzball)) hy' hzf
      · exact e.right_inv (hcoord z hzball)
  refine ⟨hbij, (finsum_mem_eq_of_bijOn _ hbij hval).trans ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ S.finite_toSet, Finset.finite_toSet_toFinset]

omit [ChartedSpace ℂ X] [TopologicalSpace Y] [ChartedSpace ℂ Y] in
/-- The fibre of `f` over `f x` inside a chart ball about `x` on which `x` is the only point over
`f x` is `{x}`. -/
private theorem fiber_center_inter_image_symm (hx : x ∈ e.source) {r : ℝ} (hr : 0 < r)
    (hisol : ∀ z ∈ Metric.closedBall (e x) r, z ≠ e x → f (e.symm z) ≠ f x) :
    f ⁻¹' {f x} ∩ e.symm '' Metric.ball (e x) r = {x} := by
  have hxmem : x ∈ e.symm '' Metric.ball (e x) r :=
    ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩
  ext b
  refine ⟨fun ⟨hbf, hbU⟩ => ?_, fun hb => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hbU
    by_cases hze : z = e x
    · rw [hze]
      exact e.left_inv hx
    · exact ((hisol z (Metric.ball_subset_closedBall hz) hze) hbf).elim
  · rw [Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨rfl, hxmem⟩

/-- Over a value `y' ≠ f x` of the target chart close enough to `f x` that the planar count at
`e' y'` equals `localMultiplicity f x`, the fibre of `y'` inside the chart ball is nonempty
and finite, and the sum of the local multiplicities over it is `localMultiplicity f x`. -/
private theorem fiber_count_of_ne [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (hx : x ∈ e.source) (hfx : f x ∈ e'.source) {r δ : ℝ} (hr : 0 < r)
    (hsrc : ∀ z ∈ Metric.closedBall (e x) r, e.symm z ∈ e.source)
    (hfimg : ∀ z ∈ Metric.closedBall (e x) r, f (e.symm z) ∈ e'.source)
    (hA : AnalyticOnNhd ℂ (fun z ↦ e' (f (e.symm z))) (Metric.closedBall (e x) r))
    (hcoord : ∀ z ∈ Metric.ball (e x) r, z ∈ e.target)
    (hmd : ∀ z ∈ Metric.ball (e x) r,
      ∀ᶠ y in 𝓝 (e.symm z), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hpos : 0 < localMultiplicity f x)
    (hcount : ∀ w : ℂ, dist w (e' (f x)) < δ →
      (∑ᶠ z ∈ Metric.ball (e x) r, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - w) z) =
        localMultiplicity f x)
    {y' : Y} (hy'ne : y' ≠ f x) (hy' : y' ∈ e'.source) (hw : dist (e' y') (e' (f x)) < δ) :
    (f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r) ≠ ∅ ∧
      (f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r).Finite ∧
      (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ e.symm '' Metric.ball (e x) r, localMultiplicity f x') =
        localMultiplicity f x := by
  have hne' : e' (f x) ≠ e' y' := fun hcon => hy'ne (e'.injOn hfx hy' hcon).symm
  have hz0 : e' (f (e.symm (e x))) - e' y' ≠ 0 := by
    rw [e.left_inv hx]
    exact sub_ne_zero.mpr hne'
  obtain ⟨S, hS, hsum⟩ := exists_finset_finsum_ball_analyticOrderNatAt_eq_sum hr
    (g := fun ζ ↦ e' (f (e.symm ζ)) - e' y') (hA.sub analyticOnNhd_const) hz0
  obtain ⟨hbij, hsum2⟩ := fiber_sum_eq_sum_of_zeros he he' hy' hsrc hfimg hcoord hmd
    (S := S) fun z => (hS z).trans (and_congr_right fun _ => sub_eq_zero)
  have hcount' : (∑ z ∈ S, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - e' y') z)
      = localMultiplicity f x := by
    rw [← hsum]
    exact hcount (e' y') hw
  refine ⟨?_, hbij.finite_iff_finite.mpr S.finite_toSet, hsum2.trans hcount'⟩
  -- The count is positive, so `S` is nonempty, and `hbij` carries a point of the fibre onto it.
  obtain ⟨z, hz⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.sum_empty] at hcount'
    exact hpos.ne' hcount'.symm
  obtain ⟨x', hx', -⟩ := hbij.2.2 (Finset.mem_coe.2 hz)
  exact Set.nonempty_iff_ne_empty.1 ⟨x', hx'⟩

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
  -- (`localMultiplicity_eq_analyticOrderNatAt`). The count over a chart ball is then reindexed
  -- along `e.symm` into a sum over the fibre inside the chart neighbourhood
  -- (`fiber_count_of_ne`), and `¬ EventuallyConst f (𝓝 x)` makes the count positive by
  -- `localMultiplicity_pos_iff`, so each such fibre is nonempty.
  have hxΩ : x ∈ interior Ω₀ := mem_interior_iff_mem_nhds.2 hΩ₀mem
  have hΩf : ∀ y ∈ interior Ω₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    fun y hy => hΩ₀ y (interior_subset hy)
  have hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hxΩ) hΩf
  obtain ⟨r, hr, hsrc, hfimg, hisol, hA, hcoord, hmd⟩ :=
    exists_closedBall_chart_representative he he' hx hfx isOpen_interior hxΩ hΩf hne
  have hcoordT : ∀ z ∈ Metric.ball (e x) r, z ∈ e.target := fun z hz => (hcoord z hz).2
  -- Isolation of `x`, in the coordinates of the two charts.
  have hisol' : ∀ z ∈ Metric.closedBall (e x) r, z ≠ e x →
      e' (f (e.symm z)) ≠ e' (f (e.symm (e x))) := by
    intro z hz hzne hcon
    rw [e.left_inv hx] at hcon
    exact hisol z hz hzne (e'.injOn (hfimg z hz) hfx hcon)
  obtain ⟨δ, hδ, hcount⟩ := TauCeti.localDegree hr hA hisol'
  rw [e.left_inv hx] at hcount
  have hcount' : ∀ w : ℂ, dist w (e' (f x)) < δ →
      (∑ᶠ z ∈ Metric.ball (e x) r, analyticOrderNatAt (fun ζ ↦ e' (f (e.symm ζ)) - w) z) =
        localMultiplicity f x := fun w hw => by
    rw [localMultiplicity_eq_analyticOrderNatAt he he' hx hfx hf]
    exact hcount w (by simpa only [dist_eq_norm] using hw)
  -- The chart ball is a neighbourhood of `x`.
  have hU : e.symm '' Metric.ball (e x) r ∈ 𝓝 x :=
    (e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hcoordT).mem_nhds
      ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩
  have hV : (e' : Y → ℂ) ⁻¹' Metric.ball (e' (f x)) δ ∩ e'.source ∈ 𝓝 (f x) := by
    refine inter_mem ?_ (e'.open_source.mem_nhds hfx)
    exact (e'.continuousAt hfx).preimage_mem_nhds (Metric.ball_mem_nhds (e' (f x)) hδ)
  have hcenter := fiber_center_inter_image_symm hx hr hisol
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
  · exact fiber_count_of_ne he he' hx hfx hr hsrc hfimg hA hcoordT hmd
      ((localMultiplicity_pos_iff hf).mpr hne) hcount' hcentral hy'.2
      (Metric.mem_ball.1 (Set.mem_preimage.1 hy'.1))

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
