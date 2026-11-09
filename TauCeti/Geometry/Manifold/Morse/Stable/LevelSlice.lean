/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
public import TauCeti.Dynamics.Flow.LevelCrossing
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Level slices of transverse trajectories of an adapted pseudo-gradient

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient field adapted to `f`, and `a ≠ b` critical points of `f`. Along a trajectory from
`a` to `b` the function `f` strictly decreases from `f a` to `f b`, so the trajectory crosses each
intermediate level `{f = c}` exactly once
(`TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`). The
level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` therefore contains one point of each unparametrized
trajectory from `a` to `b`.

This file shows that, where `W^u(a)` and `W^s(b)` meet transversally, the slice is an embedded
submanifold of dimension `ind a - ind b - 1`. The level `{f = c}` cuts `W^u(a) ∩ W^s(b)`
transversally: the velocity `X y` of the trajectory through a point `y` of the slice is tangent to
`W^u(a) ∩ W^s(b)`, while `df_y (X y) < 0`. Hence a chart of the maximal atlas flattens the slice
onto the tangent space of `W^u(a) ∩ W^s(b)` at `y` cut by `ker df_y`, which has one dimension less.

Under the Morse–Smale condition the slice is therefore a smooth manifold of dimension
`ind a - ind b - 1`, and when the Morse indices differ by one it is discrete: its points are the
isolated trajectories that the Morse differential counts. These are the manifold forms of the
results of `TauCeti.Analysis.Calculus.Morse.TrajectorySpace` for a negative-gradient flow on a
vector space.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.mem_Ioo_of_mem_unstableSet_inter_stableSet`: the points of a
  trajectory from `a` to `b` have values strictly between `f b` and `f a`.
* `TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`: a
  trajectory from `a` to `b` crosses each value strictly between `f b` and `f a` exactly once.
* `TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet`
  (the case `c = (f a + f b) / 2`): a trajectory from `a` to `b` crosses the middle level exactly
  once.
* `TauCeti.IsAdaptedPseudoGradient.eq_of_flow_eq_of_value_eq`: a point of such a trajectory is
  determined by its orbit and its level.
* `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_flow_of_tendsto`: if a point of such a
  trajectory is the limit of a family of points, the crossings of an intermediate level by their
  orbits converge to the crossing of the limit orbit.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet`:
  the time at which an orbit crosses the level of a point `y` of such a trajectory depends
  continuously on the orbit near `y`.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_flow_levelCrossingTime`: the point where an orbit
  crosses a level depends continuously on the orbit near a connecting trajectory.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top`:
  every level of `f` is transverse to `W^u(a) ∩ W^s(b)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_inter_stableSet_level_chart`: under
  transversality, a chart of the maximal atlas flattens the level slice.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet_level`: its
  tangent space is the intersection of the tangent spaces of `W^u(a)` and `W^s(b)` with
  `ker df_y`.
* `finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex` (in the
  namespace `TauCeti.IsAdaptedPseudoGradient`): the slice has dimension `ind a - ind b - 1`.
* `TauCeti.IsAdaptedPseudoGradient.isDiscrete_unstableSet_inter_stableSet_level`: if the Morse
  indices differ by one, the transverse slice is discrete.
* `IsMorseSmale.exists_unstableSet_inter_stableSet_level_isManifold` (in the namespace
  `TauCeti.IsAdaptedPseudoGradient`): under the Morse–Smale condition, the slice is a smooth
  manifold of dimension `ind a - ind b - 1`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of trajectories).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b y : M} {c : ℝ}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- Along a trajectory joining distinct critical points, `df_y (X y) < 0`, read in the preferred
chart at `y`. -/
private theorem fderiv_comp_chartAt_symm_apply_lt_zero (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) (X y) < 0 := by
  rw [MDifferentiableAt.fderiv_comp_chartAt_symm hd]
  exact hX.mvfderiv_apply_lt_zero y (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hab hy)

/-- Along a trajectory joining distinct critical points, `df_y` is onto `ℝ`, read in the preferred
chart at `y`: it does not vanish on `X y`. -/
private theorem surjective_fderiv_comp_chartAt_symm (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Function.Surjective (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y)) := by
  -- A linear form that is negative on some vector `v` of the model space is nonzero.
  have key : ∀ v : E, fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) v < 0 →
      (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ) ≠ 0 := fun v hv h0 ↦
    hv.ne (by rw [← ContinuousLinearMap.coe_coe, h0, LinearMap.zero_apply])
  exact LinearMap.surjective_of_ne_zero
    (key _ (hX.fderiv_comp_chartAt_symm_apply_lt_zero hd hab hy))

/-- **`f` strictly decreases along a connecting trajectory.** A trajectory from a critical point
`a` to a different critical point `b` meets no critical point, so `f` is strictly antitone along
it. -/
theorem strictAnti_flow_of_mem_unstableSet_inter_stableSet
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    StrictAnti fun t ↦ f (hX.flow t y) :=
  hX.strictAnti_comp (hX.isMIntegralCurve_flow y)
    fun t ↦ hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet
      hab (hX.flow.isInvariant_unstableSet_inter_stableSet a b t hy)

/-- **Connecting trajectories lie strictly between the critical values of their ends.** A point
`y` on a trajectory from a critical point `a` to a different critical point `b` satisfies
`f b < f y < f a`. -/
theorem mem_Ioo_of_mem_unstableSet_inter_stableSet
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    f y ∈ Ioo (f b) (f a) := by
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy
  -- Compare `y` with its images at times `1` and `-1`, which lie on the same trajectory.
  have hb : f b ≤ f (hX.flow 1 y) := Flow.le_of_mem_stableSet_of_antitone
    ((Flow.apply_mem_stableSet_iff _ 1).2 hy.2) hf.continuous.continuousAt
    (hX.antitone_flow hf _)
  have ha : f (hX.flow (-1) y) ≤ f a := Flow.le_of_mem_unstableSet_of_antitone
    ((Flow.apply_mem_unstableSet_iff _ (-1)).2 hy.1) hf.continuous.continuousAt
    (hX.antitone_flow hf _)
  have h₁ : f (hX.flow 1 y) < f y := by
    simpa only [Flow.map_zero_apply] using hanti zero_lt_one
  have h₂ : f y < f (hX.flow (-1) y) := by
    simpa only [Flow.map_zero_apply] using hanti (neg_lt_zero.2 zero_lt_one)
  exact ⟨hb.trans_lt h₁, h₂.trans_le ha⟩

/-- **A trajectory crosses each intermediate level exactly once.** Along a trajectory from a
critical point `a` to a different critical point `b`, the function `f` strictly decreases from
`f a` to `f b`, so it takes each value `c` with `f b < c < f a` at exactly one time. -/
theorem existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (hbc : f b < c)
    (hca : c < f a) :
    ∃! t : ℝ, f (hX.flow t y) = c :=
  Flow.existsUnique_apply_flow_eq_of_mem_unstableSet_inter_stableSet
    (hf.continuous.comp (hX.flow.continuous continuous_id continuous_const))
    hf.continuous.continuousAt hf.continuous.continuousAt
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy) hy ⟨hbc, hca⟩

/-- **A trajectory crosses the middle level exactly once.** Along a trajectory from a critical
point `a` to a different critical point `b`, the function `f` takes the value `(f a + f b) / 2`
at exactly one time. -/
theorem existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    ∃! t : ℝ, f (hX.flow t y) = (f a + f b) / 2 := by
  have hval := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hab hy
  exact hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hab hy
    (by linarith [hval.1, hval.2]) (by linarith [hval.1, hval.2])

/-- **A point of a trajectory is determined by its orbit and its level.** Two points that lie on a
common orbit and a common level coincide, if one of them is on a trajectory between distinct
points. -/
theorem eq_of_flow_eq_of_value_eq {y' : M}
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {t t' : ℝ}
    (h : hX.flow t y = hX.flow t' y') (hv : f y = f y') : y = y' := by
  have hy' : y' = hX.flow (t - t') y := by
    rw [show t - t' = -t' + t by ring, Flow.map_add, h, ← Flow.map_add, neg_add_cancel,
      Flow.map_zero_apply]
  have h0 := (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy).injective
    (show f (hX.flow (t - t') y) = f (hX.flow 0 y) by rw [← hy', Flow.map_zero_apply, hv])
  rw [hy', h0, Flow.map_zero_apply]

/-- **Level-crossing times depend continuously on the point.** Let `y` lie on a trajectory from a
critical point `a` to a different critical point `b`, and let `w` tend to `y`. If the orbit of each
`w i` meets the level of `y` at the time `σ i`, then `σ i` tends to `0`, the time at which the orbit
of `y` meets that level. -/
theorem tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet {ι : Type*} {l : Filter ι}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {w : ι → M} (hw : Tendsto w l (𝓝 y))
    {σ : ι → ℝ} (hσ : ∀ i, f (hX.flow (σ i) (w i)) = f y) : Tendsto σ l (𝓝 0) := by
  have hfw : ∀ t, Tendsto (fun i ↦ f (hX.flow t (w i))) l (𝓝 (f (hX.flow t y))) := fun t ↦
    ((hf.continuous.comp (hX.contMDiff_flow_apply t).continuous).tendsto y).comp hw
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy
  -- For `t ≠ 0`, the orbit of `w i` is eventually on the same side of the level at time `t` as
  -- the orbit of `y`; since `f` decreases along orbits, it crosses the level between `0` and `t`.
  refine tendsto_order.2 ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have hlt : f y < f (hX.flow t y) := by simpa using hanti ht
    filter_upwards [(hfw t).eventually (lt_mem_nhds hlt)] with i hi
    by_contra! hle
    exact (hX.antitone_flow hf (w i) hle).not_gt ((hσ i).trans_lt hi)
  · have hlt : f (hX.flow t y) < f y := by simpa using hanti ht
    filter_upwards [(hfw t).eventually (gt_mem_nhds hlt)] with i hi
    by_contra! hle
    exact (hX.antitone_flow hf (w i) hle).not_gt (hi.trans_eq (hσ i).symm)

/-- Orbits through points near a point `y` of a trajectory between distinct critical points cross
the level of `y` at times in `[-δ, δ]`. -/
theorem eventually_exists_mem_Icc_apply_flow_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in 𝓝 y, ∃ σ ∈ Icc (-δ) δ, f (hX.flow σ w) = f y := by
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy
  have hcont : ∀ t, Continuous fun w ↦ f (hX.flow t w) := fun t ↦
    hf.continuous.comp (hX.contMDiff_flow_apply t).continuous
  have h₁ : f (hX.flow δ y) < f y := by simpa using hanti hδ
  have h₂ : f y < f (hX.flow (-δ) y) := by simpa using hanti (neg_lt_zero.2 hδ)
  filter_upwards [(hcont δ).continuousAt.eventually (gt_mem_nhds h₁),
    (hcont (-δ)).continuousAt.eventually (lt_mem_nhds h₂)] with w hw₁ hw₂
  exact intermediate_value_Icc' (by linarith)
    (hf.continuous.comp (hX.flow.continuous continuous_id continuous_const)).continuousOn
    ⟨hw₁.le, hw₂.le⟩

/-- **The level point of an orbit depends continuously on the orbit.** Let `y` lie on a trajectory
between distinct critical points, with `f (flow σ₀ y) = c`. For points `w i` tending to `y` along
whose orbits `f` strictly decreases, the points where these orbits cross the level `c` tend to
`flow σ₀ y`. -/
theorem tendsto_flow_levelCrossingTime (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {σ₀ : ℝ}
    (hσ₀ : f (hX.flow σ₀ y) = c) {ι : Type*} {l : Filter ι} {w : ι → M}
    (hw : Tendsto w l (𝓝 y)) (hanti : ∀ᶠ i in l, StrictAnti fun t ↦ f (hX.flow t (w i))) :
    Tendsto (fun i ↦ hX.flow (Flow.levelCrossingTime hX.flow f c (w i)) (w i)) l
      (𝓝 (hX.flow σ₀ y)) := by
  set z := hX.flow σ₀ y
  have hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b :=
    hX.flow.isInvariant_unstableSet_inter_stableSet a b σ₀ hy
  have hw' : Tendsto (fun i ↦ hX.flow σ₀ (w i)) l (𝓝 z) :=
    ((hX.flow.continuous_toFun σ₀).tendsto y).comp hw
  set τ := fun i ↦ Flow.levelCrossingTime hX.flow f c (w i) - σ₀
  -- The crossing time of `w i` differs from `σ₀` by a crossing time of `flow σ₀ (w i)` near `0`.
  have hτ : ∀ δ > 0, ∀ᶠ i in l, τ i ∈ Icc (-δ) δ := fun δ hδ ↦ by
    filter_upwards [hw'.eventually (hX.eventually_exists_mem_Icc_apply_flow_eq hf hab hz hδ),
      hanti] with i ⟨σ, hσ, hσc⟩ hi
    rw [hσ₀, ← Flow.map_add] at hσc
    have := (Flow.eq_levelCrossingTime_iff hi ⟨_, hσc⟩).2 hσc
    simp only [τ, ← this, add_sub_cancel_right]
    exact hσ
  have hτ0 : Tendsto τ l (𝓝 0) := tendsto_order.2
    ⟨fun r hr ↦ (hτ (-r / 2) (by linarith)).mono fun i hi ↦ by linarith [hi.1],
      fun r hr ↦ (hτ (r / 2) (by linarith)).mono fun i hi ↦ by linarith [hi.2]⟩
  have h := (hX.flow.cont'.tendsto (0, z)).comp (hτ0.prodMk_nhds hw')
  simp only [Function.comp_def, Function.uncurry_apply_pair, Flow.map_zero_apply] at h
  refine h.congr fun i ↦ ?_
  rw [← Flow.map_add, sub_add_cancel]

/-- **Level crossings converge along converging orbits.** Let `w` lie on a trajectory from `a` to
`b`, and `c` a value strictly between `f b` and `f a`. If `u i → w` and the orbit of `u i` meets
the level `c` at time `s i`, then the crossing points converge to the point where the orbit of `w`
meets the level `c`. -/
theorem exists_tendsto_flow_of_tendsto (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {w : M}
    (hw : w ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (hbc : f b < c)
    (hca : c < f a) {ι : Type*} {l : Filter ι} {u : ι → M} (hu : Tendsto u l (𝓝 w))
    {s : ι → ℝ} (hs : ∀ i, f (hX.flow (s i) (u i)) = c) :
    ∃ σ : ℝ, f (hX.flow σ w) = c ∧
      Tendsto (fun i ↦ hX.flow (s i) (u i)) l (𝓝 (hX.flow σ w)) := by
  have hab : a ≠ b := by rintro rfl; exact (hbc.trans hca).false
  obtain ⟨σ, hσ, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hab hw hbc hca
  -- Move everything to the crossing point `flow σ w`, where the crossing time is `0`.
  have hu' : Tendsto (fun i ↦ hX.flow σ (u i)) l (𝓝 (hX.flow σ w)) :=
    ((hX.flow.continuous continuous_const continuous_id).tendsto w).comp hu
  have ht := hX.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet hf hab
    (hX.flow.isInvariant_unstableSet_inter_stableSet a b σ hw) hu' (σ := fun i ↦ s i - σ)
    fun i ↦ by rw [← Flow.map_add, sub_add_cancel, hs, hσ]
  refine ⟨σ, hσ, ?_⟩
  simpa only [Function.comp_def, ← Flow.map_add, sub_add_cancel, zero_add] using
    ((hX.flow.continuous continuous_fst continuous_snd).tendsto (0, hX.flow σ w)).comp
      (ht.prodMk_nhds hu')

/-- **Levels are transverse to connecting trajectories.** At a point `y` of `W^u(a) ∩ W^s(b)` with
`a ≠ b`, the tangent space of `W^u(a) ∩ W^s(b)` and the kernel of `df_y`, the tangent space of the
level of `f` through `y`, span the tangent space of `M`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊔
      (mvfderiv 𝓘(ℝ, E) f y).ker = ⊤ := by
  have hmem := hX.mem_span_mtangentConeAt_unstableSet_inter_stableSet hy
  rw [hf.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm]
  refine top_unique ?_
  rw [← LinearMap.span_singleton_sup_ker_eq_top
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ)
    (hX.fderiv_comp_chartAt_symm_apply_lt_zero hf hab hy).ne]
  exact sup_le_sup_right ((Submodule.span_singleton_le_iff_mem (R := ℝ) (M := E) _ _).2 hmem) _

/-- Under transversality, the level slice through `y` is cut out of `W^u(a) ∩ W^s(b)` by a
transverse regular level set: it is flattened by a chart of the maximal atlas, and its tangent
space is that of `W^u(a) ∩ W^s(b)` cut by `ker df_y`. -/
private theorem level_slice (hf : IsMorse 𝓘(ℝ, E) f) (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0)
    (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    (∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊓
          (mvfderiv 𝓘(ℝ, E) f y).ker : Submodule ℝ E) : Set E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c})) ∧
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y) =
      Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊓
        (mvfderiv 𝓘(ℝ, E) f y).ker := by
  obtain ⟨q, hyq, hq, hs⟩ := hX.exists_unstableSet_inter_stableSet_chart hf ha hb hy htr
  rw [← hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr] at hs
  -- The level `{f = c}` is a regular level set near `y`, since `df_y (X y) < 0`.
  have hlevel : {x | f x = c} = f ⁻¹' {c} := by
    ext
    simp
  have hrange : (mvfderiv 𝓘(ℝ, E) f y).range = ⊤ := by
    rw [← MDifferentiableAt.fderiv_comp_chartAt_symm (hf.contMDiff.mdifferentiable (by simp) y)]
    exact LinearMap.range_eq_top_of_surjective _
      (hX.surjective_fderiv_comp_chartAt_symm (hf.contMDiff.mdifferentiable (by simp) y) hab hy)
  have htr' := hX.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top
    (hf.contMDiff.mdifferentiable (by simp) y) hab hy
  -- In finite dimensions every subspace is complemented.
  have hcc (p : Submodule ℝ E) : p.ClosedComplemented :=
    .of_finiteDimensional_quotient (Submodule.closed_of_finiteDimensional _)
  rw [hlevel]
  exact ⟨exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hq hs
      hyq hy isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn hyc hrange htr'
      (hcc _) (hcc _) (hcc _),
    span_mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hq hs hyq
      hy isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn hyc hrange htr'
      (hcc _) (hcc _) (hcc _)⟩

/-- **The level slice of a transverse intersection is an embedded submanifold.** If the unstable
manifold of a critical point `a` and the stable manifold of a different critical point `b` meet
transversally at `y`, and `f y = c`, then near `y` a chart of the maximal atlas flattens the level
slice `W^u(a) ∩ W^s(b) ∩ {f = c}` onto the intersection of the tangent spaces of `W^u(a)` and
`W^s(b)` with `ker df_y`. -/
theorem exists_unstableSet_inter_stableSet_level_chart (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) ⊓
          (mvfderiv 𝓘(ℝ, E) f y).ker : Submodule ℝ E) : Set E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) := by
  obtain ⟨⟨q, hyq, hq, hs⟩, -⟩ := hX.level_slice hf ha hb hab hy htr hyc
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr] at hs
  exact ⟨q, hyq, hq, hs⟩

/-- **The tangent space of a transverse level slice.** If the unstable manifold of a critical point
`a` and the stable manifold of a different critical point `b` meet transversally at `y`, and
`f y = c`, then the tangent space of the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` at `y` is the
intersection of the tangent spaces of `W^u(a)` and `W^s(b)` with `ker df_y`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet_level (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) ⊓
        (mvfderiv 𝓘(ℝ, E) f y).ker := by
  rw [(hX.level_slice hf ha hb hab hy htr hyc).2,
    hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr]

/-- **The level slice has dimension the index difference minus one.** If the unstable manifold of a
critical point `a` and the stable manifold of a different critical point `b` meet transversally at
`y`, then the tangent space at `y` of the level slice `W^u(a) ∩ W^s(b) ∩ {f = f y}` has dimension
`ind a - ind b - 1`. -/
theorem finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex
    (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f b + 1 = manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have hd := hf.contMDiff.mdifferentiable (by simp)
  have hsup := hX.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top (hd y) hab hy
  have hslice := (hX.level_slice hf ha hb hab hy htr hyc).2
  rw [(hd y).ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm] at hsup hslice
  -- Cutting by the hyperplane `ker df_y`, which is transverse, lowers the dimension by one.
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y))
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y)).ker
  rw [hsup, finrank_top, ← hslice] at hdim
  have hker := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top_of_surjective _
      (hX.surjective_fderiv_comp_chartAt_symm (hd y) hab hy), finrank_top,
    Module.finrank_self] at hker
  have hW :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf ha hb hy
      htr
  omega

/-- **Index-difference-one level slices are discrete.** If the Morse indices of critical points `a`
and `b` differ by one and the unstable manifold of `a` meets the stable manifold of `b`
transversally at every point of the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}`, then the slice is
discrete: each of the trajectories it parametrizes is isolated. -/
theorem isDiscrete_unstableSet_inter_stableSet_level (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1)
    (htr : ∀ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c},
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    IsDiscrete (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) := by
  have hab : a ≠ b := by rintro rfl; omega
  refine isDiscrete_of_forall_exists_isSliceChart_zero (F := E) fun y hy ↦ ?_
  have htry := htr y hy
  obtain ⟨hyab, hyc⟩ := hy
  -- The slice is zero-dimensional, so the chart at `y` flattens it onto the point `0`.
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf ha
      hb hab hyab htry hyc
  obtain ⟨q, hyq, -, hq⟩ :=
    hX.exists_unstableSet_inter_stableSet_level_chart hf ha hb hab hyab htry hyc
  have h0 : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y)) = 0 := by
    omega
  rw [← hX.span_mtangentConeAt_unstableSet_inter_stableSet_level hf ha hb hab hyab htry hyc,
    Submodule.finrank_eq_zero.1 h0, Submodule.bot_coe] at hq
  exact ⟨q, hyq, hq⟩

omit hX in
/-- **Spaces of unparametrized trajectories are manifolds.** Under the Morse–Smale condition, if
some trajectory from a critical point `a` to a different critical point `b` crosses the level
`{f = c}`, then the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` carries a smooth manifold structure,
modelled on a subspace of dimension `ind a - ind b - 1`, with its subspace topology and a smooth
inclusion into `M`. -/
theorem IsMorseSmale.exists_unstableSet_inter_stableSet_level_isManifold
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f b + 1 =
        manifoldMorseIndex 𝓘(ℝ, E) f a ∧
      ∃ C : ChartedSpace L ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}),
        letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) → M) := by
  obtain ⟨y₀, hy₀, hy₀c⟩ := hne
  have htr₀ := h.span_mtangentConeAt_sup_eq_top ha hb hy₀
  have hdim₀ :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf ha
      hb hab hy₀ htr₀ hy₀c
  -- Every tangent space of the slice has dimension `ind a - ind b - 1`; model it on one of them.
  refine ⟨Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y₀), hdim₀,
    exists_isManifold_of_finrankSubspaceCharts fun y hy ↦ ?_⟩
  obtain ⟨hyab, hyc⟩ := hy
  have htry := h.span_mtangentConeAt_sup_eq_top ha hb hyab
  obtain ⟨q, hyq, hq, hs⟩ :=
    hX.exists_unstableSet_inter_stableSet_level_chart hf ha hb hab hyab htry hyc
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf ha
      hb hab hyab htry hyc
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet_level hf ha hb hab hyab htry
    hyc] at hdim
  exact ⟨q, _, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs, by omega⟩

end IsAdaptedPseudoGradient

end TauCeti
