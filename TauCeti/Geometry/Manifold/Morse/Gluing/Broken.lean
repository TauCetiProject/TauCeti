/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.BoxCrossing
public import TauCeti.Geometry.Manifold.Morse.Gluing.TransverseDisc
public import TauCeti.Geometry.Manifold.Morse.Stable.Gluing
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Analysis.Calculus.Morse.Gluing.Centre
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Data.Set.Function

/-!
# Gluing at a broken trajectory

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `q`, `r` critical points with
`p ≠ q` and `q ≠ r`, with no condition on their Morse indices. A broken trajectory from `p` to `r`
through `q` enters a Morse box at `q` along the stable set of `q` and leaves it along its unstable
set. This file sets up such a box and shows that every once-broken trajectory is a limit of
unbroken ones: the Morse–Smale condition gives a disc in `W^u(p)` through the entrance point and a
disc in `W^s(r)` through the exit point, transverse to the stable and unstable sets of `q` and of
the dimensions of the expanding and contracting coordinates there
(`IsMorseSmale.exists_hasStrictFDerivAt_mem_unstableSet_of_eventually_mem_stableSet_iff` and
`IsMorseSmale.exists_hasStrictFDerivAt_mem_stableSet_of_eventually_mem_unstableSet_iff`, in the
namespace `TauCeti.IsAdaptedPseudoGradient`), and the model gluing
(`TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`) joins them by
trajectories from `p` to `r` converging to the broken one. These discs are in general only part of
`W^u(p)` and `W^s(r)`, so these trajectories need not contain every nearby one.

**Any transverse set.** The outgoing disc need not lie in a stable manifold. For any set `Z`
flattened near a point `y ≠ q` of `W^u(q)` by a chart of the maximal atlas and transverse to
`W^u(q)` at `y`, the flow carries `Z` to the exit face along the orbit of `y`, still flattened and
transverse there (`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_preimage_flow`), and the
same gluing produces points of `W^u(p) ∩ Z` converging to `y`, on orbits which follow the
trajectory from `p` to `q`. With `Z` the stable manifold of a second pseudo-gradient, this glues
the broken configurations of a Morse–Smale pair.

The Morse box at the break, with the transverse set carried to its exit point
(`exists_morseBox_of_broken_of_isSliceChart`), the local description of the split coordinates
near its entrance and exit points (`eventually_of_entranceFace` and `eventually_of_morseBox`) and
the continuity of reading gluing pairs back on `M`
(`continuousAt_toChart_symm_of_mem_insert_splitGluingPairs`), in
the namespace `TauCeti.IsAdaptedPseudoGradient`, are also the setting of the half-open gluing
charts of `TauCeti.Geometry.Manifold.Morse.Gluing.Transverse`.

**Through the critical point.** The point `y` may also be `q` itself, for a set `Z` through `q`
transverse to `W^u(q)` there. Its orbit is then constant and never reaches the exit face; instead,
`Z` is read in the Morse box as a Lipschitz graph through the centre, and the orbits from a disc
of `W^u(p)` at the entrance face that meet it at a late time are the fixed points of a contraction
(`TauCeti.eventually_exists_splitQuadraticFlow_snd_eq`). They converge to `q` as that time grows.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `exists_morseBox_of_broken_of_isSliceChart`: a Morse box at a broken configuration ending in a
  transverse set, with that set carried by the flow to the exit point.
* `IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart`: points of `W^u(p) ∩ Z`
  accumulate at each point `y` of `W^u(q)`, `q` included, where a flattened set `Z` meets
  `W^u(q)` transversally, along orbits following a given trajectory from `p` to `q`.
* `IsMorseSmale.exists_mem_unstableSet_inter_stableSet_flow_mem`: for any indices, a trajectory
  from `p` to `r` passes through any given neighbourhoods of a point of a trajectory from `p` to
  `q` and of a point of a trajectory from `q` to `r`.
* `IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet`: for any indices, every broken
  trajectory recorded on two levels is a limit of unbroken ones.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-- **A Morse chart with a box at a critical point.** At the critical point `q` there are a Morse
chart `φ` in which `X` is linear and a radius `ρ > 0` such that the coordinates of sup norm less
than `ρ` are coordinates of points of the chart, and on the cube of radius `ρ` the stable and
unstable sets of `q` are the coordinate planes. -/
theorem exists_morseChart_box (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {q : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) :
    ∃ (φ : MorseChart E f q) (ρ : ℝ),
      (∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) ∧
      0 < ρ ∧ (∀ z, ‖z‖ < ρ → φ.coord.symm z ∈ φ.toChart.target) ∧
      (∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
        (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
        (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)) := by
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart q hq
  have hφ' := φ.coord_mfderiv_neg hφ hnd
  -- The local descriptions of the stable and unstable sets.
  obtain ⟨ρs, hρs, hs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨ρu, hρu, hu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd) hφ'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply,
    Left.neg_neg_iff, ← hX.unstableSet_eq_stableSet_neg hf] at hu
  obtain ⟨rT, hrT, hT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  refine ⟨φ, min (min ρs ρu) rT, hφ, by positivity,
    fun z hz ↦ hT z (hz.trans_le (min_le_right _ _)), fun w hw hwρ ↦ ⟨?_, ?_⟩⟩
  · exact (hs w hw (hwρ.trans_le ((min_le_left _ _).trans (min_le_left _ _)))).trans
      (by simp [funext_iff, φ.weight_ne_one_iff])
  · exact (hu w hw (hwρ.trans_le ((min_le_left _ _).trans (min_le_right _ _)))).trans
      (by simp [funext_iff, φ.weight_eq_one_iff])

/-- **A trajectory enters every small box.** Let `φ` be a Morse chart at `q` in which `X` is linear,
and `a₁` a point of a trajectory from `p ≠ q` to `q`. For every small `ε > 0`, the trajectory
crosses the sphere of radius `ε` of the coordinates of `φ`. -/
private theorem eventually_exists_flow_norm_coord_eq (hX : IsAdaptedPseudoGradient f X)
    {p q a₁ : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hpq : p ≠ q) (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ T, hX.flow T a₁ ∈ φ.toChart.source ∧
      ‖φ.coord (φ.toChart (hX.flow T a₁))‖ = ε := by
  obtain ⟨ρ, hρ, hc⟩ := hX.exists_forall_coord_flow_eq_exp_smul φ hφ
  -- A point `b` of the trajectory in the cube of radius `ρ`, where the flow contracts linearly.
  obtain ⟨t, hb, hbρ⟩ :=
    ((Flow.mem_stableSet.1 ha₁.2).eventually (φ.eventually_mem_source_norm_coord_lt hρ)).exists
  set b := hX.flow t a₁
  have hbm : b ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q t ha₁
  -- Its coordinates are nonzero, since it is not the critical point.
  have hz : 0 < ‖φ.coord (φ.toChart b)‖ := by
    refine norm_pos_iff.2 fun h ↦ ?_
    have hbq := (φ.toChart_eq_zero_iff hb).1 (by simpa using h)
    have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq hbm
    rw [hbq] at this
    exact this.1.ne rfl
  -- Flow `b` to the sphere of radius `ε ≤ ‖b‖`.
  filter_upwards [Ioc_mem_nhdsGT hz] with ε hε
  have hs : 0 ≤ Real.log (‖φ.coord (φ.toChart b)‖ / ε) :=
    Real.log_nonneg ((one_le_div hε.1).2 hε.2)
  obtain ⟨hy, hyc⟩ := hc b hbm.2 hb hbρ _ hs
  refine ⟨Real.log (‖φ.coord (φ.toChart b)‖ / ε) + t, by rwa [Flow.map_add], ?_⟩
  rw [Flow.map_add, hyc, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg,
    Real.exp_log (div_pos hz hε.1)]
  field_simp

/-- **A trajectory enters every small Morse box through its entrance face.** Let `φ` be a Morse
chart at `q` in which `X` is linear and on whose cube of radius `ρ` the stable set of `q` is the
plane where the expanding split coordinate `v` vanishes, and let `a₁` be a point of a trajectory
from `p ≠ q` to `q`. For every small `ε > 0`, the trajectory crosses the entrance face
`‖u‖ = ε, v = 0` of the box of radius `ε`. -/
theorem eventually_exists_flow_mem_entranceFace (hX : IsAdaptedPseudoGradient f X)
    {p q a₁ : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ρ : ℝ} (hρ : 0 < ρ) (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0))
    (hpq : p ≠ q) (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ T, hX.flow T a₁ ∈ φ.toChart.source ∧
      (φ.splitCoord (φ.coord (φ.toChart (hX.flow T a₁)))).snd = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart (hX.flow T a₁)))).fst‖ = ε := by
  filter_upwards [hX.eventually_exists_flow_norm_coord_eq φ hφ hpq ha₁,
    nhdsWithin_le_nhds (gt_mem_nhds hρ)] with ε ⟨T, hT, hTε⟩ hερ
  -- The crossing point lies on the stable plane, so its contracting coordinate has norm `ε`.
  have hs := (hloc _ hT (hTε ▸ hερ)).1
    (hX.flow.isInvariant_unstableSet_inter_stableSet p q T ha₁).2
  have hn := φ.max_norm_fst_norm_snd_splitCoord (φ.coord (φ.toChart (hX.flow T a₁)))
  rw [hs, norm_zero, max_eq_left (norm_nonneg _), hTε] at hn
  exact ⟨T, hT, hs, hn⟩

/-- **A Morse box at the middle of a broken trajectory.** For a trajectory from `p` to `q` through
`a₁` and one from `q` to `r` through `a₂`, there are a Morse chart `φ` at `q` in which `X` is
linear and a radius `ε` such that the cube of radius `2 ε` lies in the chart, the stable and
unstable sets of `q` are the coordinate planes on a cube of radius larger than `2 ε`, and the two
trajectories cross the entrance and exit faces of the box at points `y₁` and `y₂` of the
coordinate planes. -/
private theorem exists_morseBox_of_broken (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {p q r a₁ a₂ : M}
    (hpq : p ≠ q) (hqr : q ≠ r) (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (φ : MorseChart E f q) (ε ρ T₁ T₂ : ℝ) (y₁ y₂ : M),
      (∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) ∧
      0 < ε ∧ 2 * ε < ρ ∧ (∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target) ∧
      (∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
        (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
        (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)) ∧
      hX.flow T₁ a₁ = y₁ ∧ hX.flow T₂ a₂ = y₂ ∧ y₁ ∈ φ.toChart.source ∧ y₂ ∈ φ.toChart.source ∧
      (φ.splitCoord (φ.coord (φ.toChart y₁))).snd = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε ∧
      (φ.splitCoord (φ.coord (φ.toChart y₂))).fst = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε := by
  have hq := hX.mfderiv_eq_zero_of_mem_stableSet ha₁.2
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
  obtain ⟨φ, ρ, hφ, hρ, hT, hloc⟩ := hX.exists_morseChart_box hf hq
  -- Both trajectories cross every small sphere around `q`; the second one backwards, as a
  -- trajectory of `-X` from `r` to `q`.
  have h₁ := hX.eventually_exists_flow_mem_entranceFace φ hφ hρ (fun w hw hwρ ↦ (hloc w hw hwρ).1)
    hpq ha₁
  have h₂ := (hX.neg hf).eventually_exists_flow_norm_coord_eq (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd) hqr.symm (a₁ := a₂)
    ⟨by rw [← hX.stableSet_eq_unstableSet_neg hf]; exact ha₂.2,
      by rw [← hX.unstableSet_eq_stableSet_neg hf]; exact ha₂.1⟩
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, hX.neg_flow hf,
    Flow.reverse_apply] at h₂
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 2 * ε < ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (half_pos hρ))]
      with ε hε hερ
    exact ⟨hε, by linarith⟩
  obtain ⟨ε, ⟨T₁, hy₁, hy₁s, hn₁⟩, ⟨T₂, hy₂, hy₂ε⟩, hε, hερ⟩ := (h₁.and (h₂.and hsmall)).exists
  -- The exit point lies on the unstable plane, so its expanding coordinate has norm `ε`.
  have hy₂u := ((hloc _ hy₂ (by linarith)).2.1
    (hX.flow.isInvariant_unstableSet_inter_stableSet q r (-T₂) ha₂).1)
  have hn₂ := φ.max_norm_fst_norm_snd_splitCoord (φ.coord (φ.toChart (hX.flow (-T₂) a₂)))
  rw [hy₂u, norm_zero, max_eq_right (norm_nonneg _), hy₂ε] at hn₂
  exact ⟨φ, ε, ρ, T₁, -T₂, _, _, hφ, hε, hερ, fun z hz ↦ hT z (by linarith), hloc, rfl, rfl, hy₁,
    hy₂, hy₁s, hn₁, hy₂u, hn₂⟩

/-- **A Morse box near its entrance point.** Let `φ` be a Morse chart at `q` in which, on the
cube of radius `ρ > 2 ε`, the stable and unstable sets of `q` are the coordinate planes, and let
`y₁` be a point of the entrance face `‖u‖ = ε, v = 0` of the box of radius `ε`, in the split
coordinates `(u, v)` of `φ`. Near `y₁`, `0 < ‖u‖ < 2 ε`, `‖v‖ < ε` and the stable set of `q` is the
plane `v = 0`, and the product `‖u‖ ‖v‖` tends to `0` at `y₁`. -/
theorem eventually_of_entranceFace (hX : IsAdaptedPseudoGradient f X) {q y₁ : M}
    (φ : MorseChart E f q) {ε ρ : ℝ} (hε : 0 < ε) (hερ : 2 * ε < ρ)
    (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0))
    (hy₁φ : y₁ ∈ φ.toChart.source) (hy₁s : (φ.splitCoord (φ.coord (φ.toChart y₁))).snd = 0)
    (hy₁ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε) :
    (∀ᶠ w in 𝓝 y₁, w ∈ φ.toChart.source ∧ 0 < ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε ∧
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0)) ∧
    Tendsto (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) (𝓝 y₁) (𝓝 0) := by
  have hy₁fst := φ.tendsto_norm_fst_splitCoord_coord_toChart hy₁φ
  have hy₁snd := φ.tendsto_norm_snd_splitCoord_coord_toChart hy₁φ
  rw [hy₁ε] at hy₁fst
  rw [hy₁s, norm_zero] at hy₁snd
  refine ⟨?_, by simpa only [mul_zero] using hy₁fst.mul hy₁snd⟩
  filter_upwards [φ.toChart.open_source.mem_nhds hy₁φ, hy₁fst.eventually (lt_mem_nhds hε),
    hy₁fst.eventually (gt_mem_nhds (by linarith : ε < 2 * ε)),
    hy₁snd.eventually (gt_mem_nhds hε)] with w h₁ h₂ h₃ h₄
  refine ⟨h₁, h₂, h₃, h₄, (hloc w h₁ ?_).1⟩
  rw [← φ.max_norm_fst_norm_snd_splitCoord]
  exact max_lt (by linarith) (by linarith)

/-- **A Morse box near its entrance and exit points.** Let `φ` be a Morse chart at `q` in which,
on the cube of radius `ρ > 2 ε`, the stable and unstable sets of `q` are the coordinate planes, and
let `y₁` be a point of the entrance face `‖u‖ = ε, v = 0` and `y₂` a point of the exit face
`u = 0, ‖v‖ = ε` of the box of radius `ε`, in the split coordinates `(u, v)` of `φ`. Near `y₁`,
`0 < ‖u‖ < 2 ε`, `‖v‖ < ε` and the stable set of `q` is the plane `v = 0`; symmetrically near `y₂`.
The product `‖u‖ ‖v‖` tends to `0` at both points. -/
theorem eventually_of_morseBox (hX : IsAdaptedPseudoGradient f X) {q y₁ y₂ : M}
    (φ : MorseChart E f q) {ε ρ : ℝ} (hε : 0 < ε) (hερ : 2 * ε < ρ)
    (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0))
    (hy₁φ : y₁ ∈ φ.toChart.source) (hy₂φ : y₂ ∈ φ.toChart.source)
    (hy₁s : (φ.splitCoord (φ.coord (φ.toChart y₁))).snd = 0)
    (hy₁ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε)
    (hy₂u : (φ.splitCoord (φ.coord (φ.toChart y₂))).fst = 0)
    (hy₂ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε) :
    (∀ᶠ w in 𝓝 y₁, w ∈ φ.toChart.source ∧ 0 < ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε ∧
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0)) ∧
    (∀ᶠ w in 𝓝 y₂, w ∈ φ.toChart.source ∧ 0 < ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < 2 * ε ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < ε ∧
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)) ∧
    Tendsto (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) (𝓝 y₁) (𝓝 0) ∧
    Tendsto (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) (𝓝 y₂) (𝓝 0) := by
  obtain ⟨h₁, hy₁κ⟩ := hX.eventually_of_entranceFace φ hε hερ hloc hy₁φ hy₁s hy₁ε
  have hy₂snd := φ.tendsto_norm_snd_splitCoord_coord_toChart hy₂φ
  have hy₂fst := φ.tendsto_norm_fst_splitCoord_coord_toChart hy₂φ
  rw [hy₂ε] at hy₂snd
  rw [hy₂u, norm_zero] at hy₂fst
  refine ⟨h₁, ?_, hy₁κ, by simpa only [zero_mul] using hy₂fst.mul hy₂snd⟩
  filter_upwards [φ.toChart.open_source.mem_nhds hy₂φ, hy₂snd.eventually (lt_mem_nhds hε),
    hy₂snd.eventually (gt_mem_nhds (by linarith : ε < 2 * ε)),
    hy₂fst.eventually (gt_mem_nhds hε)] with w h₁ h₂ h₃ h₄
  refine ⟨h₁, h₂, h₃, h₄, (hloc w h₁ ?_).2⟩
  rw [← φ.max_norm_fst_norm_snd_splitCoord]
  exact max_lt (by linarith) (by linarith)

/-- **The flow through a gluing pair of a Morse box.** Let `φ` be a Morse chart at `q` in which
`X` is linear and which contains the cube of radius `2 ε`, and let `z` be a gluing pair of the box
of radius `ε` whose entrance point is the model entry point of a point `w` near the entrance face,
and whose exit point is the model exit point of a point `w'` near the exit face. Then `w` flows
to the point with the coordinates of the entrance point at its entry time, that point flows to the
point with the coordinates of the exit point at its exit time, and `w'` reaches the latter at its
own exit time. -/
theorem flow_eq_of_mem_splitGluingPairs (hX : IsAdaptedPseudoGradient f X) {q : M}
    (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε r₀ : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ splitGluingPairs ε r₀ g k) {w w' : M} (hw : w ∈ φ.toChart.source)
    (hwf : ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε)
    (hws : ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε)
    (hwz : splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
      (φ.splitCoord (φ.coord (φ.toChart w))) = z.1)
    (hw' : w' ∈ φ.toChart.source) (hw'f : ‖(φ.splitCoord (φ.coord (φ.toChart w'))).fst‖ < ε)
    (hw's : ‖(φ.splitCoord (φ.coord (φ.toChart w'))).snd‖ < 2 * ε)
    (hw'z : splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w'))))
      (φ.splitCoord (φ.coord (φ.toChart w'))) = z.2) :
    hX.flow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w)))) w =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1)) ∧
      hX.flow (splitExitTime ε z.1) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1))) =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2)) ∧
      hX.flow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w')))) w' =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2)) := by
  have h₁ := hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw hwf hws
  have h₂ := hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw' hw'f hw's
  rw [hwz] at h₁
  rw [hw'z] at h₂
  obtain ⟨hsrc, -, -, hpass, -⟩ := mem_splitGluingPairs.1 hz
  refine ⟨h₁, ?_, h₂⟩
  rw [hpass]; exact hX.flow_splitExitTime φ hφ (fun z hz ↦ hε₂ z (by linarith)) hsrc

/-- **Gluing pairs of a Morse box lie on orbits from their entrance disc to their exit disc.**
Let `φ` be a Morse chart at `q` in which `X` is linear and which contains the cube of radius
`2 ε`, and let `z` be a gluing pair of the box of radius `ε` whose entrance point is the model entry
point of a point `w` near the entrance face, and whose exit point is the model exit point of a
point `w'` near the exit face. Then the orbit of `w` passes through `w'`. -/
private theorem exists_flow_eq_of_mem_splitGluingPairs (hX : IsAdaptedPseudoGradient f X) {q : M}
    (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε r₀ : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ splitGluingPairs ε r₀ g k) {w w' : M} (hw : w ∈ φ.toChart.source)
    (hwf : ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε)
    (hws : ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε)
    (hwz : splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
      (φ.splitCoord (φ.coord (φ.toChart w))) = z.1)
    (hw' : w' ∈ φ.toChart.source) (hw'f : ‖(φ.splitCoord (φ.coord (φ.toChart w'))).fst‖ < ε)
    (hw's : ‖(φ.splitCoord (φ.coord (φ.toChart w'))).snd‖ < 2 * ε)
    (hw'z : splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w'))))
      (φ.splitCoord (φ.coord (φ.toChart w'))) = z.2) :
    ∃ τ : ℝ, hX.flow τ w = w' := by
  obtain ⟨h₁, h₃, h₂⟩ := hX.flow_eq_of_mem_splitGluingPairs φ hφ hε hε₂ hz hw hwf hws hwz hw'
    hw'f hw's hw'z
  -- Enter the box, cross it, and leave it backwards from `w'`.
  refine ⟨-splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w'))) +
    (splitExitTime ε z.1 + splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w)))), ?_⟩
  rw [Flow.map_add, Flow.map_add, h₁, h₃, ← h₂, Flow.map_neg_apply_map]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- If a Morse chart contains the cube of radius `ε`, reading pairs of split coordinates back on
`M` is continuous at the gluing pairs of the box of radius `ε`, and at the pair of coordinates of
two points of the chart. -/
theorem continuousAt_toChart_symm_of_mem_insert_splitGluingPairs {q y₁ y₂ : M}
    (φ : MorseChart E f q) {ε r₀ : ℝ} (hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    (hy₁φ : y₁ ∈ φ.toChart.source) (hy₂φ : y₂ ∈ φ.toChart.source)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ insert (φ.splitCoord (φ.coord (φ.toChart y₁)), φ.splitCoord (φ.coord (φ.toChart y₂)))
      (splitGluingPairs ε r₀ g k)) :
    ContinuousAt (fun z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
        WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ↦
      (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1)),
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2)))) z := by
  have hbox₀ : ∀ w ∈ φ.toChart.source,
      φ.coord.symm (φ.splitCoord.symm (φ.splitCoord (φ.coord (φ.toChart w)))) ∈
        φ.toChart.target := fun w hw ↦ by
    simpa using φ.toChart.map_source hw
  obtain ⟨hb₁, hb₂⟩ : φ.coord.symm (φ.splitCoord.symm z.1) ∈ φ.toChart.target ∧
      φ.coord.symm (φ.splitCoord.symm z.2) ∈ φ.toChart.target := by
    rcases hz with rfl | hz
    · exact ⟨hbox₀ y₁ hy₁φ, hbox₀ y₂ hy₂φ⟩
    · obtain ⟨hsrc, -, -, hpass, -⟩ := mem_splitGluingPairs.1 hz
      have htgt := (splitPassage ε).map_source hsrc
      rw [← hpass] at htgt
      exact ⟨MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₁
          (mem_splitPassage_source.1 hsrc).1.le (mem_splitPassage_source.1 hsrc).2.2,
        MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε₁
          (mem_splitPassage_target.1 htgt).2.2 (mem_splitPassage_target.1 htgt).1.le⟩
  exact ((φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm hb₁).comp
    continuous_fst.continuousAt).prodMk
    ((φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm hb₂).comp continuous_snd.continuousAt)

/-- **The flow carries a set transverse to an unstable manifold along it.** Let `Z` be a set
through a point `y` of `W^u(q)`, flattened near `y` by a chart of the maximal atlas and transverse
to `W^u(q)` at `y`. For every time `T`, the set `flow T '' Z`, written as the preimage of `Z`
under `flow (-T)`, is flattened near `flow T y` by a chart of the maximal atlas and is transverse
to `W^u(q)` there. -/
theorem exists_isSliceChart_preimage_flow (hX : IsAdaptedPseudoGradient f X) {q y : M}
    {Z : Set M} {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) (T : ℝ) :
    ∃ φ' : OpenPartialHomeomorph M E, φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart φ' (L : Set E) (hX.flow (-T) ⁻¹' Z) ∧ hX.flow T y ∈ φ'.source ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow (-T) ⁻¹' Z) (hX.flow T y)) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) (hX.flow T y)) = ⊤ := by
  set G := hX.flowDiffeomorph T
  have hGy : G y = hX.flow T y := hX.flowDiffeomorph_apply T y
  refine ⟨G.symm.toHomeomorph.transOpenPartialHomeomorph φZ,
    G.symm.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl hφZ,
    isSliceChart_iff.2 fun w hw ↦ ?_, ?_, ?_⟩
  · simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
      Diffeomorph.coe_toHomeomorph, G, hX.flowDiffeomorph_symm_apply] at hw
    simp only [mem_preimage, Homeomorph.transOpenPartialHomeomorph_apply, comp_apply,
      Diffeomorph.coe_toHomeomorph, G, hX.flowDiffeomorph_symm_apply]
    exact isSliceChart_iff.1 hZ _ hw
  · simpa [G, ← Flow.map_add] using hyφZ
  -- The derivative of the time-`T` map is surjective, so it carries transversality along.
  have hG : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) G y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) G y) :=
    (G.mdifferentiable (by simp) y).hasMFDerivAt
  have h := hG.span_mtangentConeAt_image_sup_eq_top
    (fun v ↦ ⟨_, G.mfderiv_apply_mfderiv_symm_apply (by simp) y v⟩) htr
  rw [hGy] at h
  refine top_unique (h.symm.le.trans (sup_le_sup (Submodule.span_mono (mtangentConeAt_mono ?_ _))
    (Submodule.span_mono (mtangentConeAt_mono ?_ _))))
  · rintro _ ⟨z, hz, rfl⟩
    simpa [G, ← Flow.map_add] using hz
  · rintro _ ⟨z, hz, rfl⟩
    simpa [G] using (Flow.apply_mem_unstableSet_iff _ _).2 hz

/-- **A Morse box at a broken configuration into a transverse set.** Let `a₁` be a point of a
trajectory from `p` to a critical point `q ≠ p`, and `y ≠ q` a point of `W^u(q)`. Let `Z` be a set
through `y`, flattened near `y` by a chart of the maximal atlas and transverse to `W^u(q)` at `y`.
Then `y` lies on a trajectory from `q` to a critical point `r ≠ q`, and there is a Morse box at
`q`, in a Morse chart in which `X` is linear and the stable and unstable sets of `q` are the
coordinate planes, with entrance point `y₁` on the trajectory through `a₁` and exit point
`y₂ = flow T₂ y`. The image `flow (-T₂) ⁻¹' Z` of `Z` under the flow passes through `y₂`, is
flattened near `y₂` by a chart of the maximal atlas, and is transverse to `W^u(q)` there. -/
theorem exists_morseBox_of_broken_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {p q a₁ y : M} {Z : Set M} (hpq : p ≠ q)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hy : y ∈ hX.flow.unstableSet q)
    (hyq : y ≠ q) {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) :
    ∃ (r : M) (φ : MorseChart E f q) (ε ρ T₁ T₂ : ℝ) (y₁ y₂ : M) (φ' : OpenPartialHomeomorph M E),
      q ≠ r ∧
      (∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) ∧
      0 < ε ∧ 2 * ε < ρ ∧ (∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target) ∧
      (∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
        (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
        (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)) ∧
      hX.flow T₁ a₁ = y₁ ∧ hX.flow T₂ y = y₂ ∧ y₁ ∈ φ.toChart.source ∧ y₂ ∈ φ.toChart.source ∧
      (φ.splitCoord (φ.coord (φ.toChart y₁))).snd = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε ∧
      (φ.splitCoord (φ.coord (φ.toChart y₂))).fst = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε ∧
      y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧
      y₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧
      φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart φ' (L : Set E) (hX.flow (-T₂) ⁻¹' Z) ∧ y₂ ∈ φ'.source ∧
      y₂ ∈ hX.flow (-T₂) ⁻¹' Z ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow (-T₂) ⁻¹' Z) y₂) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y₂) = ⊤ := by
  obtain ⟨r, -, hyr⟩ := hX.exists_mem_stableSet hf y
  have hqr : q ≠ r := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hy, hyr⟩)
  obtain ⟨φ, ε, ρ, T₁, T₂, y₁, y₂, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s, hy₁ε,
    hy₂u, hy₂ε⟩ := hX.exists_morseBox_of_broken hf hpq hqr ha₁ ⟨hy, hyr⟩
  obtain ⟨φ', hφ', hZ', hy₂φ', htr'⟩ := hX.exists_isSliceChart_preimage_flow hφZ hZ hyφZ htr T₂
  rw [hT₂] at hy₂φ' htr'
  refine ⟨r, φ, ε, ρ, T₁, T₂, y₁, y₂, φ', hqr, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ,
    hy₁s, hy₁ε, hy₂u, hy₂ε, hT₁ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁,
    hT₂ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet q r T₂ ⟨hy, hyr⟩, hφ', hZ', hy₂φ', ?_,
    htr'⟩
  rw [mem_preimage, ← hT₂, Flow.map_neg_apply_map]
  exact hyZ

/-- **A transverse disc crosses the entrance face of a Morse box in a Lipschitz graph.** Let `φ`
be a Morse chart at `q` in which `X` is linear and whose cube of radius `2 ε` lies in the chart,
and `y₁` a point of the chart on the entrance face `‖u‖ = ε, v = 0`. Let `ψ` be a disc through the
split coordinates of `y₁`, strictly differentiable at `0` with the derivative of its expanding
coordinate `v` invertible, whose points near `0` lie in a set `S`. For every neighbourhood `N₁` of
`y₁` there is a Lipschitz graph `v ↦ (g v, v)` in the entrance face over a closed ball, through the
split coordinates of `y₁`, each of whose points is reached by the flow from a point of `S ∩ N₁`;
conversely, the entrance points of the orbits through the points of the disc near `0` lie on the
graph. -/
theorem exists_lipschitzOnWith_entranceFace_graph (hX : IsAdaptedPseudoGradient f X)
    {q y₁ : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    (hy₁φ : y₁ ∈ φ.toChart.source) (hy₁s : (φ.splitCoord (φ.coord (φ.toChart y₁))).snd = 0)
    (hy₁f : ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε) {S : Set M}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ψ : F → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    {ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hψ : HasStrictFDerivAt ψ ψ' 0)
    (hψ' : (WithLp.sndL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
      ψ').IsInvertible)
    (hψ₀ : ψ 0 = φ.splitCoord (φ.coord (φ.toChart y₁)))
    (hψs : ∀ᶠ z in 𝓝 0, φ.coord.symm (φ.splitCoord.symm (ψ z)) ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (ψ z))) ∈ S)
    {N₁ : Set M} (hN₁ : N₁ ∈ 𝓝 y₁) :
    ∃ δ > 0, ∃ (K : NNReal) (g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ),
      LipschitzOnWith K g (Metric.closedBall 0 δ) ∧
      g 0 = (φ.splitCoord (φ.coord (φ.toChart y₁))).fst ∧
      (∀ v ∈ Metric.closedBall 0 δ, ‖g v‖ = ε ∧
        ∃ u ∈ S ∩ N₁, ∃ τ : ℝ,
          hX.flow τ u =
            φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (g v, v))))) ∧
      ∀ᶠ z in 𝓝 0, (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).fst =
        g (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).snd := by
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  -- Near `0`, the points of the disc lie near `y₁`, inside the box near its entrance face.
  have hΨψ : Tendsto (fun z ↦ Ψ (ψ z)) (𝓝 0) (𝓝 y₁) := by
    have hc := φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm
      (z := φ.splitCoord (φ.coord (φ.toChart y₁))) (by simpa using φ.toChart.map_source hy₁φ)
    have h' := hc.tendsto.comp (hψ₀ ▸ hψ.continuousAt.tendsto)
    rwa [show φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
      (φ.splitCoord (φ.coord (φ.toChart y₁))))) = y₁ by simp [φ.toChart.left_inv hy₁φ]] at h'
  have hψf : ∀ᶠ z in 𝓝 0, ‖(ψ z).fst‖ < 2 * ε ∧ ‖(ψ z).snd‖ < ε := by
    have h₁ : ContinuousAt (fun z ↦ ‖(ψ z).fst‖) 0 :=
      ((WithLp.continuous_fst 2 _ _).norm.continuousAt).comp hψ.continuousAt
    have h₂ : ContinuousAt (fun z ↦ ‖(ψ z).snd‖) 0 :=
      ((WithLp.continuous_snd 2 _ _).norm.continuousAt).comp hψ.continuousAt
    filter_upwards [h₁.eventually (gt_mem_nhds
        (by rw [hψ₀, hy₁f]; linarith : ‖(ψ 0).fst‖ < 2 * ε)),
      h₂.eventually (gt_mem_nhds (by rw [hψ₀, hy₁s, norm_zero]; exact hε : ‖(ψ 0).snd‖ < ε))]
      with z hz₁ hz₂
    exact ⟨hz₁, hz₂⟩
  set U' : Set F := {z | ‖(ψ z).fst‖ < 2 * ε ∧ ‖(ψ z).snd‖ < ε ∧
    φ.coord.symm (φ.splitCoord.symm (ψ z)) ∈ φ.toChart.target ∧ Ψ (ψ z) ∈ S ∧ Ψ (ψ z) ∈ N₁}
  have hU' : U' ∈ 𝓝 0 := (hψf.and (hψs.and (hΨψ.eventually hN₁))).mono
    fun z ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hΦy₁ : WithLp.toLp 2 ((φ.splitCoord (φ.coord (φ.toChart y₁))).fst, 0) =
      φ.splitCoord (φ.coord (φ.toChart y₁)) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hy₁s.symm))
  obtain ⟨δ, hδ, K, g, hg, hg₀, hpts, hexh⟩ := exists_splitQuadraticFlow_splitEntryTime_eq_graph
    hψ hψ' (hψ₀.trans hΦy₁.symm) hy₁f hε hU'
  refine ⟨δ, hδ, K, g, hg, hg₀, fun v hv ↦ ⟨(hpts v hv).1, ?_⟩, hexh⟩
  -- The point of the disc over `v` flows to the entrance point `(g v, v)` at its entry time.
  obtain ⟨-, z, ⟨hzf, hzs, hzT, hzS, hzN₁⟩, hzflow⟩ := hpts v hv
  have hΦΨ : φ.splitCoord (φ.coord (φ.toChart (Ψ (ψ z)))) = ψ z := by
    simp [hΨdef, φ.toChart.right_inv hzT]
  have hentry := hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ (φ.toChart.map_target hzT)
    (by rw [hΦΨ]; exact hzf) (by rw [hΦΨ]; exact hzs)
  rw [hΦΨ, hzflow] at hentry
  exact ⟨_, ⟨hzS, hzN₁⟩, _, hentry⟩

/-- **A set transverse to the unstable manifold at the critical point is a graph near the
centre.** Let `φ` be a Morse chart at `q` on whose cube of radius `ρ` the unstable set of `q` is
the plane where the contracting split coordinate `u` vanishes, and let `Z` be a set through `q`,
flattened near `q` by a chart of the maximal atlas and transverse to `W^u(q)` at `q`. Near the
centre, `Z` contains a Lipschitz graph `u ↦ (u, k u)` over a closed ball of the contracting
factor, with `k 0 = 0`. -/
private theorem exists_lipschitzOnWith_graph_mem_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    {q : M} (φ : MorseChart E f q) {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0))
    (hq : q ∈ hX.flow.unstableSet q) {Z : Set M} {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hqφZ : q ∈ φZ.source) (hqZ : q ∈ Z)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) q) = ⊤) :
    ∃ η > 0, ∃ (K : NNReal) (k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ),
      LipschitzOnWith K k (Metric.closedBall 0 η) ∧ k 0 = 0 ∧ ∀ u ∈ Metric.closedBall 0 η,
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (WithLp.toLp 2 (u, k u)))) ∈ Z := by
  -- Near `q`, the unstable set of `q` is the kernel of `u`; `Z` contains a disc transverse to it.
  have hlocq : ∀ᶠ w in 𝓝 q,
      w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0 := by
    filter_upwards [φ.eventually_mem_source_norm_coord_lt hρ] with w ⟨hw, hwρ⟩
    exact hloc w hw hwρ
  obtain ⟨χ, χ', hχ, hχ', hχ₀, hχs⟩ :=
    exists_hasStrictFDerivAt_splitCoord φ (pr := WithLp.fstL 2 ℝ _ _)
      (fun u ↦ ⟨WithLp.toLp 2 (u, 0), rfl⟩) hlocq hφZ hZ φ.mem_source hqφZ hqZ hq htr
  obtain ⟨η, hη, K, k, hk, hk₀, hkpts, -⟩ := exists_lipschitzOnWith_graph_of_hasStrictFDerivAt hχ
    (by rw [hχ']; exact ⟨.refl ℝ _, rfl⟩) (by simp [hχ₀, φ.apply_self])
    (hχs.mono fun _ hz ↦ hz.2)
  refine ⟨η, hη, K, k, hk, hk₀, fun u hu ↦ ?_⟩
  obtain ⟨z, hz, hzk⟩ := hkpts u hu
  rw [← hzk]
  exact hz

/-- **Gluing a broken trajectory into a transverse set through the critical point.** Let `X` be a
Morse–Smale adapted pseudo-gradient for a Morse function `f` on a compact manifold, and `a₁` a
point of a trajectory from `p` to a critical point `q ≠ p`. Let `Z` be a set through `q`, flattened
near `q` by a chart of the maximal atlas, which meets `W^u(q)` transversally at `q`. Then, for all
neighbourhoods `N₁` of `a₁` and `N` of `q`, some point of `W^u(p) ∩ Z` lies in `N` and its orbit
passes through `N₁`. -/
private theorem IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart_self
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q a₁ : M} {Z : Set M} (hpq : p ≠ q)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hqφZ : q ∈ φZ.source) (hqZ : q ∈ Z)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z q) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) q) = ⊤)
    {N₁ N : Set M} (hN₁ : N₁ ∈ 𝓝 a₁) (hN : N ∈ 𝓝 q) :
    ∃ w ∈ hX.flow.unstableSet p ∩ Z, w ∈ N ∧ ∃ s : ℝ, hX.flow s w ∈ N₁ := by
  -- Plan: choose a Morse box at `q` with entrance point `y₁` on the trajectory through `a₁`; glue
  -- the trace of `W^u(p)` on the entrance face to the graph of `Z` through the centre of the box,
  -- where the flow is the split hyperbolic flow (`eventually_exists_splitQuadraticFlow_snd_eq`).
  have hq := hX.mfderiv_eq_zero_of_mem_stableSet ha₁.2
  obtain ⟨φ, ρ, hφ, hρ, hT, hloc⟩ := hX.exists_morseChart_box hf hq
  obtain ⟨ρd, hρd, hdisc⟩ := h.exists_hasStrictFDerivAt_mem_unstableSet hf φ hφ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 2 * ε < ρ ∧ ε < ρd := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (half_pos hρ)),
      nhdsWithin_le_nhds (gt_mem_nhds hρd)] with ε hε hερ hερd
    exact ⟨hε, by linarith, hερd⟩
  obtain ⟨ε, ⟨T₁, hy₁φ, hy₁s, hy₁f⟩, hε, hερ, hερd⟩ :=
    ((hX.eventually_exists_flow_mem_entranceFace φ hφ hρ (fun w hw hwρ ↦ (hloc w hw hwρ).1) hpq
      ha₁).and hsmall).exists
  have hy₁ρ : ‖φ.coord (φ.toChart (hX.flow T₁ a₁))‖ < ρd := by
    rw [← φ.max_norm_fst_norm_snd_splitCoord, hy₁s, hy₁f, norm_zero, max_eq_left hε.le]
    exact hερd
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hT z (by linarith)
  -- The trace of `W^u(p)` on the entrance face, from points whose orbits reach `N₁`.
  obtain ⟨ψ, ψ', hψ, hψ', hψ₀, hψs⟩ := hdisc
    (hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁) hy₁φ hy₁ρ
  have hN₁' : hX.flow (-T₁) ⁻¹' N₁ ∈ 𝓝 (hX.flow T₁ a₁) :=
    (hX.flow.continuous_toFun (-T₁)).continuousAt.preimage_mem_nhds
      (by rwa [Flow.map_neg_apply_map])
  obtain ⟨δ, hδ, Kg, g, hg, -, hpts, -⟩ := hX.exists_lipschitzOnWith_entranceFace_graph φ hφ hε
    (fun z hz ↦ hT z (by linarith)) hy₁φ hy₁s hy₁f hψ (by rw [hψ']; exact ⟨.refl ℝ _, rfl⟩) hψ₀
    hψs hN₁'
  -- `Z` as a graph through the centre, and the glued orbit, which meets it near `q`.
  obtain ⟨η, hη, Kk, k, hk, hk₀, hkZ⟩ := hX.exists_lipschitzOnWith_graph_mem_of_isSliceChart φ hρ
    (fun w hw hwρ ↦ (hloc w hw hwρ).2) (hX.mem_unstableSet_inter_stableSet_self hq).1 hφZ hZ
    hqφZ hqZ htr
  have hN' : (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) ⁻¹' N ∈ 𝓝 0 :=
    (φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm
      (by simpa using hε₁ 0 (by simp [hε.le]))).preimage_mem_nhds (by simpa using hN)
  obtain ⟨T, ⟨y, hy, hbox, hW, hxη, hgraph⟩, hT0⟩ :=
    ((eventually_exists_splitQuadraticFlow_snd_eq hδ hη hg (fun y hy ↦ (hpts y hy).1) hk hk₀
      hN').and (eventually_ge_atTop 0)).exists
  obtain ⟨-, u, ⟨hu, huN₁⟩, τ, hτ⟩ := hpts y hy
  have hcross := hX.flow_toChart_symm_splitCoord_symm φ hφ hε₁
    (w := WithLp.toLp 2 (g y, y)) (t := T) (by rwa [uIcc_of_le hT0])
  have hw : splitQuadraticFlow T (WithLp.toLp 2 (g y, y)) = WithLp.toLp 2
      ((splitQuadraticFlow T (WithLp.toLp 2 (g y, y))).fst,
        k (splitQuadraticFlow T (WithLp.toLp 2 (g y, y))).fst) :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hgraph))
  refine ⟨φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm
    (splitQuadraticFlow T (WithLp.toLp 2 (g y, y))))), ⟨?_, by rw [hw]; exact hkZ _ hxη⟩, hW,
    -T₁ + (-(T + τ)), ?_⟩
  · rw [← hcross, ← hτ, ← Flow.map_add]
    exact (Flow.apply_mem_unstableSet_iff _ _).2 hu
  · rw [← hcross, ← hτ, ← Flow.map_add, ← Flow.map_add]
    convert mem_preimage.1 huN₁ using 2
    ring

/-- **Gluing a broken trajectory into a transverse set.** Let `X` be a Morse–Smale adapted
pseudo-gradient for a Morse function `f` on a compact manifold, `a₁` a point of a trajectory from
`p` to a critical point `q ≠ p`, and `y` a point of the unstable manifold `W^u(q)`, possibly `q`
itself. Let `Z` be a set through `y`, flattened near `y` by a chart of the maximal atlas, which
meets `W^u(q)` transversally at `y`. Then, for all neighbourhoods `N₁` of `a₁` and `N` of `y`, some
point of `W^u(p) ∩ Z` lies in `N` and its orbit passes through `N₁`. So `W^u(p) ∩ Z` accumulates at
`y`, along orbits which follow the trajectory through `a₁`. For `Z` the stable manifold of a
critical point this is the gluing of a broken trajectory
(`IsMorseSmale.exists_mem_unstableSet_inter_stableSet_flow_mem`). -/
theorem IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q a₁ y : M} {Z : Set M} (hpq : p ≠ q)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hy : y ∈ hX.flow.unstableSet q)
    {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤)
    {N₁ N : Set M} (hN₁ : N₁ ∈ 𝓝 a₁) (hN : N ∈ 𝓝 y) :
    ∃ w ∈ hX.flow.unstableSet p ∩ Z, w ∈ N ∧ ∃ s : ℝ, hX.flow s w ∈ N₁ := by
  rcases eq_or_ne y q with rfl | hyq
  · exact h.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart_self hf hpq ha₁ hφZ hZ hyφZ hyZ
      htr hN₁ hN
  -- Plan: choose a Morse box at `q` with entrance point `y₁` on the trajectory through `a₁` and
  -- exit point `y₂` on the orbit of `y`; glue a disc in `W^u(p)` through `y₁` to a disc through
  -- `y₂` in the image of `Z` under the flow, and flow a glued point back to `Z`.
  obtain ⟨r, φ, ε, ρ, T₁, T₂, y₁, y₂, φ', -, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s,
    hy₁ε, hy₂u, hy₂ε, hy₁, ⟨hy₂, -⟩, hφ', hZ', hy₂φ', hy₂Z', htr'⟩ :=
    hX.exists_morseBox_of_broken_of_isSliceChart hf hpq ha₁ hy hyq hφZ hZ hyφZ hyZ htr
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  obtain ⟨hA₁, hA₂, -, -⟩ :=
    hX.eventually_of_morseBox φ hε hερ hloc hy₁φ hy₂φ hy₁s hy₁ε hy₂u hy₂ε
  set U := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < 2 * ε ∧ ‖(Φ w).snd‖ < ε}
  set V := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < ε ∧ ‖(Φ w).snd‖ < 2 * ε}
  have hU : U ∈ 𝓝 y₁ := hA₁.mono fun w ⟨h₁, _, h₂, h₃, _⟩ ↦ ⟨h₁, h₂, h₃⟩
  have hV : V ∈ 𝓝 y₂ := hA₂.mono fun w ⟨h₁, _, h₂, h₃, _⟩ ↦ ⟨h₁, h₃, h₂⟩
  -- A transverse disc in `W^u(p)` through the entrance point, and one through the exit point in
  -- the image `Z'` of `Z` under the flow.
  set Z' := hX.flow (-T₂) ⁻¹' Z
  have hy₂Z : hX.flow (-T₂) y₂ = y := by
    rw [← hT₂, Flow.map_neg_apply_map]
  obtain ⟨ψ, ψ', hψ, hψ', hψ₀, hψs⟩ :=
    h.exists_hasStrictFDerivAt_mem_unstableSet_of_eventually_mem_stableSet_iff hf φ hy₁ hy₁φ
      (hA₁.mono fun w hw ↦ hw.2.2.2.2)
  obtain ⟨χ, χ', hχ, hχ', hχ₀, hχs⟩ :=
    exists_hasStrictFDerivAt_splitCoord φ (pr := WithLp.fstL 2 ℝ _ _)
      (fun u ↦ ⟨WithLp.toLp 2 (u, 0), rfl⟩) (hA₂.mono fun w hw ↦ hw.2.2.2.2) hφ' hZ' hy₂φ hy₂φ'
      hy₂Z' hy₂ htr'
  have hΦy₁ : WithLp.toLp 2 ((Φ y₁).fst, 0) = Φ y₁ :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hy₁s.symm))
  have hΦy₂ : WithLp.toLp 2 (0, (Φ y₂).snd) = Φ y₂ :=
    WithLp.ofLp_injective 2 (Prod.ext (by simpa using hy₂u.symm) (by simp))
  -- Near `0`, the points of the discs lie near the entrance and exit points.
  have hΨψ : Tendsto (fun z ↦ Ψ (ψ z)) (𝓝 0) (𝓝 y₁) := by
    have hc : ContinuousAt Ψ (Φ y₁) := φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm
      (by simpa [hΦdef] using φ.toChart.map_source hy₁φ)
    have hψc := hψ.continuousAt.tendsto
    rw [hψ₀] at hψc
    have h := hc.tendsto.comp hψc
    rwa [hΨΦ y₁ hy₁φ] at h
  have hΨχ : Tendsto (fun z ↦ Ψ (χ z)) (𝓝 0) (𝓝 y₂) := by
    have hc : ContinuousAt Ψ (Φ y₂) := φ.continuousAt_toChart_symm_coord_symm_splitCoord_symm
      (by simpa [hΦdef] using φ.toChart.map_source hy₂φ)
    have hχc := hχ.continuousAt.tendsto
    rw [hχ₀] at hχc
    have h := hc.tendsto.comp hχc
    rwa [hΨΦ y₂ hy₂φ] at h
  -- Flowing back by `T₁` and `T₂`, points near the entrance and exit points land in `N₁` and `N`.
  have hN₁' : hX.flow (-T₁) ⁻¹' N₁ ∈ 𝓝 y₁ := by
    refine (hX.flow.continuous_toFun (-T₁)).continuousAt.preimage_mem_nhds ?_
    rwa [← hT₁, Flow.map_neg_apply_map]
  have hN' : hX.flow (-T₂) ⁻¹' N ∈ 𝓝 y₂ :=
    (hX.flow.continuous_toFun (-T₂)).continuousAt.preimage_mem_nhds (hy₂Z ▸ hN)
  set U' : Set ({i // ¬φ.weight i = 1} → ℝ) := {z | Ψ (ψ z) ∈ U ∧
    φ.coord.symm (φ.splitCoord.symm (ψ z)) ∈ φ.toChart.target ∧
    Ψ (ψ z) ∈ hX.flow.unstableSet p ∧ Ψ (ψ z) ∈ hX.flow (-T₁) ⁻¹' N₁}
  set V' : Set ({i // φ.weight i = 1} → ℝ) := {z | Ψ (χ z) ∈ V ∧
    φ.coord.symm (φ.splitCoord.symm (χ z)) ∈ φ.toChart.target ∧
    Ψ (χ z) ∈ Z' ∧ Ψ (χ z) ∈ hX.flow (-T₂) ⁻¹' N}
  have hU' : U' ∈ 𝓝 0 :=
    ((hΨψ.eventually hU).and (hψs.and (hΨψ.eventually hN₁'))).mono
      fun z ⟨h₁, ⟨h₂, h₃⟩, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩
  have hV' : V' ∈ 𝓝 0 :=
    ((hΨχ.eventually hV).and (hχs.and (hΨχ.eventually hN'))).mono
      fun z ⟨h₁, ⟨h₂, h₃⟩, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨r₀, hr₀, g, k, ⟨e, -, he₀⟩, hcl, hpairs, -⟩ :=
    exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt hψ
      (by rw [hψ']; exact ⟨.refl ℝ _, rfl⟩) (hψ₀.trans hΦy₁.symm) hy₁ε hχ
      (by rw [hχ']; exact ⟨.refl ℝ _, rfl⟩) (hχ₀.trans hΦy₂.symm) hy₂ε hε hU' hV'
  rw [hΦy₁, hΦy₂] at he₀ hcl
  -- The end of the gluing arc is an unbroken gluing pair.
  have hz : (e ⟨r₀, right_mem_Icc.2 hr₀.le⟩).val ∈ splitGluingPairs ε r₀ g k :=
    e.injective.val_mem_of_subset_insert hcl.subset he₀ fun h ↦ hr₀.ne' (congrArg Subtype.val h)
  set z := (e ⟨r₀, right_mem_Icc.2 hr₀.le⟩).val
  obtain ⟨⟨z₁, ⟨⟨hw, hwf, hws⟩, hz₁, hwu, hwN₁⟩, hwz⟩,
    z₂, ⟨⟨hw', hw'f, hw's⟩, hz₂, hw'Z, hw'N⟩, hw'z⟩ := hpairs z hz
  -- The entrance-side point flows to the exit-side point, which therefore lies in `W^u(p)`.
  have hΦΨ₁ : Φ (Ψ (ψ z₁)) = ψ z₁ := by simp [hΦdef, hΨdef, φ.toChart.right_inv hz₁]
  have hΦΨ₂ : Φ (Ψ (χ z₂)) = χ z₂ := by simp [hΦdef, hΨdef, φ.toChart.right_inv hz₂]
  rw [← hΦΨ₁] at hwz
  rw [← hΦΨ₂] at hw'z
  obtain ⟨τ, hτ⟩ := hX.exists_flow_eq_of_mem_splitGluingPairs φ hφ hε hε₂ hz hw hwf hws hwz hw'
    hw'f hw's hw'z
  refine ⟨hX.flow (-T₂) (Ψ (χ z₂)), ⟨(Flow.apply_mem_unstableSet_iff _ _).2
    (hτ ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hwu), hw'Z⟩, hw'N, -T₁ + (-τ + T₂), ?_⟩
  rw [← hτ, ← Flow.map_add, ← Flow.map_add]
  convert mem_preimage.1 hwN₁ using 2
  ring

/-- **Broken trajectories of any index are limits of unbroken ones.** Let `X` be a Morse–Smale
adapted pseudo-gradient for a Morse function `f` on a compact manifold, and `p`, `q`, `r` critical
points with `p ≠ q`, with no condition on their Morse indices. For a point `a₁` of a
trajectory from `p` to `q`, a point `a₂` of a trajectory from `q` to `r`, and neighbourhoods `N₁`
of `a₁` and `N₂` of `a₂`, there is a trajectory from `p` to `r` which passes through `N₁` and,
later or earlier, through `N₂`: the broken trajectory through `a₁` and `a₂` is a limit of unbroken
trajectories in the sense of Morse theory. -/
theorem IsMorseSmale.exists_mem_unstableSet_inter_stableSet_flow_mem
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M} (hpq : p ≠ q)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) {N₁ N₂ : Set M} (hN₁ : N₁ ∈ 𝓝 a₁)
    (hN₂ : N₂ ∈ 𝓝 a₂) :
    ∃ u ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r, ∃ s₁ s₂ : ℝ,
      hX.flow s₁ u ∈ N₁ ∧ hX.flow s₂ u ∈ N₂ := by
  -- Glue into the stable manifold of `r`, which is flattened near `a₂` and transverse to `W^u(q)`.
  obtain ⟨L, φZ, -, ha₂φZ, hφZ, hZ⟩ :=
    hX.exists_isSliceChart_stableSet (hX.mfderiv_eq_zero_of_mem_stableSet ha₂.2) ha₂.2
  obtain ⟨u, hu, hu₂, s, hs⟩ := h.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart hf hpq ha₁
    ha₂.1 hφZ hZ ha₂φZ ha₂.2 (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top ha₂)
    hN₁ hN₂
  exact ⟨u, hu, s, 0, hs, by rwa [Flow.map_zero_apply]⟩

/-- **Every broken trajectory is a limit of unbroken ones, on two levels.** Let `p`, `q`, `r` be
critical points with `p ≠ q` and `q ≠ r`, with no condition on their Morse indices. The pair
`(a₁, a₂)` recording a trajectory broken at `q` lies in the closure of the pairs recording the
unbroken trajectories from `p` to `r` on the same two levels. -/
theorem IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M} (hpq : p ≠ q) (hqr : q ≠ r)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    (a₁, a₂) ∈ closure {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq ha₁
  have hfa₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr ha₂
  have hpr : p ≠ r := by rintro rfl; linarith [hfa₁.1, hfa₁.2, hfa₂.1, hfa₂.2]
  -- Unbroken trajectories `u n` passing through the `n`-th neighbourhoods of countable bases at
  -- `a₁` and `a₂`, and their points on the two levels.
  obtain ⟨B₁, hB₁⟩ := (𝓝 a₁).exists_antitone_basis
  obtain ⟨B₂, hB₂⟩ := (𝓝 a₂).exists_antitone_basis
  choose u hu s₁ s₂ hs₁ hs₂ using fun n ↦
    h.exists_mem_unstableSet_inter_stableSet_flow_mem hf hpq ha₁ ha₂ (hB₁.mem n) (hB₂.mem n)
  choose τ₁ hτ₁ using fun n ↦ (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr
    (hu n) (by linarith [hfa₁.1, hfa₂.1, hfa₂.2]) hfa₁.2).exists
  choose τ₂ hτ₂ using fun n ↦ (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr
    (hu n) hfa₂.1 (by linarith [hfa₁.1, hfa₁.2, hfa₂.2])).exists
  -- On each level, the points converge to the point of the component crossing it.
  have hlim₁ := hX.tendsto_flow_of_tendsto_flow_of_mem_unstableSet_inter_stableSet hpq ha₁
    (σ := 0) (by rw [Flow.map_zero_apply]) (hB₁.tendsto hs₁) hτ₁
  have hlim₂ := hX.tendsto_flow_of_tendsto_flow_of_mem_unstableSet_inter_stableSet hqr ha₂
    (σ := 0) (by rw [Flow.map_zero_apply]) (hB₂.tendsto hs₂) hτ₂
  rw [Flow.map_zero_apply] at hlim₁ hlim₂
  refine mem_closure_of_tendsto (hlim₁.prodMk_nhds hlim₂)
    (.of_forall fun n ↦ ⟨?_, hτ₁ n, hτ₂ n, τ₂ n - τ₁ n, ?_⟩)
  · exact hX.flow.isInvariant_unstableSet_inter_stableSet p r _ (hu n)
  · rw [← Flow.map_add, sub_add_cancel]

end IsAdaptedPseudoGradient

end TauCeti
