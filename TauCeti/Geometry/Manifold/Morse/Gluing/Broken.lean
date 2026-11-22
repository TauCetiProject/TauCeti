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
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Gluing at a broken trajectory

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `q`, `r` critical points, first with
`ind p = ind q + 1 = ind r + 2`. Record the trajectories from `p` to `r` by their points on two
levels: for a point `a₁` of a trajectory from `p` to `q` and a point `a₂` of a trajectory from `q`
to `r`, the unbroken trajectories give the pairs `(w₁, w₂)` of points of one trajectory from `p` to
`r` with `f w₁ = f a₁` and `f w₂ = f a₂`, and the broken trajectory through `a₁` and `a₂` gives
the pair `(a₁, a₂)`. The main theorem shows that `(a₁, a₂)` has a neighbourhood among these pairs
homeomorphic to a half-open interval `[0, δ)`. These are the boundary charts of the compactified
space of index-two trajectories, whose boundary points therefore come in pairs
(`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`).

The proof transports the gluing in the split model of a Morse box at `q`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`), which
describes the pairs of a model entrance point and a model exit point joined by the passage map as
a half-open arc whose closure adds only the broken pair, to the two levels:

* a trajectory near the broken one crosses the box once, so its model entrance and exit points
  form one of these pairs
  (`TauCeti.IsAdaptedPseudoGradient.splitPassage_splitEntryTime_eq_splitExitTime`);
* following the flow to the two levels is continuous at both broken and unbroken trajectories,
  since the level points depend continuously on the orbit along connecting trajectories.

So the level points of the gluing arc form a continuous injective arc in `M × M` from `(a₁, a₂)`,
which contains every unbroken pair near `(a₁, a₂)`.

**Any index.** Without conditions on the Morse indices, so for `p ≠ q` and `q ≠ r` only, the same
construction still glues: the Morse–Smale condition gives a disc in `W^u(p)` through the entrance
point and a disc in `W^s(r)` through the exit point, transverse to the stable and unstable sets of
`q` and of the dimensions of the expanding and contracting coordinates there
(`IsMorseSmale.exists_hasStrictFDerivAt_mem_unstableSet_of_eventually_mem_stableSet_iff` and
`IsMorseSmale.exists_hasStrictFDerivAt_mem_stableSet_of_eventually_mem_unstableSet_iff`, in the
namespace `TauCeti.IsAdaptedPseudoGradient`), and the model gluing joins
them by trajectories from `p` to `r` converging to the broken one. These discs are in general only
part of `W^u(p)` and `W^s(r)`, so these trajectories need not contain every nearby one, but they
show that every once-broken trajectory is a limit of unbroken ones.

**Any transverse set.** The outgoing disc need not lie in a stable manifold. For any set `Z`
flattened near a point `y ≠ q` of `W^u(q)` by a chart of the maximal atlas and transverse to
`W^u(q)` at `y`, the flow carries `Z` to the exit face along the orbit of `y`, still flattened and
transverse there, and the same gluing produces points of `W^u(p) ∩ Z` converging to `y`, on orbits
which follow the trajectory from `p` to `q`. With `Z` the stable manifold of a second
pseudo-gradient, this glues the broken configurations of a Morse–Smale pair.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`: for consecutive indices,
  a broken trajectory has a neighbourhood homeomorphic to `[0, δ)` among the unbroken trajectories
  recorded on two levels.
* `IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart`: points of `W^u(p) ∩ Z`
  accumulate at each point `y ≠ q` of `W^u(q)` where a flattened set `Z` meets `W^u(q)`
  transversally, along orbits following a given trajectory from `p` to `q`.
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
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart q hq
  have hφ' := φ.coord_mfderiv_neg hφ hnd
  -- The local descriptions of the stable and unstable sets, and of the flow on them.
  obtain ⟨ρs, hρs, hs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨ρu, hρu, hu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd) hφ'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply,
    Left.neg_neg_iff, ← hX.unstableSet_eq_stableSet_neg hf] at hu
  obtain ⟨ρc, hρc, hc⟩ := hX.exists_forall_coord_flow_eq_exp_smul φ hφ
  obtain ⟨ρc', hρc', hc'⟩ := (hX.neg hf).exists_forall_coord_flow_eq_exp_smul (φ.neg hnd) hφ'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, hX.neg_flow hf, Flow.stableSet_reverse,
    Flow.reverse_apply] at hc'
  obtain ⟨rT, hrT, hT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have hsplit : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < min ρs ρu →
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0) :=
    fun w hw hwρ ↦ ⟨(hs w hw (hwρ.trans_le (min_le_left _ _))).trans
      (by simp [funext_iff, φ.weight_ne_one_iff]),
      (hu w hw (hwρ.trans_le (min_le_right _ _))).trans (by simp [funext_iff, φ.weight_eq_one_iff])⟩
  set δ := min (min (min ρs ρu / 2) ρc) (min ρc' (rT / 4)) with hδdef
  have hδ : 0 < δ := by positivity
  -- Points of the two trajectories in the cube of radius `δ`.
  have hN : {w | w ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart w)‖ < δ} ∈ 𝓝 q := by
    have hcont : ContinuousAt (fun w ↦ ‖φ.coord (φ.toChart w)‖) q :=
      (φ.continuous_coord.norm.continuousAt).comp (φ.toChart.continuousAt φ.mem_source)
    filter_upwards [φ.toChart.open_source.mem_nhds φ.mem_source,
      hcont.eventually (gt_mem_nhds (by simpa using hδ))] with w hw hwδ using ⟨hw, hwδ⟩
  obtain ⟨t₁, hb₁, hb₁δ⟩ := ((Flow.mem_stableSet.1 ha₁.2).eventually hN).exists
  obtain ⟨t₂, hb₂, hb₂δ⟩ := ((Flow.mem_unstableSet.1 ha₂.1).eventually hN).exists
  set b₁ := hX.flow t₁ a₁
  set b₂ := hX.flow t₂ a₂
  have hb₁m : b₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q t₁ ha₁
  have hb₂m : b₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hX.flow.isInvariant_unstableSet_inter_stableSet q r t₂ ha₂
  -- Their coordinates are nonzero, since they are not the critical point.
  have hz₁ : 0 < ‖φ.coord (φ.toChart b₁)‖ := by
    refine norm_pos_iff.2 fun h ↦ ?_
    have hb := (φ.toChart_eq_zero_iff hb₁).1 (by simpa using h)
    have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq hb₁m
    rw [hb] at this
    exact this.1.ne rfl
  have hz₂ : 0 < ‖φ.coord (φ.toChart b₂)‖ := by
    refine norm_pos_iff.2 fun h ↦ ?_
    have hb := (φ.toChart_eq_zero_iff hb₂).1 (by simpa using h)
    have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr hb₂m
    rw [hb] at this
    exact this.2.ne rfl
  set ε := min ‖φ.coord (φ.toChart b₁)‖ ‖φ.coord (φ.toChart b₂)‖
  have hε : 0 < ε := lt_min hz₁ hz₂
  have hεδ : ε < δ := (min_le_left _ _).trans_lt hb₁δ
  -- Flow the two points to the faces of the box of radius `ε`.
  set s₁ := Real.log (‖φ.coord (φ.toChart b₁)‖ / ε)
  set s₂ := Real.log (‖φ.coord (φ.toChart b₂)‖ / ε)
  have hs₁ : 0 ≤ s₁ := Real.log_nonneg ((one_le_div hε).2 (min_le_left _ _))
  have hs₂ : 0 ≤ s₂ := Real.log_nonneg ((one_le_div hε).2 (min_le_right _ _))
  obtain ⟨hy₁, hy₁c⟩ := hc b₁ hb₁m.2 hb₁ (hb₁δ.trans_le (by simp [hδdef])) s₁ hs₁
  obtain ⟨hy₂, hy₂c⟩ := hc' b₂ hb₂m.1 hb₂ (hb₂δ.trans_le (by simp [hδdef])) s₂ hs₂
  have he₁ : Real.exp (-s₁) * ‖φ.coord (φ.toChart b₁)‖ = ε := by
    rw [Real.exp_neg, Real.exp_log (div_pos hz₁ hε)]; field_simp
  have he₂ : Real.exp (-s₂) * ‖φ.coord (φ.toChart b₂)‖ = ε := by
    rw [Real.exp_neg, Real.exp_log (div_pos hz₂ hε)]; field_simp
  have hδρ : δ ≤ min ρs ρu / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδT : δ ≤ rT / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hb₁s := ((hsplit b₁ hb₁ (by linarith [hb₁δ])).1.1 hb₁m.2)
  have hb₂u := ((hsplit b₂ hb₂ (by linarith [hb₂δ])).2.1 hb₂m.1)
  refine ⟨φ, ε, min ρs ρu, s₁ + t₁, -s₂ + t₂, hX.flow s₁ b₁, hX.flow (-s₂) b₂, hφ, hε,
    by linarith, fun z hz ↦ hT z (by linarith), hsplit, Flow.map_add _ _ _ _,
    Flow.map_add _ _ _ _, hy₁, hy₂, ?_, ?_, ?_, ?_⟩
  · rw [hy₁c, map_smul, WithLp.smul_snd, hb₁s, smul_zero]
  · have h := φ.max_norm_fst_norm_snd_splitCoord (φ.coord (φ.toChart (hX.flow s₁ b₁)))
    rw [hy₁c, map_smul, WithLp.smul_snd, hb₁s, smul_zero, norm_zero, ← map_smul, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, he₁] at h
    rwa [max_eq_left (norm_nonneg _), ← hy₁c] at h
  · rw [hy₂c, map_smul, WithLp.smul_fst, hb₂u, smul_zero]
  · have h := φ.max_norm_fst_norm_snd_splitCoord (φ.coord (φ.toChart (hX.flow (-s₂) b₂)))
    rw [hy₂c, map_smul, WithLp.smul_fst, hb₂u, smul_zero, norm_zero, ← map_smul, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, he₂] at h
    rwa [max_eq_right (norm_nonneg _), ← hy₂c] at h


/-- **A Morse box near its entrance and exit points.** Let `φ` be a Morse chart at `q` in which,
on the cube of radius `ρ > 2 ε`, the stable and unstable sets of `q` are the coordinate planes, and
let `y₁` be a point of the entrance face `‖u‖ = ε, v = 0` and `y₂` a point of the exit face
`u = 0, ‖v‖ = ε` of the box of radius `ε`, in the split coordinates `(u, v)` of `φ`. Near `y₁`,
`0 < ‖u‖ < 2 ε`, `‖v‖ < ε` and the stable set of `q` is the plane `v = 0`; symmetrically near `y₂`.
The product `‖u‖ ‖v‖` tends to `0` at both points. -/
private theorem eventually_of_morseBox (hX : IsAdaptedPseudoGradient f X) {q y₁ y₂ : M}
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
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w))
  have hΦc : ∀ w ∈ φ.toChart.source, ContinuousAt Φ w := fun w hw ↦
    (φ.splitCoordL.continuous.continuousAt.comp (φ.toChart.continuousAt hw)).congr
      (.of_forall fun _ ↦ φ.splitCoordL_apply _)
  have hfst : ∀ w ∈ φ.toChart.source, ContinuousAt (fun w ↦ ‖(Φ w).fst‖) w := fun w hw ↦
    ((WithLp.continuous_fst 2 _ _).norm.continuousAt (x := Φ w)).comp (hΦc w hw)
  have hsnd : ∀ w ∈ φ.toChart.source, ContinuousAt (fun w ↦ ‖(Φ w).snd‖) w := fun w hw ↦
    ((WithLp.continuous_snd 2 _ _).norm.continuousAt (x := Φ w)).comp (hΦc w hw)
  have hy₁fst : Tendsto (fun w ↦ ‖(Φ w).fst‖) (𝓝 y₁) (𝓝 ε) := by
    have h := (hfst y₁ hy₁φ).tendsto
    rwa [hy₁ε] at h
  have hy₁snd : Tendsto (fun w ↦ ‖(Φ w).snd‖) (𝓝 y₁) (𝓝 0) := by
    have h := (hsnd y₁ hy₁φ).tendsto
    rwa [hy₁s, norm_zero] at h
  have hy₂snd : Tendsto (fun w ↦ ‖(Φ w).snd‖) (𝓝 y₂) (𝓝 ε) := by
    have h := (hsnd y₂ hy₂φ).tendsto
    rwa [hy₂ε] at h
  have hy₂fst : Tendsto (fun w ↦ ‖(Φ w).fst‖) (𝓝 y₂) (𝓝 0) := by
    have h := (hfst y₂ hy₂φ).tendsto
    rwa [hy₂u, norm_zero] at h
  -- On the cube of radius `2 ε` the coordinate planes are the stable and unstable sets.
  have hρ : ∀ w ∈ φ.toChart.source, ‖(Φ w).fst‖ < 2 * ε → ‖(Φ w).snd‖ < 2 * ε →
      (w ∈ hX.flow.stableSet q ↔ (Φ w).snd = 0) ∧ (w ∈ hX.flow.unstableSet q ↔ (Φ w).fst = 0) :=
    fun w hw h₁ h₂ ↦ hloc w hw (by
      rw [← φ.max_norm_fst_norm_snd_splitCoord]; exact max_lt (by linarith) (by linarith))
  refine ⟨?_, ?_, by simpa only [mul_zero] using hy₁fst.mul hy₁snd,
    by simpa only [zero_mul] using hy₂fst.mul hy₂snd⟩
  · filter_upwards [φ.toChart.open_source.mem_nhds hy₁φ, hy₁fst.eventually (lt_mem_nhds hε),
      hy₁fst.eventually (gt_mem_nhds (by linarith : ε < 2 * ε)),
      hy₁snd.eventually (gt_mem_nhds hε)] with w h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄, (hρ w h₁ h₃ (by linarith)).1⟩
  · filter_upwards [φ.toChart.open_source.mem_nhds hy₂φ, hy₂snd.eventually (lt_mem_nhds hε),
      hy₂snd.eventually (gt_mem_nhds (by linarith : ε < 2 * ε)),
      hy₂fst.eventually (gt_mem_nhds hε)] with w h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄, (hρ w h₁ (by linarith) h₃).2⟩

/-- **The flow through a gluing pair of a Morse box.** Let `φ` be a Morse chart at `q` in which
`X` is linear and which contains the cube of radius `2 ε`, and let `z` be a gluing pair of the box
of radius `ε` whose entrance point is the model entry point of a point `w` near the entrance face,
and whose exit point is the model exit point of a point `w'` near the exit face. Then `w` flows
to the point with the coordinates of the entrance point at its entry time, that point flows to the
point with the coordinates of the exit point at its exit time, and `w'` reaches the latter at its
own exit time. -/
private theorem flow_eq_of_mem_splitGluingPairs (hX : IsAdaptedPseudoGradient f X) {q : M}
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

/-- **Gluing pairs of a Morse box lie on trajectories from `p` to `r`.** Let `φ` be a Morse chart
at `q` in which `X` is linear and which contains the cube of radius `2 ε`, and let `z` be a gluing
pair of the box of radius `ε` whose entrance point is the model entry point of a point `w` of
`W^u(p)` near the entrance face, and whose exit point is the model exit point of a point `w'` of
`W^s(r)` near the exit face. Then the point with the coordinates of the entrance point lies on a
trajectory from `p` to `r`, which reaches the point with the coordinates of the exit point at the
exit time. -/
private theorem mem_unstableSet_inter_stableSet_of_mem_splitGluingPairs
    (hX : IsAdaptedPseudoGradient f X) {p q r : M} (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε r₀ : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ}
    {k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) ×
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ splitGluingPairs ε r₀ g k) {w w' : M} (hw : w ∈ φ.toChart.source)
    (hwf : ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε)
    (hws : ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε) (hwu : w ∈ hX.flow.unstableSet p)
    (hwz : splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
      (φ.splitCoord (φ.coord (φ.toChart w))) = z.1)
    (hw' : w' ∈ φ.toChart.source) (hw'f : ‖(φ.splitCoord (φ.coord (φ.toChart w'))).fst‖ < ε)
    (hw's : ‖(φ.splitCoord (φ.coord (φ.toChart w'))).snd‖ < 2 * ε)
    (hw'r : w' ∈ hX.flow.stableSet r)
    (hw'z : splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w'))))
      (φ.splitCoord (φ.coord (φ.toChart w'))) = z.2) :
    φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1)) ∈
        hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      hX.flow (splitExitTime ε z.1) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.1))) =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z.2)) := by
  obtain ⟨h₁, h₃, h₂⟩ := hX.flow_eq_of_mem_splitGluingPairs φ hφ hε hε₂ hz hw hwf hws hwz hw'
    hw'f hw's hw'z
  refine ⟨⟨h₁ ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hwu, ?_⟩, h₃⟩
  have h₄ := h₂ ▸ (Flow.apply_mem_stableSet_iff _ _).2 hw'r
  rw [← h₃] at h₄
  exact (Flow.apply_mem_stableSet_iff _ _).1 h₄

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
  rw [Flow.map_add, Flow.map_add, h₁, h₃, ← h₂, ← Flow.map_add, neg_add_cancel,
    Flow.map_zero_apply]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Reading split coordinates back on `M` through a Morse chart is continuous at the coordinates of
points of the chart. -/
private theorem continuousAt_toChart_symm_coord_symm_splitCoord_symm {q : M}
    (φ : MorseChart E f q)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) :
    ContinuousAt (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) z :=
  (φ.toChart.continuousAt_symm hz).comp (f := fun z ↦ φ.coord.symm (φ.splitCoord.symm z))
    ((φ.splitCoordL.symm.continuous.continuousAt (x := z)).congr
      (.of_forall fun _ ↦ φ.splitCoordL_symm_apply _))

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- If a Morse chart contains the cube of radius `ε`, reading pairs of split coordinates back on
`M` is continuous at the gluing pairs of the box of radius `ε`, and at the pair of coordinates of
two points of the chart. -/
private theorem continuousAt_toChart_symm_of_mem_insert_splitGluingPairs {q y₁ y₂ : M}
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
  exact ((continuousAt_toChart_symm_coord_symm_splitCoord_symm φ hb₁).comp
    continuous_fst.continuousAt).prodMk
    ((continuousAt_toChart_symm_coord_symm_splitCoord_symm φ hb₂).comp continuous_snd.continuousAt)

/-- **The model gluing arc at a broken trajectory, on the manifold.** For a trajectory from `p`
through `a₁` to `q` and one from `q` through `a₂` to `r`, of consecutive indices, there are points
`flow T₁ a₁` and `flow T₂ a₂` of the two trajectories and a continuous arc `B` in `M × M`, starting
at this pair, along which `B s` is, for `s ≠ 0`, a pair of points of one trajectory from `p` to
`r`, different `s` giving different trajectories. Every pair of points of one trajectory from `p`
to `r` on the levels of `flow T₁ a₁` and `flow T₂ a₂` near this pair lies on the trajectories of
some `B s` with `s` below the end of the arc. -/
private theorem IsMorseSmale.exists_gluingArc {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q r a₁ a₂ : M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (T₁ T₂ δ : ℝ) (hδ : 0 < δ) (B : Icc (0 : ℝ) δ → M × M), Continuous B ∧
      B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, hX.flow T₂ a₂) ∧
      (∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 →
        (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ ∃ t, hX.flow t (B s).1 = (B s).2) ∧
      (∀ s s' : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (s' : ℝ) ≠ 0 → ∀ t,
        hX.flow t (B s).1 = (B s').1 → s = s') ∧
      ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, hX.flow T₂ a₂),
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r → f w.1 = f (hX.flow T₁ a₁) →
        f w.2 = f (hX.flow T₂ a₂) → (∃ t, hX.flow t w.1 = w.2) →
        ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧
          ∃ t, hX.flow t w.2 = (B s).2 := by
  -- Plan: choose a Morse box at `q` with entrance point `y₁` and exit point `y₂`
  -- (`exists_morseBox_of_broken`), apply the model gluing theorem there, and take as `B` the points
  -- with the coordinates of the gluing pairs of small parameter. Uniqueness of the passage gives
  -- the injectivity clause, and `splitPassage_splitEntryTime_eq_splitExitTime` the last clause.
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hpr' : p ≠ r := by rintro rfl; omega
  obtain ⟨φ, ε, ρ, T₁, T₂, y₁, y₂, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s, hy₁ε,
    hy₂u, hy₂ε⟩ := hX.exists_morseBox_of_broken hf hpq' hqr' ha₁ ha₂
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦
    hε₂ z (by linarith)
  have hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hT₁ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hy₂ : y₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hT₂ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet q r T₂ ha₂
  -- The split coordinates near the entrance and exit points.
  obtain ⟨hA₁, hA₂, hy₁κ, hy₂κ⟩ :=
    hX.eventually_of_morseBox φ hε hερ hloc hy₁φ hy₂φ hy₁s hy₁ε hy₂u hy₂ε
  have hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet q → (Φ w).snd = 0 :=
    hA₁.mono fun w hw ↦ hw.2.2.2.2.1
  have hloc₂ : ∀ᶠ w in 𝓝 y₂, w ∈ hX.flow.unstableSet q → (Φ w).fst = 0 :=
    hA₂.mono fun w hw ↦ hw.2.2.2.2.1
  set U := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < 2 * ε ∧ ‖(Φ w).snd‖ < ε}
  set V := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < ε ∧ ‖(Φ w).snd‖ < 2 * ε}
  have hU : U ∈ 𝓝 y₁ := hA₁.mono fun w ⟨h₁, _, h₂, h₃, _⟩ ↦ ⟨h₁, h₂, h₃⟩
  have hV : V ∈ 𝓝 y₂ := hA₂.mono fun w ⟨h₁, _, h₂, h₃, _⟩ ↦ ⟨h₁, h₃, h₂⟩
  obtain ⟨r₀, hr₀, g, k, ⟨e, he, he₀⟩, hcl, hpairs, hexh⟩ :=
    h.exists_homeomorph_closure_splitGluingPairs hf hpq hqr φ hy₁ hy₁φ hy₂ hy₂φ hloc₁
      hloc₂ hε hy₁ε hy₂ε hU hV
  -- The orbits through the points of the gluing pairs run from `p` to `r`.
  have hP : ∀ z ∈ splitGluingPairs ε r₀ g k,
      Ψ z.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        hX.flow (splitExitTime ε z.1) (Ψ z.1) = Ψ z.2 := fun z hz ↦ by
    obtain ⟨⟨w, ⟨hw, hwf, hws⟩, hwu, -, hwz⟩, w', ⟨hw', hw'f, hw's⟩, hw'r, -, hw'z⟩ :=
      hpairs z hz
    exact hX.mem_unstableSet_inter_stableSet_of_mem_splitGluingPairs φ hφ hε hε₂ hz hw hwf hws
      hwu hwz hw' hw'f hw's hw'r hw'z
  -- Restrict to gluing parameters small enough for the passage to be unique.
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set r₁ := min r₀ (1 / (n + 1))
  have hr₁ : 0 < r₁ := lt_min hr₀ (by positivity)
  have hr₁r₀ : r₁ ≤ r₀ := min_le_left _ _
  have hr₁1 : r₁ ≤ 1 := (min_le_right _ _).trans
    ((div_le_one (by positivity)).2 (by linarith))
  have hr₁n : n * (r₁ * ε) ^ 2 < ε ^ 2 := by
    have h₁ : r₁ * (n + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    have h₂ : 0 < r₁ * ε := mul_pos hr₁ hε
    have h₃ : r₁ * ε * (n + 1) ≤ ε := by nlinarith
    have h₄ : (r₁ * ε * (n + 1)) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) h₃ 2
    nlinarith [mul_pos h₂ h₂]
  have hsmall : ∀ u : ℝ, 0 ≤ u → u ≤ r₁ * ε → n * u ^ 2 < ε ^ 2 := fun u hu hu' ↦
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hu' 2) hn) hr₁n
  have hr₁ε : r₁ * ε ≤ ε := mul_le_of_le_one_left hε.le hr₁1
  -- The points of the arc with nonzero parameter are unbroken pairs.
  have hz₀ : (Φ y₁, Φ y₂) ∈ closure (splitGluingPairs ε r₀ g k) := hcl ▸ mem_insert _ _
  have he₀' : e ⟨0, left_mem_Icc.2 hr₀.le⟩ = ⟨_, hz₀⟩ := Subtype.ext he₀
  have hepair : ∀ s : Icc (0 : ℝ) r₀, (s : ℝ) ≠ 0 →
      (e s).val ∈ splitGluingPairs ε r₀ g k ∧ ‖(e s).val.1.snd‖ = s * ε := by
    intro s hs
    have hsn : ‖(e s).val.1.snd‖ = s * ε := by
      have := he (e s)
      rw [e.symm_apply_apply] at this
      rw [this, div_mul_cancel₀ _ hε.ne']
    refine ⟨?_, hsn⟩
    have hmem : (e s).val ∈ insert (Φ y₁, Φ y₂) (splitGluingPairs ε r₀ g k) := hcl ▸ (e s).property
    refine hmem.resolve_left fun h0 ↦ hs ?_
    have : e s = e ⟨0, left_mem_Icc.2 hr₀.le⟩ := by rw [he₀']; exact Subtype.ext h0
    exact congrArg Subtype.val (e.injective this)
  -- The arc: the points with the coordinates of the gluing pairs.
  set B : Icc (0 : ℝ) r₁ → M × M := fun s ↦
    (Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.1,
      Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.2) with hBdef
  refine ⟨T₁, T₂, r₁, hr₁, B, ?_, ?_, fun s hs ↦ ?_, fun s s' hs hs' t hss' ↦ ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun s ↦ ?_
    have hc : Continuous fun s : Icc (0 : ℝ) r₁ ↦
        (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val :=
      continuous_subtypeVal.comp (e.continuous.comp (continuous_inclusion _))
    exact (continuousAt_toChart_symm_of_mem_insert_splitGluingPairs φ hε₁ hy₁φ hy₂φ
      (by rw [← hcl]; exact (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).property)).comp
      hc.continuousAt
  · simp only [hBdef]
    rw [inclusion_mk, he₀', hΨΦ y₁ hy₁φ, hΨΦ y₂ hy₂φ, hT₁, hT₂]
  · obtain ⟨hpz, hflow⟩ := hP _ (hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs).1
    exact ⟨hpz, _, hflow⟩
  · -- Two unbroken pairs whose entrance points lie on one orbit are equal.
    set z := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val
    set z' := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s')).val
    obtain ⟨hz, hzn⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs
    obtain ⟨hz', hzn'⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s') hs'
    have hle : ∀ u : Icc (0 : ℝ) r₁, (u : ℝ) * ε ≤ r₁ * ε := fun u ↦
      mul_le_mul_of_nonneg_right u.property.2 hε.le
    have h1 := hX.eq_of_flow_eq_of_mem_splitPassage_source φ hφ hε₁ (mem_splitGluingPairs.1 hz).1
      (mem_splitGluingPairs.1 hz').1
      (hsmall _ (norm_nonneg _) (hzn ▸ hle s)) (hsmall _ (norm_nonneg _) (hzn' ▸ hle s'))
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' (hP z hz).1) hss'
    have hzz : z = z' := Prod.ext h1 (by
      rw [(mem_splitGluingPairs.1 hz).2.2.2.1, (mem_splitGluingPairs.1 hz').2.2.2.1, h1])
    exact inclusion_injective _ (e.injective (Subtype.ext hzz))
  · -- A trajectory near the broken one crosses the box once; its entrance and exit points form a
    -- gluing pair of small parameter.
    have hκ₁ : ∀ᶠ w in 𝓝 y₁, ‖(Φ w).fst‖ * ‖(Φ w).snd‖ / ε < r₁ * ε := by
      have h := hy₁κ.div_const ε
      rw [zero_div] at h
      exact h.eventually (gt_mem_nhds (mul_pos hr₁ hε))
    have hκ₂ : ∀ᶠ w in 𝓝 y₂, ‖(Φ w).fst‖ * ‖(Φ w).snd‖ / ε < r₁ * ε := by
      have h := hy₂κ.div_const ε
      rw [zero_div] at h
      exact h.eventually (gt_mem_nhds (mul_pos hr₁ hε))
    rw [hT₁, hT₂]
    filter_upwards [(hA₁.and hκ₁).prod_nhds (hA₂.and hκ₂), hexh] with w hw hpairw hw1 hw1f hw2f hwt
    obtain ⟨⟨⟨hw₁src, hw₁f0, hw₁f, hw₁s, hw₁q⟩, hκw₁⟩, ⟨⟨hw₂src, hw₂s0, hw₂s, hw₂f, hw₂q⟩, hκw₂⟩⟩ :=
      hw
    obtain ⟨t, ht⟩ := hwt
    have hw2 : w.2 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r :=
      ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hw1
    -- Off the broken trajectory, the coordinate that vanishes on it does not vanish.
    have hsnd₁ : (Φ w.1).snd ≠ 0 := fun h0 ↦
      (Flow.disjoint_stableSet hqr').ne_of_mem (hw₁q.2 h0) hw1.2 rfl
    have hfst₂ : (Φ w.2).fst ≠ 0 := fun h0 ↦
      (Flow.disjoint_unstableSet hpq').ne_of_mem hw2.1 (hw₂q.2 h0) rfl
    obtain ⟨hE, hEQ'⟩ := hX.splitPassage_splitEntryTime_eq_splitExitTime φ hφ hε hε₂ hw₁src
      (norm_pos_iff.1 hw₁f0) hw₁f hsnd₁ hw₁s hw₂src (norm_pos_iff.1 hw₂s0) hw₂s hfst₂ hw₂f
      (by linarith) (hsmall _ (by positivity) hκw₁.le) (by linarith)
      (hsmall _ (by positivity) hκw₂.le)
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw1) ht
    have hEQ := hpairw hw1.1 hw1f hw2.2 hw2f (mem_splitPassage_source.1 hE).2.1 hEQ'
    -- The pair is a point of the arc of small parameter.
    set s₀ := e.symm ⟨_, subset_closure hEQ⟩ with hs₀def
    have hs₀r₁ : (s₀ : ℝ) < r₁ := by
      rw [hs₀def, he, div_lt_iff₀ hε, norm_snd_splitQuadraticFlow_splitEntryTime hε
        (norm_pos_iff.1 hw₁f0)]
      exact hκw₁
    have hes : e (inclusion (Icc_subset_Icc_right hr₁r₀) ⟨(s₀ : ℝ), s₀.property.1, hs₀r₁.le⟩) =
        ⟨_, subset_closure hEQ⟩ := by
      rw [← e.apply_symm_apply ⟨_, subset_closure hEQ⟩, ← hs₀def]
    refine ⟨⟨s₀, s₀.property.1, hs₀r₁.le⟩, hs₀r₁, ⟨splitEntryTime ε (Φ w.1), ?_⟩,
      ⟨splitExitTime ε (Φ w.2), ?_⟩⟩
    · simp only [hBdef, hes]
      exact hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₁src hw₁f hw₁s
    · simp only [hBdef, hes]
      exact hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw₂src hw₂f hw₂s

/-- **Gluing at a broken trajectory.** Let `X` be a Morse–Smale adapted pseudo-gradient for a
Morse function `f` on a compact manifold, and `p`, `q`, `r` critical points of consecutive indices
`ind p = ind q + 1 = ind r + 2`. Record trajectories from `p` to `r` by their points on two levels:
take a point `a₁` of a trajectory from `p` to `q` and a point `a₂` of a trajectory from `q` to `r`,
and let `S` be the set of pairs `(w₁, w₂)` of points of one trajectory from `p` to `r` with
`f w₁ = f a₁` and `f w₂ = f a₂`. Then the broken trajectory `(a₁, a₂)` has a neighbourhood `N` in
`S ∪ {(a₁, a₂)}` homeomorphic to a half-open interval `[0, δ)`, with `(a₁, a₂)` corresponding to
`0`.

So the broken trajectories are endpoints of the compactified space of index-two trajectories
recorded on two levels, and every broken trajectory is a limit of unbroken ones. -/
theorem IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, a₂) ∧
      N ⊆ insert (a₁, a₂) {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₁, a₂) {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2}] (a₁, a₂) := by
  -- Plan: follow the arc `B` of `exists_gluingArc` to the two levels. The resulting map `F` is
  -- continuous and injective on a closed interval, hence an embedding, and every unbroken pair
  -- near `(a₁, a₂)` is a value of `F` at a parameter below the end of the interval.
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hpr' : p ≠ r := by rintro rfl; omega
  obtain ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, hBinj, hBfwd⟩ :=
    h.exists_gluingArc hf hpq hqr ha₁ ha₂
  set S := {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
    f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} with hSdef
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' ha₁
  have hfa₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr' ha₂
  have hy₁ : hX.flow T₁ a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hy₂ : hX.flow T₂ a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hX.flow.isInvariant_unstableSet_inter_stableSet q r T₂ ha₂
  -- Along the arc, the first points run from `p`, and the second points run to `r`.
  have hB : ∀ s, (∃ b, p ≠ b ∧ (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧
      f b < f a₁) ∧ ∃ a, a ≠ r ∧ (B s).2 ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet r ∧
      f a₂ < f a := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
      rw [hB₀]
      exact ⟨⟨q, hpq', hy₁, hfa₁.1⟩, ⟨q, hqr', hy₂, hfa₂.2⟩⟩
    · obtain ⟨hs₁, t, ht⟩ := hBS s hs
      exact ⟨⟨r, hpr', hs₁, by linarith [hfa₁.1, hfa₂.1, hfa₂.2]⟩,
        ⟨p, hpr', ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hs₁,
          by linarith [hfa₁.1, hfa₁.2, hfa₂.2]⟩⟩
  -- The level points along the arc.
  set F : Icc (0 : ℝ) δ → M × M := fun s ↦
    (hX.flow (Flow.levelCrossingTime hX.flow f (f a₁) (B s).1) (B s).1,
      hX.flow (Flow.levelCrossingTime hX.flow f (f a₂) (B s).2) (B s).2) with hFdef
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun s ↦ ?_
    obtain ⟨⟨b, hpb, hb, hfb⟩, ⟨a, har, ha, hfa⟩⟩ := hB s
    obtain ⟨σ₁, hσ₁, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpb hb hfb hfa₁.2
    obtain ⟨σ₂, hσ₂, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet har ha hfa₂.1 hfa
    have h₁ := hX.tendsto_flow_levelCrossingTime hpb hb hσ₁
      ((continuous_fst.comp hBc).tendsto s) (.of_forall fun s' ↦ by
        obtain ⟨⟨b', hpb', hb', -⟩, -⟩ := hB s'
        exact hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb' hb')
    have h₂ := hX.tendsto_flow_levelCrossingTime har ha hσ₂
      ((continuous_snd.comp hBc).tendsto s) (.of_forall fun s' ↦ by
        obtain ⟨-, ⟨a', ha'r, ha', -⟩⟩ := hB s'
        exact hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet ha'r ha')
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) hσ₁ 0
    have e₂ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet har ha) hσ₂ 0
    rw [Flow.map_zero_apply] at e₁ e₂
    rw [← e₁] at h₁
    rw [← e₂] at h₂
    exact h₁.prodMk_nhds h₂
  have hF₀ : F ⟨0, left_mem_Icc.2 hδ.le⟩ = (a₁, a₂) := by
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpq' ha₁)
      (by rw [Flow.map_zero_apply] : f (hX.flow 0 a₁) = f a₁) T₁
    have e₂ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hqr' ha₂)
      (by rw [Flow.map_zero_apply] : f (hX.flow 0 a₂) = f a₂) T₂
    rw [Flow.map_zero_apply] at e₁ e₂
    simp only [hFdef, hB₀, e₁, e₂]
  -- Away from `0`, the level points are an unbroken trajectory.
  have hFS : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ∈ S := by
    intro s hs
    obtain ⟨hs₁, t, ht⟩ := hBS s hs
    have hs₂ : (B s).2 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r :=
      ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hs₁
    obtain ⟨σ₁, hσ₁, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr' hs₁
      (by linarith [hfa₁.1, hfa₂.1, hfa₂.2]) hfa₁.2
    obtain ⟨σ₂, hσ₂, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr' hs₂
      hfa₂.1 (by linarith [hfa₁.1, hfa₁.2, hfa₂.2])
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hs₁) hσ₁ 0
    have e₂ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hs₂) hσ₂ 0
    rw [Flow.map_zero_apply] at e₁ e₂
    simp only [hFdef, hSdef, mem_ofPred_eq, e₁, e₂]
    refine ⟨hX.flow.isInvariant_unstableSet_inter_stableSet p r _ hs₁, hσ₁, hσ₂, σ₂ + t - σ₁, ?_⟩
    rw [← Flow.map_add, sub_add_cancel, Flow.map_add, ht]
  have hFinj : Injective F := by
    have hne : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ≠ (a₁, a₂) := fun s hs h ↦
      (Flow.disjoint_stableSet hqr'.symm).ne_of_mem (hFS s hs).1.2 (h ▸ ha₁.2) rfl
    intro s s' hss'
    by_cases hs : (s : ℝ) = 0
    · by_cases hs' : (s' : ℝ) = 0
      · exact Subtype.ext (hs.trans hs'.symm)
      · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
        rw [hF₀] at hss'
        exact absurd hss'.symm (hne s' hs')
    by_cases hs' : (s' : ℝ) = 0
    · obtain rfl : s' = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs'
      rw [hF₀] at hss'
      exact absurd hss' (hne s hs)
    -- Equal first level points put the first points of `B s` and `B s'` on one orbit.
    refine hBinj s s' hs hs' (Flow.levelCrossingTime hX.flow f (f a₁) (B s).1 -
      Flow.levelCrossingTime hX.flow f (f a₁) (B s').1) ?_
    have h₁ := congrArg Prod.fst hss'
    simp only [hFdef] at h₁
    rw [sub_eq_add_neg, add_comm, Flow.map_add, h₁, ← Flow.map_add, neg_add_cancel,
      Flow.map_zero_apply]
  -- Every unbroken trajectory near the broken one is a level point of the arc.
  have hfwd : ∀ᶠ w in 𝓝[S] (a₁, a₂),
      ∃ s : Ico (0 : ℝ) δ, F (inclusion Ico_subset_Icc_self s) = w := by
    have hSmem : ∀ᶠ w in 𝓝[S] (a₁, a₂), w ∈ S := self_mem_nhdsWithin
    have hw₂m : ∀ w ∈ S, w.2 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r := fun w hw ↦ by
      obtain ⟨t, ht⟩ := hw.2.2.2
      exact ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hw.1
    -- The points of the trajectories on the levels of the arc's start tend to its start.
    have hm₁ := hX.tendsto_flow_levelCrossingTime hpq' ha₁ (σ₀ := T₁) rfl
      ((continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds)
      (hSmem.mono fun w hw ↦ hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw.1)
    have hm₂ := hX.tendsto_flow_levelCrossingTime hqr' ha₂ (σ₀ := T₂) rfl
      ((continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds)
      (hSmem.mono fun w hw ↦ hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr'
        (hw₂m w hw))
    have hfy₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq' hy₁
    have hfy₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr' hy₂
    filter_upwards [hSmem, (hm₁.prodMk_nhds hm₂).eventually hBfwd] with w hw hfw
    have hw2 := hw₂m w hw
    obtain ⟨hw1, hw1f, hw2f, t, ht⟩ := hw
    have hanti₁ := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw1
    have hanti₂ := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw2
    obtain ⟨σ₁, hσ₁, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr' hw1
      (by linarith [hfy₁.1, hfa₂.1, hfa₂.2]) hfy₁.2
    obtain ⟨σ₂, hσ₂, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr' hw2
      hfy₂.1 (by linarith [hfy₂.2, hfa₁.1, hfa₁.2])
    set τ₁ := Flow.levelCrossingTime hX.flow f (f (hX.flow T₁ a₁)) w.1
    set τ₂ := Flow.levelCrossingTime hX.flow f (f (hX.flow T₂ a₂)) w.2
    obtain ⟨s, hs, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := hfw
      (hX.flow.isInvariant_unstableSet_inter_stableSet p r _ hw1)
      (Flow.apply_flow_levelCrossingTime ⟨σ₁, hσ₁⟩) (Flow.apply_flow_levelCrossingTime ⟨σ₂, hσ₂⟩)
      ⟨τ₂ + t - τ₁, by rw [← Flow.map_add, sub_add_cancel, Flow.map_add, ht]⟩
    refine ⟨⟨s, s.property.1, hs⟩, ?_⟩
    have e₁ := Flow.flow_levelCrossingTime_flow hanti₁
      (by rw [Flow.map_zero_apply]; exact hw1f : f (hX.flow 0 w.1) = f a₁) (t₁ + τ₁)
    have e₂ := Flow.flow_levelCrossingTime_flow hanti₂
      (by rw [Flow.map_zero_apply]; exact hw2f : f (hX.flow 0 w.2) = f a₂) (t₂ + τ₂)
    rw [Flow.map_zero_apply, Flow.map_add] at e₁ e₂
    rw [ht₁] at e₁
    rw [ht₂] at e₂
    exact Prod.ext e₁ e₂
  have hemb : IsEmbedding (F ∘ inclusion (Ico_subset_Icc_self : Ico (0 : ℝ) δ ⊆ Icc 0 δ)) :=
    (hFc.isClosedEmbedding hFinj).isEmbedding.comp (IsEmbedding.inclusion Ico_subset_Icc_self)
  refine ⟨range (F ∘ inclusion Ico_subset_Icc_self), δ, hδ, hemb.toHomeomorph, hF₀, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    by_cases hs : (s : ℝ) = 0
    · left
      rw [← hF₀]
      exact congrArg F (Subtype.ext hs)
    · exact Or.inr (hFS _ hs)
  · rw [mem_nhdsWithin_insert]
    refine ⟨⟨⟨0, left_mem_Ico.2 hδ⟩, hF₀⟩, ?_⟩
    filter_upwards [hfwd] with w ⟨s, hs⟩ using ⟨s, hs⟩

/-- **The flow carries a set transverse to an unstable manifold along it.** Let `Z` be a set
through a point `y` of `W^u(q)`, flattened near `y` by a chart of the maximal atlas and transverse
to `W^u(q)` at `y`. For every time `T`, the set `flow T '' Z`, written as the preimage of `Z`
under `flow (-T)`, is flattened near `flow T y` by a chart of the maximal atlas and is transverse
to `W^u(q)` there. -/
private theorem exists_isSliceChart_preimage_flow (hX : IsAdaptedPseudoGradient f X) {q y : M}
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

/-- **Gluing a broken trajectory into a transverse set.** Let `X` be a Morse–Smale adapted
pseudo-gradient for a Morse function `f` on a compact manifold, `a₁` a point of a trajectory from
`p` to a critical point `q ≠ p`, and `y ≠ q` a point of the unstable manifold `W^u(q)`. Let `Z` be
a set through `y`, flattened near `y` by a chart of the maximal atlas, which meets `W^u(q)`
transversally at `y`. Then, for all neighbourhoods `N₁` of `a₁` and `N` of `y`, some point of
`W^u(p) ∩ Z` lies in `N` and its orbit passes through `N₁`. So `W^u(p) ∩ Z` accumulates at `y`,
along orbits which follow the trajectory through `a₁`. For `Z` the stable manifold of a critical
point this is the gluing of a broken trajectory
(`IsMorseSmale.exists_mem_unstableSet_inter_stableSet_flow_mem`). -/
theorem IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q a₁ y : M} {Z : Set M} (hpq : p ≠ q)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hy : y ∈ hX.flow.unstableSet q)
    (hyq : y ≠ q) {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤)
    {N₁ N : Set M} (hN₁ : N₁ ∈ 𝓝 a₁) (hN : N ∈ 𝓝 y) :
    ∃ w ∈ hX.flow.unstableSet p ∩ Z, w ∈ N ∧ ∃ s : ℝ, hX.flow s w ∈ N₁ := by
  -- Plan: choose a Morse box at `q` with entrance point `y₁` on the trajectory through `a₁` and
  -- exit point `y₂` on the orbit of `y`; glue a disc in `W^u(p)` through `y₁` to a disc through
  -- `y₂` in the image of `Z` under the flow, and flow a glued point back to `Z`.
  obtain ⟨r, -, hyr⟩ := hX.exists_mem_stableSet hf y
  have hqr : q ≠ r := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hy, hyr⟩)
  obtain ⟨φ, ε, ρ, T₁, T₂, y₁, y₂, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s, hy₁ε,
    hy₂u, hy₂ε⟩ := hX.exists_morseBox_of_broken hf hpq hqr ha₁ ⟨hy, hyr⟩
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hT₁ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hy₂ : y₂ ∈ hX.flow.unstableSet q := hT₂ ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hy
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
    rw [← hT₂, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  obtain ⟨φ', hφ', hZ', hy₂φ', htr'⟩ :=
    hX.exists_isSliceChart_preimage_flow hφZ hZ hyφZ htr T₂
  rw [hT₂] at hy₂φ' htr'
  obtain ⟨ψ, ψ', hψ, hψ', hψ₀, hψs⟩ :=
    h.exists_hasStrictFDerivAt_mem_unstableSet_of_eventually_mem_stableSet_iff hf φ hy₁ hy₁φ
      (hA₁.mono fun w hw ↦ hw.2.2.2.2)
  obtain ⟨χ, χ', hχ, hχ', hχ₀, hχs⟩ :=
    exists_hasStrictFDerivAt_splitCoord φ (pr := WithLp.fstL 2 ℝ _ _)
      (fun u ↦ ⟨WithLp.toLp 2 (u, 0), rfl⟩) (hA₂.mono fun w hw ↦ hw.2.2.2.2) hφ' hZ' hy₂φ hy₂φ'
      (mem_preimage.2 (hy₂Z ▸ hyZ)) hy₂ htr'
  have hΦy₁ : WithLp.toLp 2 ((Φ y₁).fst, 0) = Φ y₁ :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simpa using hy₁s.symm))
  have hΦy₂ : WithLp.toLp 2 (0, (Φ y₂).snd) = Φ y₂ :=
    WithLp.ofLp_injective 2 (Prod.ext (by simpa using hy₂u.symm) (by simp))
  -- Near `0`, the points of the discs lie near the entrance and exit points.
  have hΨψ : Tendsto (fun z ↦ Ψ (ψ z)) (𝓝 0) (𝓝 y₁) := by
    have hc : ContinuousAt Ψ (Φ y₁) := continuousAt_toChart_symm_coord_symm_splitCoord_symm φ
      (by simpa [hΦdef] using φ.toChart.map_source hy₁φ)
    have hψc := hψ.continuousAt.tendsto
    rw [hψ₀] at hψc
    have h := hc.tendsto.comp hψc
    rwa [hΨΦ y₁ hy₁φ] at h
  have hΨχ : Tendsto (fun z ↦ Ψ (χ z)) (𝓝 0) (𝓝 y₂) := by
    have hc : ContinuousAt Ψ (Φ y₂) := continuousAt_toChart_symm_coord_symm_splitCoord_symm φ
      (by simpa [hΦdef] using φ.toChart.map_source hy₂φ)
    have hχc := hχ.continuousAt.tendsto
    rw [hχ₀] at hχc
    have h := hc.tendsto.comp hχc
    rwa [hΨΦ y₂ hy₂φ] at h
  -- Flowing back by `T₁` and `T₂`, points near the entrance and exit points land in `N₁` and `N`.
  have hN₁' : hX.flow (-T₁) ⁻¹' N₁ ∈ 𝓝 y₁ := by
    refine (hX.flow.continuous_toFun (-T₁)).continuousAt.preimage_mem_nhds ?_
    rwa [← hT₁, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
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
  have hz : (e ⟨r₀, right_mem_Icc.2 hr₀.le⟩).val ∈ splitGluingPairs ε r₀ g k := by
    have hmem : (e ⟨r₀, right_mem_Icc.2 hr₀.le⟩).val ∈
        insert (Φ y₁, Φ y₂) (splitGluingPairs ε r₀ g k) :=
      hcl ▸ (e ⟨r₀, right_mem_Icc.2 hr₀.le⟩).property
    refine hmem.resolve_left fun h0 ↦ hr₀.ne ?_
    have : e ⟨r₀, right_mem_Icc.2 hr₀.le⟩ = e ⟨0, left_mem_Icc.2 hr₀.le⟩ :=
      Subtype.ext (h0.trans he₀.symm)
    exact (congrArg Subtype.val (e.injective this)).symm
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
points with `p ≠ q` and `q ≠ r`, with no condition on their Morse indices. For a point `a₁` of a
trajectory from `p` to `q`, a point `a₂` of a trajectory from `q` to `r`, and neighbourhoods `N₁`
of `a₁` and `N₂` of `a₂`, there is a trajectory from `p` to `r` which passes through `N₁` and,
later or earlier, through `N₂`: the broken trajectory through `a₁` and `a₂` is a limit of unbroken
trajectories in the sense of Morse theory. -/
theorem IsMorseSmale.exists_mem_unstableSet_inter_stableSet_flow_mem
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M} (hpq : p ≠ q) (hqr : q ≠ r)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) {N₁ N₂ : Set M} (hN₁ : N₁ ∈ 𝓝 a₁)
    (hN₂ : N₂ ∈ 𝓝 a₂) :
    ∃ u ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r, ∃ s₁ s₂ : ℝ,
      hX.flow s₁ u ∈ N₁ ∧ hX.flow s₂ u ∈ N₂ := by
  -- Glue into the stable manifold of `r`, which is flattened near `a₂` and transverse to `W^u(q)`.
  have ha₂q : a₂ ≠ q := by
    rintro rfl
    exact (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hqr ha₂).2.false
  obtain ⟨L, φZ, -, ha₂φZ, hφZ, hZ⟩ :=
    hX.exists_isSliceChart_stableSet (hX.mfderiv_eq_zero_of_mem_stableSet ha₂.2) ha₂.2
  obtain ⟨u, hu, hu₂, s, hs⟩ := h.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart hf hpq ha₁
    ha₂.1 ha₂q hφZ hZ ha₂φZ ha₂.2 (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top ha₂)
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
    h.exists_mem_unstableSet_inter_stableSet_flow_mem hf hpq hqr ha₁ ha₂ (hB₁.mem n) (hB₂.mem n)
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
