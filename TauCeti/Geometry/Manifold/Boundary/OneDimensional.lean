/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
import Mathlib.Algebra.Order.Interval.Set.Group
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Compact one-dimensional manifolds have an even number of boundary points

Let `M` be a compact Hausdorff topological manifold modelled on the half-line
`EuclideanHalfSpace 1`. This file proves that its boundary `(𝓡∂ 1).boundary M` is finite and has
an even number of points, and that when `M` is oriented, as many of them are outgoing as incoming.
No smoothness of the atlas is assumed.

This is the parity fact behind the classical proof that the Morse boundary squares to zero. There,
the compactified spaces of index-two trajectories are compact one-dimensional manifolds whose
boundary points are the broken trajectories, so the broken trajectories come in pairs; their
parity is exactly the criterion of `TauCeti.morseBoundary_comp_morseBoundary_eq_zero_iff`. The
gluing charts of such a compactification are only homeomorphisms, which is why the statement here
is topological.

Such a compactification comes with local models rather than an atlas: each broken trajectory has a
neighbourhood homeomorphic to `[0, ε)`, and each unbroken trajectory a neighbourhood homeomorphic to
an open subset of a line. The last section assembles these local models into an atlas, so that a
compact Hausdorff space described this way has finitely many, and an even number of, points with a
half-open model.

An orientation is given topologically, by local coordinates (`TauCeti.IsOrientingCoordinates`):
functions `φ x`, continuous and injective near `x`, any two of which induce the same order near
every point where both are defined. At a boundary point `x` the orientation points out of `M`
when `x` is a local maximum of `φ x`, and into `M` when it is a local minimum; exactly one of the
two holds. The oriented count says that these two kinds of boundary points are equally many. It
is the topological counterpart of
`TauCeti.ncard_setOf_signBasis_eq_one_eq_ncard_setOf_signBasis_eq_neg_one`, which needs a smooth
structure. It is the topological input to the proof that the integral Morse boundary squares to
zero, where the broken trajectories at the two ends of an arc of index-two trajectories carry
opposite signs.

Mathlib defines a boundary point through the preferred chart at that point, and proves the notion
chart-independent only for `C¹` manifolds. In dimension one chart independence is elementary: a
chart transition sending a boundary point to an interior point would carry a connected punctured
half-interval onto a disconnected punctured interval
(`ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff`).

## Strategy

Rather than classify compact one-manifolds as circles and closed intervals, we count ends. By
compactness, finitely many coordinate intervals cover `M`. Their endpoints form a finite set `P` of
interior points such that each connected component `K` of the complement of `P` lies in a single
chart, inside a compact interval of coordinates. The coordinates of `K` form a relatively open
interval of `[0, ∞)`, whose supremum is not attained and whose infimum is attained only at the
boundary coordinate `0`. So each of its two endpoints is either the coordinate of a boundary point
lying in `K`, or the coordinate of a point of `P` which `K` approaches from one side.

Every point of `P` has two sides, and no component contains both sides of the same point. Sending
each side of each point of `P`, and each boundary point, to the component containing it therefore
gives a map whose fibres all have exactly two elements. Hence `2 * #P + #(∂M)` is even.

For the oriented count, call an end a *tail* when the orientation leaves its point into the
component. Along a component the coordinates `φ z` all increase, or all decrease, with the chart
coordinate, so of its two ends exactly one is a tail. Of the two sides of a point of `P` exactly
one is a tail as well. Counting tails with `1` and the other ends with `-1`, every component and
every point of `P` therefore contribute `0`, and so do the boundary points, which are tails exactly
when they are incoming.

## Main results

* `TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff`: a point is a boundary point
  exactly when some, equivalently any, chart around it reads it with coordinate `0`.
* `TauCeti.ModelWithCorners.finite_boundary_euclideanHalfSpace_one`: a compact one-dimensional
  manifold has finitely many boundary points.
* `TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`: a compact Hausdorff
  one-dimensional manifold has an even number of boundary points.
* `TauCeti.finite_of_forall_exists_homeomorph_Ico` and
  `TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`: the same for a compact (Hausdorff) space
  given by local models, counting the points whose model is `[0, ε)`.
* `TauCeti.IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin`: at a boundary point an
  orientation points either out or in.
* `TauCeti.IsOrientingCoordinates.isLocalMax_iff_of_mem` and
  `TauCeti.IsOrientingCoordinates.isLocalMin_iff_of_mem`: whether it points out or in can be read
  in any orienting coordinate defined at the boundary point.
* `TauCeti.ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin`: a compact oriented
  one-dimensional manifold has as many outgoing as incoming boundary points.
* `TauCeti.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin_of_forall_exists_homeomorph_Ico`: the
  same for a compact Hausdorff space given by local models.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  Appendix (the classification of one-manifolds, and its corollary that the boundary of a compact
  one-manifold has an even number of points) and §5 (the boundary points of a compact oriented
  one-manifold have signs adding up to zero).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactified trajectory spaces as compact one-manifolds with boundary).
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold

open TauCeti.EuclideanHalfSpace

namespace TauCeti

section Chart

variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- Reading the point of the normal ray at height `s ≥ 0` back through a chart gives `s`. -/
private theorem coord_symm_normalRay {s : ℝ} (hs : 0 ≤ s) (h : normalRay s ∈ e.target) :
    (e (e.symm (normalRay s))).val 0 = s := by
  rw [e.right_inv h, normalRay_coe_apply, max_eq_left hs]

/-- A point of a chart domain is recovered from its normal coordinate. -/
private theorem symm_normalRay_coord {y : M} (hy : y ∈ e.source) :
    e.symm (normalRay ((e y).val 0)) = y := by
  rw [normalRay_normalCoord, e.left_inv hy]

private theorem injOn_coord : InjOn (fun y ↦ (e y).val 0) e.source := fun y hy z hz h ↦ by
  rw [← symm_normalRay_coord hy, ← symm_normalRay_coord hz]
  exact congrArg (fun s ↦ e.symm (normalRay s)) h

private theorem continuousOn_coord : ContinuousOn (fun y ↦ (e y).val 0) e.source := by
  have h : Continuous fun t : EuclideanHalfSpace 1 ↦ t.val 0 := by fun_prop
  exact h.comp_continuousOn e.continuousOn

private theorem continuousOn_symm_normalRay {S : Set ℝ} (h : ∀ s ∈ S, normalRay s ∈ e.target) :
    ContinuousOn (fun s ↦ e.symm (normalRay s)) S :=
  e.continuousOn_symm.comp continuous_normalRay.continuousOn h

/-- The normal coordinate of a chart maps open sets to relatively open subsets of `[0, ∞)`: around
the coordinate of a point of an open set `V` inside the chart domain there is an interval, of
radius smaller than the coordinate itself when that is positive, whose points all come from `V`. -/
private theorem exists_coord_nhds {V : Set M} (hV : IsOpen V) (hVe : V ⊆ e.source) {y : M}
    (hy : y ∈ V) : ∃ ε > 0, (0 < (e y).val 0 → ε < (e y).val 0) ∧
      ∀ s, |s - (e y).val 0| ≤ ε → normalRay s ∈ e.target ∧ e.symm (normalRay s) ∈ V := by
  set c := (e y).val 0
  have hU : IsOpen (normalRay ⁻¹' (e.target ∩ e.symm ⁻¹' V)) :=
    (e.isOpen_inter_preimage_symm hV).preimage continuous_normalRay
  have hc : c ∈ normalRay ⁻¹' (e.target ∩ e.symm ⁻¹' V) := by
    simp only [mem_preimage, mem_inter_iff, c, normalRay_normalCoord, e.left_inv (hVe hy)]
    exact ⟨e.map_source (hVe hy), hy⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hU c hc
  set ε := min (ε₀ / 2) (if 0 < c then c / 2 else ε₀)
  have hεε₀ : ε ≤ ε₀ / 2 := min_le_left _ _
  refine ⟨ε, lt_min (by positivity) (by split_ifs <;> positivity), fun h ↦ ?_, fun s hs ↦ ?_⟩
  · exact (min_le_right _ _).trans_lt (by simp only [h, ↓reduceIte]; linarith)
  · exact hball (by rw [Metric.mem_ball, Real.dist_eq]; linarith)

/-- **Boundary invariance in dimension one.** If one chart reads a point with vanishing normal
coordinate, so does every other chart. -/
private theorem coord_eq_zero_of_coord_eq_zero {e' : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    {y : M} (hy : y ∈ e.source) (hy' : y ∈ e'.source) (h : (e y).val 0 = 0) :
    (e' y).val 0 = 0 := by
  by_contra hne
  set c := (e' y).val 0
  have hc : 0 < c := lt_of_le_of_ne (e' y).property (Ne.symm hne)
  have hV : IsOpen (e.source ∩ e'.source) := e.open_source.inter e'.open_source
  obtain ⟨ε, hε, -, hεV⟩ := exists_coord_nhds hV inter_subset_left ⟨hy, hy'⟩
  rw [h] at hεV
  -- The points of the common domain with `e`-coordinate below `ε`.
  set O := e.source ∩ e'.source ∩ (fun z ↦ (e z).val 0) ⁻¹' Iio ε
  have hO : IsOpen O :=
    (continuousOn_coord.mono inter_subset_left).isOpen_inter_preimage hV isOpen_Iio
  obtain ⟨η, hη, hηc, hηO⟩ :=
    exists_coord_nhds (e := e') hO (fun z hz ↦ hz.1.2) ⟨⟨hy, hy'⟩, by simp [h, hε]⟩
  replace hηc : η < c := hηc hc
  -- The `e'`-coordinate as a function of the `e`-coordinate, on `[0, ε)`.
  set g : ℝ → ℝ := fun s ↦ (e' (e.symm (normalRay s))).val 0
  have hmem : ∀ s ∈ Ico 0 ε, normalRay s ∈ e.target ∧ e.symm (normalRay s) ∈ e.source ∩ e'.source :=
    fun s hs ↦ hεV s (by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2.le)
  have hcont : ContinuousOn g (Ico 0 ε) :=
    continuousOn_coord.comp (continuousOn_symm_normalRay fun s hs ↦ (hmem s hs).1)
      fun s hs ↦ (hmem s hs).2.2
  have hinj : InjOn g (Ico 0 ε) := fun s hs s' hs' hss' ↦ by
    have := injOn_coord (hmem s hs).2.2 (hmem s' hs').2.2 hss'
    rw [← coord_symm_normalRay hs.1 (hmem s hs).1, ← coord_symm_normalRay hs'.1 (hmem s' hs').1]
    exact congrArg (fun z ↦ (e z).val 0) this
  have hg0 : g 0 = c := by
    have : normalRay 0 = e y := by rw [← normalRay_normalCoord (e y), h]
    simp only [g, this, e.left_inv hy, c]
  -- Every `e'`-coordinate near `c` is a value of `g` at a positive `e`-coordinate.
  have hval : ∀ s', |s' - c| ≤ η → s' ≠ c → ∃ s ∈ Ioo 0 ε, g s = s' := by
    intro s' hs' hs'c
    have hs'0 : 0 ≤ s' := by linarith [abs_le.1 hs']
    obtain ⟨ht, hO'⟩ := hηO s' hs'
    refine ⟨(e (e'.symm (normalRay s'))).val 0, ⟨?_, hO'.2⟩, ?_⟩
    · refine lt_of_le_of_ne (e _).property fun h0 ↦ hs'c ?_
      rw [← hg0, ← coord_symm_normalRay hs'0 ht]
      simp only [g, h0, symm_normalRay_coord hO'.1.1]
    · simp only [g, symm_normalRay_coord hO'.1.1, coord_symm_normalRay hs'0 ht]
  obtain ⟨s₁, hs₁, hg₁⟩ := hval (c - η) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη])
    (by linarith)
  obtain ⟨s₂, hs₂, hg₂⟩ := hval (c + η) (by rw [add_sub_cancel_left, abs_of_pos hη])
    (by linarith)
  have hsub : uIcc s₁ s₂ ⊆ Ioo 0 ε := ordConnected_Ioo.uIcc_subset hs₁ hs₂
  have hcg : c ∈ uIcc (g s₁) (g s₂) := by
    rw [hg₁, hg₂, uIcc_of_le (by linarith)]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hgs⟩ :=
    intermediate_value_uIcc (hcont.mono (hsub.trans Ioo_subset_Ico_self)) hcg
  exact (hsub hs).1.ne' (hinj (Ioo_subset_Ico_self (hsub hs)) ⟨le_rfl, hε⟩ (hgs.trans hg0.symm))

end Chart

section Direction

variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- A function `ψ` *increases along the chart `e` at `y`* when it exceeds `ψ y` at the points read
by `e` with coordinate slightly above that of `y`. -/
private def IncreasesAt (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (ψ : M → ℝ) (y : M) :
    Prop :=
  ∀ᶠ s in 𝓝[>] (e y).val 0, ψ y < ψ (e.symm (normalRay s))

/-- The points of a chart domain with coordinate within `η` of that of `y` form a neighbourhood of
`y`. -/
private theorem coord_mem_nhds {y : M} (hy : y ∈ e.source) {η : ℝ} (hη : 0 < η) :
    e.source ∩ (fun z ↦ (e z).val 0) ⁻¹' {s | |s - (e y).val 0| < η} ∈ 𝓝 y :=
  (continuousOn_coord.isOpen_inter_preimage e.open_source
    (isOpen_lt (by fun_prop) continuous_const)).mem_nhds ⟨hy, by simpa using hη⟩

/-- Reading the coordinates slightly above that of `y` back through the chart tends to `y`. -/
private theorem tendsto_symm_normalRay {y : M} (hy : y ∈ e.source) :
    Filter.Tendsto (fun s ↦ e.symm (normalRay s)) (𝓝[>] (e y).val 0) (𝓝 y) := by
  obtain ⟨ε, hε, -, h⟩ := exists_coord_nhds e.open_source subset_rfl hy
  have hc : ContinuousAt (fun s ↦ e.symm (normalRay s)) ((e y).val 0) :=
    (continuousOn_symm_normalRay (S := Icc ((e y).val 0 - ε) ((e y).val 0 + ε)) fun s hs ↦
      (h s ((abs_sub_comm _ _).trans_le (mem_Icc_iff_abs_le.2 hs))).1).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  simpa only [symm_normalRay_coord hy] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- **Continuous injective functions are monotone in a coordinate.** If `ψ` is continuous and
injective on an open neighbourhood `V` of a point `y` of a chart domain, then on a coordinate
interval around `y`, read through the chart, `ψ` is strictly monotone if it increases along the
chart at `y`, and strictly antitone otherwise. -/
private theorem exists_strictMonoOn_of_increasesAt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {y : M} (hyV : y ∈ V) (hye : y ∈ e.source) :
    ∃ η > 0, (∀ s, |s - (e y).val 0| ≤ η → normalRay s ∈ e.target ∧ e.symm (normalRay s) ∈ V) ∧
      (IncreasesAt e ψ y → StrictMonoOn (fun s ↦ ψ (e.symm (normalRay s)))
        (Icc (max ((e y).val 0 - η) 0) ((e y).val 0 + η))) ∧
      (¬IncreasesAt e ψ y → StrictAntiOn (fun s ↦ ψ (e.symm (normalRay s)))
        (Icc (max ((e y).val 0 - η) 0) ((e y).val 0 + η))) := by
  obtain ⟨η, hη, -, h⟩ :=
    exists_coord_nhds (hV.inter e.open_source) inter_subset_right ⟨hyV, hye⟩
  set t := (e y).val 0
  have ht : 0 ≤ t := (e y).property
  set I := Icc (max (t - η) 0) (t + η)
  have hI : ∀ s ∈ I, |s - t| ≤ η ∧ 0 ≤ s := fun s hs ↦
    ⟨abs_sub_le_iff.2 ⟨by linarith [hs.2], by linarith [le_max_left (t - η) 0, hs.1]⟩,
      (le_max_right _ _).trans hs.1⟩
  have hcont : ContinuousOn (fun s ↦ ψ (e.symm (normalRay s))) I :=
    hψc.comp (continuousOn_symm_normalRay fun s hs ↦ (h s (hI s hs).1).1)
      fun s hs ↦ (h s (hI s hs).1).2.1
  have hinj : InjOn (fun s ↦ ψ (e.symm (normalRay s))) I := fun s hs s' hs' hss' ↦ by
    rw [← coord_symm_normalRay (hI s hs).2 (h s (hI s hs).1).1,
      ← coord_symm_normalRay (hI s' hs').2 (h s' (hI s' hs').1).1,
      hψi (h s (hI s hs).1).2.1 (h s' (hI s' hs').1).2.1 hss']
  have htI : t ∈ I := ⟨max_le (by linarith) ht, by linarith⟩
  have hyt : e.symm (normalRay t) = y := symm_normalRay_coord hye
  have hev : ∀ᶠ s in 𝓝[>] t, s ∈ I ∧ t < s := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t < t + η)] with s hs
    exact ⟨⟨(max_le (by linarith) ht).trans hs.1.le, hs.2.le⟩, hs.1⟩
  refine ⟨η, hη, fun s hs ↦ ⟨(h s hs).1, (h s hs).2.1⟩, fun hinc ↦ ?_, fun hinc ↦ ?_⟩ <;>
    rcases hcont.strictMonoOn_of_injOn_Icc' (htI.1.trans htI.2) hinj with hm | ha
  · exact hm
  · obtain ⟨s, ⟨hsI, hts⟩, hlt⟩ := (hev.and hinc).exists
    have := ha htI hsI hts
    simp only [hyt] at this
    exact absurd hlt (lt_asymm this)
  · refine absurd ?_ hinc
    filter_upwards [hev] with s hs
    simpa only [hyt] using hm htI hs.1 hs.2
  · exact ha

/-- A function strictly monotone on `S` when `P` holds, and strictly antitone otherwise, increases
from `s` to `s' > s` in `S` exactly when `P` holds, and decreases exactly when it does not. -/
private theorem lt_iff_of_strictMonoOn_of_strictAntiOn {f : ℝ → ℝ} {S : Set ℝ} {P : Prop}
    (hmono : P → StrictMonoOn f S) (hanti : ¬P → StrictAntiOn f S) {s s' : ℝ} (hs : s ∈ S)
    (hs' : s' ∈ S) (hss' : s < s') : (f s < f s' ↔ P) ∧ (f s' < f s ↔ ¬P) := by
  by_cases hP : P
  · have := hmono hP hs hs' hss'
    exact ⟨iff_of_true this hP, iff_of_false (lt_asymm this) (not_not.2 hP)⟩
  · have := hanti hP hs hs' hss'
    exact ⟨iff_of_false (lt_asymm this) hP, iff_of_true this hP⟩

/-- **Sides of a point and the direction of a coordinate.** Let `ψ` be continuous and injective on
an open neighbourhood of a point `p` of a chart domain, and let `S` accumulate at `p`, with all its
points in the chart domain, read above `p` if `a` holds and below `p` otherwise. Then `ψ` exceeds
`ψ p` on `S` near `p` exactly when `ψ` increases along the chart at `p` if and only if `a`. -/
private theorem eventually_lt_iff_increasesAt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {p : M} (hpV : p ∈ V) (hpe : p ∈ e.source)
    {S : Set M} (hpS : p ∈ closure S) {a : Prop}
    (hS : ∀ w ∈ S, w ∈ e.source ∧
      ((e p).val 0 < (e w).val 0 ∧ a ∨ (e w).val 0 < (e p).val 0 ∧ ¬a)) :
    (∀ᶠ w in 𝓝 p, w ∈ S → ψ p < ψ w) ↔ (IncreasesAt e ψ p ↔ a) := by
  obtain ⟨η, hη, -, hmono, hanti⟩ := exists_strictMonoOn_of_increasesAt hV hψc hψi hpV hpe
  set t := (e p).val 0
  have htI : t ∈ Icc (max (t - η) 0) (t + η) := ⟨max_le (by linarith) (e p).property, by linarith⟩
  -- On `S` near `p`, comparing values of `ψ` with `ψ p` compares coordinates with that of `p`.
  have hcmp : ∀ w ∈ S, |(e w).val 0 - t| < η → (ψ p < ψ w ↔ (IncreasesAt e ψ p ↔ a)) := by
    intro w hwS hwη
    obtain ⟨hwe, hw⟩ := hS w hwS
    have hwI : (e w).val 0 ∈ Icc (max (t - η) 0) (t + η) :=
      ⟨max_le (by linarith [(abs_lt.1 hwη).1]) (e w).property, by linarith [(abs_lt.1 hwη).2]⟩
    have hp : ψ p = ψ (e.symm (normalRay t)) := by rw [symm_normalRay_coord hpe]
    have hw' : ψ w = ψ (e.symm (normalRay ((e w).val 0))) := by rw [symm_normalRay_coord hwe]
    rw [hp, hw']
    rcases hw with ⟨hlt, ha⟩ | ⟨hlt, ha⟩
    · rw [(lt_iff_of_strictMonoOn_of_strictAntiOn hmono hanti htI hwI hlt).1, iff_true_intro ha,
        iff_true]
    · rw [(lt_iff_of_strictMonoOn_of_strictAntiOn hmono hanti hwI htI hlt).2, iff_false_intro ha,
        iff_false]
  constructor
  · intro h
    by_contra hne
    obtain ⟨w, hwS, hlt, -, hwη⟩ := ((mem_closure_iff_frequently.1 hpS).and_eventually
      (h.and (coord_mem_nhds hpe hη))).exists
    exact hne ((hcmp w hwS hwη).1 (hlt hwS))
  · intro h
    filter_upwards [coord_mem_nhds hpe hη] with w hw hwS
    exact (hcmp w hwS hw.2).2 h

/-- If, in a chart, a set `S` accumulating at `p` is read above `p` and a set `T` accumulating at
`p` below `p`, then a function continuous and injective near `p` exceeds its value at `p` near
`p` on exactly one of `S` and `T`. -/
private theorem eventually_lt_iff_not_eventually_lt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {p : M} (hpV : p ∈ V) (hpe : p ∈ e.source)
    {S T : Set M} (hpS : p ∈ closure S) (hpT : p ∈ closure T)
    (hS : ∀ w ∈ S, w ∈ e.source ∧ (e p).val 0 < (e w).val 0)
    (hT : ∀ w ∈ T, w ∈ e.source ∧ (e w).val 0 < (e p).val 0) :
    (∀ᶠ w in 𝓝 p, w ∈ S → ψ p < ψ w) ↔ ¬∀ᶠ w in 𝓝 p, w ∈ T → ψ p < ψ w := by
  rw [eventually_lt_iff_increasesAt hV hψc hψi hpV hpe hpS (a := True)
      fun w hw ↦ ⟨(hS w hw).1, .inl ⟨(hS w hw).2, trivial⟩⟩,
    eventually_lt_iff_increasesAt hV hψc hψi hpV hpe hpT (a := False)
      fun w hw ↦ ⟨(hT w hw).1, .inr ⟨(hT w hw).2, not_false⟩⟩]
  simp

end Direction

section Boundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

/-- **Boundary points of a one-dimensional topological manifold are visible in every chart.** A
point of a charted space modelled on the half-line `EuclideanHalfSpace 1` is a boundary point
exactly when some (equivalently, any) partial homeomorphism to the model defined around it reads
it with vanishing coordinate. No smoothness of the atlas is needed. -/
theorem ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {y : M} (hy : y ∈ e.source) :
    y ∈ (𝓡∂ 1).boundary M ↔ (e y).val 0 = 0 := by
  have hy' := mem_chart_source (EuclideanHalfSpace 1) y
  simp only [ModelWithCorners.boundary, mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace, extChartAt_coe, comp_apply,
    eq_comm (a := (0 : ℝ))]
  rw [modelWithCornersEuclideanHalfSpace_toFun]
  exact ⟨coord_eq_zero_of_coord_eq_zero hy' hy, coord_eq_zero_of_coord_eq_zero hy hy'⟩

/-- A point of a chart domain which is not a boundary point has positive coordinate. -/
private theorem coord_pos_of_notMem_boundary {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    {y : M} (hy : y ∈ e.source) (h : y ∉ (𝓡∂ 1).boundary M) : 0 < (e y).val 0 :=
  lt_of_le_of_ne (e y).property
    (Ne.symm ((ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hy).not.1 h))

/-- A compact one-dimensional topological manifold has finitely many boundary points: each chart
domain contains at most one, the point of coordinate zero. -/
theorem ModelWithCorners.finite_boundary_euclideanHalfSpace_one [CompactSpace M] :
    ((𝓡∂ 1).boundary M).Finite := by
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (chartAt (EuclideanHalfSpace 1) x).source)
    (fun x ↦ (chartAt (EuclideanHalfSpace 1) x).open_source)
    (fun y _ ↦ mem_iUnion.2 ⟨y, mem_chart_source _ y⟩)
  refine ((S.finite_toSet.image fun x ↦ (chartAt (EuclideanHalfSpace 1) x).symm 0)).subset ?_
  intro y hy
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hS (mem_univ y))
  refine ⟨x, hx, ?_⟩
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hyx, ← eq_zero_iff] at hy
  rw [← hy]
  exact OpenPartialHomeomorph.left_inv _ hyx

end Boundary

section Arc

variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
  {α β : ℝ} {K : Set M}

/-- An *arc in a chart*: an open preconnected nonempty set `K` inside the domain of a chart `e`,
whose coordinates lie in a compact interval `[α, β]` of coordinates of `e`. -/
private structure IsArcIn (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (α β : ℝ)
    (K : Set M) : Prop where
  isOpen : IsOpen K
  isPreconnected : IsPreconnected K
  nonempty : K.Nonempty
  target : ∀ s ∈ Icc α β, normalRay s ∈ e.target
  mem : ∀ z ∈ K, z ∈ e.source ∧ (e z).val 0 ∈ Icc α β

private theorem IsArcIn.image_subset_Icc (h : IsArcIn e α β K) :
    (fun z ↦ (e z).val 0) '' K ⊆ Icc α β :=
  image_subset_iff.2 fun z hz ↦ (h.mem z hz).2

private theorem IsArcIn.isConnected_image (h : IsArcIn e α β K) :
    IsConnected ((fun z ↦ (e z).val 0) '' K) :=
  ⟨h.nonempty.image _, h.isPreconnected.image _ (continuousOn_coord.mono fun z hz ↦ (h.mem z hz).1)⟩

private theorem IsArcIn.bddBelow (h : IsArcIn e α β K) : BddBelow ((fun z ↦ (e z).val 0) '' K) :=
  ⟨α, fun _ hs ↦ (h.image_subset_Icc hs).1⟩

private theorem IsArcIn.bddAbove (h : IsArcIn e α β K) : BddAbove ((fun z ↦ (e z).val 0) '' K) :=
  ⟨β, fun _ hs ↦ (h.image_subset_Icc hs).2⟩

/-- A point of the chart domain lies in an arc exactly when its coordinate is a coordinate of the
arc. -/
private theorem IsArcIn.mem_iff (h : IsArcIn e α β K) {z : M} (hz : z ∈ e.source) :
    z ∈ K ↔ (e z).val 0 ∈ (fun z ↦ (e z).val 0) '' K :=
  ⟨mem_image_of_mem _, fun ⟨w, hw, hwz⟩ ↦ injOn_coord (h.mem w hw).1 hz hwz ▸ hw⟩

/-- An arc is the image of its coordinates under the inverse chart. -/
private theorem IsArcIn.image_symm_normalRay (h : IsArcIn e α β K) :
    (fun s ↦ e.symm (normalRay s)) '' ((fun z ↦ (e z).val 0) '' K) = K := by
  rw [image_image]
  exact (image_congr fun z hz ↦ symm_normalRay_coord (h.mem z hz).1).trans (image_id' K)

/-- The coordinates of an arc form a relatively open subset of `[0, ∞)`. -/
private theorem IsArcIn.exists_nhds (h : IsArcIn e α β K) {z : M} (hz : z ∈ K) :
    ∃ ε > 0, (0 < (e z).val 0 → ε < (e z).val 0) ∧
      ∀ s, 0 ≤ s → |s - (e z).val 0| ≤ ε → s ∈ (fun z ↦ (e z).val 0) '' K := by
  obtain ⟨ε, hε, hεz, hs⟩ := exists_coord_nhds h.isOpen (fun w hw ↦ (h.mem w hw).1) hz
  exact ⟨ε, hε, hεz, fun s hs0 hsz ↦ ⟨_, (hs s hsz).2, coord_symm_normalRay hs0 (hs s hsz).1⟩⟩

/-- The supremum of the coordinates of an arc is not attained. -/
private theorem IsArcIn.sSup_notMem (h : IsArcIn e α β K) :
    sSup ((fun z ↦ (e z).val 0) '' K) ∉ (fun z ↦ (e z).val 0) '' K := by
  rintro ⟨z, hz, hzb⟩
  obtain ⟨ε, hε, -, hs⟩ := h.exists_nhds hz
  have := le_csSup h.bddAbove (hs ((e z).val 0 + ε) (add_nonneg (e z).property hε.le)
    (by rw [add_sub_cancel_left, abs_of_pos hε]))
  linarith

/-- The infimum of the coordinates of an arc is attained only at the boundary coordinate `0`. -/
private theorem IsArcIn.sInf_eq_zero_of_mem (h : IsArcIn e α β K)
    (ha : sInf ((fun z ↦ (e z).val 0) '' K) ∈ (fun z ↦ (e z).val 0) '' K) :
    sInf ((fun z ↦ (e z).val 0) '' K) = 0 := by
  obtain ⟨z, hz, hza⟩ := ha
  obtain ⟨ε, hε, hεz, hs⟩ := h.exists_nhds hz
  rw [← hza]
  by_contra hne
  have hεz := hεz (lt_of_le_of_ne (e z).property (Ne.symm hne))
  have := csInf_le h.bddBelow (hs ((e z).val 0 - ε) (by linarith)
    (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]))
  linarith

private theorem IsArcIn.sInf_lt_sSup (h : IsArcIn e α β K) :
    sInf ((fun z ↦ (e z).val 0) '' K) < sSup ((fun z ↦ (e z).val 0) '' K) := by
  obtain ⟨z, hz⟩ := h.nonempty
  obtain ⟨ε, hε, -, hs⟩ := h.exists_nhds hz
  have h₁ := csInf_le h.bddBelow (mem_image_of_mem (fun z ↦ (e z).val 0) hz)
  have h₂ := le_csSup h.bddAbove (hs ((e z).val 0 + ε) (add_nonneg (e z).property hε.le)
    (by rw [add_sub_cancel_left, abs_of_pos hε]))
  dsimp only at h₁ h₂
  linarith

private theorem IsArcIn.closure_subset_source [T2Space M] (h : IsArcIn e α β K) :
    closure K ⊆ e.source := by
  have hA : IsCompact ((fun s ↦ e.symm (normalRay s)) '' Icc α β) :=
    isCompact_Icc.image_of_continuousOn (continuousOn_symm_normalRay h.target)
  have hKA : K ⊆ (fun s ↦ e.symm (normalRay s)) '' Icc α β := fun z hz ↦
    ⟨(e z).val 0, (h.mem z hz).2, symm_normalRay_coord (h.mem z hz).1⟩
  refine (closure_minimal hKA hA.isClosed).trans ?_
  rintro _ ⟨s, hs, rfl⟩
  exact e.map_target (h.target s hs)

/-- A point in the closure of an arc but outside it lies in the chart domain, and its coordinate
is an endpoint, not attained by the arc, of the interval of coordinates of the arc. -/
private theorem IsArcIn.coord_of_mem_closure [T2Space M] (h : IsArcIn e α β K) {z : M}
    (hz : z ∈ closure K) (hzK : z ∉ K) :
    z ∈ e.source ∧ (e z).val 0 ∉ (fun z ↦ (e z).val 0) '' K ∧
      ((e z).val 0 = sInf ((fun z ↦ (e z).val 0) '' K) ∨
        (e z).val 0 = sSup ((fun z ↦ (e z).val 0) '' K)) := by
  have hze := h.closure_subset_source hz
  have hzI : (e z).val 0 ∉ (fun z ↦ (e z).val 0) '' K := fun hI ↦ hzK ((h.mem_iff hze).2 hI)
  have hIcc := closure_minimal (subset_Icc_csInf_csSup h.bddBelow h.bddAbove) isClosed_Icc
    ((continuousOn_coord.mono h.closure_subset_source).image_closure (mem_image_of_mem _ hz))
  refine ⟨hze, hzI, ?_⟩
  by_contra hne
  rw [not_or] at hne
  exact hzI (h.isConnected_image.Ioo_csInf_csSup_subset h.bddBelow h.bddAbove
    ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hne.1), lt_of_le_of_ne hIcc.2 hne.2⟩)

/-- An endpoint of the interval of coordinates of an arc which is not attained by the arc is the
coordinate of a point in the closure of the arc but outside it. -/
private theorem IsArcIn.exists_mem_closure (h : IsArcIn e α β K) {c : ℝ}
    (hc : c = sInf ((fun z ↦ (e z).val 0) '' K) ∨ c = sSup ((fun z ↦ (e z).val 0) '' K))
    (hcI : c ∉ (fun z ↦ (e z).val 0) '' K) :
    ∃ z ∈ closure K, z ∉ K ∧ z ∈ e.source ∧ (e z).val 0 = c := by
  have hne := h.nonempty.image fun z ↦ (e z).val 0
  have hcl : c ∈ closure ((fun z ↦ (e z).val 0) '' K) := by
    rcases hc with rfl | rfl
    exacts [csInf_mem_closure hne h.bddBelow, csSup_mem_closure hne h.bddAbove]
  have hcαβ : c ∈ Icc α β := closure_minimal h.image_subset_Icc isClosed_Icc hcl
  have hIci : (fun z ↦ (e z).val 0) '' K ⊆ Ici 0 := by
    rintro _ ⟨z, -, rfl⟩
    exact (e z).property
  have hc0 : 0 ≤ c := closure_minimal hIci isClosed_Ici hcl
  have hzc := coord_symm_normalRay hc0 (h.target c hcαβ)
  refine ⟨_, ?_, fun hK ↦ hcI (hzc ▸ mem_image_of_mem _ hK), e.map_target (h.target c hcαβ), hzc⟩
  rw [← h.image_symm_normalRay]
  exact (((continuousOn_symm_normalRay h.target) c hcαβ).mono h.image_subset_Icc).mem_closure_image
    hcl

/-- A preconnected set meeting the open coordinate interval `|s - t| < δ` of a chart, and avoiding
the points of coordinate `t ± δ`, lies in that interval. -/
private theorem forall_mem_coord_lt_of_isPreconnected [T2Space M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {t δ : ℝ} (ht : 0 ≤ t)
    (htarget : ∀ s, |s - t| ≤ δ → normalRay s ∈ e.target) {K : Set M} (hK : IsPreconnected K)
    (hKδ : ∀ z ∈ K, z ∈ e.source → |(e z).val 0 - t| ≠ δ) {y : M} (hyK : y ∈ K)
    (hy : y ∈ e.source) (hyt : |(e y).val 0 - t| < δ) :
    ∀ z ∈ K, z ∈ e.source ∧ |(e z).val 0 - t| < δ := by
  set W := e.source ∩ (fun z ↦ (e z).val 0) ⁻¹' {s | |s - t| < δ}
  set A := (fun s ↦ e.symm (normalRay s)) '' Icc (t - δ) (t + δ)
  have hIcc : ∀ s ∈ Icc (t - δ) (t + δ), |s - t| ≤ δ := fun s hs ↦
    (abs_sub_comm s t).trans_le (mem_Icc_iff_abs_le.2 hs)
  have hW : IsOpen W := continuousOn_coord.isOpen_inter_preimage e.open_source
    (isOpen_lt (by fun_prop) continuous_const)
  have hA : IsClosed A := (isCompact_Icc.image_of_continuousOn
    (continuousOn_symm_normalRay fun s hs ↦ htarget s (hIcc s hs))).isClosed
  have hWA : W ⊆ A := fun z hz ↦ by
    have hzδ : |(e z).val 0 - t| < δ := hz.2
    have hzt := abs_sub_lt_iff.1 hzδ
    exact ⟨(e z).val 0, ⟨by linarith, by linarith⟩, symm_normalRay_coord hz.1⟩
  have hcover : K ⊆ W ∪ Aᶜ := by
    intro z hz
    by_cases hzA : z ∈ A
    · obtain ⟨s, hs, rfl⟩ := hzA
      have hse := htarget s (hIcc s hs)
      refine Or.inl ⟨e.map_target hse, lt_of_le_of_ne ?_ (hKδ _ hz (e.map_target hse))⟩
      rw [e.right_inv hse, normalRay_coe_apply]
      calc |max s 0 - t| = |max s 0 - max t 0| := by rw [max_eq_left ht]
        _ ≤ |s - t| := abs_max_sub_max_le_abs s t 0
        _ ≤ δ := hIcc s hs
    · exact Or.inr hzA
  exact fun z hz ↦ IsPreconnected.subset_left_of_subset_union hW hA.isOpen_compl
    (disjoint_compl_right.mono_left hWA) hcover ⟨y, hyK, hy, hyt⟩ hK hz

end Arc

section Parity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

/-- **Cutting a compact one-dimensional manifold into arcs.** There is a finite set `P` of interior
points such that every connected component of the complement of `P` lies in the domain of a single
chart, with coordinates in a compact interval of coordinates of that chart. -/
private theorem exists_cutSet [CompactSpace M] [T2Space M] :
    ∃ P : Set M, P.Finite ∧ Disjoint P ((𝓡∂ 1).boundary M) ∧
      ∀ y ∉ P, ∃ e : OpenPartialHomeomorph M (EuclideanHalfSpace 1), ∃ α β : ℝ,
        (∀ s ∈ Icc α β, normalRay s ∈ e.target) ∧
        ∀ z ∈ connectedComponentIn Pᶜ y, z ∈ e.source ∧ (e z).val 0 ∈ Icc α β := by
  set e : M → OpenPartialHomeomorph M (EuclideanHalfSpace 1) :=
    fun x ↦ chartAt (EuclideanHalfSpace 1) x
  -- Around each point `x`, a closed coordinate interval of radius `δ x` in the chart at `x`.
  have hδ : ∀ x, ∃ δ > 0, (0 < (e x x).val 0 → δ < (e x x).val 0) ∧
      ∀ s, |s - (e x x).val 0| ≤ δ → normalRay s ∈ (e x).target := fun x ↦ by
    obtain ⟨δ, hδ, hδx, h⟩ :=
      exists_coord_nhds (e x).open_source subset_rfl (mem_chart_source _ x)
    exact ⟨δ, hδ, hδx, fun s hs ↦ (h s hs).1⟩
  choose δ hδ hδx hδt using hδ
  -- Finitely many of the open coordinate intervals cover `M`; `P` is the set of their endpoints.
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (e x).source ∩ (fun y ↦ (e x y).val 0) ⁻¹' {s | |s - (e x x).val 0| < δ x})
    (fun x ↦ continuousOn_coord.isOpen_inter_preimage (e x).open_source
      (isOpen_lt (by fun_prop) continuous_const))
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source _ x, by simpa using hδ x⟩)
  set P := ⋃ x ∈ S, {y ∈ (e x).source | |(e x y).val 0 - (e x x).val 0| = δ x}
  refine ⟨P, ?_, ?_, ?_⟩
  · refine S.finite_toSet.biUnion fun x _ ↦ ((((finite_singleton ((e x x).val 0 + δ x)).insert
      ((e x x).val 0 - δ x)).image fun s ↦ (e x).symm (normalRay s)).subset ?_)
    rintro y ⟨hy, hyδ⟩
    refine ⟨(e x y).val 0, ?_, symm_normalRay_coord hy⟩
    rcases (abs_eq (hδ x).le).1 hyδ with h | h
    · exact Or.inr (by rw [mem_singleton_iff]; linarith)
    · exact Or.inl (by linarith)
  · refine disjoint_left.2 fun y hy hyB ↦ ?_
    obtain ⟨x, -, hy, hyδ⟩ := mem_iUnion₂.1 hy
    rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hy] at hyB
    rw [hyB, zero_sub, abs_neg, abs_of_nonneg (e x x).property] at hyδ
    exact (hδx x (hyδ ▸ hδ x)).ne hyδ.symm
  · intro y hyP
    obtain ⟨x, hxS, hy, hyδ⟩ := mem_iUnion₂.1 (hS (mem_univ y))
    have hball := forall_mem_coord_lt_of_isPreconnected (K := connectedComponentIn Pᶜ y)
      (e x x).property (hδt x) isPreconnected_connectedComponentIn (fun z hz hze hzδ ↦
        absurd (mem_iUnion₂.2 ⟨x, hxS, hze, hzδ⟩ : z ∈ P) (connectedComponentIn_subset _ _ hz))
      (mem_connectedComponentIn hyP) hy hyδ
    refine ⟨e x, (e x x).val 0 - δ x, (e x x).val 0 + δ x, fun s hs ↦ hδt x s
      ((abs_sub_comm _ _).trans_le (mem_Icc_iff_abs_le.2 hs)), fun z hz ↦ ⟨(hball z hz).1, ?_⟩⟩
    have := abs_sub_lt_iff.1 (hball z hz).2
    exact ⟨by linarith, by linarith⟩

/-- The two sides of a point `p` relative to a set `P`: preconnected sets `J true` and `J false`
avoiding `P`, accumulating at `p`, containing chosen points `q true` and `q false`, and together
exhausting a punctured open neighbourhood `N \ {p}` of `p`. A function continuous and injective
near `p` exceeds its value at `p` near `p` on exactly one of the two sides. -/
private structure IsSides (P : Set M) (p : M) (J : Bool → Set M) (N : Set M) (q : Bool → M) :
    Prop where
  isPreconnected (b : Bool) : IsPreconnected (J b)
  mem (b : Bool) : q b ∈ J b
  disjoint (b : Bool) : Disjoint (J b) P
  mem_closure (b : Bool) : p ∈ closure (J b)
  disjoint_true_false : Disjoint (J true) (J false)
  isOpen : IsOpen N
  mem_nhds : p ∈ N
  diff_subset : N \ {p} ⊆ J true ∪ J false
  opposite (ψ : M → ℝ) (V : Set M) : IsOpen V → p ∈ V → ContinuousOn ψ V → InjOn ψ V →
    ((∀ᶠ w in 𝓝 p, w ∈ J true → ψ p < ψ w) ↔ ¬∀ᶠ w in 𝓝 p, w ∈ J false → ψ p < ψ w)

/-- The two half-intervals `(t, t + η]` and `[t - η, t)` lie in `[t - η, t + η]`, miss `t`, and
have `t` in their closure. -/
private theorem cond_Ioc_Ico_facts {t η : ℝ} (hη : 0 < η) (b : Bool) :
    cond b (Ioc t (t + η)) (Ico (t - η) t) ⊆ Icc (t - η) (t + η) ∧
      t ∉ cond b (Ioc t (t + η)) (Ico (t - η) t) ∧
      t ∈ closure (cond b (Ioc t (t + η)) (Ico (t - η) t)) := by
  cases b
  · exact ⟨Ico_subset_Icc_self.trans (Icc_subset_Icc_right (by linarith)), fun h ↦ h.2.false,
      by simp [closure_Ico (by linarith : t - η ≠ t), hη.le]⟩
  · exact ⟨Ioc_subset_Icc_self.trans (Icc_subset_Icc_left (by linarith)), fun h ↦ h.1.false,
      by simp [closure_Ioc (by linarith : t ≠ t + η), hη.le]⟩

/-- An interior point has two sides relative to any finite set: the two half-intervals around it
in a chart. -/
private theorem exists_isSides [T1Space M] {P : Set M} (hP : P.Finite) {p : M}
    (hp : p ∉ (𝓡∂ 1).boundary M) : ∃ J N q, IsSides P p J N q := by
  -- In the chart at `p`, with `t > 0` the coordinate of `p`, the sides are the images of
  -- `(t, t + η]` and `[t - η, t)` for a radius `η` small enough to avoid `P \ {p}` and `0`.
  set e := chartAt (EuclideanHalfSpace 1) p
  have hpe : p ∈ e.source := mem_chart_source _ p
  set t := (e p).val 0
  have ht : 0 < t := coord_pos_of_notMem_boundary hpe hp
  obtain ⟨η, hη, hηt, hηV⟩ := exists_coord_nhds
    (e.open_source.inter (hP.subset sdiff_subset).isClosed.isOpen_compl) inter_subset_left
    ⟨hpe, fun h ↦ h.2 (mem_singleton p)⟩
  replace hηt := hηt ht
  -- On `[t - η, t + η]` the inverse chart is defined and meets `P` only at `p`.
  have hγ : ∀ s ∈ Icc (t - η) (t + η), normalRay s ∈ e.target ∧
      (e (e.symm (normalRay s))).val 0 = s ∧ (e.symm (normalRay s) ∈ P → s = t) := by
    intro s hs
    obtain ⟨hst, hsV⟩ := hηV s ((abs_sub_comm _ _).trans_le (mem_Icc_iff_abs_le.2 hs))
    have hcoord := coord_symm_normalRay (by linarith [hs.1]) hst
    refine ⟨hst, hcoord, fun hsP ↦ ?_⟩
    by_contra hne
    exact hsV.2 ⟨hsP, fun hsp ↦ hne (by rw [← hcoord, mem_singleton_iff.1 hsp])⟩
  have hcont := continuousOn_symm_normalRay fun s hs ↦ (hγ s hs).1
  set D : Bool → Set ℝ := fun b ↦ cond b (Ioc t (t + η)) (Ico (t - η) t)
  have hD : ∀ b, D b ⊆ Icc (t - η) (t + η) ∧ t ∉ D b ∧ t ∈ closure (D b) :=
    cond_Ioc_Ico_facts hη
  have hcl (b : Bool) : p ∈ closure ((fun s ↦ e.symm (normalRay s)) '' D b) := by
    have hpt : e.symm (normalRay t) = p := symm_normalRay_coord hpe
    rw [← hpt]
    exact ((hcont t ⟨by linarith, by linarith⟩).mono (hD b).1).mem_closure_image (hD b).2.2
  have hside (b : Bool) : ∀ w ∈ (fun s ↦ e.symm (normalRay s)) '' D b,
      w ∈ e.source ∧ (e w).val 0 ∈ D b := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨e.map_target (hγ s ((hD b).1 hs)).1, ?_⟩
    rwa [(hγ s ((hD b).1 hs)).2.1]
  refine ⟨fun b ↦ (fun s ↦ e.symm (normalRay s)) '' D b,
    e.source ∩ (fun y ↦ (e y).val 0) ⁻¹' Ioo (t - η) (t + η),
    fun b ↦ e.symm (normalRay (cond b (t + η) (t - η))), ⟨fun b ↦ ?_, fun b ↦ ?_, fun b ↦ ?_,
    hcl, ?_, ?_, ⟨hpe, by simpa [t] using hη⟩, ?_, ?_⟩⟩
  · exact (by cases b <;> [exact isPreconnected_Ico; exact isPreconnected_Ioc] :
      IsPreconnected (D b)).image _ (hcont.mono (hD b).1)
  · refine mem_image_of_mem _ ?_
    cases b <;> simp [D, hη]
  · refine disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact (hD b).2.1 ((hγ s ((hD b).1 hs)).2.2 hsP ▸ hs)
  · refine disjoint_left.2 fun w hw hw' ↦ ?_
    have h₁ := (hside true w hw).2
    have h₂ := (hside false w hw').2
    simp only [D, Bool.cond_true, Bool.cond_false, mem_Ioc, mem_Ico] at h₁ h₂
    linarith
  · exact continuousOn_coord.isOpen_inter_preimage e.open_source isOpen_Ioo
  · rintro z ⟨⟨hze, hzI⟩, hzp⟩
    have hzs : e.symm (normalRay ((e z).val 0)) = z := symm_normalRay_coord hze
    have hst : (e z).val 0 ≠ t := fun h ↦
      hzp (by rw [mem_singleton_iff, ← hzs, h, symm_normalRay_coord hpe])
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inr ⟨_, ⟨hzI.1.le, h⟩, hzs⟩
    · exact Or.inl ⟨_, ⟨h, hzI.2.le⟩, hzs⟩
  · -- The side `true` is read above `p` and the side `false` below it.
    exact fun ψ V hV hpV hψc hψi ↦ eventually_lt_iff_not_eventually_lt hV hψc hψi hpV hpe
      (hcl true) (hcl false) (fun w hw ↦ ⟨(hside true w hw).1, (hside true w hw).2.1⟩)
      fun w hw ↦ ⟨(hside false w hw).1, (hside false w hw).2.2⟩

/-- The data of the counting argument: a cut set `P` whose complementary components are arcs in
charts, and two sides `J p true`, `J p false` of every point `p ∈ P`. -/
private structure CutData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] where
  P : Set M
  J : M → Bool → Set M
  N : M → Set M
  q : M → Bool → M
  finite : P.Finite
  disjoint : Disjoint P ((𝓡∂ 1).boundary M)
  arc : ∀ y ∉ P, ∃ (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (α β : ℝ),
    IsArcIn e α β (connectedComponentIn Pᶜ y)
  sides : ∀ p ∈ P, IsSides P p (J p) (N p) (q p)

private theorem nonempty_cutData [CompactSpace M] [T2Space M] : Nonempty (CutData M) := by
  obtain ⟨P, hP, hPB, hParc⟩ := exists_cutSet (M := M)
  have hsides : ∀ p, ∃ J N q, p ∈ P → IsSides P p J N q := fun p ↦ by
    by_cases hp : p ∈ P
    · obtain ⟨J, N, q, h⟩ := exists_isSides hP (disjoint_left.1 hPB hp)
      exact ⟨J, N, q, fun _ ↦ h⟩
    · exact ⟨fun _ ↦ ∅, ∅, fun _ ↦ p, fun h ↦ absurd h hp⟩
  choose J N q hJ using hsides
  have := ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 1) M
  refine ⟨⟨P, J, N, q, hP, hPB, fun y hy ↦ ?_, hJ⟩⟩
  obtain ⟨e, α, β, htarget, hmem⟩ := hParc y hy
  exact ⟨e, α, β, ⟨hP.isClosed.isOpen_compl.connectedComponentIn,
    isPreconnected_connectedComponentIn, ⟨y, mem_connectedComponentIn hy⟩, htarget, hmem⟩⟩

/-- The point from which an element of `P × Bool ⊕ ∂M` starts: the chosen point on a side of a
point of `P`, or a boundary point itself. -/
private def CutData.base (D : CutData M) : M × Bool ⊕ M → M := Sum.elim (fun pb ↦ D.q pb.1 pb.2) id

/-- The arc of an element of `P × Bool ⊕ ∂M`: the component of the complement of `P` containing
its base point. -/
private def CutData.arcOf (D : CutData M) (ω : M × Bool ⊕ M) : Set M :=
  connectedComponentIn D.Pᶜ (D.base ω)

/-- The side of a point of `P` lies in the arc of its chosen point. -/
private theorem CutData.J_subset_arcOf (D : CutData M) {p : M} (hp : p ∈ D.P) (c : Bool) :
    D.J p c ⊆ D.arcOf (.inl (p, c)) :=
  ((D.sides p hp).isPreconnected c).subset_connectedComponentIn ((D.sides p hp).mem c)
    (subset_compl_iff_disjoint_right.2 ((D.sides p hp).disjoint c))

/-- A component of the complement of `P` meeting a side of `p` is the arc of that side. -/
private theorem CutData.arcOf_inl_eq (D : CutData M) {p : M} (hp : p ∈ D.P) {c : Bool}
    {y w : M} (hw : w ∈ D.J p c) (hwy : w ∈ connectedComponentIn D.Pᶜ y) :
    D.arcOf (.inl (p, c)) = connectedComponentIn D.Pᶜ y := by
  rw [connectedComponentIn_eq hwy]
  exact connectedComponentIn_eq (D.J_subset_arcOf hp c hw)

/-- No arc contains both sides of a point of `P`. -/
private theorem CutData.not_subset_and_subset [T2Space M] (D : CutData M) {p : M} (hp : p ∈ D.P)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ} {K : Set M}
    (h : IsArcIn e α β K) (hpK : p ∉ K) (htrue : D.J p true ⊆ K) (hfalse : D.J p false ⊆ K) :
    False := by
  have hs := D.sides p hp
  obtain ⟨hpe, -, hpab⟩ := h.coord_of_mem_closure (closure_mono htrue (hs.mem_closure true)) hpK
  have hp0 : 0 < (e p).val 0 := coord_pos_of_notMem_boundary hpe (disjoint_left.1 D.disjoint hp)
  obtain ⟨ε, hε, hεp, hεN⟩ :=
    exists_coord_nhds (hs.isOpen.inter e.open_source) inter_subset_right ⟨hs.mem_nhds, hpe⟩
  replace hεp := hεp hp0
  -- The points of coordinates `(e p) ∓ ε` lie in `N \ {p}`, hence on a side, hence in `K`.
  have hK : ∀ s, |s - (e p).val 0| ≤ ε → s ≠ (e p).val 0 → s ∈ (fun z ↦ (e z).val 0) '' K := by
    intro s hs₁ hs₂
    obtain ⟨hst, hsN⟩ := hεN s hs₁
    have hcoord := coord_symm_normalRay (by linarith [(abs_sub_le_iff.1 hs₁).2]) hst
    refine ⟨_, ?_, hcoord⟩
    rcases hs.diff_subset ⟨hsN.1, fun hsp ↦ hs₂ (by rw [← hcoord, mem_singleton_iff.1 hsp])⟩
      with h' | h'
    exacts [htrue h', hfalse h']
  have h₁ := csInf_le h.bddBelow (hK ((e p).val 0 - ε)
    (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]) (by linarith))
  have h₂ := le_csSup h.bddAbove (hK ((e p).val 0 + ε)
    (by rw [add_sub_cancel_left, abs_of_pos hε]) (by linarith))
  rcases hpab with hpa | hpb <;> linarith

/-- A boundary point in an arc has coordinate `0`, which is then the attained infimum of the
coordinates of the arc. -/
private theorem IsArcIn.coord_eq_sInf_of_mem_boundary
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ} {K : Set M}
    (h : IsArcIn e α β K) {y : M} (hyK : y ∈ K) (hyB : y ∈ (𝓡∂ 1).boundary M) :
    (e y).val 0 ∈ (fun z ↦ (e z).val 0) '' K ∧ (e y).val 0 = sInf ((fun z ↦ (e z).val 0) '' K) := by
  have hyI : (e y).val 0 ∈ (fun z ↦ (e z).val 0) '' K := mem_image_of_mem _ hyK
  refine ⟨hyI, le_antisymm ?_ (csInf_le h.bddBelow hyI)⟩
  rw [(ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (h.mem y hyK).1).1 hyB]
  exact le_csInf (h.nonempty.image _) (by rintro _ ⟨z, -, rfl⟩; exact (e z).property)

/-- Each endpoint of the interval of coordinates of a component `K` of the complement of `P` is
the coordinate of a boundary point in `K`, or of a point of `P` one of whose sides has arc `K`. -/
private theorem CutData.exists_of_endpoint [T2Space M] (D : CutData M) {y : M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ}
    (h : IsArcIn e α β (connectedComponentIn D.Pᶜ y)) {c : ℝ}
    (hc : c = sInf ((fun z ↦ (e z).val 0) '' connectedComponentIn D.Pᶜ y) ∨
      c = sSup ((fun z ↦ (e z).val 0) '' connectedComponentIn D.Pᶜ y)) :
    (∃ z ∈ connectedComponentIn D.Pᶜ y, z ∈ (𝓡∂ 1).boundary M ∧ (e z).val 0 = c) ∨
      ∃ p ∈ D.P, ∃ b, D.arcOf (.inl (p, b)) = connectedComponentIn D.Pᶜ y ∧ (e p).val 0 = c := by
  by_cases hcI : c ∈ (fun z ↦ (e z).val 0) '' connectedComponentIn D.Pᶜ y
  · -- An attained endpoint is the infimum `0`, the coordinate of a boundary point.
    have hca := hc.resolve_right fun hcb ↦ h.sSup_notMem (hcb ▸ hcI)
    have hc0 : c = 0 := hca.trans (h.sInf_eq_zero_of_mem (hca ▸ hcI))
    obtain ⟨z, hzK, hzc⟩ := hcI
    exact Or.inl ⟨z, hzK, (ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff
      (h.mem z hzK).1).2 (hzc.trans hc0), hzc⟩
  · -- An unattained endpoint is the coordinate of a point of `P`, a side of which meets the arc.
    obtain ⟨z, hzcl, hzK, -, hzc⟩ := h.exists_mem_closure hc hcI
    have := ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 1) M
    have hzP : z ∈ D.P := by
      simpa using frontier_connectedComponentIn_subset_compl D.finite.isClosed.isOpen_compl _
        ⟨hzcl, by rwa [h.isOpen.interior_eq]⟩
    have hs := D.sides z hzP
    obtain ⟨w, hwN, hwK⟩ := mem_closure_iff.1 hzcl _ hs.isOpen hs.mem_nhds
    obtain ⟨b, hb⟩ : ∃ b, w ∈ D.J z b :=
      (hs.diff_subset ⟨hwN, fun hwz ↦ hzK (mem_singleton_iff.1 hwz ▸ hwK)⟩).elim
        (fun h' ↦ ⟨true, h'⟩) fun h' ↦ ⟨false, h'⟩
    exact Or.inr ⟨z, hzP, b, D.arcOf_inl_eq hzP hb hwK, hzc⟩

/-- The base point of an element of `P × Bool ⊕ ∂M` lies outside `P`. -/
private theorem CutData.base_notMem (D : CutData M) {B : Finset M}
    (hB : ∀ y ∈ B, y ∈ (𝓡∂ 1).boundary M) {ω : M × Bool ⊕ M}
    (hω : ω ∈ (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum B) : D.base ω ∉ D.P := by
  rcases Finset.mem_disjSum.1 hω with ⟨⟨p, c⟩, hpc, rfl⟩ | ⟨y, hy, rfl⟩
  · have hp : p ∈ D.P := by simpa using (Finset.mem_product.1 hpc).1
    exact disjoint_left.1 ((D.sides p hp).disjoint c) ((D.sides p hp).mem c)
  · exact disjoint_right.1 D.disjoint (hB y hy)

/-- A side, in an arc `K`, of a point `p` of `P` lies in `K`, and the coordinate of `p` is an
endpoint, not attained by `K`, of the interval of coordinates of `K`. -/
private theorem CutData.inl_end [T2Space M] (D : CutData M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ} {K : Set M}
    (h : IsArcIn e α β K) (hKP : Disjoint K D.P) {p : M} (hp : p ∈ D.P) {c : Bool}
    (hK : D.arcOf (.inl (p, c)) = K) :
    D.J p c ⊆ K ∧ p ∈ e.source ∧ (e p).val 0 ∉ (fun z ↦ (e z).val 0) '' K ∧
      ((e p).val 0 = sInf ((fun z ↦ (e z).val 0) '' K) ∨
        (e p).val 0 = sSup ((fun z ↦ (e z).val 0) '' K)) := by
  have hJ : D.J p c ⊆ K := by rw [← hK]; exact D.J_subset_arcOf hp c
  exact ⟨hJ, h.coord_of_mem_closure (closure_mono hJ ((D.sides p hp).mem_closure c))
    (disjoint_right.1 hKP hp)⟩

/-- A boundary point whose arc is `K` lies in `K`, and its coordinate `0` is the attained infimum
of the coordinates of `K`. -/
private theorem CutData.inr_end (D : CutData M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ} {K : Set M}
    (h : IsArcIn e α β K) {y : M} (hy : y ∈ (𝓡∂ 1).boundary M) (hK : D.arcOf (.inr y) = K) :
    y ∈ K ∧ (e y).val 0 ∈ (fun z ↦ (e z).val 0) '' K ∧
      (e y).val 0 = sInf ((fun z ↦ (e z).val 0) '' K) := by
  have hyK : y ∈ K := by rw [← hK]; exact mem_connectedComponentIn (disjoint_right.1 D.disjoint hy)
  exact ⟨hyK, h.coord_eq_sInf_of_mem_boundary hyK hy⟩

/-- **The ends of an arc.** Among the sides of the points of `P` and the boundary points, read the
ones lying in a given component of the complement of `P` by the coordinate of their point. This is
injective, with image the two endpoints of the interval of coordinates of the arc. -/
private theorem CutData.injOn_image_ends [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ}
    (h : IsArcIn e α β (D.arcOf ω₀)) :
    InjOn (fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0)
        (↑(((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
          (fun ω ↦ D.arcOf ω = D.arcOf ω₀)) : Set (M × Bool ⊕ M)) ∧
      (((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
          (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).image (fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0) =
        {sInf ((fun z ↦ (e z).val 0) '' D.arcOf ω₀), sSup ((fun z ↦ (e z).val 0) '' D.arcOf ω₀)}
            := by
  classical
  set Ω := (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset
  set K := D.arcOf ω₀
  set v : M × Bool ⊕ M → ℝ := fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0
  have hKP : Disjoint K D.P :=
    subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)
  have hP : ∀ p c, (.inl (p, c) : M × Bool ⊕ M) ∈ Ω → p ∈ D.P := fun p c hω ↦ by
    simpa [Ω] using hω
  have hB' : ∀ y, (.inr y : M × Bool ⊕ M) ∈ Ω → y ∈ (𝓡∂ 1).boundary M := fun y hω ↦ by
    simpa [Ω] using hω
  have hinj : Set.InjOn v (Ω.filter fun ω ↦ D.arcOf ω = K) := by
    rintro (⟨p, c⟩ | y) hω (⟨p', c'⟩ | y') hω' hvv <;>
      rw [Finset.coe_filter, mem_ofPred_eq] at hω hω' <;>
      simp only [v, Sum.elim_inl, Sum.elim_inr, id_eq] at hvv
    · obtain ⟨hJ, hpe, -, -⟩ := D.inl_end h hKP (hP p c hω.1) hω.2
      obtain ⟨hJ', hpe', -, -⟩ := D.inl_end h hKP (hP p' c' hω'.1) hω'.2
      obtain rfl : p = p' := injOn_coord hpe hpe' hvv
      have hpK := disjoint_right.1 hKP (hP p c hω.1)
      cases c <;> cases c'
      exacts [rfl, (D.not_subset_and_subset (hP p _ hω.1) h hpK hJ' hJ).elim,
        (D.not_subset_and_subset (hP p _ hω.1) h hpK hJ hJ').elim, rfl]
    · exact ((D.inl_end h hKP (hP p c hω.1) hω.2).2.2.1
        (hvv ▸ (D.inr_end h (hB' y' hω'.1) hω'.2).2.1)).elim
    · exact ((D.inl_end h hKP (hP p' c' hω'.1) hω'.2).2.2.1
        (hvv ▸ (D.inr_end h (hB' y hω.1) hω.2).2.1)).elim
    · rw [injOn_coord (h.mem y (D.inr_end h (hB' y hω.1) hω.2).1).1
        (h.mem y' (D.inr_end h (hB' y' hω'.1) hω'.2).1).1 hvv]
  refine ⟨hinj, ?_⟩
  ext c
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨(⟨p, c'⟩ | y), hω, rfl⟩ <;> rw [Finset.mem_filter] at hω
    · exact (D.inl_end h hKP (hP p c' hω.1) hω.2).2.2.2
    · exact Or.inl (D.inr_end h (hB' y hω.1) hω.2).2.2
  · intro hc
    rcases D.exists_of_endpoint h hc with ⟨z, hzK, hzB, hzc⟩ | ⟨p, hp, b, hpb, hpc⟩
    · exact ⟨.inr z, Finset.mem_filter.2 ⟨Finset.inr_mem_disjSum.2 (hB.mem_toFinset.2 hzB),
        (connectedComponentIn_eq hzK).symm⟩, hzc⟩
    · exact ⟨.inl (p, b), Finset.mem_filter.2 ⟨Finset.inl_mem_disjSum.2
        (Finset.mem_product.2 ⟨D.finite.mem_toFinset.2 hp, Finset.mem_univ _⟩), hpb⟩, hpc⟩

/-- **Every arc has exactly two ends.** Among the sides of the points of `P` and the boundary
points, exactly two lie in any given component of the complement of `P`: the coordinate of the
point of `P` or of the boundary point is a bijection onto the two endpoints of the interval of
coordinates of the arc. -/
private theorem CutData.card_filter_arcOf_eq_two [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M}
    (hω₀ : ω₀ ∈ (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset) :
    (((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
      (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).card = 2 := by
  obtain ⟨e, α, β, h⟩ := D.arc _ (D.base_notMem (fun y hy ↦ hB.mem_toFinset.1 hy) hω₀)
  obtain ⟨hinj, himage⟩ := D.injOn_image_ends hB h
  rw [← Finset.card_image_of_injOn hinj, himage]
  exact Finset.card_pair h.sInf_lt_sSup.ne

end Parity

section Orientation

/-- **Orientations of a one-dimensional space by local coordinates.** The functions `φ x : X → ℝ`,
each continuous and injective on an open neighbourhood `U x` of `x`, *orient* `X` when any two of
them induce the same order near every point at which both are defined: near a point `z` of
`U x ∩ U y`, a point `w` lies above `z` for `φ x` exactly when it lies above `z` for `φ y`. On a
one-dimensional manifold this is an orientation, for which the local coordinates `φ x` are
positively oriented. It needs no smooth structure, so it applies to spaces such as compactified
spaces of trajectories, which are described by local homeomorphisms only. Local orientations
through local homology are `TauCeti.IsLocalOrientation`; the description by coordinates used here
is specific to dimension one. -/
structure IsOrientingCoordinates {X : Type*} [TopologicalSpace X] (U : X → Set X)
    (φ : X → X → ℝ) : Prop where
  /-- The domain of each coordinate is open. -/
  isOpen (x : X) : IsOpen (U x)
  /-- The domain of the coordinate at `x` contains `x`. -/
  mem (x : X) : x ∈ U x
  /-- Each coordinate is continuous on its domain. -/
  continuousOn (x : X) : ContinuousOn (φ x) (U x)
  /-- Each coordinate is injective on its domain. -/
  injOn (x : X) : InjOn (φ x) (U x)
  /-- Any two coordinates induce the same order near each point of their common domain. -/
  coherent (x y : X) : ∀ z ∈ U x ∩ U y, ∀ᶠ w in 𝓝 z, (φ x z < φ x w ↔ φ y z < φ y w)

variable {M : Type*} [TopologicalSpace M] {U : M → Set M} {φ : M → M → ℝ}
  {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- Two orienting coordinates defined at a point `z` of a chart domain increase along the chart at
`z` together. -/
private theorem IsOrientingCoordinates.increasesAt_iff_increasesAt
    (hφ : IsOrientingCoordinates U φ) {x y z : M} (hz : z ∈ U x ∩ U y) (hze : z ∈ e.source) :
    IncreasesAt e (φ x) z ↔ IncreasesAt e (φ y) z :=
  Filter.eventually_congr ((tendsto_symm_normalRay hze).eventually (hφ.coherent x y z hz))

/-- Along a chart, whether the orienting coordinate `φ z` increases at `z` is locally constant in
the coordinate of `z`. -/
private theorem IsOrientingCoordinates.exists_increasesAt_iff (hφ : IsOrientingCoordinates U φ)
    {y : M} (hye : y ∈ e.source) :
    ∃ η > 0, ∀ z ∈ e.source, |(e z).val 0 - (e y).val 0| < η →
      (IncreasesAt e (φ z) z ↔ IncreasesAt e (φ y) y) := by
  obtain ⟨η, hη, hball, hmono, hanti⟩ := exists_strictMonoOn_of_increasesAt (hφ.isOpen y)
    (hφ.continuousOn y) (hφ.injOn y) (hφ.mem y) hye
  refine ⟨η, hη, fun z hze hzy ↦ ?_⟩
  set t := (e y).val 0
  set t' := (e z).val 0
  have hzt : e.symm (normalRay t') = z := symm_normalRay_coord hze
  have hzU : z ∈ U y := hzt ▸ (hball t' hzy.le).2
  obtain ⟨η', hη', -, hmono', hanti'⟩ := exists_strictMonoOn_of_increasesAt (hφ.isOpen z)
    (hφ.continuousOn z) (hφ.injOn z) (hφ.mem z) hze
  set δ := min η' (η - |t' - t|)
  have hδ : 0 < δ := lt_min hη' (by linarith)
  -- A coordinate `s` just above `t'` at which the coordinates `φ y` and `φ z` are compared.
  obtain ⟨s, ⟨hts, hsδ⟩, hcoh⟩ :=
    ((show ∀ᶠ s in 𝓝[>] t', s ∈ Ioo t' (t' + δ) from Ioo_mem_nhdsGT (by linarith)).and
      ((tendsto_symm_normalRay hze).eventually (hφ.coherent y z z ⟨hzU, hφ.mem z⟩))).exists
  have hδη' := min_le_left η' (η - |t' - t|)
  have hδη := min_le_right η' (η - |t' - t|)
  have ht' : 0 ≤ t' := (e z).property
  have hI : ∀ r, t' ≤ r → r ≤ s → r ∈ Icc (max (t - η) 0) (t + η) := fun r h₁ h₂ ↦
    ⟨max_le (by linarith [neg_abs_le (t' - t)]) (by linarith),
      by linarith [le_abs_self (t' - t)]⟩
  have hI' : ∀ r, t' ≤ r → r ≤ s → r ∈ Icc (max (t' - η') 0) (t' + η') := fun r h₁ h₂ ↦
    ⟨max_le (by linarith) (by linarith), by linarith⟩
  have h₁ := (lt_iff_of_strictMonoOn_of_strictAntiOn hmono hanti (hI t' le_rfl hts.le)
    (hI s hts.le le_rfl) hts).1
  have h₂ := (lt_iff_of_strictMonoOn_of_strictAntiOn hmono' hanti' (hI' t' le_rfl hts.le)
    (hI' s hts.le le_rfl) hts).1
  simp only [hzt] at h₁ h₂
  exact h₂.symm.trans (hcoh.symm.trans h₁)

/-- Along a chart, whether the orienting coordinate `φ z` increases at `z` is the same at all
points `z` of a preconnected subset of the chart domain. -/
private theorem IsOrientingCoordinates.increasesAt_iff_of_isPreconnected
    (hφ : IsOrientingCoordinates U φ) {K : Set M} (hK : IsPreconnected K) (hKe : K ⊆ e.source)
    {z z' : M} (hz : z ∈ K) (hz' : z' ∈ K) :
    IncreasesAt e (φ z) z ↔ IncreasesAt e (φ z') z' := by
  classical
  have hcont : ContinuousOn (fun w ↦ decide (IncreasesAt e (φ w) w)) K := fun w hw ↦ by
    obtain ⟨η, hη, h⟩ := hφ.exists_increasesAt_iff (hKe hw)
    refine ((continuousAt_const : ContinuousAt (fun _ ↦ decide (IncreasesAt e (φ w) w)) w).congr
      ?_).continuousWithinAt
    filter_upwards [coord_mem_nhds (hKe hw) hη] with v hv
    simp only [h v hv.1 hv.2]
  simpa using hK.constant hcont hz hz'

/-- At a point of coordinate `0`, a function continuous and injective nearby has a local minimum
exactly when it increases along the chart, and a local maximum exactly when it does not. -/
private theorem isLocalMin_iff_increasesAt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {y : M} (hyV : y ∈ V) (hye : y ∈ e.source)
    (hy0 : (e y).val 0 = 0) :
    (IsLocalMin ψ y ↔ IncreasesAt e ψ y) ∧ (IsLocalMax ψ y ↔ ¬IncreasesAt e ψ y) := by
  obtain ⟨η, hη, -, hmono, hanti⟩ := exists_strictMonoOn_of_increasesAt hV hψc hψi hyV hye
  simp only [hy0, zero_sub, zero_add, max_eq_right (neg_nonpos.2 hη.le)] at hmono hanti
  have h0 : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, hη.le⟩
  have hy : ψ y = ψ (e.symm (normalRay 0)) := by rw [← hy0, symm_normalRay_coord hye]
  -- Near `y`, every point is read at a coordinate in `[0, η]`.
  have hW : ∀ᶠ w in 𝓝 y, (e w).val 0 ∈ Icc 0 η ∧ ψ w = ψ (e.symm (normalRay ((e w).val 0))) := by
    filter_upwards [coord_mem_nhds hye hη] with w hw
    have hwη : |(e w).val 0 - (e y).val 0| < η := hw.2
    rw [hy0, sub_zero, abs_of_nonneg (e w).property] at hwη
    exact ⟨⟨(e w).property, hwη.le⟩, by rw [symm_normalRay_coord hw.1]⟩
  -- Just above the coordinate `0`, the normal ray stays near `y` and in `(0, η]`.
  have hR : ∀ᶠ s in 𝓝[>] (e y).val 0, s ∈ Icc 0 η ∧ 0 < s := by
    rw [hy0]
    filter_upwards [Ioo_mem_nhdsGT hη] with s hs
    exact ⟨⟨hs.1.le, hs.2.le⟩, hs.1⟩
  have hγ := tendsto_symm_normalRay hye
  by_cases hinc : IncreasesAt e ψ y
  · have hmin : IsLocalMin ψ y := by
      filter_upwards [hW] with w hw
      rw [hy, hw.2]
      exact ((hmono hinc).le_iff_le h0 hw.1).2 hw.1.1
    refine ⟨iff_of_true hmin hinc, iff_of_false (fun hmax ↦ ?_) (not_not.2 hinc)⟩
    obtain ⟨s, hs, hle⟩ := (hinc.and (hγ.eventually hmax)).exists
    exact (lt_irrefl _) (hs.trans_le hle)
  · have hmax : IsLocalMax ψ y := by
      filter_upwards [hW] with w hw
      rw [hy, hw.2]
      exact ((hanti hinc).le_iff_ge hw.1 h0).2 hw.1.1
    refine ⟨iff_of_false (fun hmin ↦ ?_) hinc, iff_of_true hmax hinc⟩
    obtain ⟨s, ⟨hsI, hs⟩, hle⟩ := (hR.and (hγ.eventually hmin)).exists
    have : ψ (e.symm (normalRay s)) < ψ (e.symm (normalRay 0)) := hanti hinc h0 hsI hs
    rw [← hy] at this
    exact (lt_irrefl _) (this.trans_le hle)

end Orientation

section OrientedParity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  {U : M → Set M} {φ : M → M → ℝ}

/-- An end of an arc is a *tail* when the orientation leaves its point into the arc: for a side
`J p c` of a point `p` of `P`, when `φ p` exceeds its value at `p` on that side near `p`; for a
boundary point `y`, when `y` is a local minimum of `φ y`. -/
private def CutData.IsTail (D : CutData M) (φ : M → M → ℝ) : M × Bool ⊕ M → Prop
  | .inl (p, c) => ∀ᶠ w in 𝓝 p, w ∈ D.J p c → φ p p < φ p w
  | .inr y => IsLocalMin (φ y) y

/-- **Tails of an arc.** Let `z₀` be a point of an arc `K`, read in the chart `e`. An end of `K` is
a tail exactly when the orientation increases along `e` at `z₀` if and only if the end lies at the
lower end of the interval of coordinates of `K`. -/
private theorem CutData.isTail_iff [T2Space M] (D : CutData M) (hB : ((𝓡∂ 1).boundary M).Finite)
    (hφ : IsOrientingCoordinates U φ) {ω₀ : M × Bool ⊕ M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ}
    (h : IsArcIn e α β (D.arcOf ω₀)) {z₀ : M} (hz₀ : z₀ ∈ D.arcOf ω₀) {ω : M × Bool ⊕ M}
    (hω : ω ∈ ((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
      (fun ω ↦ D.arcOf ω = D.arcOf ω₀)) :
    D.IsTail φ ω ↔ (IncreasesAt e (φ z₀) z₀ ↔
      (e (Sum.elim Prod.fst id ω)).val 0 = sInf ((fun z ↦ (e z).val 0) '' D.arcOf ω₀)) := by
  set K := D.arcOf ω₀
  set I := (fun z ↦ (e z).val 0) '' K with hI
  have hKe : K ⊆ e.source := fun z hz ↦ (h.mem z hz).1
  rcases ω with ⟨p, c⟩ | y <;> rw [Finset.mem_filter] at hω
  · have hp : p ∈ D.P := by simpa using hω.1
    obtain ⟨hJ, hpe, hpI, hpend⟩ := D.inl_end h
      (subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)) hp hω.2
    -- The arc lies above `p` in the chart if `p` is its lower end, and below `p` otherwise.
    have hS : ∀ w ∈ D.J p c, w ∈ e.source ∧ ((e p).val 0 < (e w).val 0 ∧ (e p).val 0 = sInf I ∨
        (e w).val 0 < (e p).val 0 ∧ ¬(e p).val 0 = sInf I) := by
      intro w hw
      have hwI : (e w).val 0 ∈ I := mem_image_of_mem _ (hJ hw)
      have hne : (e w).val 0 ≠ (e p).val 0 := fun h' ↦ hpI (h' ▸ hwI)
      refine ⟨hKe (hJ hw), ?_⟩
      rcases hpend with h' | h'
      · exact Or.inl ⟨lt_of_le_of_ne (h' ▸ csInf_le h.bddBelow hwI) hne.symm, h'⟩
      · exact Or.inr ⟨lt_of_le_of_ne (h' ▸ le_csSup h.bddAbove hwI) hne,
          fun h'' ↦ h.sInf_lt_sSup.ne (h''.symm.trans h')⟩
    have hpcl : p ∈ closure (D.J p c) := (D.sides p hp).mem_closure c
    -- The direction at `p` is the direction along the arc.
    obtain ⟨η, hη, hloc⟩ := hφ.exists_increasesAt_iff hpe
    obtain ⟨z, ⟨hze, hzη⟩, hzK⟩ :=
      mem_closure_iff_nhds.1 (closure_mono hJ hpcl) _ (coord_mem_nhds hpe hη)
    rw [CutData.IsTail, eventually_lt_iff_increasesAt (hφ.isOpen p) (hφ.continuousOn p)
      (hφ.injOn p) (hφ.mem p) hpe hpcl hS, ← hloc z hze hzη,
      hφ.increasesAt_iff_of_isPreconnected h.isPreconnected hKe hzK hz₀, Sum.elim_inl]
  · have hy : y ∈ (𝓡∂ 1).boundary M := by simpa using hω.1
    obtain ⟨hyK, -, hyI⟩ := D.inr_end h hy hω.2
    rw [← hI] at hyI
    have hye := hKe hyK
    rw [CutData.IsTail, (isLocalMin_iff_increasesAt (hφ.isOpen y) (hφ.continuousOn y)
      (hφ.injOn y) (hφ.mem y) hye
      ((ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hye).1 hy)).1,
      hφ.increasesAt_iff_of_isPreconnected h.isPreconnected hKe hyK hz₀, Sum.elim_inr, id_eq,
      hyI, eq_self_iff_true, iff_true]

/-- Two signs `±1`, positive exactly when the corresponding one of two exclusive and exhaustive
propositions holds, add up to `0`. -/
private theorem ite_add_ite_eq_zero {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ ¬Q) :
    ((if P then 1 else -1 : ℤ) + if Q then 1 else -1) = 0 := by
  by_cases hQ : Q <;> simp [hQ, h]

open scoped Classical in
/-- **Every arc has one tail and one head.** For the orientation given by the coordinates `φ`,
exactly one of the two ends of an arc is a tail: counting tails with `1` and the other ends with
`-1`, the ends of an arc add up to `0`. -/
private theorem CutData.sum_filter_arcOf_isTail [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) (hφ : IsOrientingCoordinates U φ) {ω₀ : M × Bool ⊕ M}
    (hω₀ : ω₀ ∈ (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset) :
    ∑ ω ∈ ((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
      (fun ω ↦ D.arcOf ω = D.arcOf ω₀), (if D.IsTail φ ω then (1 : ℤ) else -1) = 0 := by
  obtain ⟨e, α, β, h⟩ := D.arc _ (D.base_notMem (fun y hy ↦ hB.mem_toFinset.1 hy) hω₀)
  obtain ⟨hinj, himage⟩ := D.injOn_image_ends hB h
  obtain ⟨z₀, hz₀⟩ := h.nonempty
  set I := (fun z ↦ (e z).val 0) '' D.arcOf ω₀
  set v : M × Bool ⊕ M → ℝ := fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0
  set F := ((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
    (fun ω ↦ D.arcOf ω = D.arcOf ω₀)
  -- The arc has two ends, one at each end of its interval of coordinates.
  have hcard : F.card = 2 := D.card_filter_arcOf_eq_two hB hω₀
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 hcard
  have ha : a ∈ F := by rw [hF]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ F := by rw [hF]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hva : v a = sInf I ∨ v a = sSup I := by
    simpa [himage] using Finset.mem_image_of_mem v ha
  have hvb : v b = sInf I ∨ v b = sSup I := by
    simpa [himage] using Finset.mem_image_of_mem v hb
  have hvab : v a ≠ v b := fun h' ↦ hab (hinj (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) h')
  have hne := h.sInf_lt_sSup.ne
  have hxor : v a = sInf I ↔ ¬v b = sInf I := by
    rcases hva with hva | hva <;> rcases hvb with hvb | hvb
    · exact absurd (hva.trans hvb.symm) hvab
    · exact iff_of_true hva fun h' ↦ hne (h'.symm.trans hvb)
    · exact iff_of_false (fun h' ↦ hne (h'.symm.trans hva)) (not_not.2 hvb)
    · exact absurd (hva.trans hvb.symm) hvab
  -- Exactly one of the two ends is a tail.
  have htail : D.IsTail φ a ↔ ¬D.IsTail φ b := by
    simp only [v] at hxor
    rw [D.isTail_iff hB hφ h hz₀ ha, D.isTail_iff hB hφ h hz₀ hb, hxor]
    tauto
  rw [hF, Finset.sum_pair hab]
  exact ite_add_ite_eq_zero htail

end OrientedParity

section Main

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

/-- **A compact one-dimensional manifold has an even number of boundary points.** For a compact
Hausdorff topological manifold modelled on the half-line `EuclideanHalfSpace 1`, the boundary is
finite (`ModelWithCorners.finite_boundary_euclideanHalfSpace_one`) and has even cardinality.

The Hausdorff hypothesis is necessary: a closed interval with a doubled endpoint is a compact
non-Hausdorff one-dimensional manifold with three boundary points. -/
theorem ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one [CompactSpace M]
    [T2Space M] : Even ((𝓡∂ 1).boundary M).ncard := by
  classical
  obtain ⟨D⟩ := nonempty_cutData (M := M)
  have hB := ModelWithCorners.finite_boundary_euclideanHalfSpace_one (M := M)
  set Ω := (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset
  -- Grouping the sides of points of `P` and the boundary points by their arc, each arc gets two.
  have hcard : Ω.card = (Ω.image D.arcOf).card * 2 := by
    rw [Finset.card_eq_sum_card_image D.arcOf Ω, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun K hK ↦ ?_
    obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hK
    exact D.card_filter_arcOf_eq_two hB hω₀
  have hΩ : Ω.card = D.finite.toFinset.card * 2 + hB.toFinset.card := by
    simp [Ω, Finset.card_disjSum, Finset.card_product]
  rw [ncard_eq_toFinset_card _ hB]
  exact ⟨(Ω.image D.arcOf).card - D.finite.toFinset.card, by omega⟩

/-- **At a boundary point, an orientation points either out or in.** At a boundary point `x` of a
one-dimensional manifold oriented by coordinates `φ`, the coordinate `φ x` has a local maximum,
where the orientation points out of `M`, exactly when it has no local minimum, where the
orientation points into `M`. -/
theorem IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin {U : M → Set M} {φ : M → M → ℝ}
    (hφ : IsOrientingCoordinates U φ) {x : M} (hx : x ∈ (𝓡∂ 1).boundary M) :
    IsLocalMax (φ x) x ↔ ¬IsLocalMin (φ x) x := by
  have hxe := mem_chart_source (EuclideanHalfSpace 1) x
  obtain ⟨hmin, hmax⟩ := isLocalMin_iff_increasesAt (hφ.isOpen x) (hφ.continuousOn x)
    (hφ.injOn x) (hφ.mem x) hxe
    ((ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hxe).1 hx)
  rw [hmax, hmin]

/-- **Whether an orientation points out does not depend on the coordinate.** At a boundary point
`x` of a one-dimensional manifold oriented by coordinates `φ`, every coordinate `φ y` defined at `x`
has a local maximum there exactly when `φ x` does. -/
theorem IsOrientingCoordinates.isLocalMax_iff_of_mem {U : M → Set M} {φ : M → M → ℝ}
    (hφ : IsOrientingCoordinates U φ) {x y : M} (hx : x ∈ (𝓡∂ 1).boundary M) (hxy : x ∈ U y) :
    IsLocalMax (φ x) x ↔ IsLocalMax (φ y) x := by
  have hxe := mem_chart_source (EuclideanHalfSpace 1) x
  have hx0 := (ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hxe).1 hx
  rw [(isLocalMin_iff_increasesAt (hφ.isOpen x) (hφ.continuousOn x) (hφ.injOn x) (hφ.mem x) hxe
      hx0).2, (isLocalMin_iff_increasesAt (hφ.isOpen y) (hφ.continuousOn y) (hφ.injOn y) hxy hxe
      hx0).2, hφ.increasesAt_iff_increasesAt ⟨hφ.mem x, hxy⟩ hxe]

/-- **Whether an orientation points in does not depend on the coordinate.** At a boundary point
`x` of a one-dimensional manifold oriented by coordinates `φ`, every coordinate `φ y` defined at `x`
has a local minimum there exactly when `φ x` does. -/
theorem IsOrientingCoordinates.isLocalMin_iff_of_mem {U : M → Set M} {φ : M → M → ℝ}
    (hφ : IsOrientingCoordinates U φ) {x y : M} (hx : x ∈ (𝓡∂ 1).boundary M) (hxy : x ∈ U y) :
    IsLocalMin (φ x) x ↔ IsLocalMin (φ y) x := by
  have hxe := mem_chart_source (EuclideanHalfSpace 1) x
  have hx0 := (ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hxe).1 hx
  rw [(isLocalMin_iff_increasesAt (hφ.isOpen x) (hφ.continuousOn x) (hφ.injOn x) (hφ.mem x) hxe
      hx0).1, (isLocalMin_iff_increasesAt (hφ.isOpen y) (hφ.continuousOn y) (hφ.injOn y) hxy hxe
      hx0).1, hφ.increasesAt_iff_increasesAt ⟨hφ.mem x, hxy⟩ hxe]

/-- **A compact oriented one-dimensional manifold has as many outgoing as incoming boundary
points.** Let `M` be a compact Hausdorff topological manifold modelled on the half-line
`EuclideanHalfSpace 1`, oriented by local coordinates `φ`. The boundary points at which the
orientation points out of `M`, the local maxima of `φ x`, are as many as those at which it points
into `M`, the local minima of `φ x`. Every boundary point is of exactly one of these two kinds
(`TauCeti.IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin`), so this refines
`TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`. No smoothness of the atlas
or of the coordinates is assumed. -/
theorem ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin [CompactSpace M]
    [T2Space M] {U : M → Set M} {φ : M → M → ℝ} (hφ : IsOrientingCoordinates U φ) :
    {x ∈ (𝓡∂ 1).boundary M | IsLocalMax (φ x) x}.ncard =
      {x ∈ (𝓡∂ 1).boundary M | IsLocalMin (φ x) x}.ncard := by
  classical
  obtain ⟨D⟩ := nonempty_cutData (M := M)
  have hB := ModelWithCorners.finite_boundary_euclideanHalfSpace_one (M := M)
  set Ω := (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset
  set g : M × Bool ⊕ M → ℤ := fun ω ↦ if D.IsTail φ ω then 1 else -1
  -- Grouped by arcs, the signs of the ends add up to zero.
  have hsum : ∑ ω ∈ Ω, g ω = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun ω hω ↦ Finset.mem_image_of_mem D.arcOf hω)]
    refine Finset.sum_eq_zero fun K hK ↦ ?_
    obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hK
    simp only [g]
    exact D.sum_filter_arcOf_isTail hB hφ hω₀
  -- The two sides of each point of `P` have opposite signs.
  have hP : ∑ pc ∈ D.finite.toFinset ×ˢ (Finset.univ : Finset Bool), g (.inl pc) = 0 := by
    rw [Finset.sum_product]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have hopp : D.IsTail φ (.inl (p, true)) ↔ ¬D.IsTail φ (.inl (p, false)) := by
      simp only [CutData.IsTail]
      exact (D.sides p (D.finite.mem_toFinset.1 hp)).opposite (φ p) (U p) (hφ.isOpen p)
        (hφ.mem p) (hφ.continuousOn p) (hφ.injOn p)
    simp only [g, Fintype.sum_bool]
    exact ite_add_ite_eq_zero hopp
  -- So on the boundary the local minima, of sign `1`, cancel the other points, of sign `-1`.
  rw [Finset.sum_disjSum, hP, zero_add] at hsum
  have hcount : (hB.toFinset.filter fun x ↦ IsLocalMin (φ x) x).card =
      (hB.toFinset.filter fun x ↦ ¬IsLocalMin (φ x) x).card := by
    simp only [g] at hsum
    have h' : ∑ y ∈ hB.toFinset, (if IsLocalMin (φ y) y then (1 : ℤ) else -1) = 0 :=
      (Finset.sum_congr rfl fun y _ ↦ if_congr (by rw [CutData.IsTail]) rfl rfl).trans hsum
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const] at h'
    simp only [nsmul_eq_mul, mul_one, mul_neg] at h'
    omega
  have hconv (q : M → Prop) :
      {x ∈ (𝓡∂ 1).boundary M | q x}.ncard = (hB.toFinset.filter q).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp only [Set.Finite.mem_toFinset]
  rw [hconv, hconv, hcount,
    Finset.filter_congr fun x hx ↦ hφ.isLocalMax_iff_not_isLocalMin (hB.mem_toFinset.1 hx)]

end Main

section LocalModels

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Set X}

/-- A point with a neighbourhood homeomorphic to `[0, ε)`, by a homeomorphism sending `0` to it,
lies in a chart of the half-line model reading it with coordinate `0`. -/
private theorem exists_openPartialHomeomorph_coord_eq_zero {x : X} {N : Set X} (hN : N ∈ 𝓝 x)
    {ε : ℝ} (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N) (hex : (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x) :
    ∃ c : OpenPartialHomeomorph X (EuclideanHalfSpace 1), x ∈ c.source ∧ (c x).val 0 = 0 := by
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.2 hN
  let g : interior N → EuclideanHalfSpace 1 := fun y ↦
    ((homeomorphNormalIio ε).symm (e.symm (inclusion interior_subset y)) : EuclideanHalfSpace 1)
  have hg : IsOpenEmbedding g :=
    (isOpen_normalIio ε).isOpenEmbedding_subtypeVal.comp
      ((homeomorphNormalIio ε).symm.isOpenEmbedding.comp
        (e.symm.isOpenEmbedding.comp
          (IsOpenEmbedding.inclusion interior_subset
            (isOpen_interior.preimage continuous_subtypeVal))))
  obtain ⟨c, hcs, hcg⟩ :=
    OpenPartialHomeomorph.exists_source_eq_of_isOpenEmbedding isOpen_interior hg ⟨x, hx⟩
  have hxc : x ∈ c.source := hcs ▸ hx
  have hcx : c x = g ⟨x, hx⟩ := hcg ⟨x, hx⟩
  refine ⟨c, hxc, ?_⟩
  have he : e.symm (inclusion interior_subset ⟨x, hx⟩) = ⟨0, left_mem_Ico.2 hε⟩ :=
    e.symm_apply_eq.2 (Subtype.ext hex.symm)
  rw [hcx, ← coe_homeomorphNormalIio, Homeomorph.apply_symm_apply, he]

/-- A point with a neighbourhood homeomorphic to an open subset of a one-dimensional real normed
space lies in a chart of the half-line model reading it with positive coordinate. -/
private theorem exists_openPartialHomeomorph_coord_pos (hF : Module.finrank ℝ F = 1) {x : X}
    {N : Set X} (hN : N ∈ 𝓝 x) {V : Set F} (hV : IsOpen V) (e : V ≃ₜ N) :
    ∃ c : OpenPartialHomeomorph X (EuclideanHalfSpace 1), x ∈ c.source ∧ 0 < (c x).val 0 := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.2 hN
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hF, finrank_euclideanSpace_fin])
  let g : interior N → EuclideanHalfSpace 1 := fun y ↦
    interiorEmbedding 0 (L (e.symm (inclusion interior_subset y)))
  have hg : IsOpenEmbedding g :=
    (isOpenEmbedding_interiorEmbedding 0).comp (L.toHomeomorph.isOpenEmbedding.comp
      (hV.isOpenEmbedding_subtypeVal.comp (e.symm.isOpenEmbedding.comp
        (IsOpenEmbedding.inclusion interior_subset
          (isOpen_interior.preimage continuous_subtypeVal)))))
  obtain ⟨c, hcs, hcg⟩ :=
    OpenPartialHomeomorph.exists_source_eq_of_isOpenEmbedding isOpen_interior hg ⟨x, hx⟩
  have hxc : x ∈ c.source := hcs ▸ hx
  have hcx : c x = g ⟨x, hx⟩ := hcg ⟨x, hx⟩
  refine ⟨c, hxc, ?_⟩
  rw [hcx]
  exact (range_interiorEmbedding 0).subset (mem_range_self _)

/-- **Local models assemble into a one-dimensional manifold with boundary.** If each point of `B`
has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to it, and each other point
has a neighbourhood homeomorphic to an open subset of a one-dimensional real normed space `F`, then
`X` carries an atlas modelled on the half-line `EuclideanHalfSpace 1` whose boundary is exactly
`B`. The atlas is topological: no compatibility of its charts is claimed. -/
theorem exists_chartedSpace_euclideanHalfSpace_one_boundary_eq (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) :
    ∃ _ : ChartedSpace (EuclideanHalfSpace 1) X, (𝓡∂ 1).boundary X = B := by
  have hc (x : X) : ∃ c : OpenPartialHomeomorph X (EuclideanHalfSpace 1),
      x ∈ c.source ∧ ((c x).val 0 = 0 ↔ x ∈ B) := by
    by_cases hxB : x ∈ B
    · obtain ⟨N, hN, ε, hε, e, hex⟩ := hB x hxB
      obtain ⟨c, hxc, hcx⟩ := exists_openPartialHomeomorph_coord_eq_zero hN hε e hex
      exact ⟨c, hxc, iff_of_true hcx hxB⟩
    · obtain ⟨N, hN, V, hV, ⟨e⟩⟩ := hX x hxB
      obtain ⟨c, hxc, hcx⟩ := exists_openPartialHomeomorph_coord_pos hF hN hV e
      exact ⟨c, hxc, iff_of_false hcx.ne' hxB⟩
  choose c hxc hcB using hc
  let C : ChartedSpace (EuclideanHalfSpace 1) X :=
    { atlas := range c
      chartAt := c
      mem_chart_source := hxc
      chart_mem_atlas := mem_range_self }
  refine ⟨C, Set.ext fun x ↦ ?_⟩
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (hxc x)]
  exact hcB x

/-- **At an endpoint, an orientation points either out or in.** For a space `X` described by local
models as in `TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq` and oriented by
local coordinates `φ`, at each point `x ∈ B` the coordinate `φ x` has a local maximum exactly
when it has no local minimum. -/
theorem IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin_of_forall_exists_homeomorph_Ico
    (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) {x : X} (hx : x ∈ B) :
    IsLocalMax (φ x) x ↔ ¬IsLocalMin (φ x) x := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hφ.isLocalMax_iff_not_isLocalMin (hC ▸ hx)

/-- **At an endpoint, whether an orientation points out does not depend on the coordinate.** For a
space `X` described by local models as in
`TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq` and oriented by local coordinates
`φ`, at each point `x ∈ B` every coordinate `φ y` defined at `x` has a local maximum there exactly
when `φ x` does. -/
theorem
    IsOrientingCoordinates.isLocalMax_iff_of_mem_of_forall_exists_homeomorph_Ico
    (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) {x y : X} (hx : x ∈ B) (hxy : x ∈ U y) :
    IsLocalMax (φ x) x ↔ IsLocalMax (φ y) x := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hφ.isLocalMax_iff_of_mem (hC ▸ hx) hxy

/-- **At an endpoint, whether an orientation points in does not depend on the coordinate.** For a
space `X` described by local models as in
`TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq` and oriented by local coordinates
`φ`, at each point `x ∈ B` every coordinate `φ y` defined at `x` has a local minimum there exactly
when `φ x` does. -/
theorem
    IsOrientingCoordinates.isLocalMin_iff_of_mem_of_forall_exists_homeomorph_Ico
    (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) {x y : X} (hx : x ∈ B) (hxy : x ∈ U y) :
    IsLocalMin (φ x) x ↔ IsLocalMin (φ y) x := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hφ.isLocalMin_iff_of_mem (hC ▸ hx) hxy

variable [CompactSpace X]

/-- **A compact space locally modelled on the half-line has finitely many endpoints.** Let `X` be
compact, and let `B` be a set of points of `X` such that

* each `x ∈ B` has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x`, and
* each `x ∉ B` has a neighbourhood homeomorphic to an open subset of a one-dimensional real
  normed space `F`.

Then `B` is finite. -/
theorem finite_of_forall_exists_homeomorph_Ico (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) :
    B.Finite := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hC ▸ ModelWithCorners.finite_boundary_euclideanHalfSpace_one

/-- **A compact Hausdorff space locally modelled on the half-line has an even number of
endpoints.** Let `X` be compact and Hausdorff, and let `B` be a set of points of `X` such that

* each `x ∈ B` has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x`, and
* each `x ∉ B` has a neighbourhood homeomorphic to an open subset of a one-dimensional real
  normed space `F`.

Then `B` has an even number of elements; it is finite by
`TauCeti.finite_of_forall_exists_homeomorph_Ico`. This is
`TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one` for a space described by
local homeomorphisms rather than by an atlas. Local gluing describes a neighbourhood of a broken
trajectory in this way (compare `TauCeti.exists_homeomorph_closure_splitGluingPairs`), so for a
compactified space of index-two trajectories `B` is the set of broken trajectories. -/
theorem even_ncard_of_forall_exists_homeomorph_Ico [T2Space X] (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) :
    Even B.ncard := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hC ▸ ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one

/-- **A compact oriented space locally modelled on the half-line has as many outgoing as incoming
endpoints.** Let `X` be compact and Hausdorff, and let `B` be a set of points of `X` such that

* each `x ∈ B` has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x`, and
* each `x ∉ B` has a neighbourhood homeomorphic to an open subset of a one-dimensional real
  normed space `F`.

If local coordinates `φ` orient `X`, then the points of `B` at which `φ x` has a local maximum,
where the orientation points out of `X`, are as many as those at which it has a local minimum,
where it points into `X`. This is
`TauCeti.ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin` for a space described
by local homeomorphisms rather than by an atlas, and the oriented refinement of
`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`. For an oriented compactified space of
index-two trajectories, `B` is the set of broken trajectories. -/
theorem ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin_of_forall_exists_homeomorph_Ico
    [T2Space X] (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) :
    {x ∈ B | IsLocalMax (φ x) x}.ncard = {x ∈ B | IsLocalMin (φ x) x}.ncard := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  subst hC
  exact ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin hφ

end LocalModels

end TauCeti
