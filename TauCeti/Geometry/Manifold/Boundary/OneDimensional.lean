/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Topology.Order.LocalMonotone
import Mathlib.Algebra.Order.Interval.Set.Group
import TauCeti.Order.Monotone.Basic
import TauCeti.Topology.ConnectedComponents

/-!
# Boundary points of compact one-dimensional manifolds

Let `M` be a compact Hausdorff topological manifold modelled on the half-line
`EuclideanHalfSpace 1`. This file proves that its boundary `(𝓡∂ 1).boundary M` is finite and has
an even number of points, and that if the interior of `M` is oriented, the boundary points at which
the orientation points outward are as many as those at which it points inward. No smoothness of
the atlas is assumed.

These are the facts behind the classical proof that the Morse boundary squares to zero. There,
the compactified spaces of index-two trajectories are compact one-dimensional manifolds whose
boundary points are the broken trajectories, so the broken trajectories come in pairs; their
parity is exactly the criterion of `TauCeti.morseBoundary_comp_morseBoundary_eq_zero_iff`. Over
`ℤ`, the trajectory spaces are oriented and the signed count of the broken trajectories vanishes.
The gluing charts of such a compactification are only homeomorphisms, which is why the statements
here are topological. Such a compactification comes with local models rather than an atlas; the
corresponding statements are in `TauCeti.Geometry.Manifold.Boundary.LocalModels`.

Mathlib defines a boundary point through the preferred chart at that point, and proves the notion
chart-independent only for `C¹` manifolds. In dimension one chart independence is elementary: a
chart transition sending a boundary point to an interior point would carry a connected punctured
half-interval onto a disconnected punctured interval
(`ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff`).

An orientation of the interior is recorded topologically, by a set `𝒪` of charts to `ℝ` covering
the interior points whose transition maps are increasing near every common point. A boundary point
is *outward* when the charts of `𝒪` decrease along an injective path leaving it, and *inward* when
they increase. Orientations by coherent local coordinates defined at every point, boundary points
included, are in `TauCeti.Geometry.Manifold.Boundary.OrientingCoordinates`.

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

For the signed count, the orientation is constant along each component `K`, which is connected, so
it points towards exactly one of the two ends of `K`: the *outward* end. At a point of `P` it
points out of one side and into the other, so exactly one of its two sides is an outward end.
At a boundary point it points out of `M` exactly when it points towards that end of its component.
Counting the outward ends and the inward ends of all components gives
`#P + #(outward boundary points) = #(components) = #P + #(inward boundary points)`.

## Main results

* `TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff`: a point is a boundary point
  exactly when some, equivalently any, chart around it reads it with coordinate `0`.
* `TauCeti.ModelWithCorners.finite_boundary_euclideanHalfSpace_one`: a compact one-dimensional
  manifold has finitely many boundary points.
* `TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`: a compact Hausdorff
  one-dimensional manifold has an even number of boundary points.
* `TauCeti.ModelWithCorners.ncard_eq_ncard_boundary_euclideanHalfSpace_one`: a compact Hausdorff
  one-dimensional manifold with oriented interior has as many outward as inward boundary points.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  Appendix (the classification of one-manifolds, and its corollary that the boundary of a compact
  one-manifold has an even number of points).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactified trajectory spaces as compact one-manifolds with boundary).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the signed count of the ends of oriented compactified
  trajectory spaces, which proves that the integral Morse boundary squares to zero).
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
exhausting a punctured open neighbourhood `N \ {p}` of `p`. In the chart at `p`, where `p` has
coordinate `t`, they are the images of `(t, t + η]` and `[t - η, t)`. -/
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
  param : ∃ η > 0, η < (chartAt (EuclideanHalfSpace 1) p p).val 0 ∧
    (∀ s ∈ Icc ((chartAt (EuclideanHalfSpace 1) p p).val 0 - η)
      ((chartAt (EuclideanHalfSpace 1) p p).val 0 + η),
        normalRay s ∈ (chartAt (EuclideanHalfSpace 1) p).target) ∧
    ∀ b, J b = (fun s ↦ (chartAt (EuclideanHalfSpace 1) p).symm (normalRay s)) ''
      cond b (Ioc ((chartAt (EuclideanHalfSpace 1) p p).val 0)
        ((chartAt (EuclideanHalfSpace 1) p p).val 0 + η))
        (Ico ((chartAt (EuclideanHalfSpace 1) p p).val 0 - η)
          ((chartAt (EuclideanHalfSpace 1) p p).val 0))

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
  refine ⟨fun b ↦ (fun s ↦ e.symm (normalRay s)) '' D b,
    e.source ∩ (fun y ↦ (e y).val 0) ⁻¹' Ioo (t - η) (t + η),
    fun b ↦ e.symm (normalRay (cond b (t + η) (t - η))), ⟨fun b ↦ ?_, fun b ↦ ?_, fun b ↦ ?_,
    fun b ↦ ?_, ?_, ?_, ⟨hpe, by simpa [t] using hη⟩, ?_,
    ⟨η, hη, hηt, fun s hs ↦ (hγ s hs).1, fun b ↦ rfl⟩⟩⟩
  · exact (by cases b <;> [exact isPreconnected_Ico; exact isPreconnected_Ioc] :
      IsPreconnected (D b)).image _ (hcont.mono (hD b).1)
  · refine mem_image_of_mem _ ?_
    cases b <;> simp [D, hη]
  · refine disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact (hD b).2.1 ((hγ s ((hD b).1 hs)).2.2 hsP ▸ hs)
  · have hpt : e.symm (normalRay t) = p := symm_normalRay_coord hpe
    rw [← hpt]
    exact ((hcont t ⟨by linarith, by linarith⟩).mono (hD b).1).mem_closure_image (hD b).2.2
  · refine disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have := congrArg (fun z ↦ (e z).val 0) hss'
    simp only [(hγ s ((hD true).1 hs)).2.1, (hγ s' ((hD false).1 hs')).2.1] at this
    simp only [D, Bool.cond_true, Bool.cond_false, mem_Ioc, mem_Ico] at hs hs'
    linarith
  · exact continuousOn_coord.isOpen_inter_preimage e.open_source isOpen_Ioo
  · rintro z ⟨⟨hze, hzI⟩, hzp⟩
    have hzs : e.symm (normalRay ((e z).val 0)) = z := symm_normalRay_coord hze
    have hst : (e z).val 0 ≠ t := fun h ↦
      hzp (by rw [mem_singleton_iff, ← hzs, h, symm_normalRay_coord hpe])
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inr ⟨_, ⟨hzI.1.le, h⟩, hzs⟩
    · exact Or.inl ⟨_, ⟨h, hzI.2.le⟩, hzs⟩

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

/-- The ends counted by the argument: the two sides of each point of `P`, and the points of a
finite set `B` of boundary points. -/
private def CutData.ends (D : CutData M) (B : Finset M) : Finset (M × Bool ⊕ M) :=
  (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum B

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
    (hω : ω ∈ D.ends B) : D.base ω ∉ D.P := by
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

/-- **Every arc has exactly two ends.** Among the sides of the points of `P` and the boundary
points, those lying in a given component of the complement of `P` are exactly two: in any chart in
which the component is an arc, the coordinate of the point of `P` or of the boundary point is a
bijection onto the two endpoints of the interval of coordinates of the arc. -/
private theorem CutData.injOn_and_image_filter_arcOf [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ}
    (h : IsArcIn e α β (D.arcOf ω₀)) :
    InjOn (fun ω : M × Bool ⊕ M ↦ (e (Sum.elim Prod.fst id ω)).val 0)
        ((D.ends hB.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀) : Set (M × Bool ⊕ M)) ∧
      ((D.ends hB.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).image
          (fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0) =
        {sInf ((fun z ↦ (e z).val 0) '' D.arcOf ω₀),
          sSup ((fun z ↦ (e z).val 0) '' D.arcOf ω₀)} := by
  classical
  set Ω := D.ends hB.toFinset
  set K := D.arcOf ω₀
  set I := (fun z ↦ (e z).val 0) '' K
  set v : M × Bool ⊕ M → ℝ := fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0
  have hKP : Disjoint K D.P :=
    subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)
  -- A side in the arc belongs to a point of `P` with an unattained endpoint as coordinate.
  have hinl : ∀ p c, (.inl (p, c) : M × Bool ⊕ M) ∈ Ω → D.arcOf (.inl (p, c)) = K →
      p ∈ D.P ∧ D.J p c ⊆ K ∧ p ∈ e.source ∧ v (.inl (p, c)) ∉ I ∧
        (v (.inl (p, c)) = sInf I ∨ v (.inl (p, c)) = sSup I) := fun p c hω hK ↦ by
    have hp : p ∈ D.P := by simpa [Ω, CutData.ends] using hω
    exact ⟨hp, D.inl_end h hKP hp hK⟩
  -- A boundary point in the arc has coordinate `0`, the attained infimum.
  have hinr : ∀ y, (.inr y : M × Bool ⊕ M) ∈ Ω → D.arcOf (.inr y) = K →
      y ∈ e.source ∧ v (.inr y) ∈ I ∧ v (.inr y) = sInf I := fun y hω hK ↦ by
    obtain ⟨hyK, hy⟩ := D.inr_end h (by simpa [Ω, CutData.ends] using hω) hK
    exact ⟨(h.mem y hyK).1, hy⟩
  refine ⟨?_, ?_⟩
  · rintro (⟨p, c⟩ | y) hω (⟨p', c'⟩ | y') hω' hvv <;>
      rw [Finset.coe_filter, mem_ofPred_eq] at hω hω'
    · obtain ⟨hp, hJ, hpe, -, -⟩ := hinl p c hω.1 hω.2
      obtain ⟨-, hJ', hpe', -, -⟩ := hinl p' c' hω'.1 hω'.2
      obtain rfl : p = p' := injOn_coord hpe hpe' hvv
      have hpK := disjoint_right.1 hKP hp
      cases c <;> cases c'
      exacts [rfl, (D.not_subset_and_subset hp h hpK hJ' hJ).elim,
        (D.not_subset_and_subset hp h hpK hJ hJ').elim, rfl]
    · exact ((hinl p c hω.1 hω.2).2.2.2.1 (by rw [hvv]; exact (hinr y' hω'.1 hω'.2).2.1)).elim
    · exact ((hinl p' c' hω'.1 hω'.2).2.2.2.1 (by rw [← hvv]; exact (hinr y hω.1 hω.2).2.1)).elim
    · rw [injOn_coord (hinr y hω.1 hω.2).1 (hinr y' hω'.1 hω'.2).1 hvv]
  · ext c
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(⟨p, c'⟩ | y), hω, rfl⟩ <;> rw [Finset.mem_filter] at hω
      · exact (hinl p c' hω.1 hω.2).2.2.2.2
      · exact Or.inl (hinr y hω.1 hω.2).2.2
    · intro hc
      rcases D.exists_of_endpoint h hc with ⟨z, hzK, hzB, hzc⟩ | ⟨p, hp, b, hpb, hpc⟩
      · exact ⟨.inr z, Finset.mem_filter.2 ⟨Finset.inr_mem_disjSum.2 (hB.mem_toFinset.2 hzB),
          (connectedComponentIn_eq hzK).symm⟩, hzc⟩
      · exact ⟨.inl (p, b), Finset.mem_filter.2 ⟨Finset.inl_mem_disjSum.2
          (Finset.mem_product.2 ⟨D.finite.mem_toFinset.2 hp, Finset.mem_univ _⟩), hpb⟩, hpc⟩

/-- Every arc has exactly two ends, the sides of points of `P` and boundary points lying in it. -/
private theorem CutData.card_filter_arcOf_eq_two [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M}
    (hω₀ : ω₀ ∈ D.ends hB.toFinset) :
    ((D.ends hB.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).card = 2 := by
  obtain ⟨e, α, β, h⟩ := D.arc _ (D.base_notMem (fun y hy ↦ hB.mem_toFinset.1 hy) hω₀)
  obtain ⟨hinj, himage⟩ := D.injOn_and_image_filter_arcOf hB h
  rw [← Finset.card_image_of_injOn hinj, himage]
  exact Finset.card_pair h.sInf_lt_sSup.ne

end Parity

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
  set Ω := D.ends hB.toFinset
  -- Grouping the sides of points of `P` and the boundary points by their arc, each arc gets two.
  have hcard : Ω.card = (Ω.image D.arcOf).card * 2 := by
    rw [Finset.card_eq_sum_card_image D.arcOf Ω, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun K hK ↦ ?_
    obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hK
    exact D.card_filter_arcOf_eq_two hB hω₀
  have hΩ : Ω.card = D.finite.toFinset.card * 2 + hB.toFinset.card := by
    simp [Ω, CutData.ends, Finset.card_disjSum, Finset.card_product]
  rw [ncard_eq_toFinset_card _ hB]
  exact ⟨(Ω.image D.arcOf).card - D.finite.toFinset.card, by omega⟩

end Main

section Orientation

/-! ### Oriented one-dimensional manifolds

An orientation of the interior of a one-dimensional manifold is recorded by a set `𝒪` of charts to
`ℝ` covering the interior points, whose transition maps are increasing near every common point.
Along the coordinate of a chart `e` to the half-line, the orientation either increases or
decreases near each interior point; it is *positive* for `e` there when it increases. -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  {𝒪 : Set (OpenPartialHomeomorph M ℝ)} {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- `𝒪` orients the interior of `M`: its charts cover the interior points, and the transition
map between any two of them is strictly increasing near every common point. -/
private structure IsOrientation (𝒪 : Set (OpenPartialHomeomorph M ℝ)) : Prop where
  cover : ∀ x ∉ (𝓡∂ 1).boundary M, ∃ c ∈ 𝒪, x ∈ c.source
  compat : ∀ c ∈ 𝒪, ∀ c' ∈ 𝒪, ∀ x ∈ c.source ∩ c'.source, StrictMonoAt (c' ∘ c.symm) (c x)

omit [ChartedSpace (EuclideanHalfSpace 1) M] in
/-- The orientation `𝒪` points outward at `b`: the charts of `𝒪` are strictly decreasing along
some injective path leaving `b`. -/
private def IsOutward (𝒪 : Set (OpenPartialHomeomorph M ℝ)) (b : M) : Prop :=
  ∃ γ : ℝ → M, ∃ η > 0, γ 0 = b ∧ ContinuousOn γ (Icc 0 η) ∧ InjOn γ (Icc 0 η) ∧
    ∀ s ∈ Ioo 0 η, ∀ c ∈ 𝒪, γ s ∈ c.source → StrictAntiAt (c ∘ γ) s

omit [ChartedSpace (EuclideanHalfSpace 1) M] in
/-- The orientation `𝒪` points inward at `b`: the charts of `𝒪` are strictly increasing along
some injective path leaving `b`. -/
private def IsInward (𝒪 : Set (OpenPartialHomeomorph M ℝ)) (b : M) : Prop :=
  ∃ γ : ℝ → M, ∃ η > 0, γ 0 = b ∧ ContinuousOn γ (Icc 0 η) ∧ InjOn γ (Icc 0 η) ∧
    ∀ s ∈ Ioo 0 η, ∀ c ∈ 𝒪, γ s ∈ c.source → StrictMonoAt (c ∘ γ) s

/-- The orientation `𝒪` increases along the coordinate of the chart `e` near `y`. -/
private def IsPos (𝒪 : Set (OpenPartialHomeomorph M ℝ))
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (y : M) : Prop :=
  ∃ c ∈ 𝒪, y ∈ c.source ∧ StrictMonoAt (fun s ↦ c (e.symm (normalRay s))) ((e y).val 0)

/-- Near an interior point `y`, a chart `c` to `ℝ` read along the coordinate of `e` is continuous
and injective, so it is strictly monotone or strictly antitone. -/
private theorem exists_strictMonoAt_or_strictAntiAt {c : OpenPartialHomeomorph M ℝ} {y : M}
    (hye : y ∈ e.source) (hy : y ∉ (𝓡∂ 1).boundary M) (hyc : y ∈ c.source) :
    ∃ V ∈ 𝓝 ((e y).val 0), (∀ s ∈ V, e.symm (normalRay s) ∈ c.source) ∧
      ContinuousOn (fun s ↦ c (e.symm (normalRay s))) V ∧
      (StrictMonoAt (fun s ↦ c (e.symm (normalRay s))) ((e y).val 0) ∨
        StrictAntiAt (fun s ↦ c (e.symm (normalRay s))) ((e y).val 0)) := by
  set V := Ioi 0 ∩ normalRay ⁻¹' (e.target ∩ e.symm ⁻¹' c.source)
  have hV : IsOpen V := isOpen_Ioi.inter
    ((e.isOpen_inter_preimage_symm c.open_source).preimage continuous_normalRay)
  have hyV : (e y).val 0 ∈ V := ⟨coord_pos_of_notMem_boundary hye hy, by
    simpa [normalRay_normalCoord, e.left_inv hye] using ⟨e.map_source hye, hyc⟩⟩
  have hcont : ContinuousOn (fun s ↦ c (e.symm (normalRay s))) V :=
    c.continuousOn.comp (e.continuousOn_symm.comp continuous_normalRay.continuousOn
      fun _ hs ↦ hs.2.1) fun _ hs ↦ hs.2.2
  have hinj : InjOn (fun s ↦ c (e.symm (normalRay s))) V := fun s hs s' hs' hss' ↦ by
    have := congrArg (fun z ↦ (e z).val 0) (c.injOn hs.2.2 hs'.2.2 hss')
    simpa only [coord_symm_normalRay (le_of_lt hs.1) hs.2.1,
      coord_symm_normalRay (le_of_lt hs'.1) hs'.2.1] using this
  exact ⟨V, hV.mem_nhds hyV, fun _ hs ↦ hs.2.2, hcont,
    strictMonoAt_or_strictAntiAt (hV.mem_nhds hyV) hcont hinj⟩

/-- The direction of the orientation along the coordinate of `e` does not depend on the chart of
`𝒪` used to read it. -/
private theorem strictMonoAt_iff_strictMonoAt (h𝒪 : IsOrientation 𝒪)
    {c c' : OpenPartialHomeomorph M ℝ} (hc : c ∈ 𝒪) (hc' : c' ∈ 𝒪) {y : M} (hye : y ∈ e.source)
    (hy : y ∉ (𝓡∂ 1).boundary M) (hyc : y ∈ c.source) (hyc' : y ∈ c'.source) :
    StrictMonoAt (fun s ↦ c' (e.symm (normalRay s))) ((e y).val 0) ↔
      StrictMonoAt (fun s ↦ c (e.symm (normalRay s))) ((e y).val 0) := by
  obtain ⟨V, hV, hVc, hcont, hdir⟩ := exists_strictMonoAt_or_strictAntiAt hye hy hyc
  have hτy : c (e.symm (normalRay ((e y).val 0))) = c y := by
    rw [normalRay_normalCoord, e.left_inv hye]
  have heq : (fun s ↦ c' (e.symm (normalRay s))) =ᶠ[𝓝 ((e y).val 0)]
      (c' ∘ c.symm) ∘ fun s ↦ c (e.symm (normalRay s)) :=
    Filter.eventually_of_mem hV fun s hs ↦ by simp only [comp_apply, c.left_inv (hVc s hs)]
  have hh : StrictMonoAt (c' ∘ c.symm) (c y) := h𝒪.compat c hc c' hc' y ⟨hyc, hyc'⟩
  rw [strictMonoAt_iff_of_eventuallyEq_comp heq (hcont.continuousAt hV) hdir
    (by simp only [hτy]; exact Or.inl hh)]
  simp only [hτy]
  exact iff_true_left hh

private theorem isPos_iff (h𝒪 : IsOrientation 𝒪)
    {c : OpenPartialHomeomorph M ℝ} (hc : c ∈ 𝒪) {y : M} (hye : y ∈ e.source)
    (hy : y ∉ (𝓡∂ 1).boundary M) (hyc : y ∈ c.source) :
    IsPos 𝒪 e y ↔ StrictMonoAt (fun s ↦ c (e.symm (normalRay s))) ((e y).val 0) :=
  ⟨fun ⟨_, hc', hyc', h⟩ ↦ (strictMonoAt_iff_strictMonoAt h𝒪 hc hc' hye hy hyc hyc').1 h,
    fun h ↦ ⟨c, hc, hyc, h⟩⟩

private theorem not_isPos_iff (h𝒪 : IsOrientation 𝒪)
    {c : OpenPartialHomeomorph M ℝ} (hc : c ∈ 𝒪) {y : M} (hye : y ∈ e.source)
    (hy : y ∉ (𝓡∂ 1).boundary M) (hyc : y ∈ c.source) :
    ¬IsPos 𝒪 e y ↔ StrictAntiAt (fun s ↦ c (e.symm (normalRay s))) ((e y).val 0) := by
  rw [isPos_iff h𝒪 hc hye hy hyc]
  obtain ⟨-, -, -, -, h⟩ := exists_strictMonoAt_or_strictAntiAt hye hy hyc
  have := not_strictMonoAt_and_strictAntiAt (f := fun s ↦ c (e.symm (normalRay s)))
    (a := (e y).val 0)
  tauto

/-- **An orientation is constant along preconnected sets.** On a preconnected set of interior
points of the domain of `e`, the orientation is positive for `e` everywhere or nowhere. -/
private theorem isPos_iff_isPos_of_isPreconnected (h𝒪 : IsOrientation 𝒪)
    {S : Set M} (hS : IsPreconnected S) (hSe : S ⊆ e.source)
    (hSB : Disjoint S ((𝓡∂ 1).boundary M)) {y y' : M} (hy : y ∈ S) (hy' : y' ∈ S) :
    IsPos 𝒪 e y ↔ IsPos 𝒪 e y' := by
  -- The points where some chart of `𝒪` increases, respectively decreases, along `e` form open sets.
  have hopen : ∀ R : (ℝ → ℝ) → Set ℝ → Prop, (∀ g V V', V' ⊆ V → R g V → R g V') →
      IsOpen {z | z ∈ e.source ∧ ∃ c ∈ 𝒪, z ∈ c.source ∧
        ∃ V ∈ 𝓝 ((e z).val 0), R (fun s ↦ c (e.symm (normalRay s))) V} := by
    refine fun R hR ↦ isOpen_iff_mem_nhds.2 fun z ⟨hze, c, hc, hzc, V, hV, hRV⟩ ↦ ?_
    have hW : IsOpen (e.source ∩ c.source ∩ (fun w ↦ (e w).val 0) ⁻¹' interior V) :=
      (continuousOn_coord.mono inter_subset_left).isOpen_inter_preimage
        (e.open_source.inter c.open_source) isOpen_interior
    exact Filter.mem_of_superset (hW.mem_nhds ⟨⟨hze, hzc⟩, mem_interior_iff_mem_nhds.2 hV⟩)
      fun w hw ↦ ⟨hw.1.1, c, hc, hw.1.2, interior V, isOpen_interior.mem_nhds hw.2,
        hR _ _ _ interior_subset hRV⟩
  set A := {z | z ∈ e.source ∧ ∃ c ∈ 𝒪, z ∈ c.source ∧
    ∃ V ∈ 𝓝 ((e z).val 0), StrictMonoOn (fun s ↦ c (e.symm (normalRay s))) V}
  set A' := {z | z ∈ e.source ∧ ∃ c ∈ 𝒪, z ∈ c.source ∧
    ∃ V ∈ 𝓝 ((e z).val 0), StrictAntiOn (fun s ↦ c (e.symm (normalRay s))) V}
  have hmem : ∀ z ∈ S, (z ∈ A ↔ IsPos 𝒪 e z) ∧ (z ∈ A' ↔ ¬IsPos 𝒪 e z) := fun z hz ↦ by
    have hze := hSe hz
    have hzB := disjoint_left.1 hSB hz
    obtain ⟨c, hc, hzc⟩ := h𝒪.cover z hzB
    exact ⟨⟨fun ⟨_, c', hc', hzc', h⟩ ↦ ⟨c', hc', hzc', strictMonoAt_iff.2 h⟩,
        fun ⟨c', hc', hzc', h⟩ ↦ ⟨hze, c', hc', hzc', strictMonoAt_iff.1 h⟩⟩,
      ⟨fun ⟨_, c', hc', hzc', h⟩ ↦ (not_isPos_iff h𝒪 hc' hze hzB hzc').2 (strictAntiAt_iff.2 h),
        fun h ↦ ⟨hze, c, hc, hzc, strictAntiAt_iff.1 ((not_isPos_iff h𝒪 hc hze hzB hzc).1 h)⟩⟩⟩
  have hSAA : S ⊆ A ∪ A' := fun z hz ↦ (em (IsPos 𝒪 e z)).imp ((hmem z hz).1.2) (hmem z hz).2.2
  have key : ∀ z ∈ S, ∀ z' ∈ S, IsPos 𝒪 e z → IsPos 𝒪 e z' := fun z hz z' hz' h ↦ by
    by_contra h'
    obtain ⟨w, hwS, hwA, hwA'⟩ := hS A A' (hopen _ fun _ _ _ h hg ↦ hg.mono h)
      (hopen _ fun _ _ _ h hg ↦ hg.mono h) hSAA ⟨z, hz, (hmem z hz).1.2 h⟩
      ⟨z', hz', (hmem z' hz').2.2 h'⟩
    exact (hmem w hwS).2.1 hwA' ((hmem w hwS).1.1 hwA)
  exact ⟨key y hy y' hy', key y' hy' y hy⟩

/-- The interior points of an arc form a preconnected set. -/
private theorem IsArcIn.isPreconnected_diff_boundary {α β : ℝ} {K : Set M}
    (h : IsArcIn e α β K) : IsPreconnected (K \ (𝓡∂ 1).boundary M) := by
  have hI : IsPreconnected ((fun z ↦ (e z).val 0) '' K ∩ Ioi 0) :=
    (h.isConnected_image.isPreconnected.ordConnected.inter ordConnected_Ioi).isPreconnected
  have heq : K \ (𝓡∂ 1).boundary M =
      (fun s ↦ e.symm (normalRay s)) '' ((fun z ↦ (e z).val 0) '' K ∩ Ioi 0) := by
    ext z
    constructor
    · rintro ⟨hzK, hzB⟩
      exact ⟨_, ⟨mem_image_of_mem _ hzK, coord_pos_of_notMem_boundary (h.mem z hzK).1 hzB⟩,
        symm_normalRay_coord (h.mem z hzK).1⟩
    · rintro ⟨s, ⟨hsK, hs0⟩, rfl⟩
      have hst := h.target s (h.image_subset_Icc hsK)
      refine ⟨by rw [← h.image_symm_normalRay]; exact mem_image_of_mem _ hsK, fun hB ↦ ?_⟩
      rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (e.map_target hst),
        coord_symm_normalRay (le_of_lt hs0) hst] at hB
      exact (ne_of_gt hs0) hB
  rw [heq]
  exact hI.image _ ((continuousOn_symm_normalRay h.target).mono
    fun s hs ↦ h.image_subset_Icc hs.1)

/-- An arc has an interior point. -/
private theorem IsArcIn.nonempty_diff_boundary {α β : ℝ} {K : Set M} (h : IsArcIn e α β K) :
    (K \ (𝓡∂ 1).boundary M).Nonempty := by
  obtain ⟨z, hz⟩ := h.nonempty
  obtain ⟨ε, hε, -, hs⟩ := h.exists_nhds hz
  obtain ⟨w, hwK, hw⟩ := hs ((e z).val 0 + ε) (by linarith [(e z).property])
    (by rw [add_sub_cancel_left, abs_of_pos hε])
  refine ⟨w, hwK, fun hB ↦ ?_⟩
  simp only at hw
  rw [(ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (h.mem w hwK).1).1 hB] at hw
  linarith [(e z).property]

/-- **The orientation at a boundary point of an arc.** Let `b` be a boundary point in an arc `K`
in the chart `e`, and `γ` an injective path from `b`. At some time `s`, the direction of a chart
of `𝒪` along `γ` is the direction of the orientation along the arc in the chart `e`. -/
private theorem IsArcIn.exists_strictMonoAt_iff_isPos (h𝒪 : IsOrientation 𝒪)
    {α β : ℝ} {K : Set M} (h : IsArcIn e α β K) {b : M} (hbK : b ∈ K)
    (hbB : b ∈ (𝓡∂ 1).boundary M) {z₀ : M} (hz₀K : z₀ ∈ K) (hz₀B : z₀ ∉ (𝓡∂ 1).boundary M)
    {γ : ℝ → M} {η : ℝ} (hη : 0 < η) (hγ0 : γ 0 = b) (hγc : ContinuousOn γ (Icc 0 η))
    (hγi : InjOn γ (Icc 0 η)) :
    ∃ s ∈ Ioo 0 η, ∃ c ∈ 𝒪, γ s ∈ c.source ∧ (StrictMonoAt (c ∘ γ) s ↔ IsPos 𝒪 e z₀) := by
  have hbe := (h.mem b hbK).1
  have hb0 : (e b).val 0 = 0 := (ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hbe).1 hbB
  -- An initial piece `γ [0, η']` of the path stays in the arc.
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1
    ((hγc 0 ⟨le_rfl, hη.le⟩).preimage_mem_nhdsWithin (by
      rw [hγ0]; exact Filter.inter_mem (h.isOpen.mem_nhds hbK) (e.open_source.mem_nhds hbe)))
  set η' := min (ε / 2) η
  have hη' : 0 < η' := lt_min (by linarith) hη
  have hη'η : Icc 0 η' ⊆ Icc 0 η := Icc_subset_Icc_right (min_le_right _ _)
  have hsub : ∀ s ∈ Icc 0 η', γ s ∈ K ∩ e.source := fun s hs ↦ hεsub ⟨by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    linarith [hs.2, min_le_left (ε / 2) η], hη'η hs⟩
  -- The coordinate of `e` increases along this piece, since it starts at `0`.
  set τ : ℝ → ℝ := fun s ↦ (e (γ s)).val 0
  have hτc : ContinuousOn τ (Icc 0 η') :=
    continuousOn_coord.comp (hγc.mono hη'η) fun s hs ↦ (hsub s hs).2
  have hτm : StrictMonoOn τ (Icc 0 η') := hτc.strictMonoOn_of_injOn_Icc hη'.le
    (by simp only [τ, hγ0, hb0]; exact (e _).property) fun s hs s' hs' hss' ↦
      hγi (hη'η hs) (hη'η hs') (injOn_coord (hsub s hs).2 (hsub s' hs').2 hss')
  -- At the midpoint the path is at an interior point `y` of the arc.
  set u := η' / 2
  have hu : u ∈ Ioo 0 η' := ⟨half_pos hη', half_lt_self hη'⟩
  have hIcc : Icc 0 η' ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
  have hyK := (hsub u (Ioo_subset_Icc_self hu)).1
  have hye := (hsub u (Ioo_subset_Icc_self hu)).2
  have hyB : γ u ∉ (𝓡∂ 1).boundary M := fun hyB ↦ by
    have hyb := injOn_coord hye hbe
      (((ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hye).1 hyB).trans hb0.symm)
    have := hγi (hη'η (Ioo_subset_Icc_self hu)) ⟨le_rfl, hη.le⟩ (hyb.trans hγ0.symm)
    linarith [hu.1]
  obtain ⟨c, hc, hyc⟩ := h𝒪.cover _ hyB
  refine ⟨u, ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩, c, hc, hyc, ?_⟩
  have heq : c ∘ γ =ᶠ[𝓝 u] (fun s ↦ c (e.symm (normalRay s))) ∘ τ :=
    Filter.eventually_of_mem hIcc fun s hs ↦ by
      simp only [comp_apply, τ, symm_normalRay_coord (hsub s hs).2]
  obtain ⟨-, -, -, -, hdir⟩ := exists_strictMonoAt_or_strictAntiAt hye hyB hyc
  rw [strictMonoAt_iff_of_eventuallyEq_comp heq (hτc.continuousAt hIcc)
    (Or.inl (hτm.strictMonoAt hIcc)) hdir, iff_true_right (hτm.strictMonoAt hIcc),
    ← isPos_iff h𝒪 hc hye hyB hyc]
  exact isPos_iff_isPos_of_isPreconnected h𝒪 h.isPreconnected_diff_boundary
    (fun z hz ↦ (h.mem z hz.1).1) disjoint_sdiff_left ⟨hyK, hyB⟩ ⟨hz₀K, hz₀B⟩

omit [ChartedSpace (EuclideanHalfSpace 1) M] in
/-- **Which end of an arc a point is.** Let `p` be an end of an arc `K` in the chart `e`, and `τ`
strictly monotone or strictly antitone on `[a, b]`, taking the value `e p` at an endpoint `t` and
values in the coordinates of `K` elsewhere. Then `p` is the supremum end of `K` exactly when `τ`
increases towards `t`. -/
private theorem IsArcIn.coord_eq_sSup_iff {α β : ℝ} {K : Set M} (h : IsArcIn e α β K) {p : M}
    (hpend : (e p).val 0 = sInf ((fun z ↦ (e z).val 0) '' K) ∨
      (e p).val 0 = sSup ((fun z ↦ (e z).val 0) '' K))
    {τ : ℝ → ℝ} {a b t : ℝ} (hab : a < b) (ht : t = a ∨ t = b)
    (hmono : StrictMonoOn τ (Icc a b) ∨ StrictAntiOn τ (Icc a b)) (htt : τ t = (e p).val 0)
    (hI : ∀ s ∈ Icc a b, s ≠ t → τ s ∈ (fun z ↦ (e z).val 0) '' K) :
    (e p).val 0 = sSup ((fun z ↦ (e z).val 0) '' K) ↔ (t = b ↔ StrictMonoOn τ (Icc a b)) := by
  set I := (fun z ↦ (e z).val 0) '' K
  have ha' : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb' : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hexcl : ¬(StrictMonoOn τ (Icc a b) ∧ StrictAntiOn τ (Icc a b)) :=
    Set.Nontrivial.not_strictMonoOn_and_strictAntiOn ⟨a, ha', b, hb', hab.ne⟩
  -- A value of the arc below the coordinate of `p` makes it the supremum, one above prevents it.
  have hsup : ∀ x ∈ I, x < (e p).val 0 → (e p).val 0 = sSup I := fun x hx hlt ↦
    hpend.resolve_left fun hinf ↦ by linarith [csInf_le h.bddBelow hx]
  have hnsup : ∀ x ∈ I, (e p).val 0 < x → (e p).val 0 ≠ sSup I := fun x hx hlt hs ↦ by
    linarith [le_csSup h.bddAbove hx]
  rcases ht with rfl | rfl <;> rcases hmono with hm | hm
  · exact iff_of_false (hnsup _ (hI b hb' hab.ne') (htt ▸ hm ha' hb' hab))
      fun h' ↦ hab.ne (h'.2 hm)
  · exact iff_of_true (hsup _ (hI b hb' hab.ne') (htt ▸ hm ha' hb' hab))
      ⟨fun h' ↦ absurd h' hab.ne, fun h' ↦ (hexcl ⟨h', hm⟩).elim⟩
  · exact iff_of_true (hsup _ (hI a ha' hab.ne) (htt ▸ hm ha' hb' hab)) ⟨fun _ ↦ hm, fun _ ↦ rfl⟩
  · exact iff_of_false (hnsup _ (hI a ha' hab.ne) (htt ▸ hm ha' hb' hab))
      fun h' ↦ hexcl ⟨h'.1 rfl, hm⟩

/-- **Comparing the orientation in two charts.** Let `[a, b]` be an interval of positive
coordinates of a chart `e'` whose image lies in the domain of a chart `e`, so that the coordinate
`τ` of `e` along it is strictly monotone or strictly antitone. At a point of the image with
coordinate `u ∈ (a, b)`, the orientation is positive for `e'` exactly when its positivity for `e`
agrees with `τ` increasing. -/
private theorem isPos_iff_isPos_iff_strictMonoOn (h𝒪 : IsOrientation 𝒪)
    {e' : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {a b : ℝ} (ha : 0 < a)
    (htarget : ∀ s ∈ Icc a b, normalRay s ∈ e'.target)
    (hγe : ∀ s ∈ Icc a b, e'.symm (normalRay s) ∈ e.source)
    (hmono : StrictMonoOn (fun s ↦ (e (e'.symm (normalRay s))).val 0) (Icc a b) ∨
      StrictAntiOn (fun s ↦ (e (e'.symm (normalRay s))).val 0) (Icc a b)) {u : ℝ}
    (hu : u ∈ Ioo a b) :
    IsPos 𝒪 e' (e'.symm (normalRay u)) ↔ (IsPos 𝒪 e (e'.symm (normalRay u)) ↔
      StrictMonoOn (fun s ↦ (e (e'.symm (normalRay s))).val 0) (Icc a b)) := by
  set τ : ℝ → ℝ := fun s ↦ (e (e'.symm (normalRay s))).val 0
  set y := e'.symm (normalRay u)
  have hIcc : Icc a b ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
  have hye := hγe u (Ioo_subset_Icc_self hu)
  have hye' : y ∈ e'.source := e'.map_target (htarget u (Ioo_subset_Icc_self hu))
  have hyu : (e' y).val 0 = u :=
    coord_symm_normalRay (by linarith [hu.1]) (htarget u (Ioo_subset_Icc_self hu))
  have hyB : y ∉ (𝓡∂ 1).boundary M := fun hB ↦ by
    rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hye', hyu] at hB
    linarith [hu.1]
  obtain ⟨c, hc, hyc⟩ := h𝒪.cover y hyB
  -- Along `e'`, the chart `c` is `c` along `e` composed with `τ`.
  have heq : (fun s ↦ c (e'.symm (normalRay s))) =ᶠ[𝓝 u]
      (fun s ↦ c (e.symm (normalRay s))) ∘ τ :=
    Filter.eventually_of_mem hIcc fun s hs ↦ by
      simp only [comp_apply, τ, symm_normalRay_coord (hγe s hs)]
  have hab : (Icc a b).Nontrivial := ⟨a, left_mem_Icc.2 (hu.1.trans hu.2).le, b,
    right_mem_Icc.2 (hu.1.trans hu.2).le, (hu.1.trans hu.2).ne⟩
  have hτinc : StrictMonoAt τ u ↔ StrictMonoOn τ (Icc a b) := by
    rcases hmono with hm | hm
    · exact iff_of_true (hm.strictMonoAt hIcc) hm
    · exact iff_of_false (fun h' ↦ not_strictMonoAt_and_strictAntiAt ⟨h', hm.strictAntiAt hIcc⟩)
        fun h' ↦ hab.not_strictMonoOn_and_strictAntiOn ⟨h', hm⟩
  obtain ⟨-, -, -, -, hdir⟩ := exists_strictMonoAt_or_strictAntiAt hye hyB hyc
  have hcomp := strictMonoAt_iff_of_eventuallyEq_comp heq
    ((continuousOn_coord.comp (continuousOn_symm_normalRay htarget) hγe).continuousAt hIcc)
    (hmono.imp (·.strictMonoAt hIcc) (·.strictAntiAt hIcc)) hdir
  have hpos' : IsPos 𝒪 e' y ↔ StrictMonoAt (fun s ↦ c (e'.symm (normalRay s))) u := by
    rw [isPos_iff h𝒪 hc hye' hyB hyc, hyu]
  have hpos : IsPos 𝒪 e y ↔ StrictMonoAt (fun s ↦ c (e.symm (normalRay s))) (τ u) :=
    isPos_iff h𝒪 hc hye hyB hyc
  rw [hpos', hpos, ← hτinc]
  exact hcomp

/-- **The orientation at a side of a cut point.** Let `p` be a point outside an arc `K` in the
chart `e` but in its closure, read in another chart `e'` at the coordinate `t`, an endpoint of an
interval `[a, b]` of positive coordinates of `e'` whose other points lie in `K`. Then `p` is the
end of `K` towards which the orientation points, the supremum of the coordinates of `K` when the
orientation is positive for `e`, exactly when the orientation along `e'` points from the side
`[a, b]` towards `p`, that is, when it is positive for `e'` at `p` and `t = b`, or negative and
`t = a`. -/
private theorem IsArcIn.side_iff (h𝒪 : IsOrientation 𝒪)
    [T2Space M] {α β : ℝ} {K : Set M} (h : IsArcIn e α β K) {z₀ : M} (hz₀K : z₀ ∈ K)
    (hz₀B : z₀ ∉ (𝓡∂ 1).boundary M) {e' : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    {p : M} (hpK : p ∉ K) (hpcl : p ∈ closure K) {a b t : ℝ} (ha : 0 < a) (hab : a < b)
    (ht : t = a ∨ t = b) (htarget : ∀ s ∈ Icc a b, normalRay s ∈ e'.target)
    (hp : e'.symm (normalRay t) = p) (hK : ∀ s ∈ Icc a b, s ≠ t → e'.symm (normalRay s) ∈ K) :
    ((e p).val 0 = sSup ((fun z ↦ (e z).val 0) '' K) ↔ IsPos 𝒪 e z₀) ↔ (IsPos 𝒪 e' p ↔ t = b) := by
  obtain ⟨hpe, -, hpend⟩ := h.coord_of_mem_closure hpcl hpK
  have htab : t ∈ Icc a b := by rcases ht with rfl | rfl <;> simp [hab.le]
  have hγe : ∀ s ∈ Icc a b, e'.symm (normalRay s) ∈ e.source := fun s hs ↦ by
    by_cases hst : s = t
    · rw [hst, hp]; exact hpe
    · exact (h.mem _ (hK s hs hst)).1
  -- The coordinate `τ` of `e` along `[a, b]` is strictly monotone or strictly antitone.
  set τ : ℝ → ℝ := fun s ↦ (e (e'.symm (normalRay s))).val 0
  have hτi : InjOn τ (Icc a b) := fun s hs s' hs' hss' ↦ by
    have := congrArg (fun z ↦ (e' z).val 0) (injOn_coord (hγe s hs) (hγe s' hs') hss')
    simpa only [coord_symm_normalRay (ha.le.trans hs.1) (htarget s hs),
      coord_symm_normalRay (ha.le.trans hs'.1) (htarget s' hs')] using this
  have hmono : StrictMonoOn τ (Icc a b) ∨ StrictAntiOn τ (Icc a b) :=
    (continuousOn_coord.comp (continuousOn_symm_normalRay htarget)
      hγe).strictMonoOn_of_injOn_Icc' hab.le hτi
  have claim := h.coord_eq_sSup_iff hpend hab ht hmono (by simp only [τ, hp])
    fun s hs hst ↦ mem_image_of_mem _ (hK s hs hst)
  -- At the midpoint `u` of `[a, b]`, compare the orientation along `e'` and along `e`.
  set u := (a + b) / 2 with hu_def
  have hu : u ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hut : u ≠ t := by rcases ht with rfl | rfl <;> [exact ne_of_gt hu.1; exact ne_of_lt hu.2]
  have hcomp := isPos_iff_isPos_iff_strictMonoOn h𝒪 ha htarget hγe hmono hu
  set y := e'.symm (normalRay u)
  have hyK : y ∈ K := hK u (Ioo_subset_Icc_self hu) hut
  -- The orientation is constant along `K` for `e` and along `e' [a, b]` for `e'`.
  have hSB : Disjoint ((fun s ↦ e'.symm (normalRay s)) '' Icc a b) ((𝓡∂ 1).boundary M) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ hB
    rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (e'.map_target (htarget s hs)),
      coord_symm_normalRay (ha.le.trans hs.1) (htarget s hs)] at hB
    linarith [hs.1]
  have hyB : y ∉ (𝓡∂ 1).boundary M :=
    disjoint_left.1 hSB (mem_image_of_mem _ (Ioo_subset_Icc_self hu))
  have hK₀ : IsPos 𝒪 e y ↔ IsPos 𝒪 e z₀ :=
    isPos_iff_isPos_of_isPreconnected h𝒪 h.isPreconnected_diff_boundary
      (fun z hz ↦ (h.mem z hz.1).1) disjoint_sdiff_left ⟨hyK, hyB⟩ ⟨hz₀K, hz₀B⟩
  have hp' : IsPos 𝒪 e' y ↔ IsPos 𝒪 e' p :=
    isPos_iff_isPos_of_isPreconnected h𝒪
      (isPreconnected_Icc.image _ (continuousOn_symm_normalRay htarget))
      (image_subset_iff.2 fun s hs ↦ e'.map_target (htarget s hs)) hSB
      (mem_image_of_mem _ (Ioo_subset_Icc_self hu)) ⟨t, htab, hp⟩
  rw [claim, ← hK₀, ← hp', hcomp]
  clear * -
  tauto

/-- **The outward end of an arc.** Given an orientation with outward boundary points `Bₒ` and
inward boundary points `Bᵢ`, call outward the side `true` of a cut point `p` if the orientation is
negative at `p` for the chart at `p`, its side `false` if it is positive, and a boundary point if
it lies in `Bₒ`. Then an element of `P × Bool ⊕ ∂M` in an arc is outward exactly when it lies at
the end of the arc towards which the orientation points. -/
private theorem CutData.outward_iff [T2Space M] (h𝒪 : IsOrientation 𝒪)
    {Bₒ Bᵢ : Set M} (hB : (𝓡∂ 1).boundary M = Bₒ ∪ Bᵢ)
    (hBₒ : ∀ b ∈ Bₒ, IsOutward 𝒪 b) (hBᵢ : ∀ b ∈ Bᵢ, IsInward 𝒪 b)
    (D : CutData M) (hBf : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M} {α β : ℝ}
    (h : IsArcIn e α β (D.arcOf ω₀)) {z₀ : M} (hz₀K : z₀ ∈ D.arcOf ω₀)
    (hz₀B : z₀ ∉ (𝓡∂ 1).boundary M) :
    ∀ ω ∈ D.ends hBf.toFinset, D.arcOf ω = D.arcOf ω₀ →
      (Sum.elim (fun pc : M × Bool ↦ IsPos 𝒪 (chartAt (EuclideanHalfSpace 1) pc.1) pc.1 ↔
          pc.2 = false) (· ∈ Bₒ) ω ↔
        ((e (Sum.elim Prod.fst id ω)).val 0 = sSup ((fun z ↦ (e z).val 0) '' D.arcOf ω₀) ↔
          IsPos 𝒪 e z₀)) := by
  have hKP : Disjoint (D.arcOf ω₀) D.P :=
    subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)
  rintro (⟨p, c⟩ | b) hω hK
  · -- A side of a cut point `p`: compare with the chart at `p`.
    have hp : p ∈ D.P := by simpa [CutData.ends] using hω
    have hJ : D.J p c ⊆ D.arcOf ω₀ := hK ▸ D.J_subset_arcOf hp c
    have hpK : p ∉ D.arcOf ω₀ := disjoint_right.1 hKP hp
    have hpcl := closure_mono hJ ((D.sides p hp).mem_closure c)
    have hpB := disjoint_left.1 D.disjoint hp
    obtain ⟨η, hη, hηt, htarget, hJeq⟩ := (D.sides p hp).param
    -- Reduce the goal to the point `p` and its chart `e'`.
    simp only [Sum.elim_inl]
    set e' := chartAt (EuclideanHalfSpace 1) p
    set t := (e' p).val 0
    have hpe' : e'.symm (normalRay t) = p := symm_normalRay_coord (mem_chart_source _ p)
    have ht0 : 0 < t := coord_pos_of_notMem_boundary (mem_chart_source _ p) hpB
    cases c
    · have := h.side_iff h𝒪 hz₀K hz₀B hpK hpcl (by linarith : 0 < t - η)
        (by linarith : t - η < t) (Or.inr rfl)
        (fun s hs ↦ htarget s ⟨hs.1, by linarith [hs.2]⟩) hpe' fun s hs hst ↦
          hJ (by rw [hJeq false]; exact mem_image_of_mem _ ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)
      rw [this, eq_self false, eq_self t]
    · have := h.side_iff h𝒪 hz₀K hz₀B hpK hpcl ht0
        (by linarith : t < t + η) (Or.inl rfl)
        (fun s hs ↦ htarget s ⟨by linarith [hs.1], hs.2⟩) hpe' fun s hs hst ↦
          hJ (by rw [hJeq true]; exact mem_image_of_mem _ ⟨lt_of_le_of_ne hs.1 (Ne.symm hst), hs.2⟩)
      rw [this, iff_false_right (by linarith : t ≠ t + η)]
      simp only [Bool.true_eq_false, iff_false]
  · -- A boundary point `b`, at the infimum end: compare with the path from `b`.
    have hbB : b ∈ (𝓡∂ 1).boundary M := by simpa [CutData.ends] using hω
    have hbK : b ∈ D.arcOf ω₀ := hK ▸ mem_connectedComponentIn (disjoint_right.1 D.disjoint hbB)
    simp only [Sum.elim_inr, id]
    rw [(h.coord_eq_sInf_of_mem_boundary hbK hbB).2, iff_false_left h.sInf_lt_sSup.ne]
    have hBi : b ∈ Bᵢ → IsPos 𝒪 e z₀ := fun hb ↦ by
      obtain ⟨γ, η, hη, hγ0, hγc, hγi, hγo⟩ := hBᵢ b hb
      obtain ⟨s, hs, c, hc, hsc, hiff⟩ :=
        h.exists_strictMonoAt_iff_isPos h𝒪 hbK hbB hz₀K hz₀B hη hγ0 hγc hγi
      exact hiff.1 (hγo s hs c hc hsc)
    have hBo : b ∈ Bₒ → ¬IsPos 𝒪 e z₀ := fun hb hpos ↦ by
      obtain ⟨γ, η, hη, hγ0, hγc, hγi, hγo⟩ := hBₒ b hb
      obtain ⟨s, hs, c, hc, hsc, hiff⟩ :=
        h.exists_strictMonoAt_iff_isPos h𝒪 hbK hbB hz₀K hz₀B hη hγ0 hγc hγi
      exact not_strictMonoAt_and_strictAntiAt ⟨hiff.2 hpos, hγo s hs c hc hsc⟩
    rw [hB] at hbB
    exact ⟨hBo, fun hpos ↦ hbB.resolve_right fun hb ↦ hpos (hBi hb)⟩

/-- **Every arc has exactly one end of each kind.** If, read through the coordinates of an arc,
a property of the sides of cut points and boundary points selects the supremum end or the
infimum end of the arc, then exactly one of the elements in the arc has it. -/
private theorem CutData.card_filter_filter_arcOf_eq_one [T2Space M] (D : CutData M)
    (hBf : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M} (O : M × Bool ⊕ M → Prop)
    [DecidablePred O] {α β : ℝ} (h : IsArcIn e α β (D.arcOf ω₀)) (σ : Prop)
    (hO : ∀ ω ∈ D.ends hBf.toFinset, D.arcOf ω = D.arcOf ω₀ →
        (O ω ↔ ((e (Sum.elim Prod.fst id ω)).val 0 = sSup ((fun z ↦ (e z).val 0) '' D.arcOf ω₀) ↔
          σ))) :
    (((D.ends hBf.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).filter O).card = 1 := by
  classical
  obtain ⟨hinj, himage⟩ := D.injOn_and_image_filter_arcOf hBf h
  set I := (fun z ↦ (e z).val 0) '' D.arcOf ω₀
  set v : M × Bool ⊕ M → ℝ := fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0
  have hne : sInf I ≠ sSup I := h.sInf_lt_sSup.ne
  have htarget : (if σ then sSup I else sInf I) ∈
      ((D.ends hBf.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).image v := by
    rw [himage]; split_ifs <;> simp
  obtain ⟨ω₁, hω₁, hv₁⟩ := Finset.mem_image.1 htarget
  have hiff : ∀ ω ∈ (D.ends hBf.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀),
        O ω ↔ v ω = if σ then sSup I else sInf I := fun ω hω ↦ by
    rw [hO ω (Finset.mem_filter.1 hω).1 (Finset.mem_filter.1 hω).2]
    have hv := Finset.mem_image_of_mem v hω
    rw [himage, Finset.mem_insert, Finset.mem_singleton] at hv
    by_cases hσ : σ <;> rcases hv with hv | hv <;> simp only [v] at hv ⊢ <;>
      simp [hv, hne, hne.symm, hσ]
  rw [Finset.card_eq_one]
  refine ⟨ω₁, Finset.ext fun ω ↦ ?_⟩
  rw [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hω, hOω⟩ ↦ hinj (Finset.mem_coe.2 hω) (Finset.mem_coe.2 hω₁)
    (((hiff ω hω).1 hOω).trans hv₁.symm), by rintro rfl; exact ⟨hω₁, (hiff _ hω₁).2 hv₁⟩⟩

/-- If every arc has exactly one element with a property `Q`, these elements are as many as the
arcs. -/
private theorem CutData.card_filter_eq_card_image (D : CutData M)
    (hBf : ((𝓡∂ 1).boundary M).Finite) (Q : M × Bool ⊕ M → Prop) [DecidablePred Q]
    (hQ : ∀ ω₀ ∈ D.ends hBf.toFinset,
      (((D.ends hBf.toFinset).filter fun ω ↦ D.arcOf ω = D.arcOf ω₀).filter Q).card = 1) :
    ((D.ends hBf.toFinset).filter Q).card = ((D.ends hBf.toFinset).image D.arcOf).card := by
  classical
  set Ω := D.ends hBf.toFinset
  rw [Finset.card_eq_sum_card_fiberwise (f := D.arcOf) (t := Ω.image D.arcOf)
    fun ω hω ↦ Finset.mem_image_of_mem _ (Finset.mem_filter.1 hω).1,
    Finset.card_eq_sum_ones (Ω.image D.arcOf)]
  refine Finset.sum_congr rfl fun K hK ↦ ?_
  obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hK
  rw [← hQ ω₀ hω₀, Finset.filter_filter, Finset.filter_filter]
  simp only [and_comm]

/-- If a property `Q` holds at exactly one of the two sides of each cut point, the elements with
it are the cut points and the boundary points with it. -/
private theorem CutData.card_filter_eq_card_add (D : CutData M)
    (hBf : ((𝓡∂ 1).boundary M).Finite) (Q : M × Bool ⊕ M → Prop) [DecidablePred Q]
    (hQ : ∀ p, (Q (.inl (p, true)) ↔ ¬Q (.inl (p, false)))) :
    ((D.ends hBf.toFinset).filter Q).card =
      D.finite.toFinset.card + (hBf.toFinset.filter fun b ↦ Q (.inr b)).card := by
  rw [CutData.ends, Finset.card_filter, Finset.sum_disjSum, Finset.sum_product,
    Finset.card_filter, Finset.card_eq_sum_ones D.finite.toFinset]
  congr 1
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Fintype.sum_bool]
  by_cases h : Q (.inl (p, true)) <;> simp [h, (hQ p).1, (hQ p).not.1]

/-- **A boundary point is not both outward and inward.** The charts of an orientation cannot
decrease along one injective path leaving a boundary point and increase along another. -/
private theorem CutData.not_and_of_mem_boundary (D : CutData M)
    (h𝒪 : IsOrientation 𝒪) {b : M} (hbB : b ∈ (𝓡∂ 1).boundary M) (hBₒ : IsOutward 𝒪 b)
    (hBᵢ : IsInward 𝒪 b) : False := by
  have hbP : b ∉ D.P := disjoint_right.1 D.disjoint hbB
  obtain ⟨e, α, β, h⟩ := D.arc b hbP
  obtain ⟨z₀, hz₀K, hz₀B⟩ := h.nonempty_diff_boundary
  have hbK : b ∈ connectedComponentIn D.Pᶜ b := mem_connectedComponentIn hbP
  obtain ⟨γ, η, hη, hγ0, hγc, hγi, hγo⟩ := hBₒ
  obtain ⟨s, hs, c, hc, hsc, hiff⟩ :=
    h.exists_strictMonoAt_iff_isPos h𝒪 hbK hbB hz₀K hz₀B hη hγ0 hγc hγi
  obtain ⟨γ', η', hη', hγ0', hγc', hγi', hγo'⟩ := hBᵢ
  obtain ⟨s', hs', c', hc', hsc', hiff'⟩ :=
    h.exists_strictMonoAt_iff_isPos h𝒪 hbK hbB hz₀K hz₀B hη' hγ0' hγc' hγi'
  exact not_strictMonoAt_and_strictAntiAt
    ⟨hiff.2 (hiff'.1 (hγo' s' hs' c' hc' hsc')), hγo s hs c hc hsc⟩

/-- **A compact oriented one-dimensional manifold has as many outward as inward boundary
points.** Let `M` be a compact Hausdorff topological manifold modelled on the half-line
`EuclideanHalfSpace 1`. Orient its interior by a set `𝒪` of charts to `ℝ` covering the interior
points, any two of which have a transition map increasing near every common point. Split the
boundary into the points `Bₒ` at which the orientation points outward and the points `Bᵢ` at
which it points inward, detected along an injective path `γ` leaving the boundary point: the
charts of `𝒪` decrease along `γ` at the points of `Bₒ`, and increase along it at the points of
`Bᵢ`. Then `Bₒ` and `Bᵢ` have the same number of elements.

With the outward-first convention, the points of `Bₒ` carry the boundary sign `1` and those of
`Bᵢ` the sign `-1`, so this says that the signed boundary count vanishes. It refines the parity
statement `TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`; for smooth
oriented manifolds the same count is
`TauCeti.ncard_setOf_signBasis_eq_one_eq_ncard_setOf_signBasis_eq_neg_one`. No smoothness of the
atlas is assumed. -/
theorem ModelWithCorners.ncard_eq_ncard_boundary_euclideanHalfSpace_one [CompactSpace M]
    [T2Space M] (hcover : ∀ x ∉ (𝓡∂ 1).boundary M, ∃ c ∈ 𝒪, x ∈ c.source)
    (hcompat : ∀ c ∈ 𝒪, ∀ c' ∈ 𝒪, ∀ x ∈ c.source ∩ c'.source, StrictMonoAt (c' ∘ c.symm) (c x))
    {Bₒ Bᵢ : Set M} (hB : (𝓡∂ 1).boundary M = Bₒ ∪ Bᵢ)
    (hBₒ : ∀ b ∈ Bₒ, ∃ γ : ℝ → M, ∃ η > 0, γ 0 = b ∧ ContinuousOn γ (Icc 0 η) ∧
      InjOn γ (Icc 0 η) ∧ ∀ s ∈ Ioo 0 η, ∀ c ∈ 𝒪, γ s ∈ c.source → StrictAntiAt (c ∘ γ) s)
    (hBᵢ : ∀ b ∈ Bᵢ, ∃ γ : ℝ → M, ∃ η > 0, γ 0 = b ∧ ContinuousOn γ (Icc 0 η) ∧
      InjOn γ (Icc 0 η) ∧ ∀ s ∈ Ioo 0 η, ∀ c ∈ 𝒪, γ s ∈ c.source → StrictMonoAt (c ∘ γ) s) :
    Bₒ.ncard = Bᵢ.ncard := by
  classical
  -- Bundle the hypotheses as `IsOrientation`, `IsOutward` and `IsInward`, which they unfold.
  have h𝒪 : IsOrientation 𝒪 := ⟨hcover, hcompat⟩
  replace hBₒ : ∀ b ∈ Bₒ, IsOutward 𝒪 b := hBₒ
  replace hBᵢ : ∀ b ∈ Bᵢ, IsInward 𝒪 b := hBᵢ
  obtain ⟨D⟩ := nonempty_cutData (M := M)
  have hBf := ModelWithCorners.finite_boundary_euclideanHalfSpace_one (M := M)
  set Ω := D.ends hBf.toFinset
  set O : M × Bool ⊕ M → Prop := Sum.elim (fun pc : M × Bool ↦
    IsPos 𝒪 (chartAt (EuclideanHalfSpace 1) pc.1) pc.1 ↔ pc.2 = false) (· ∈ Bₒ)
  have hbase : ∀ ω ∈ Ω, D.base ω ∉ D.P := fun ω hω ↦
    D.base_notMem (fun y hy ↦ hBf.mem_toFinset.1 hy) hω
  -- Each arc has exactly one outward end and exactly one inward end.
  have hfib : ∀ ω₀ ∈ Ω, ((Ω.filter fun ω ↦ D.arcOf ω = D.arcOf ω₀).filter O).card = 1 ∧
      ((Ω.filter fun ω ↦ D.arcOf ω = D.arcOf ω₀).filter fun ω ↦ ¬O ω).card = 1 := by
    intro ω₀ hω₀
    obtain ⟨e, α, β, h⟩ := D.arc _ (hbase ω₀ hω₀)
    obtain ⟨z₀, hz₀K, hz₀B⟩ := h.nonempty_diff_boundary
    have hO : ∀ ω ∈ Ω, D.arcOf ω = D.arcOf ω₀ → (O ω ↔ ((e (Sum.elim Prod.fst id ω)).val 0 =
        sSup ((fun z ↦ (e z).val 0) '' D.arcOf ω₀) ↔ IsPos 𝒪 e z₀)) :=
      D.outward_iff h𝒪 hB hBₒ hBᵢ hBf h hz₀K hz₀B
    exact ⟨D.card_filter_filter_arcOf_eq_one hBf O h _ hO,
      D.card_filter_filter_arcOf_eq_one hBf (fun ω ↦ ¬O ω) h (¬IsPos 𝒪 e z₀)
        fun ω hω hK ↦ by rw [hO ω hω hK]; tauto⟩
  -- So the outward ends, and the inward ends, are as many as the arcs; each cut point has one
  -- outward and one inward side.
  have h₁ := D.card_filter_eq_card_image hBf O fun ω₀ hω₀ ↦ (hfib ω₀ hω₀).1
  have h₂ := D.card_filter_eq_card_image hBf (fun ω ↦ ¬O ω) fun ω₀ hω₀ ↦ (hfib ω₀ hω₀).2
  rw [D.card_filter_eq_card_add hBf O fun p ↦ by simp only [O, Sum.elim_inl]; tauto] at h₁
  rw [D.card_filter_eq_card_add hBf (fun ω ↦ ¬O ω) fun p ↦ by
    simp only [O, Sum.elim_inl]; tauto] at h₂
  -- The outward boundary points are `Bₒ`, and the inward ones `Bᵢ`.
  have hdisj : ∀ b ∈ Bₒ, b ∉ Bᵢ := fun b hbo hbi ↦
    D.not_and_of_mem_boundary h𝒪 (hB ▸ Or.inl hbo) (hBₒ b hbo) (hBᵢ b hbi)
  have hBₒeq : Bₒ = ↑(hBf.toFinset.filter fun b ↦ O (.inr b)) := by
    ext b
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun hb ↦ ⟨hB ▸ Or.inl hb, hb⟩, And.right⟩
  have hBᵢeq : Bᵢ = ↑(hBf.toFinset.filter fun b ↦ ¬O (.inr b)) := by
    ext b
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨fun hb ↦ ⟨hB ▸ Or.inr hb, fun hbo ↦ hdisj b hbo hb⟩, fun ⟨hbB, hbo⟩ ↦ ?_⟩
    rw [hB] at hbB
    exact hbB.resolve_left hbo
  rw [hBₒeq, hBᵢeq, ncard_coe_finset, ncard_coe_finset]
  omega

end Orientation

end TauCeti
