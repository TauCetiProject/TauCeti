/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
import TauCeti.Topology.ConnectedComponents

/-!
# Compact one-dimensional manifolds have an even number of boundary points

Let `M` be a compact Hausdorff topological manifold modelled on the half-line
`EuclideanHalfSpace 1`. This file proves that its boundary `(𝓡∂ 1).boundary M` is finite and has
an even number of points. No smoothness of the atlas is assumed.

This is the parity fact behind the classical proof that the Morse boundary squares to zero. There,
the compactified spaces of index-two trajectories are compact one-dimensional manifolds whose
boundary points are the broken trajectories, so the broken trajectories come in pairs; their
parity is exactly the criterion of `TauCeti.morseBoundary_comp_morseBoundary_eq_zero_iff`. The
gluing charts of such a compactification are only homeomorphisms, which is why the statement here
is topological.

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

## Main results

* `TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff`: a point is a boundary point
  exactly when some, equivalently any, chart around it reads it with coordinate `0`.
* `TauCeti.ModelWithCorners.finite_boundary_euclideanHalfSpace_one`: a compact one-dimensional
  manifold has finitely many boundary points.
* `TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`: a compact Hausdorff
  one-dimensional manifold has an even number of boundary points.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  Appendix (the classification of one-manifolds, and its corollary that the boundary of a compact
  one-manifold has an even number of points).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactified trajectory spaces as compact one-manifolds with boundary).
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold

open TauCeti.EuclideanHalfSpace

namespace TauCeti

/-- A point of `[t - δ, t + δ]` lies within `δ` of `t`. -/
private theorem abs_sub_le_of_mem_Icc {s t δ : ℝ} (hs : s ∈ Icc (t - δ) (t + δ)) : |s - t| ≤ δ :=
  abs_sub_le_iff.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩

section Chart

variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- Reading the point of the normal ray at height `s ≥ 0` back through a chart gives `s`. -/
private theorem coord_symm_normalRay {s : ℝ} (hs : 0 ≤ s) (h : normalRay s ∈ e.target) :
    (e (e.symm (normalRay s))).1 0 = s := by
  rw [e.right_inv h, normalRay_coe_apply, max_eq_left hs]

/-- A point of a chart domain is recovered from its normal coordinate. -/
private theorem symm_normalRay_coord {y : M} (hy : y ∈ e.source) :
    e.symm (normalRay ((e y).1 0)) = y := by
  rw [normalRay_normalCoord, e.left_inv hy]

private theorem injOn_coord : InjOn (fun y ↦ (e y).1 0) e.source := fun y hy z hz h ↦ by
  rw [← symm_normalRay_coord hy, ← symm_normalRay_coord hz]
  exact congrArg (fun s ↦ e.symm (normalRay s)) h

private theorem continuousOn_coord : ContinuousOn (fun y ↦ (e y).1 0) e.source := by
  have h : Continuous fun t : EuclideanHalfSpace 1 ↦ t.1 0 := by fun_prop
  exact h.comp_continuousOn e.continuousOn

private theorem continuousOn_symm_normalRay {S : Set ℝ} (h : ∀ s ∈ S, normalRay s ∈ e.target) :
    ContinuousOn (fun s ↦ e.symm (normalRay s)) S :=
  e.continuousOn_symm.comp continuous_normalRay.continuousOn h

/-- The normal coordinate of a chart maps open sets to relatively open subsets of `[0, ∞)`: around
the coordinate of a point of an open set `V` inside the chart domain there is an interval, of
radius smaller than the coordinate itself when that is positive, whose points all come from `V`. -/
private theorem exists_coord_nhds {V : Set M} (hV : IsOpen V) (hVe : V ⊆ e.source) {y : M}
    (hy : y ∈ V) : ∃ ε > 0, (0 < (e y).1 0 → ε < (e y).1 0) ∧
      ∀ s, |s - (e y).1 0| ≤ ε → normalRay s ∈ e.target ∧ e.symm (normalRay s) ∈ V := by
  set c := (e y).1 0
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
    {y : M} (hy : y ∈ e.source) (hy' : y ∈ e'.source) (h : (e y).1 0 = 0) :
    (e' y).1 0 = 0 := by
  by_contra hne
  set c := (e' y).1 0
  have hc : 0 < c := lt_of_le_of_ne (e' y).2 (Ne.symm hne)
  have hV : IsOpen (e.source ∩ e'.source) := e.open_source.inter e'.open_source
  obtain ⟨ε, hε, -, hεV⟩ := exists_coord_nhds hV inter_subset_left ⟨hy, hy'⟩
  rw [h] at hεV
  -- The points of the common domain with `e`-coordinate below `ε`.
  set O := e.source ∩ e'.source ∩ (fun z ↦ (e z).1 0) ⁻¹' Iio ε
  have hO : IsOpen O :=
    (continuousOn_coord.mono inter_subset_left).isOpen_inter_preimage hV isOpen_Iio
  obtain ⟨η, hη, hηc, hηO⟩ :=
    exists_coord_nhds (e := e') hO (fun z hz ↦ hz.1.2) ⟨⟨hy, hy'⟩, by simp [h, hε]⟩
  replace hηc : η < c := hηc hc
  -- The `e'`-coordinate as a function of the `e`-coordinate, on `[0, ε)`.
  set g : ℝ → ℝ := fun s ↦ (e' (e.symm (normalRay s))).1 0
  have hmem : ∀ s ∈ Ico 0 ε, normalRay s ∈ e.target ∧ e.symm (normalRay s) ∈ e.source ∩ e'.source :=
    fun s hs ↦ hεV s (by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2.le)
  have hcont : ContinuousOn g (Ico 0 ε) :=
    continuousOn_coord.comp (continuousOn_symm_normalRay fun s hs ↦ (hmem s hs).1)
      fun s hs ↦ (hmem s hs).2.2
  have hinj : InjOn g (Ico 0 ε) := fun s hs s' hs' hss' ↦ by
    have := injOn_coord (hmem s hs).2.2 (hmem s' hs').2.2 hss'
    rw [← coord_symm_normalRay hs.1 (hmem s hs).1, ← coord_symm_normalRay hs'.1 (hmem s' hs').1]
    exact congrArg (fun z ↦ (e z).1 0) this
  have hg0 : g 0 = c := by
    have : normalRay 0 = e y := by rw [← normalRay_normalCoord (e y), h]
    simp only [g, this, e.left_inv hy, c]
  -- Every `e'`-coordinate near `c` is a value of `g` at a positive `e`-coordinate.
  have hval : ∀ s', |s' - c| ≤ η → s' ≠ c → ∃ s ∈ Ioo 0 ε, g s = s' := by
    intro s' hs' hs'c
    have hs'0 : 0 ≤ s' := by linarith [abs_le.1 hs']
    obtain ⟨ht, hO'⟩ := hηO s' hs'
    refine ⟨(e (e'.symm (normalRay s'))).1 0, ⟨?_, hO'.2⟩, ?_⟩
    · refine lt_of_le_of_ne (e _).2 fun h0 ↦ hs'c ?_
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
    y ∈ (𝓡∂ 1).boundary M ↔ (e y).1 0 = 0 := by
  have hy' := mem_chart_source (EuclideanHalfSpace 1) y
  rw [ModelWithCorners.boundary, mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, extChartAt_coe,
    comp_apply, modelWithCornersEuclideanHalfSpace_toFun, eq_comm]
  exact ⟨coord_eq_zero_of_coord_eq_zero hy' hy, coord_eq_zero_of_coord_eq_zero hy hy'⟩

/-- A point of a chart domain which is not a boundary point has positive coordinate. -/
private theorem coord_pos_of_notMem_boundary {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    {y : M} (hy : y ∈ e.source) (h : y ∉ (𝓡∂ 1).boundary M) : 0 < (e y).1 0 :=
  lt_of_le_of_ne (e y).2
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
  mem : ∀ z ∈ K, z ∈ e.source ∧ (e z).1 0 ∈ Icc α β

private theorem IsArcIn.image_subset_Icc (h : IsArcIn e α β K) :
    (fun z ↦ (e z).1 0) '' K ⊆ Icc α β :=
  image_subset_iff.2 fun z hz ↦ (h.mem z hz).2

private theorem IsArcIn.isConnected_image (h : IsArcIn e α β K) :
    IsConnected ((fun z ↦ (e z).1 0) '' K) :=
  ⟨h.nonempty.image _, h.isPreconnected.image _ (continuousOn_coord.mono fun z hz ↦ (h.mem z hz).1)⟩

private theorem IsArcIn.bddBelow (h : IsArcIn e α β K) : BddBelow ((fun z ↦ (e z).1 0) '' K) :=
  ⟨α, fun _ hs ↦ (h.image_subset_Icc hs).1⟩

private theorem IsArcIn.bddAbove (h : IsArcIn e α β K) : BddAbove ((fun z ↦ (e z).1 0) '' K) :=
  ⟨β, fun _ hs ↦ (h.image_subset_Icc hs).2⟩

/-- A point of the chart domain lies in an arc exactly when its coordinate is a coordinate of the
arc. -/
private theorem IsArcIn.mem_iff (h : IsArcIn e α β K) {z : M} (hz : z ∈ e.source) :
    z ∈ K ↔ (e z).1 0 ∈ (fun z ↦ (e z).1 0) '' K :=
  ⟨mem_image_of_mem _, fun ⟨w, hw, hwz⟩ ↦ injOn_coord (h.mem w hw).1 hz hwz ▸ hw⟩

/-- An arc is the image of its coordinates under the inverse chart. -/
private theorem IsArcIn.image_symm_normalRay (h : IsArcIn e α β K) :
    (fun s ↦ e.symm (normalRay s)) '' ((fun z ↦ (e z).1 0) '' K) = K := by
  rw [image_image]
  exact (image_congr fun z hz ↦ symm_normalRay_coord (h.mem z hz).1).trans (image_id' K)

/-- The coordinates of an arc form a relatively open subset of `[0, ∞)`. -/
private theorem IsArcIn.exists_nhds (h : IsArcIn e α β K) {z : M} (hz : z ∈ K) :
    ∃ ε > 0, (0 < (e z).1 0 → ε < (e z).1 0) ∧
      ∀ s, 0 ≤ s → |s - (e z).1 0| ≤ ε → s ∈ (fun z ↦ (e z).1 0) '' K := by
  obtain ⟨ε, hε, hεz, hs⟩ := exists_coord_nhds h.isOpen (fun w hw ↦ (h.mem w hw).1) hz
  exact ⟨ε, hε, hεz, fun s hs0 hsz ↦ ⟨_, (hs s hsz).2, coord_symm_normalRay hs0 (hs s hsz).1⟩⟩

/-- The supremum of the coordinates of an arc is not attained. -/
private theorem IsArcIn.sSup_notMem (h : IsArcIn e α β K) :
    sSup ((fun z ↦ (e z).1 0) '' K) ∉ (fun z ↦ (e z).1 0) '' K := by
  rintro ⟨z, hz, hzb⟩
  obtain ⟨ε, hε, -, hs⟩ := h.exists_nhds hz
  have := le_csSup h.bddAbove (hs ((e z).1 0 + ε) (add_nonneg (e z).2 hε.le)
    (by rw [add_sub_cancel_left, abs_of_pos hε]))
  linarith

/-- The infimum of the coordinates of an arc is attained only at the boundary coordinate `0`. -/
private theorem IsArcIn.sInf_eq_zero_of_mem (h : IsArcIn e α β K)
    (ha : sInf ((fun z ↦ (e z).1 0) '' K) ∈ (fun z ↦ (e z).1 0) '' K) :
    sInf ((fun z ↦ (e z).1 0) '' K) = 0 := by
  obtain ⟨z, hz, hza⟩ := ha
  obtain ⟨ε, hε, hεz, hs⟩ := h.exists_nhds hz
  rw [← hza]
  by_contra hne
  have hεz := hεz (lt_of_le_of_ne (e z).2 (Ne.symm hne))
  have := csInf_le h.bddBelow (hs ((e z).1 0 - ε) (by linarith)
    (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]))
  linarith

private theorem IsArcIn.sInf_lt_sSup (h : IsArcIn e α β K) :
    sInf ((fun z ↦ (e z).1 0) '' K) < sSup ((fun z ↦ (e z).1 0) '' K) := by
  obtain ⟨z, hz⟩ := h.nonempty
  obtain ⟨ε, hε, -, hs⟩ := h.exists_nhds hz
  have h₁ := csInf_le h.bddBelow (mem_image_of_mem (fun z ↦ (e z).1 0) hz)
  have h₂ := le_csSup h.bddAbove (hs ((e z).1 0 + ε) (add_nonneg (e z).2 hε.le)
    (by rw [add_sub_cancel_left, abs_of_pos hε]))
  dsimp only at h₁ h₂
  linarith

private theorem IsArcIn.closure_subset_source [T2Space M] (h : IsArcIn e α β K) :
    closure K ⊆ e.source := by
  have hA : IsCompact ((fun s ↦ e.symm (normalRay s)) '' Icc α β) :=
    isCompact_Icc.image_of_continuousOn (continuousOn_symm_normalRay h.target)
  have hKA : K ⊆ (fun s ↦ e.symm (normalRay s)) '' Icc α β := fun z hz ↦
    ⟨(e z).1 0, (h.mem z hz).2, symm_normalRay_coord (h.mem z hz).1⟩
  refine (closure_minimal hKA hA.isClosed).trans ?_
  rintro _ ⟨s, hs, rfl⟩
  exact e.map_target (h.target s hs)

/-- A point in the closure of an arc but outside it lies in the chart domain, and its coordinate
is an endpoint, not attained by the arc, of the interval of coordinates of the arc. -/
private theorem IsArcIn.coord_of_mem_closure [T2Space M] (h : IsArcIn e α β K) {z : M}
    (hz : z ∈ closure K) (hzK : z ∉ K) :
    z ∈ e.source ∧ (e z).1 0 ∉ (fun z ↦ (e z).1 0) '' K ∧
      ((e z).1 0 = sInf ((fun z ↦ (e z).1 0) '' K) ∨
        (e z).1 0 = sSup ((fun z ↦ (e z).1 0) '' K)) := by
  have hze := h.closure_subset_source hz
  have hzI : (e z).1 0 ∉ (fun z ↦ (e z).1 0) '' K := fun hI ↦ hzK ((h.mem_iff hze).2 hI)
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
    (hc : c = sInf ((fun z ↦ (e z).1 0) '' K) ∨ c = sSup ((fun z ↦ (e z).1 0) '' K))
    (hcI : c ∉ (fun z ↦ (e z).1 0) '' K) :
    ∃ z ∈ closure K, z ∉ K ∧ z ∈ e.source ∧ (e z).1 0 = c := by
  have hne := h.nonempty.image fun z ↦ (e z).1 0
  have hcl : c ∈ closure ((fun z ↦ (e z).1 0) '' K) := by
    rcases hc with rfl | rfl
    exacts [csInf_mem_closure hne h.bddBelow, csSup_mem_closure hne h.bddAbove]
  have hcαβ : c ∈ Icc α β := closure_minimal h.image_subset_Icc isClosed_Icc hcl
  have hIci : (fun z ↦ (e z).1 0) '' K ⊆ Ici 0 := by
    rintro _ ⟨z, -, rfl⟩
    exact (e z).2
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
    (hKδ : ∀ z ∈ K, z ∈ e.source → |(e z).1 0 - t| ≠ δ) {y : M} (hyK : y ∈ K)
    (hy : y ∈ e.source) (hyt : |(e y).1 0 - t| < δ) :
    ∀ z ∈ K, z ∈ e.source ∧ |(e z).1 0 - t| < δ := by
  set W := e.source ∩ (fun z ↦ (e z).1 0) ⁻¹' {s | |s - t| < δ}
  set A := (fun s ↦ e.symm (normalRay s)) '' Icc (t - δ) (t + δ)
  have hIcc : ∀ s ∈ Icc (t - δ) (t + δ), |s - t| ≤ δ := fun _ ↦ abs_sub_le_of_mem_Icc
  have hW : IsOpen W := continuousOn_coord.isOpen_inter_preimage e.open_source
    (isOpen_lt (by fun_prop) continuous_const)
  have hA : IsClosed A := (isCompact_Icc.image_of_continuousOn
    (continuousOn_symm_normalRay fun s hs ↦ htarget s (hIcc s hs))).isClosed
  have hWA : W ⊆ A := fun z hz ↦ by
    have hzδ : |(e z).1 0 - t| < δ := hz.2
    have hzt := abs_sub_lt_iff.1 hzδ
    exact ⟨(e z).1 0, ⟨by linarith, by linarith⟩, symm_normalRay_coord hz.1⟩
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
        ∀ z ∈ connectedComponentIn Pᶜ y, z ∈ e.source ∧ (e z).1 0 ∈ Icc α β := by
  set e : M → OpenPartialHomeomorph M (EuclideanHalfSpace 1) :=
    fun x ↦ chartAt (EuclideanHalfSpace 1) x
  -- Around each point `x`, a closed coordinate interval of radius `δ x` in the chart at `x`.
  have hδ : ∀ x, ∃ δ > 0, (0 < (e x x).1 0 → δ < (e x x).1 0) ∧
      ∀ s, |s - (e x x).1 0| ≤ δ → normalRay s ∈ (e x).target := fun x ↦ by
    obtain ⟨δ, hδ, hδx, h⟩ :=
      exists_coord_nhds (e x).open_source subset_rfl (mem_chart_source _ x)
    exact ⟨δ, hδ, hδx, fun s hs ↦ (h s hs).1⟩
  choose δ hδ hδx hδt using hδ
  -- Finitely many of the open coordinate intervals cover `M`; `P` is the set of their endpoints.
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (e x).source ∩ (fun y ↦ (e x y).1 0) ⁻¹' {s | |s - (e x x).1 0| < δ x})
    (fun x ↦ continuousOn_coord.isOpen_inter_preimage (e x).open_source
      (isOpen_lt (by fun_prop) continuous_const))
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source _ x, by simpa using hδ x⟩)
  set P := ⋃ x ∈ S, {y ∈ (e x).source | |(e x y).1 0 - (e x x).1 0| = δ x}
  refine ⟨P, ?_, ?_, ?_⟩
  · refine S.finite_toSet.biUnion fun x _ ↦ ((((finite_singleton ((e x x).1 0 + δ x)).insert
      ((e x x).1 0 - δ x)).image fun s ↦ (e x).symm (normalRay s)).subset ?_)
    rintro y ⟨hy, hyδ⟩
    refine ⟨(e x y).1 0, ?_, symm_normalRay_coord hy⟩
    rcases (abs_eq (hδ x).le).1 hyδ with h | h
    · exact Or.inr (by rw [mem_singleton_iff]; linarith)
    · exact Or.inl (by linarith)
  · refine disjoint_left.2 fun y hy hyB ↦ ?_
    obtain ⟨x, -, hy, hyδ⟩ := mem_iUnion₂.1 hy
    rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hy] at hyB
    rw [hyB, zero_sub, abs_neg, abs_of_nonneg (e x x).2] at hyδ
    exact (hδx x (hyδ ▸ hδ x)).ne hyδ.symm
  · intro y hyP
    obtain ⟨x, hxS, hy, hyδ⟩ := mem_iUnion₂.1 (hS (mem_univ y))
    have hball := forall_mem_coord_lt_of_isPreconnected (K := connectedComponentIn Pᶜ y)
      (e x x).2 (hδt x) isPreconnected_connectedComponentIn (fun z hz hze hzδ ↦
        absurd (mem_iUnion₂.2 ⟨x, hxS, hze, hzδ⟩ : z ∈ P) (connectedComponentIn_subset _ _ hz))
      (mem_connectedComponentIn hyP) hy hyδ
    refine ⟨e x, (e x x).1 0 - δ x, (e x x).1 0 + δ x, fun s hs ↦ hδt x s
      (abs_sub_le_of_mem_Icc hs), fun z hz ↦ ⟨(hball z hz).1, ?_⟩⟩
    have := abs_sub_lt_iff.1 (hball z hz).2
    exact ⟨by linarith, by linarith⟩

/-- The two sides of a point `p` relative to a set `P`: preconnected sets `J true` and `J false`
avoiding `P`, accumulating at `p`, containing chosen points `q true` and `q false`, and together
exhausting a punctured open neighbourhood `N \ {p}` of `p`. -/
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

/-- An interior point has two sides relative to any finite set: the two half-intervals around it
in a chart. -/
private theorem exists_isSides [T1Space M] {P : Set M} (hP : P.Finite) {p : M}
    (hp : p ∉ (𝓡∂ 1).boundary M) : ∃ J N q, IsSides P p J N q := by
  -- In the chart at `p`, with `t > 0` the coordinate of `p`, the sides are the images of
  -- `(t, t + η]` and `[t - η, t)` for a radius `η` small enough to avoid `P \ {p}` and `0`.
  set e := chartAt (EuclideanHalfSpace 1) p
  have hpe : p ∈ e.source := mem_chart_source _ p
  set t := (e p).1 0
  have ht : 0 < t := coord_pos_of_notMem_boundary hpe hp
  obtain ⟨η, hη, hηt, hηV⟩ := exists_coord_nhds
    (e.open_source.inter (hP.subset sdiff_subset).isClosed.isOpen_compl) inter_subset_left
    ⟨hpe, fun h ↦ h.2 (mem_singleton p)⟩
  replace hηt := hηt ht
  -- On `[t - η, t + η]` the inverse chart is defined and meets `P` only at `p`.
  have hγ : ∀ s ∈ Icc (t - η) (t + η), normalRay s ∈ e.target ∧
      (e (e.symm (normalRay s))).1 0 = s ∧ (e.symm (normalRay s) ∈ P → s = t) := by
    intro s hs
    obtain ⟨hst, hsV⟩ := hηV s (abs_sub_le_of_mem_Icc hs)
    have hcoord := coord_symm_normalRay (by linarith [hs.1]) hst
    refine ⟨hst, hcoord, fun hsP ↦ ?_⟩
    by_contra hne
    exact hsV.2 ⟨hsP, fun hsp ↦ hne (by rw [← hcoord, mem_singleton_iff.1 hsp])⟩
  have hcont := continuousOn_symm_normalRay fun s hs ↦ (hγ s hs).1
  set D : Bool → Set ℝ := fun b ↦ cond b (Ioc t (t + η)) (Ico (t - η) t)
  have hD : ∀ b, D b ⊆ Icc (t - η) (t + η) ∧ t ∉ D b ∧ t ∈ closure (D b) := by
    intro b
    cases b
    · exact ⟨Ico_subset_Icc_self.trans (Icc_subset_Icc_right (by linarith)), fun h ↦ h.2.false,
        by simp [D, closure_Ico (by linarith : t - η ≠ t), hη.le]⟩
    · exact ⟨Ioc_subset_Icc_self.trans (Icc_subset_Icc_left (by linarith)), fun h ↦ h.1.false,
        by simp [D, closure_Ioc (by linarith : t ≠ t + η), hη.le]⟩
  refine ⟨fun b ↦ (fun s ↦ e.symm (normalRay s)) '' D b,
    e.source ∩ (fun y ↦ (e y).1 0) ⁻¹' Ioo (t - η) (t + η),
    fun b ↦ e.symm (normalRay (cond b (t + η) (t - η))), ⟨fun b ↦ ?_, fun b ↦ ?_, fun b ↦ ?_,
    fun b ↦ ?_, ?_, ?_, ⟨hpe, by simpa [t] using hη⟩, ?_⟩⟩
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
    have := congrArg (fun z ↦ (e z).1 0) hss'
    simp only [(hγ s ((hD true).1 hs)).2.1, (hγ s' ((hD false).1 hs')).2.1] at this
    simp only [D, Bool.cond_true, Bool.cond_false, mem_Ioc, mem_Ico] at hs hs'
    linarith
  · exact continuousOn_coord.isOpen_inter_preimage e.open_source isOpen_Ioo
  · rintro z ⟨⟨hze, hzI⟩, hzp⟩
    have hzs : e.symm (normalRay ((e z).1 0)) = z := symm_normalRay_coord hze
    have hst : (e z).1 0 ≠ t := fun h ↦
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
  have hp0 : 0 < (e p).1 0 := coord_pos_of_notMem_boundary hpe (disjoint_left.1 D.disjoint hp)
  obtain ⟨ε, hε, hεp, hεN⟩ :=
    exists_coord_nhds (hs.isOpen.inter e.open_source) inter_subset_right ⟨hs.mem_nhds, hpe⟩
  replace hεp := hεp hp0
  -- The points of coordinates `(e p) ∓ ε` lie in `N \ {p}`, hence on a side, hence in `K`.
  have hK : ∀ s, |s - (e p).1 0| ≤ ε → s ≠ (e p).1 0 → s ∈ (fun z ↦ (e z).1 0) '' K := by
    intro s hs₁ hs₂
    obtain ⟨hst, hsN⟩ := hεN s hs₁
    have hcoord := coord_symm_normalRay (by linarith [(abs_sub_le_iff.1 hs₁).2]) hst
    refine ⟨_, ?_, hcoord⟩
    rcases hs.diff_subset ⟨hsN.1, fun hsp ↦ hs₂ (by rw [← hcoord, mem_singleton_iff.1 hsp])⟩
      with h' | h'
    exacts [htrue h', hfalse h']
  have h₁ := csInf_le h.bddBelow (hK ((e p).1 0 - ε)
    (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]) (by linarith))
  have h₂ := le_csSup h.bddAbove (hK ((e p).1 0 + ε)
    (by rw [add_sub_cancel_left, abs_of_pos hε]) (by linarith))
  rcases hpab with hpa | hpb <;> linarith

/-- A boundary point in an arc has coordinate `0`, which is then the attained infimum of the
coordinates of the arc. -/
private theorem IsArcIn.coord_eq_sInf_of_mem_boundary
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ} {K : Set M}
    (h : IsArcIn e α β K) {y : M} (hyK : y ∈ K) (hyB : y ∈ (𝓡∂ 1).boundary M) :
    (e y).1 0 ∈ (fun z ↦ (e z).1 0) '' K ∧ (e y).1 0 = sInf ((fun z ↦ (e z).1 0) '' K) := by
  have hyI : (e y).1 0 ∈ (fun z ↦ (e z).1 0) '' K := mem_image_of_mem _ hyK
  refine ⟨hyI, le_antisymm ?_ (csInf_le h.bddBelow hyI)⟩
  rw [(ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (h.mem y hyK).1).1 hyB]
  exact le_csInf (h.nonempty.image _) (by rintro _ ⟨z, -, rfl⟩; exact (e z).2)

/-- Each endpoint of the interval of coordinates of a component `K` of the complement of `P` is
the coordinate of a boundary point in `K`, or of a point of `P` one of whose sides has arc `K`. -/
private theorem CutData.exists_of_endpoint [T2Space M] (D : CutData M) {y : M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ}
    (h : IsArcIn e α β (connectedComponentIn D.Pᶜ y)) {c : ℝ}
    (hc : c = sInf ((fun z ↦ (e z).1 0) '' connectedComponentIn D.Pᶜ y) ∨
      c = sSup ((fun z ↦ (e z).1 0) '' connectedComponentIn D.Pᶜ y)) :
    (∃ z ∈ connectedComponentIn D.Pᶜ y, z ∈ (𝓡∂ 1).boundary M ∧ (e z).1 0 = c) ∨
      ∃ p ∈ D.P, ∃ b, D.arcOf (.inl (p, b)) = connectedComponentIn D.Pᶜ y ∧ (e p).1 0 = c := by
  by_cases hcI : c ∈ (fun z ↦ (e z).1 0) '' connectedComponentIn D.Pᶜ y
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

/-- **Every arc has exactly two ends.** Among the sides of the points of `P` and the boundary
points, exactly two lie in any given component of the complement of `P`: the coordinate of the
point of `P` or of the boundary point is a bijection onto the two endpoints of the interval of
coordinates of the arc. -/
private theorem CutData.card_filter_arcOf_eq_two [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) {ω₀ : M × Bool ⊕ M}
    (hω₀ : ω₀ ∈ (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset) :
    (((D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset).filter
      (fun ω ↦ D.arcOf ω = D.arcOf ω₀)).card = 2 := by
  classical
  set Ω := (D.finite.toFinset ×ˢ (Finset.univ : Finset Bool)).disjSum hB.toFinset
  have hbase : ∀ ω ∈ Ω, D.base ω ∉ D.P := fun ω hω ↦
    D.base_notMem (fun y hy ↦ hB.mem_toFinset.1 hy) hω
  obtain ⟨e, α, β, h⟩ := D.arc _ (hbase ω₀ hω₀)
  set K := D.arcOf ω₀
  set I := (fun z ↦ (e z).1 0) '' K
  set v : M × Bool ⊕ M → ℝ := fun ω ↦ (e (Sum.elim Prod.fst id ω)).1 0
  have hKP : Disjoint K D.P :=
    subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)
  -- A side in the arc belongs to a point of `P` with an unattained endpoint as coordinate.
  have hinl : ∀ p c, (.inl (p, c) : M × Bool ⊕ M) ∈ Ω → D.arcOf (.inl (p, c)) = K →
      p ∈ D.P ∧ D.J p c ⊆ K ∧ p ∈ e.source ∧ v (.inl (p, c)) ∉ I ∧
        (v (.inl (p, c)) = sInf I ∨ v (.inl (p, c)) = sSup I) := by
    intro p c hω hK
    have hp : p ∈ D.P := by simpa [Ω] using hω
    have hJ : D.J p c ⊆ K := by rw [← hK]; exact D.J_subset_arcOf hp c
    exact ⟨hp, hJ, h.coord_of_mem_closure (closure_mono hJ ((D.sides p hp).mem_closure c))
      (disjoint_right.1 hKP hp)⟩
  -- A boundary point in the arc has coordinate `0`, the attained infimum.
  have hinr : ∀ y, (.inr y : M × Bool ⊕ M) ∈ Ω → D.arcOf (.inr y) = K →
      y ∈ e.source ∧ v (.inr y) ∈ I ∧ v (.inr y) = sInf I := by
    intro y hω hK
    have hyK : y ∈ K := by rw [← hK]; exact mem_connectedComponentIn (hbase _ hω)
    exact ⟨(h.mem y hyK).1, h.coord_eq_sInf_of_mem_boundary hyK (by simpa [Ω] using hω)⟩
  have hinj : Set.InjOn v (Ω.filter fun ω ↦ D.arcOf ω = K) := by
    rintro (⟨p, c⟩ | y) hω (⟨p', c'⟩ | y') hω' hvv <;>
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
  have himage : (Ω.filter fun ω ↦ D.arcOf ω = K).image v = {sInf I, sSup I} := by
    ext c
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

end Main

end TauCeti
