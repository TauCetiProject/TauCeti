/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Graph.Basic
public import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# The region bounded by a Liouville graph

Let `W ⊆ M` be a Liouville domain (`TauCeti.IsLiouvilleDomain`) whose Liouville field `Z` is
complete, with flow `φ`, and let `ι : S → M` be an injective parametrization of its boundary `∂W`.
For a function `f > 1` on `S`, the Liouville graph `j_f(s) = φ_{log f(s)}(ι s)`
(`TauCeti.liouvilleGraph`) is a hypersurface outside `W` on which the primitive restricts to
`f ι^* α`. The **region bounded by the graph** (`TauCeti.liouvilleGraphRegion`) is

`U_f = W ∪ {φ_t(ι s) | t < log f(s)}`,

the union of `W` with the part of the flow-out of `∂W` below the graph. In the coordinates
`(r, s) = (eᵗ, s)` of the symplectization `((0, ∞) × ∂W, d(r α|∂W))`, which the Liouville flow
embeds in `M`, it is `W` together with the points `1 ≤ r < f(s)`.

This is the domain of the graph construction of Barraud, Damian, Humilière and Oancea in their
proof of Corollary E. Their argument applies an almost existence theorem to the hypersurface
`j_f(S)`, which needs it to bound a relatively compact domain containing `W` that deformation
retracts onto `W`. We prove these properties:

* the graph lies outside the region
  (`TauCeti.IsLiouvilleDomain.liouvilleGraph_notMem_liouvilleGraphRegion`), since the trajectories
  through the boundary are disjoint and leave `W` at positive times;
* the region is open, when `ι` is a smooth injective immersion onto `∂W` of a boundaryless manifold
  of one dimension less (`TauCeti.IsLiouvilleDomain.isOpen_liouvilleGraphRegion`), because the
  flow-out `(t, s) ↦ φ_t(ι s)` is then an open embedding of `ℝ × S`;
* for compact `S`, its closure is the region together with the graph
  (`TauCeti.IsLiouvilleDomain.closure_liouvilleGraphRegion`), it is relatively compact
  (`TauCeti.IsLiouvilleDomain.isCompact_closure_liouvilleGraphRegion`), and its frontier is the
  graph (`TauCeti.IsLiouvilleDomain.frontier_liouvilleGraphRegion`);
* it deformation retracts onto `W`
  (`TauCeti.IsLiouvilleDomain.exists_liouvilleGraphRegion_deformation`), by pulling each point
  `φ_t(ι s)` with `t > 0` back along its trajectory, `φ_{τ t}(ι s)` for `τ ∈ [0, 1]`, and fixing
  `W`; so the inclusion of `W` is a homotopy equivalence
  (`TauCeti.IsLiouvilleDomain.exists_liouvilleGraphRegion_homotopyEquiv`).

The proofs use only the point-set description of the flow-out: a trajectory through the boundary
lies in `W` exactly at nonpositive times
(`TauCeti.IsLiouvilleDomain.flowOf_mem_iff_of_mem_frontier`), and the flow-out is an open
embedding (`TauCeti.IsLiouvilleDomain.isOpenEmbedding_flowOf_comp`). A smooth function with the
graph as a regular level is not constructed here.

## Main definitions

* `TauCeti.liouvilleGraphRegion Z W ι f`: the set `W ∪ {φ_t(ι s) | t < log f(s)}`.

## Main results

* `TauCeti.IsLiouvilleDomain.isOpen_liouvilleGraphRegion`: the region is open.
* `TauCeti.IsLiouvilleDomain.closure_liouvilleGraphRegion`,
  `TauCeti.IsLiouvilleDomain.frontier_liouvilleGraphRegion`: its closure adds the graph, which is
  its frontier.
* `TauCeti.IsLiouvilleDomain.isCompact_closure_liouvilleGraphRegion`: it is relatively compact.
* `TauCeti.IsLiouvilleDomain.exists_liouvilleGraphRegion_deformation`: it deformation retracts
  onto the Liouville domain.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E and its proof (the domain
  bounded by the graph of a contact form in the symplectization of a hypersurface of restricted
  contact type).
-/

public section

open Function Module Set Topology
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x} {W : Set M} {S : Type*} {ι : S → M} {f : S → ℝ}

variable (Z W ι f) in
/-- The **region bounded by the Liouville graph** of `f` over `ι : S → M`: the union of `W` with
the points `φ_t(ι s)` that the flow `φ` of `Z` reaches from `ι s` before the time `log f(s)` of the
graph. For a Liouville domain `W` with complete Liouville field, an injective immersion `ι` of a
compact manifold onto its boundary and `f > 1`, it is an open set bounded by the graph
(`TauCeti.IsLiouvilleDomain.frontier_liouvilleGraphRegion`) which deformation retracts onto `W`
(`TauCeti.IsLiouvilleDomain.exists_liouvilleGraphRegion_deformation`). -/
noncomputable def liouvilleGraphRegion : Set M :=
  W ∪ (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) '' {p | p.1 < Real.log (f p.2)}

@[simp]
theorem mem_liouvilleGraphRegion {x : M} :
    x ∈ liouvilleGraphRegion Z W ι f ↔
      x ∈ W ∨ ∃ t s, t < Real.log (f s) ∧ flowOf Z t (ι s) = x := by
  simp only [liouvilleGraphRegion, mem_union, mem_image, mem_ofPred_eq, Prod.exists]

/-- The region bounded by a Liouville graph over `W` contains `W`. -/
theorem subset_liouvilleGraphRegion : W ⊆ liouvilleGraphRegion Z W ι f :=
  subset_union_left

/-- The point `φ_t(ι s)` lies in the region bounded by the Liouville graph of `f` when
`t < log f(s)`. -/
theorem flowOf_mem_liouvilleGraphRegion {t : ℝ} {s : S} (ht : t < Real.log (f s)) :
    flowOf Z t (ι s) ∈ liouvilleGraphRegion Z W ι f :=
  mem_liouvilleGraphRegion.2 (Or.inr ⟨t, s, ht, rfl⟩)

/-! ### Set-theoretic description -/

/-- For `f > 1`, the region bounded by a Liouville graph over a parametrization `ι` of the boundary
of `W` is the interior of `W` together with the flow-out of the times `t < log f(s)`: every
boundary point `ι s` is the flow-out at the time `0 < log f(s)`. -/
private theorem liouvilleGraphRegion_eq_interior_union (hιW : range ι = frontier W)
    (hf₁ : ∀ s, 1 < f s) :
    liouvilleGraphRegion Z W ι f = interior W ∪
      (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) '' {p | p.1 < Real.log (f p.2)} := by
  refine Subset.antisymm (union_subset (fun x hx ↦ ?_) subset_union_right)
    (union_subset_union_left _ interior_subset)
  by_cases hxi : x ∈ interior W
  · exact Or.inl hxi
  · obtain ⟨s, rfl⟩ : x ∈ range ι := hιW ▸ ⟨subset_closure hx, hxi⟩
    exact Or.inr ⟨(0, s), Real.log_pos (hf₁ s), by simp⟩

/-- The flow-out of the times between the boundary and the graph lies in the region or on the
graph. -/
private theorem union_subset_liouvilleGraphRegion_union :
    W ∪ (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) '' {p | 0 ≤ p.1 ∧ p.1 ≤ Real.log (f p.2)} ⊆
      liouvilleGraphRegion Z W ι f ∪ range (liouvilleGraph Z ι f) := by
  refine union_subset (subset_liouvilleGraphRegion.trans subset_union_left) ?_
  rintro _ ⟨⟨t, s⟩, ⟨-, ht⟩, rfl⟩
  rcases ht.lt_or_eq with ht | ht
  · exact Or.inl (flowOf_mem_liouvilleGraphRegion ht)
  · exact Or.inr ⟨s, by rw [liouvilleGraph_apply, ← ht]⟩

variable [TopologicalSpace S]

/-- The set of times below the graph is open. -/
private theorem isOpen_setOf_lt_log (hf : Continuous f) (hf₁ : ∀ s, 1 < f s) :
    IsOpen {p : ℝ × S | p.1 < Real.log (f p.2)} :=
  isOpen_lt continuous_fst
    ((hf.log fun s ↦ (one_pos.trans (hf₁ s)).ne').comp continuous_snd)

/-- The times between the boundary and the graph form a compact set. -/
private theorem isCompact_setOf_nonneg_le_log [CompactSpace S] (hf : Continuous f)
    (hf₀ : ∀ s, f s ≠ 0) :
    IsCompact {p : ℝ × S | 0 ≤ p.1 ∧ p.1 ≤ Real.log (f p.2)} := by
  have hlog : Continuous fun s ↦ Real.log (f s) := hf.log hf₀
  obtain ⟨m, hm⟩ := (isCompact_range hlog).bddAbove
  refine (isCompact_Icc.prod isCompact_univ).of_isClosed_subset
    ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst (hlog.comp continuous_snd))) fun p hp ↦
    ⟨⟨hp.1, hp.2.trans (hm (mem_range_self p.2))⟩, mem_univ _⟩

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1}

namespace IsLiouvilleDomain

variable (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
  (hc : IsCompleteVectorField Z)
include h hZ hc

omit [TopologicalSpace S] [FiniteDimensional ℝ E] in
/-- **The region outside the domain is swept by the flow-out at positive times.** A point of the
region bounded by a Liouville graph over the boundary of `W` that is not in `W` is `φ_t(ι s)` for a
time `0 < t < log f(s)`. -/
theorem exists_flowOf_eq_of_mem_liouvilleGraphRegion (hιW : ∀ s, ι s ∈ frontier W) {x : M}
    (hx : x ∈ liouvilleGraphRegion Z W ι f) (hxW : x ∉ W) :
    ∃ t s, 0 < t ∧ t < Real.log (f s) ∧ flowOf Z t (ι s) = x := by
  obtain hx | ⟨t, s, ht, rfl⟩ := mem_liouvilleGraphRegion.1 hx
  · exact absurd hx hxW
  · exact ⟨t, s, not_le.1 fun h0 ↦ hxW ((h.flowOf_mem_iff_of_mem_frontier hZ hc (hιW s)).2 h0),
      ht, rfl⟩

omit [TopologicalSpace S] [FiniteDimensional ℝ E] in
/-- **The Liouville graph lies outside the region it bounds.** If `ι` is injective into the
boundary of `W` and `f s > 1`, then `j_f(s)` is not in the region bounded by the Liouville graph of
`f`: it is outside `W`, and it lies on the trajectory through `ι s` at the time `log f(s)` itself.
-/
theorem liouvilleGraph_notMem_liouvilleGraphRegion (hιinj : Injective ι)
    (hιW : ∀ s, ι s ∈ frontier W) {s : S} (hfs : 1 < f s) :
    liouvilleGraph Z ι f s ∉ liouvilleGraphRegion Z W ι f := by
  rw [mem_liouvilleGraphRegion, not_or]
  refine ⟨h.liouvilleGraph_notMem hZ (hc.mem_flowDomain _ _) (hιW s).2 hfs, ?_⟩
  rintro ⟨t, s', ht, hts⟩
  rw [liouvilleGraph_apply] at hts
  obtain ⟨ht', hs'⟩ := Prod.ext_iff.1
    (h.injective_flowOf_comp hZ hc hιinj hιW (a₁ := (t, s')) (a₂ := (Real.log (f s), s)) hts)
  simp only at ht' hs'
  subst ht' hs'
  exact lt_irrefl _ ht

/-! ### Openness -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [ChartedSpace H' S]

/-- **The region bounded by a Liouville graph is open.** Let `ι : S → M` be a smooth injective
immersion onto the boundary of `W` of a boundaryless manifold of one dimension less, and `f > 1`
continuous. Then the region bounded by the Liouville graph of `f` is open: it is the interior of
`W` together with the image of an open set under the flow-out `(t, s) ↦ φ_t(ι s)`, an open
embedding. -/
theorem isOpen_liouvilleGraphRegion [IsManifold J (⊤ : ℕ∞) S] [BoundarylessManifold J S]
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (himm : ∀ s, Injective (mfderiv J I ι s))
    (hιinj : Injective ι) (hιW : range ι = frontier W) (hdim : finrank ℝ E = finrank ℝ E' + 1)
    (hf : Continuous f) (hf₁ : ∀ s, 1 < f s) :
    IsOpen (liouvilleGraphRegion Z W ι f) := by
  rw [liouvilleGraphRegion_eq_interior_union hιW hf₁]
  exact isOpen_interior.union <| (h.isOpenEmbedding_flowOf_comp hZ hc hι himm hιinj
    (fun s ↦ hιW ▸ mem_range_self s) hdim).isOpenMap _ (isOpen_setOf_lt_log hf hf₁)

/-! ### Closure and compactness -/

omit [TopologicalSpace S] [FiniteDimensional ℝ E] in
/-- The region bounded by a Liouville graph lies in `W` together with the flow-out of the times
between the boundary and the graph: the flow-out at negative times stays in `W`. -/
private theorem liouvilleGraphRegion_subset_union (hιW : ∀ s, ι s ∈ frontier W) :
    liouvilleGraphRegion Z W ι f ⊆ W ∪
      (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) '' {p | 0 ≤ p.1 ∧ p.1 ≤ Real.log (f p.2)} := by
  refine union_subset subset_union_left ?_
  rintro _ ⟨⟨t, s⟩, ht, rfl⟩
  rcases le_or_gt t 0 with h0 | h0
  · exact Or.inl ((h.flowOf_mem_iff_of_mem_frontier hZ hc (hιW s)).2 h0)
  · exact Or.inr ⟨(t, s), ⟨h0.le, ht.le⟩, rfl⟩

/-- **The closure of the region bounded by a Liouville graph adds the graph.** If `S` is compact,
`ι` is a continuous map into the boundary of `W` and `f` is continuous and nowhere zero, then the
closure of the region bounded by the Liouville graph of `f` is the region together with the
graph. -/
theorem closure_liouvilleGraphRegion [CompactSpace S] (hι : Continuous ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hf : Continuous f) (hf₀ : ∀ s, f s ≠ 0) :
    closure (liouvilleGraphRegion Z W ι f) =
      liouvilleGraphRegion Z W ι f ∪ range (liouvilleGraph Z ι f) := by
  have hΦ := continuous_flowOf_comp hc ((h.contMDiff_of_interior_eq hZ).of_le (by simp)) hι
  refine Subset.antisymm ((closure_minimal (h.liouvilleGraphRegion_subset_union hZ hc hιW)
    (h.isClosed.union ((isCompact_setOf_nonneg_le_log hf hf₀).image hΦ).isClosed)).trans
    union_subset_liouvilleGraphRegion_union) (union_subset subset_closure ?_)
  -- The graph point `φ_{log f(s)}(ι s)` is a limit of the points `φ_t(ι s)` with `t < log f(s)`.
  rintro _ ⟨s, rfl⟩
  have hs : ContinuousWithinAt (fun t ↦ flowOf Z t (ι s)) (Iio (Real.log (f s)))
      (Real.log (f s)) :=
    (hΦ.comp (continuous_id.prodMk continuous_const)).continuousWithinAt
  rw [liouvilleGraph_apply]
  refine closure_mono ?_ (hs.mem_closure_image (by simp [closure_Iio]))
  rintro _ ⟨t, ht, rfl⟩
  exact flowOf_mem_liouvilleGraphRegion ht

/-- **The region bounded by a Liouville graph is relatively compact.** If `S` is compact, `ι` is a
continuous map into the boundary of `W` and `f` is continuous and nowhere zero, then the closure of
the region bounded by the Liouville graph of `f` is compact. -/
theorem isCompact_closure_liouvilleGraphRegion [CompactSpace S] (hι : Continuous ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hf : Continuous f) (hf₀ : ∀ s, f s ≠ 0) :
    IsCompact (closure (liouvilleGraphRegion Z W ι f)) := by
  have hK := (isCompact_setOf_nonneg_le_log hf hf₀).image
    (continuous_flowOf_comp hc ((h.contMDiff_of_interior_eq hZ).of_le (by simp)) hι)
  exact (h.isCompact.union hK).of_isClosed_subset isClosed_closure
    (closure_minimal (h.liouvilleGraphRegion_subset_union hZ hc hιW)
      (h.isClosed.union hK.isClosed))

/-- **The Liouville graph is the frontier of the region it bounds.** Let `S` be a compact
boundaryless manifold of one dimension less than `M`, `ι : S → M` a smooth injective immersion
onto the boundary of `W`, and `f > 1` continuous. Then the frontier of the region bounded by the
Liouville graph of `f` is the image of the graph. -/
theorem frontier_liouvilleGraphRegion [IsManifold J (⊤ : ℕ∞) S] [BoundarylessManifold J S]
    [CompactSpace S] (hι : ContMDiff J I (⊤ : ℕ∞) ι) (himm : ∀ s, Injective (mfderiv J I ι s))
    (hιinj : Injective ι) (hιW : range ι = frontier W) (hdim : finrank ℝ E = finrank ℝ E' + 1)
    (hf : Continuous f) (hf₁ : ∀ s, 1 < f s) :
    frontier (liouvilleGraphRegion Z W ι f) = range (liouvilleGraph Z ι f) := by
  have hιW' (s : S) : ι s ∈ frontier W := hιW ▸ mem_range_self s
  rw [frontier, (h.isOpen_liouvilleGraphRegion hZ hc hι himm hιinj hιW hdim hf hf₁).interior_eq,
    h.closure_liouvilleGraphRegion hZ hc hι.continuous hιW' hf
      fun s ↦ (one_pos.trans (hf₁ s)).ne', union_sdiff_left, sdiff_eq_left]
  refine disjoint_left.2 ?_
  rintro _ ⟨s, rfl⟩
  exact h.liouvilleGraph_notMem_liouvilleGraphRegion hZ hc hιinj hιW' (hf₁ s)

/-! ### The deformation retraction onto the Liouville domain -/

/-- **The region bounded by a Liouville graph deformation retracts onto the Liouville domain.**
Let `ι : S → M` be a smooth injective immersion onto the boundary of `W` of a boundaryless manifold
of one dimension less, and `f > 1`. Then there is a retraction `r` of the region bounded
by the Liouville graph of `f` onto `W`, and a homotopy from its composite with the inclusion to the
identity that fixes `W` pointwise.

The proof constructs the homotopy by moving a point `φ_t(ι s)` outside `W` along its trajectory,
through `φ_{τ t}(ι s)`, `τ ∈ [0, 1]`; the statement does not record this. -/
theorem exists_liouvilleGraphRegion_deformation [IsManifold J (⊤ : ℕ∞) S]
    [BoundarylessManifold J S] (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hιinj : Injective ι) (hιW : range ι = frontier W)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) (hf₁ : ∀ s, 1 < f s) :
    ∃ r : C(liouvilleGraphRegion Z W ι f, W),
      (∀ x, r (ContinuousMap.inclusion subset_liouvilleGraphRegion x) = x) ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((ContinuousMap.inclusion subset_liouvilleGraphRegion).comp r)
        (ContinuousMap.id _) {x | (x : M) ∈ W}) := by
  have hιW' (s : S) : ι s ∈ frontier W := hιW ▸ mem_range_self s
  have hemb := h.isOpenEmbedding_flowOf_comp hZ hc hι himm hιinj hιW' hdim
  have hΦW (p : ℝ × S) : flowOf Z p.1 (ι p.2) ∈ W ↔ p.1 ≤ 0 :=
    h.flowOf_mem_iff_of_mem_frontier hZ hc (hιW' p.2)
  have hts : {p : ℝ × S | p.1 ≤ 0} ⊆ {p | p.1 < Real.log (f p.2)} :=
    fun p hp ↦ (show p.1 ≤ 0 from hp).trans_lt (Real.log_pos (hf₁ p.2))
  -- Along the flow-out the region is the set of times `t < log f(s)`, and `W` that of `t ≤ 0`.
  have hs : (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) ⁻¹' liouvilleGraphRegion Z W ι f =
      {p | p.1 < Real.log (f p.2)} := by
    refine Subset.antisymm (fun p hp ↦ ?_) fun _ hp ↦ flowOf_mem_liouvilleGraphRegion hp
    obtain hp | ⟨t, s, ht, hp⟩ := mem_liouvilleGraphRegion.1 hp
    · exact hts ((hΦW p).1 hp)
    · rwa [← hemb.injective (a₁ := (t, s)) (a₂ := p) hp]
  -- The rest of the region lies in the interior of `W`.
  have hSV : liouvilleGraphRegion Z W ι f \ range (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) ⊆
      interior W := fun x hx ↦
    ((liouvilleGraphRegion_eq_interior_union hιW hf₁).subset hx.1).resolve_right
      fun hx' ↦ hx.2 (image_subset_range _ _ hx')
  -- In the coordinates `(t, s)` of the flow-out, a time `t > 0` is pulled back to `τ t`.
  have hD : Continuous fun q : unitInterval × (ℝ × S) ↦ (min q.2.1 ((q.1 : ℝ) * q.2.1), q.2.2) := by
    fun_prop
  refine hemb.exists_deformation_of_preimage subset_liouvilleGraphRegion hts hs (Set.ext hΦW)
    isOpen_interior hSV (fun _ hx ↦ interior_subset hx.2)
    ⟨fun p ↦ ⟨(min p.val.1 0, p.val.2), show min _ _ ≤ _ from min_le_right _ _⟩,
      (((continuous_fst.min continuous_const).prodMk continuous_snd).comp
        continuous_subtypeVal).subtype_mk _⟩
    { toFun := fun q ↦ ⟨(min q.2.val.1 ((q.1 : ℝ) * q.2.val.1), q.2.val.2),
        show min _ _ < _ from (min_le_left _ _).trans_lt q.2.property⟩
      continuous_toFun :=
        (hD.comp (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _
      map_zero_left := fun p ↦ Subtype.ext (Prod.ext (by simp) rfl)
      map_one_left := fun p ↦ Subtype.ext (Prod.ext (by simp) rfl)
      prop' := fun τ p hp ↦ ?_ }
  have hp : p.val.1 ≤ 0 := hp
  refine Subtype.ext (Prod.ext ?_ rfl)
  change min p.val.1 ((τ : ℝ) * p.val.1) = min p.val.1 0
  rw [min_eq_left hp, min_eq_left (by nlinarith [unitInterval.le_one τ])]

/-- **The inclusion of the Liouville domain into the region bounded by a Liouville graph is a
homotopy equivalence.** Under the hypotheses of
`TauCeti.IsLiouvilleDomain.exists_liouvilleGraphRegion_deformation`, there is a homotopy
equivalence between `W` and the region bounded by the Liouville graph of `f` whose forward map is
the inclusion. -/
theorem exists_liouvilleGraphRegion_homotopyEquiv [IsManifold J (⊤ : ℕ∞) S]
    [BoundarylessManifold J S] (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hιinj : Injective ι) (hιW : range ι = frontier W)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) (hf₁ : ∀ s, 1 < f s) :
    ∃ e : ContinuousMap.HomotopyEquiv W (liouvilleGraphRegion Z W ι f),
      ∀ x : W, (e x : M) = x := by
  obtain ⟨r, hr, ⟨F⟩⟩ :=
    h.exists_liouvilleGraphRegion_deformation hZ hc hι himm hιinj hιW hdim hf₁
  exact ⟨.ofDeformationRetraction (.inclusion subset_liouvilleGraphRegion) r hr
    (ContinuousMap.HomotopicRel.homotopic ⟨F⟩), fun x ↦ by
      rw [ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply]; rfl⟩

end IsLiouvilleDomain

end TauCeti
