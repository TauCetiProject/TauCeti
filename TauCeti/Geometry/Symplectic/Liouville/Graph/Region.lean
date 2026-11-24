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

open Classical in
variable (W) in
/-- The deformation of the region bounded by a Liouville graph onto `W`, given a left inverse `ρ`
of the flow-out `Φ` on its range: at time `τ`, a point `x = Φ(t, s)` outside `W` goes to
`Φ(τ t, s)`, and `W` is fixed. -/
private noncomputable def graphRegionDeformation (Φ : ℝ × S → M) (ρ : M → ℝ × S)
    (q : unitInterval × M) : M :=
  if q.2 ∈ W then q.2 else Φ ((q.1 : ℝ) * (ρ q.2).1, (ρ q.2).2)

omit [TopologicalSpace M] in
/-- Along the flow-out, the deformation pulls a point back along its trajectory as long as it is
outside `W`, at positive times, and fixes the points of `W`, at nonpositive times. -/
private theorem graphRegionDeformation_apply {Φ : ℝ × S → M} {ρ : M → ℝ × S}
    (hρ : ∀ p, ρ (Φ p) = p) (hΦW : ∀ p, Φ p ∈ W ↔ p.1 ≤ 0) (τ : unitInterval) (p : ℝ × S) :
    graphRegionDeformation W Φ ρ (τ, Φ p) = Φ (min p.1 ((τ : ℝ) * p.1), p.2) := by
  have h₁ := unitInterval.le_one τ
  rw [graphRegionDeformation, hρ]
  split_ifs with hp
  · rw [min_eq_left (by nlinarith [(hΦW p).1 hp])]
  · rw [min_eq_right (by nlinarith [not_le.1 (mt (hΦW p).2 hp)])]

omit [TopologicalSpace M] in
/-- The deformation fixes the points of `W`. -/
private theorem graphRegionDeformation_of_mem {Φ : ℝ × S → M} {ρ : M → ℝ × S} (τ : unitInterval)
    {x : M} (hx : x ∈ W) : graphRegionDeformation W Φ ρ (τ, x) = x :=
  ite_eq_left hx

/-- The deformation keeps the region, ends in `W` and starts at the identity. -/
private theorem graphRegionDeformation_spec {Φ : ℝ × S → M} {ρ : M → ℝ × S}
    (hΦdef : Φ = fun p ↦ flowOf Z p.1 (ι p.2)) (hρ : ∀ p, ρ (Φ p) = p)
    (hΦW : ∀ p, Φ p ∈ W ↔ p.1 ≤ 0)
    (hU : ∀ x ∈ liouvilleGraphRegion Z W ι f, x ∉ W →
      ∃ t s, 0 < t ∧ t < Real.log (f s) ∧ Φ (t, s) = x)
    {x : M} (hx : x ∈ liouvilleGraphRegion Z W ι f) (τ : unitInterval) :
    graphRegionDeformation W Φ ρ (τ, x) ∈ liouvilleGraphRegion Z W ι f ∧
      graphRegionDeformation W Φ ρ (0, x) ∈ W ∧ graphRegionDeformation W Φ ρ (1, x) = x := by
  by_cases hxW : x ∈ W
  · simp only [graphRegionDeformation_of_mem _ hxW]
    exact ⟨hx, hxW, trivial⟩
  obtain ⟨t, s, ht₀, ht, rfl⟩ := hU x hx hxW
  simp only [graphRegionDeformation_apply hρ hΦW]
  refine ⟨?_, (hΦW _).2 (by simp [ht₀.le]), by simp⟩
  subst hΦdef
  exact flowOf_mem_liouvilleGraphRegion ((min_le_left _ _).trans_lt ht)

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

/-- The deformation is continuous on the region: near a point of the interior of `W` it is the
identity, and on the open flow-out of the times `t < log f(s)` it is the continuous map
`Φ(t, s) ↦ Φ(min(t, τ t), s)`, read through the left inverse `ρ`. -/
private theorem continuous_graphRegionDeformation {Φ : ℝ × S → M} {ρ : M → ℝ × S}
    (hΦdef : Φ = fun p ↦ flowOf Z p.1 (ι p.2)) (hemb : IsOpenEmbedding Φ)
    (hρ : ∀ p, ρ (Φ p) = p) (hρc : ContinuousOn ρ (range Φ)) (hΦW : ∀ p, Φ p ∈ W ↔ p.1 ≤ 0)
    (hιW : range ι = frontier W) (hf : Continuous f) (hf₁ : ∀ s, 1 < f s) :
    Continuous fun q : unitInterval × liouvilleGraphRegion Z W ι f ↦
      graphRegionDeformation W Φ ρ (q.1, q.2) := by
  subst hΦdef
  have hval : Continuous fun q : unitInterval × liouvilleGraphRegion Z W ι f ↦ (q.2 : M) :=
    continuous_subtypeVal.comp continuous_snd
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  rcases (liouvilleGraphRegion_eq_interior_union hιW hf₁).subset q.2.property with hq | hq
  · -- Near a point of the interior of `W`, the deformation is the identity.
    refine hval.continuousAt.congr (Filter.eventuallyEq_of_mem
      ((isOpen_interior.preimage hval).mem_nhds hq) fun q' hq' ↦ ?_)
    exact (ite_eq_left (interior_subset hq')).symm
  · -- On the open flow-out it is read through the left inverse of `Φ`.
    have hopen : IsOpen ((fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) ''
        {p | p.1 < Real.log (f p.2)}) :=
      hemb.isOpenMap _ (isOpen_setOf_lt_log hf hf₁)
    have hρq : ContinuousAt (fun q' : unitInterval × liouvilleGraphRegion Z W ι f ↦ ρ q'.2) q :=
      (hρc.continuousAt (hemb.isOpen_range.mem_nhds (image_subset_range _ _ hq))).comp
        (f := fun q' : unitInterval × liouvilleGraphRegion Z W ι f ↦ (q'.2 : M))
        hval.continuousAt
    have hmin : ContinuousAt (fun q' : unitInterval × liouvilleGraphRegion Z W ι f ↦
        min (ρ q'.2).1 ((q'.1 : ℝ) * (ρ q'.2).1)) q :=
      hρq.fst.min ((continuous_subtypeVal.comp continuous_fst).continuousAt.mul hρq.fst)
    have hcont := ContinuousAt.comp (g := fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2))
      hemb.continuous.continuousAt (hmin.prodMk hρq.snd)
    refine hcont.congr (Filter.eventuallyEq_of_mem ((hopen.preimage hval).mem_nhds hq)
      fun q' hq' ↦ ?_)
    obtain ⟨p, -, hp⟩ := hq'
    have hp' : flowOf Z p.1 (ι p.2) = (q'.2 : M) := hp
    have hG := graphRegionDeformation_apply (W := W) hρ hΦW q'.1 p
    simp only at hG
    rw [Function.comp_apply, ← hp', hρ p]
    exact hG.symm

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

/-- The flow-out `(t, s) ↦ φ_t(ι s)` of a continuous map is continuous. -/
private theorem continuous_flowOf_comp (hι : Continuous ι) :
    Continuous fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2) := by
  have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  rw [flowOf_eq_globalFlow hZs hc]
  exact (contMDiff_globalFlow_uncurry hc le_rfl hZs).continuous.comp
    (continuous_fst.prodMk (hι.comp continuous_snd))

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
  have hΦ := h.continuous_flowOf_comp hZ hc hι
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
  have hK := (isCompact_setOf_nonneg_le_log hf hf₀).image (h.continuous_flowOf_comp hZ hc hι)
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
of one dimension less, and `f > 1` continuous. Then there is a retraction `r` of the region bounded
by the Liouville graph of `f` onto `W`, and a homotopy from its composite with the inclusion to the
identity that fixes `W` pointwise: a point `φ_t(ι s)` outside `W` moves along its trajectory,
through `φ_{τ t}(ι s)`, `τ ∈ [0, 1]`. -/
theorem exists_liouvilleGraphRegion_deformation [IsManifold J (⊤ : ℕ∞) S]
    [BoundarylessManifold J S] (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hιinj : Injective ι) (hιW : range ι = frontier W)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) (hf : Continuous f) (hf₁ : ∀ s, 1 < f s) :
    ∃ r : C(liouvilleGraphRegion Z W ι f, W),
      (∀ x, r (ContinuousMap.inclusion subset_liouvilleGraphRegion x) = x) ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((ContinuousMap.inclusion subset_liouvilleGraphRegion).comp r)
        (ContinuousMap.id _) {x | (x : M) ∈ W}) := by
  have hιW' (s : S) : ι s ∈ frontier W := hιW ▸ mem_range_self s
  rcases isEmpty_or_nonempty S with hS | hS
  · -- Without boundary points the region is `W` itself.
    have hUW (x : liouvilleGraphRegion Z W ι f) : (x : M) ∈ W := by
      obtain hx | ⟨-, s, -⟩ := mem_liouvilleGraphRegion.1 x.property
      exacts [hx, isEmptyElim s]
    let r : C(liouvilleGraphRegion Z W ι f, W) :=
      ⟨fun x ↦ ⟨x, hUW x⟩, continuous_subtypeVal.subtype_mk _⟩
    have hr : (ContinuousMap.inclusion subset_liouvilleGraphRegion).comp r =
        ContinuousMap.id _ := by
      ext; rfl
    exact ⟨r, fun _ ↦ rfl, ⟨hr ▸ ContinuousMap.HomotopyRel.refl _ _⟩⟩
  set Φ : ℝ × S → M := fun p ↦ flowOf Z p.1 (ι p.2) with hΦdef
  have hemb : IsOpenEmbedding Φ := h.isOpenEmbedding_flowOf_comp hZ hc hι himm hιinj hιW' hdim
  have hΦW (p : ℝ × S) : Φ p ∈ W ↔ p.1 ≤ 0 := h.flowOf_mem_iff_of_mem_frontier hZ hc (hιW' p.2)
  -- A left inverse of the flow-out, continuous on its open range.
  set e := hemb.toOpenPartialHomeomorph Φ
  have hρ (p : ℝ × S) : e.symm (Φ p) = p := hemb.toOpenPartialHomeomorph_left_inv Φ
  have hρc : ContinuousOn e.symm (range Φ) := by
    rw [← IsOpenEmbedding.toOpenPartialHomeomorph_target Φ hemb]
    exact e.continuousOn_symm
  set G := graphRegionDeformation W Φ e.symm
  have hGW (τ : unitInterval) {x : M} (hx : x ∈ W) : G (τ, x) = x :=
    graphRegionDeformation_of_mem τ hx
  have hG (x : liouvilleGraphRegion Z W ι f) (τ : unitInterval) :
      G (τ, x) ∈ liouvilleGraphRegion Z W ι f ∧ G (0, x) ∈ W ∧ G (1, x) = x :=
    graphRegionDeformation_spec hΦdef hρ hΦW
      (fun _ hx hxW ↦ h.exists_flowOf_eq_of_mem_liouvilleGraphRegion hZ hc hιW' hx hxW)
      x.property τ
  have hGc : Continuous fun q : unitInterval × liouvilleGraphRegion Z W ι f ↦ G (q.1, q.2) :=
    continuous_graphRegionDeformation hΦdef hemb hρ hρc hΦW hιW hf hf₁
  refine ⟨⟨fun x ↦ ⟨G (0, x), (hG x 0).2.1⟩, (hGc.comp (Continuous.prodMk_right 0)).subtype_mk _⟩,
    fun x ↦ Subtype.ext (hGW 0 x.property), ⟨?_⟩⟩
  exact
    { toFun := fun q ↦ ⟨G (q.1, q.2), (hG q.2 q.1).1⟩
      continuous_toFun := hGc.subtype_mk _
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun x ↦ Subtype.ext (hG x 0).2.2
      prop' := fun τ x hx ↦ Subtype.ext ((hGW τ hx).trans (hGW 0 hx).symm) }

/-- **The inclusion of the Liouville domain into the region bounded by a Liouville graph is a
homotopy equivalence.** Under the hypotheses of
`TauCeti.IsLiouvilleDomain.exists_liouvilleGraphRegion_deformation`, there is a homotopy
equivalence between `W` and the region bounded by the Liouville graph of `f` whose forward map is
the inclusion. -/
theorem exists_liouvilleGraphRegion_homotopyEquiv [IsManifold J (⊤ : ℕ∞) S]
    [BoundarylessManifold J S] (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hιinj : Injective ι) (hιW : range ι = frontier W)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) (hf : Continuous f) (hf₁ : ∀ s, 1 < f s) :
    ∃ e : ContinuousMap.HomotopyEquiv W (liouvilleGraphRegion Z W ι f),
      ∀ x : W, (e x : M) = x := by
  obtain ⟨r, hr, ⟨F⟩⟩ :=
    h.exists_liouvilleGraphRegion_deformation hZ hc hι himm hιinj hιW hdim hf hf₁
  exact ⟨.ofDeformationRetraction (.inclusion subset_liouvilleGraphRegion) r hr
    (ContinuousMap.HomotopicRel.homotopic ⟨F⟩), fun x ↦ by
      rw [ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply]; rfl⟩

end IsLiouvilleDomain

end TauCeti
