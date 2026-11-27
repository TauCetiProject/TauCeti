/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ChartedSpace
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Boundary
public import TauCeti.Geometry.Manifold.Boundary.Homeomorph
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic

/-!
# Manifold boundary of the realization of a combinatorial manifold

The charted-space structure `IsCombinatorialManifold.realizationChartedSpace` on the weak
realization of a positive-dimensional combinatorial manifold is only a topological manifold with
boundary, so its manifold boundary cannot be determined by taking derivatives. By topological
invariance of the boundary
(`ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional` and
`Homeomorph.isBoundaryPoint_iff`), every half-space chart detects boundary points cleanly.

Proceeding by induction on the dimension `n`, we prove that for any combinatorial
`(n + 1)`-manifold `K`, a point `x : Realization K` is a manifold boundary point if and only if
its carrier `x.val.support` belongs to `K.toPreAbstractSimplicialComplex.manifoldBoundary`.
In particular, the manifold boundary of `Realization K` is
`{x | x.val.support ∈ manifoldBoundary K}`.

We also record the combinatorial specialization for surfaces (`dim = 2`): an edge lies in the
boundary of a combinatorial 2-manifold precisely when it is contained in a unique 2-simplex.

## Main results

* `IsCombinatorialManifold.isBoundaryPoint_realizationChartedSpace_iff`: characterization of
  boundary points of `Realization K` via `manifoldBoundary`.
* `IsCombinatorialManifold.boundary_realizationChartedSpace`:
  `(𝓡∂ (n + 1)).boundary (Realization K) = {x | x.val.support ∈ manifoldBoundary K}`.
* `IsCombinatorialManifold.interior_realizationChartedSpace`:
  `(𝓡∂ (n + 1)).interior (Realization K) = {x | x.val.support ∉ manifoldBoundary K}`.
* `IsCombinatorialManifold.edge_mem_manifoldBoundary_iff`: an edge of a combinatorial
  `2`-manifold lies in `manifoldBoundary` iff it is contained in a unique `2`-simplex.
-/

public section

noncomputable section

open AbstractSimplicialComplex Metric Set Topology TauCeti
open scoped Manifold RealInnerProductSpace

namespace PreAbstractSimplicialComplex

universe u

variable {ι : Type u} [DecidableEq ι]

/-- Restrict a link precomplex `L` to its vertex subtype as an abstract simplicial complex. -/
private def linkComplex {K : AbstractSimplicialComplex ι} (v : ι) :
    AbstractSimplicialComplex
      {w : ι // ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v}} :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex _
    ((link K.toPreAbstractSimplicialComplex {v}).restrict
      {w : ι | ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v}})
    fun w => by
      rw [mem_faces, mem_restrict_iff_map, Finset.map_singleton]
      exact w.property

@[simp]
private theorem map_val_linkComplex {K : AbstractSimplicialComplex ι} (v : ι) :
    (linkComplex (K := K) v).toPreAbstractSimplicialComplex.map Subtype.val =
      link K.toPreAbstractSimplicialComplex {v} := by
  refine map_val_restrict fun τ hτ w hw => ?_
  exact singleton_mem_of_mem hτ hw

/-- The canonical homeomorphism between `Realization (linkComplex v)` and `geometricLink K v`. -/
private def linkComplexHomeomorph {K : AbstractSimplicialComplex ι} (v : ι) :
    Realization (linkComplex (K := K) v) ≃ₜ geometricLink K v := by
  let Labs := linkComplex (K := K) v
  have hmap : Labs.toPreAbstractSimplicialComplex.map (Function.Embedding.subtype _) =
      link K.toPreAbstractSimplicialComplex {v} :=
    map_val_linkComplex (K := K) v
  let r := Labs.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
    (K := Labs) (L := K) (Function.Embedding.subtype _) hmap rfl link_le
  have hcod : {y : Realization K | y.val.support ∈ link K.toPreAbstractSimplicialComplex {v}} =
      geometricLink K v := by
    ext y
    exact (mem_geometricLink_iff K v y).symm
  exact r.trans (Homeomorph.setCongr hcod)

private theorem linkComplexHomeomorph_val {K : AbstractSimplicialComplex ι} (v : ι)
    (z : Realization (linkComplex (K := K) v)) :
    (linkComplexHomeomorph v z).val.val = Finsupp.mapDomain Subtype.val z.val := by
  dsimp [linkComplexHomeomorph]
  exact realizationRelabelingHomeomorph_val _ (Function.Embedding.subtype _) _ rfl link_le z

private theorem linkComplexHomeomorph_support_mem_manifoldBoundary_iff
    {K : AbstractSimplicialComplex ι} (v : ι) (z : Realization (linkComplex (K := K) v)) :
    (linkComplexHomeomorph v z).val.val.support ∈
        manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) ↔
      z.val.support ∈
        manifoldBoundary (linkComplex (K := K) v).toPreAbstractSimplicialComplex := by
  rw [linkComplexHomeomorph_val,
    Finsupp.mapDomain_support_of_injective Subtype.val_injective]
  have hmb : manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) =
      (manifoldBoundary (linkComplex (K := K) v).toPreAbstractSimplicialComplex).map
        (Function.Embedding.subtype _) := by
    conv_lhs => rw [← map_val_linkComplex (K := K) v]
    exact (map_manifoldBoundary _ Subtype.val_injective).symm
  rw [hmb, mem_map_iff]
  constructor
  · rintro ⟨σ, hσ, heq⟩
    have hinj : Function.Injective (Finset.image (Subtype.val :
        {w : ι // ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v}} → ι)) :=
      Finset.image_injective Subtype.val_injective
    rwa [← hinj heq]
  · intro hz
    exact ⟨z.val.support, hz, rfl⟩

private theorem support_starLinkProjection {K : AbstractSimplicialComplex ι} {v : ι}
    (x : puncturedClosedStar K v) :
    (starLinkProjection K v x).val.val.support = x.val.val.support.erase v := by
  ext w
  rw [Finsupp.mem_support_iff, starLinkProjection_apply, Finset.mem_erase,
    Finsupp.mem_support_iff]
  by_cases hwv : w = v
  · simp [hwv]
  · have hlt : x.val.val v < 1 := ((K.mem_puncturedClosedStar v x.val).mp x.property).2
    have hpos : (1 - x.val.val v)⁻¹ ≠ 0 := (inv_pos.mpr (sub_pos.mpr hlt)).ne'
    simp [hwv, mul_eq_zero, hpos]

private theorem mem_manifoldBoundary_of_openStar_lt_one {K : AbstractSimplicialComplex ι}
    {n : ℕ} (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) {v : ι}
    {x : Realization K} (hx : x ∈ K.openStarRealization v) (hlt : x.val v < 1) :
    x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex ↔
      (starLinkProjection K v ⟨x, (K.mem_puncturedClosedStar v x).mpr
        ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩).val.val.support ∈
          manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) := by
  let p₀ : puncturedClosedStar K v := ⟨x, (K.mem_puncturedClosedStar v x).mpr
    ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩
  rw [support_starLinkProjection p₀, ← h.link_manifoldBoundary {v}, mem_link_nonempty]
  have hvsup : v ∈ x.val.support := (K.mem_openStarRealization_iff_mem_support).mp hx
  have hne : (x.val.support.erase v).Nonempty := by
    rw [← support_starLinkProjection p₀, Finsupp.support_nonempty_iff]
    intro h0
    have hsum := Realization.sum_eq_one K (starLinkProjection K v p₀).val
    simp [h0] at hsum
  have hdisj : Disjoint (x.val.support.erase v) {v} :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase v _)
  have hunion : x.val.support.erase v ∪ {v} = x.val.support := by
    rw [Finset.union_singleton, Finset.insert_erase hvsup]
  change _ ↔ (x.val.support.erase v).Nonempty ∧ Disjoint (x.val.support.erase v) {v} ∧
    x.val.support.erase v ∪ {v} ∈ manifoldBoundary K.toPreAbstractSimplicialComplex
  rw [hunion]
  exact ⟨fun hxbd => ⟨hne, hdisj, hxbd⟩, fun h3 => h3.2.2⟩

/-- Pointwise boundary characterization for the realization of a combinatorial `(n + 1)`-manifold:
a point lies on the manifold boundary iff its support lies in `manifoldBoundary`. -/
theorem IsCombinatorialManifold.isBoundaryPoint_realizationChartedSpace_iff :
    ∀ {n : ℕ} {ι : Type u} [DecidableEq ι] {K : AbstractSimplicialComplex ι}
      (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
      (x : Realization K),
      letI := h.realizationChartedSpace
      (𝓡∂ (n + 1)).IsBoundaryPoint x ↔
        x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex
  | n, ι, _, K, h, x => by
    let := h.realizationChartedSpace
    obtain ⟨v, hx⟩ := K.exists_mem_openStarRealization x
    have hvsup : v ∈ x.val.support := (K.mem_openStarRealization_iff_mem_support).mp hx
    have hv : ({v} : Finset ι) ∈ K := singleton_mem_of_mem (support_mem K x) hvsup
    rcases (isCombinatorialManifold_succ_iff.mp h) hv with hsphere | hball
    · -- Interior vertex: `openStarRealization K v` embeds into the open half-space.
      obtain ⟨c, hc, -, -, -⟩ := hsphere.exists_openPartialHomeomorph_openStar_ball
      let j : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
          (EuclideanHalfSpace (n + 1)) :=
        (TauCeti.EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
      have hxs : x ∈ (c.trans j).source := by
        simpa [hc, j] using hx
      rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
        TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff]
      have hpos : 0 < ((c.trans j) x).val 0 := by
        simp [j, TauCeti.EuclideanHalfSpace.interiorEmbedding_coe_apply_zero, Real.exp_pos]
      refine iff_of_false hpos.ne' fun hxbd => ?_
      have hvbd : ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex :=
        singleton_mem_of_mem hxbd hvsup
      exact hsphere.not_isCombinatorialBall (h.singleton_mem_manifoldBoundary_iff.mp hvbd)
    · -- Boundary vertex: split by `n = 0` vs `n = m + 1`.
      cases n with
      | zero =>
        obtain ⟨c, hc, -, -, hrad⟩ := hball.exists_openPartialHomeomorph_openStar_halfBall
        have hxs : x ∈ c.source := hc ▸ hx
        rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
          TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff]
        have hcoord : (c x).val 0 = 0 ↔ x.val v = 1 := by
          rw [← TauCeti.EuclideanHalfSpace.eq_zero_iff]
          have hnorm : ‖(c x).val‖ = 1 - x.val v := hrad ⟨x, hx⟩
          constructor
          · intro hcz
            rw [hcz] at hnorm
            have h0 : (0 : EuclideanHalfSpace 1).val = 0 := rfl
            rw [h0, norm_zero] at hnorm
            linarith
          · intro hx1
            apply Subtype.ext
            apply norm_eq_zero.mp
            linarith [hnorm]
        rw [hcoord]
        constructor
        · intro hx1
          have heq := (Realization.eq_vertex_iff K x v).mpr hx1
          have hsup : x.val.support = {v} := by
            rw [heq, vertex_val, Finsupp.support_single v one_ne_zero]
          rw [hsup]
          exact h.singleton_mem_manifoldBoundary_iff.mpr hball
        · intro hxbd
          obtain ⟨_, hb⟩ := h.mem_manifoldBoundary_iff.mp hxbd
          have hle : x.val.support.card ≤ 1 := h.card_le_of_link_ne_bot hb.ne_bot
          have hsup : x.val.support = {v} :=
            Finset.eq_singleton_iff_unique_mem.mpr
              ⟨hvsup, fun w hw => Finset.card_le_one.mp hle w hw v hvsup⟩
          have hxeq : x = vertex K v := Realization.eq_vertex_of_support_eq K x hsup
          simp [hxeq]
      | succ m =>
        by_cases hlt : x.val v < 1
        · -- Away from the vertex `v`, reduce radially to the `(m + 1)`-dimensional link.
          let E := EuclideanSpace ℝ (Fin (m + 2))
          let p : Metric.sphere (0 : E) 1 := ⟨EuclideanSpace.single 0 1,
            mem_sphere_zero_iff_norm.mpr (by
              simpa only [E, EuclideanSpace.single, norm_one] using
                (PiLp.norm_single 2 (fun _ : Fin (m + 2) => ℝ) 0 1))⟩
          have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
          let : Fact (Module.finrank ℝ E = m + 2) := ⟨by simp [E]⟩
          let b := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (m + 1) hp).repr.symm
          let d : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
              closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
            b.toHomeomorph.subtype fun z => by simp
          obtain ⟨a⟩ := hball.nonempty_homeomorph_closedBall (A := K) link_le
          let r := Homeomorph.setCongr (s := K.geometricLink v)
            (t := {y : Realization K | y.val.support ∈ K.link {v}})
            (Set.ext (mem_geometricLink_iff K v))
          let l := r.trans (a.trans (d.trans (TauCeti.hemisphereHomeomorph p).symm))
          have hcomp := K.isCompact_closedStarRealization
            (finite_faces_closedStar_iff.mpr hball.finite_faces)
          let f := openStarHomeomorphHalfBall hcomp l
          have hinner (z : E) : ⟪z, (p : E)⟫ = z 0 := by
            simp [p, E, EuclideanSpace.inner_single_right]
          let q : ↥(ball (0 : E) 1 ∩ {z | 0 ≤ ⟪z, (p : E)⟫}) ≃ₜ
              {z : EuclideanHalfSpace (m + 2) | ‖z.val‖ < 1} := {
            toFun z := ⟨⟨z.val, by
              simpa only [Set.mem_ofPred_eq, hinner] using z.property.2⟩,
              mem_ball_zero_iff.mp z.property.1⟩
            invFun z := ⟨z.val.val, mem_ball_zero_iff.mpr z.property, by
              simpa only [Set.mem_ofPred_eq, hinner] using z.val.property⟩
            left_inv _ := rfl
            right_inv _ := rfl
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }
          have hU : IsOpen {z : EuclideanHalfSpace (m + 2) | ‖z.val‖ < 1} :=
            isOpen_lt continuous_subtypeVal.norm continuous_const
          obtain ⟨c, hc_src, -, hc_apply⟩ :=
            OpenPartialHomeomorph.exists_source_eq_target_eq_of_homeomorph
              (K.isOpen_openStarRealization v) hU (f.trans q)
              ⟨vertex K v, by simp [mem_openStarRealization]⟩
          have hxs : x ∈ c.source := hc_src ▸ hx
          rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
            TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff]
          let p₀ : puncturedClosedStar K v := ⟨x, (K.mem_puncturedClosedStar v x).mpr
            ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩
          let y : geometricLink K v := starLinkProjection K v p₀
          have hzero : (c x).val 0 = 0 ↔ ⟪((l y : sphere (0 : E) 1) : E), (p : E)⟫ = 0 := by
            have hcx : (c x).val = ((openStarHomeomorphHalfBall hcomp l ⟨x, hx⟩ : _) : E) :=
              congrArg (fun z : EuclideanHalfSpace (m + 2) => z.val) (hc_apply ⟨x, hx⟩)
            have h0eq : (c x).val 0 = ⟪(c x).val, (p : E)⟫ := (hinner _).symm
            rw [h0eq, hcx, coe_openStarHomeomorphHalfBall_apply,
              coe_closedStarHomeomorphHalfBall_of_lt hcomp l _ hlt, real_inner_smul_left,
              mul_eq_zero]
            have hne : 1 - x.val v ≠ 0 := (sub_pos.mpr hlt).ne'
            exact ⟨fun hor => hor.resolve_left hne, fun hir => Or.inr hir⟩
          have hhemi : ⟪((l y : sphere (0 : E) 1) : E), (p : E)⟫ = 0 ↔
              ‖(a (r y) : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := by
            have h1 := TauCeti.norm_hemisphereHomeomorph_apply_eq_one_iff p (l y)
            have hl : TauCeti.hemisphereHomeomorph p (l y) = d (a (r y)) := by
              simp [l]
            rw [← h1, hl]
            simp [d, b]
          let Labs := linkComplex (K := K) v
          have hLman : IsCombinatorialManifold Labs.toPreAbstractSimplicialComplex (m + 1) := by
            rw [← isCombinatorialManifold_map_iff (Subtype.val_injective (p := fun w : ι =>
              ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v})),
              map_val_linkComplex]
            exact hball.isCombinatorialManifold
          let := hLman.realizationChartedSpace
          let eBall : Realization Labs ≃ₜ
              closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
            (linkComplexHomeomorph v).trans (r.trans a)
          have hIH := hLman.isBoundaryPoint_realizationChartedSpace_iff
            ((linkComplexHomeomorph v).symm y)
          have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) =
              Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) := rfl
          let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
            ⟨by simp⟩
          have hbd_equiv : ‖(a (r y) : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 ↔
              (𝓡∂ (m + 1)).IsBoundaryPoint (eBall ((linkComplexHomeomorph v).symm y)) := by
            rw [TauCeti.isBoundaryPoint_closedBall_iff (n := m + 1)]
            simp [eBall]
          rw [hzero, hhemi, hbd_equiv,
            ← (eBall.isBoundaryPoint_iff (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) hfin _), hIH,
            ← linkComplexHomeomorph_support_mem_manifoldBoundary_iff, Homeomorph.apply_symm_apply]
          exact (mem_manifoldBoundary_of_openStar_lt_one h hx hlt).symm
        · -- At the vertex `v` itself (`x = vertex K v`), both sides hold.
          have hx1 : x.val v = 1 := le_antisymm (Realization.le_one K x v) (not_lt.mp hlt)
          have heq : x = vertex K v := (Realization.eq_vertex_iff K x v).mpr hx1
          obtain ⟨c, hc, -, hcv, -⟩ := hball.exists_openPartialHomeomorph_openStar_halfBall
          have hxs : x ∈ c.source := hc ▸ hx
          rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
            TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff, heq, hcv]
          have hsup : (vertex K v).val.support = {v} := by simp
          rw [hsup]
          refine iff_of_true rfl (h.singleton_mem_manifoldBoundary_iff.mpr hball)

/-- The manifold boundary of the realization of a positive-dimensional combinatorial manifold
consists of the points whose carrier lies in `manifoldBoundary`. -/
theorem IsCombinatorialManifold.boundary_realizationChartedSpace {n : ℕ}
    {K : AbstractSimplicialComplex ι}
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).boundary (Realization K) =
      {x : Realization K |
        x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex} := by
  let := h.realizationChartedSpace
  ext x
  exact h.isBoundaryPoint_realizationChartedSpace_iff x

/-- The manifold interior of the realization of a positive-dimensional combinatorial manifold
consists of the points whose carrier avoids `manifoldBoundary`. -/
theorem IsCombinatorialManifold.interior_realizationChartedSpace {n : ℕ}
    {K : AbstractSimplicialComplex ι}
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).interior (Realization K) =
      {x : Realization K |
        x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex} := by
  let := h.realizationChartedSpace
  rw [← ModelWithCorners.compl_boundary, h.boundary_realizationChartedSpace]
  rfl

/-- An edge (`σ.card = 2`) of a combinatorial `2`-manifold belongs to `manifoldBoundary K`
precisely when it is contained in a unique `2`-simplex (`τ.card = 3`) of `K`. -/
theorem IsCombinatorialManifold.edge_mem_manifoldBoundary_iff
    {K : PreAbstractSimplicialComplex ι} (hK : IsCombinatorialManifold K 2) {σ : Finset ι}
    (hcard : σ.card = 2) :
    σ ∈ manifoldBoundary K ↔
      σ ∈ K ∧ ∃! τ : Finset ι, τ ∈ K ∧ σ ⊆ τ ∧ τ.card = 3 := by
  rw [hK.mem_manifoldBoundary_iff, hcard]
  simp only [Nat.reduceSub, isCombinatorialBall_zero_iff]
  refine ⟨fun ⟨hσ, w, hlink⟩ =>
      ⟨hσ, insert w σ, ?_, fun τ ⟨hτK, hστ, hτcard⟩ => ?_⟩,
    fun ⟨hσ, τ, ⟨hτK, hστ, hτcard⟩, huniq⟩ => ⟨hσ, ?_⟩⟩
  · have hwmem : ({w} : Finset ι) ∈ link K σ := by
      rw [hlink]
      exact mem_simplex.mpr ⟨Finset.singleton_nonempty w, Finset.Subset.rfl⟩
    obtain ⟨_, hdisj, hmem⟩ := mem_link_nonempty.mp hwmem
    have hw : w ∉ σ := Finset.disjoint_singleton_left.mp hdisj
    refine ⟨?_, Finset.subset_insert w σ, by rw [Finset.card_insert_of_notMem hw, hcard]⟩
    rwa [← Finset.singleton_union]
  · have hdiff : (τ \ σ).card = 1 := by rw [Finset.card_sdiff_of_subset hστ, hτcard, hcard]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdiff
    have hulink : ({u} : Finset ι) ∈ link K σ := by
      refine mem_link_nonempty.mpr ⟨Finset.singleton_nonempty u, ?_, ?_⟩
      · have hdisj : Disjoint (τ \ σ) σ := Finset.sdiff_disjoint
        rwa [hu] at hdisj
      · rw [← hu, Finset.sdiff_union_of_subset hστ]
        exact hτK
    rw [hlink, mem_simplex] at hulink
    obtain rfl : u = w :=
      Finset.singleton_injective ((Finset.subset_singleton_iff.mp hulink.2).resolve_left
        (Finset.singleton_nonempty u).ne_empty)
    calc
      τ = (τ \ σ) ∪ σ := (Finset.sdiff_union_of_subset hστ).symm
      _ = {u} ∪ σ := by rw [hu]
      _ = insert u σ := Finset.singleton_union u σ
  · have hdiff : (τ \ σ).card = 1 := by rw [Finset.card_sdiff_of_subset hστ, hτcard, hcard]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
    refine ⟨w, PreAbstractSimplicialComplex.ext ?_⟩
    ext ρ
    rw [faces_simplex_singleton]
    refine ⟨fun hρ => ?_, fun hρ => ?_⟩
    · rw [Set.mem_singleton_iff]
      obtain ⟨hρne, hdisj, hmem⟩ := mem_link_nonempty.mp hρ
      have hcardle : (ρ ∪ σ).card ≤ 3 := by
        have := hK.isPure.card_le hmem
        simpa [Nat.succ_eq_add_one] using this
      have hρcard : ρ.card = 1 := by
        have := Finset.card_union_of_disjoint hdisj
        have := hρne.card_pos
        omega
      obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hρcard
      have huσ : u ∉ σ := Finset.disjoint_singleton_left.mp hdisj
      have hτ' : insert u σ = τ := huniq (insert u σ) ⟨by rwa [← Finset.singleton_union],
        Finset.subset_insert u σ, by rw [Finset.card_insert_of_notMem huσ, hcard]⟩
      have huτ : u ∈ τ \ σ := by
        rw [Finset.mem_sdiff]
        exact ⟨hτ' ▸ Finset.mem_insert_self u σ, huσ⟩
      rw [hw, Finset.mem_singleton] at huτ
      rw [huτ]
    · rw [Set.mem_singleton_iff] at hρ
      subst hρ
      refine mem_link_nonempty.mpr ⟨Finset.singleton_nonempty w, ?_, ?_⟩
      · have hdisj : Disjoint (τ \ σ) σ := Finset.sdiff_disjoint
        rwa [hw] at hdisj
      · rw [← hw, Finset.sdiff_union_of_subset hστ]
        exact hτK

end PreAbstractSimplicialComplex
