/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Brown
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Topology.Instances.Real.IcoScale

/-!
# The topological collar of the boundary of a manifold

Let `M` be a charted space modelled on the half-space `𝓡∂ (n + 1)`.
Every boundary point has a product collar chart
(`TauCeti.exists_isProductCollarChart_of_mem_boundary`), whose source is homeomorphic to its part
of the boundary times a half-open interval
(`TauCeti.IsProductCollarChart.homeomorphProdOpens`).
Rescaling the interval to `[0, 1)` makes this a collar of the boundary points of the source, in
the sense of `TauCeti.IsCollar`, whose points of positive depth are interior points of `M`
(`TauCeti.IsProductCollarChart.exists_isCollar`). So the inclusion of the boundary `∂M → M` is
locally collared in the sense of M. Brown (`TauCeti.isLocallyCollared_subtypeVal_boundary`).

When the boundary is compact and `M` is Hausdorff, Brown's collaring theorem
(`TauCeti.IsLocallyCollared.isCollared`) assembles these local collars into a single collar: an
open embedding `c : ∂M × [0, 1) → M` with `c (x, 0) = x`
(`TauCeti.isCollared_subtypeVal_boundary`). This holds in particular for compact `M`, whose
boundary is closed by invariance of domain
(`ModelWithCorners.isClosed_boundary_of_finiteDimensional`,
`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`).

Both steps work for any finite-dimensional model. If the boundary of the model space itself is
collared, a chart carries a small collar of the model back to a local collar of `∂M`
(`TauCeti.isLocallyCollared_subtypeVal_boundary_of_isCollared`); this is how the quadrant case,
manifolds with corners, is treated in `TauCeti.Geometry.Manifold.Corners.Collar`. Brown's theorem
then globalizes local collars of a compact boundary for every model
(`TauCeti.isCollared_subtypeVal_boundary_of_isLocallyCollared`,
`TauCeti.isCollared_subtypeVal_boundary_of_isLocallyCollared_of_compactSpace`), and the half-space
results above are its instances.

The collar is only a topological one. It is what comparisons of the relative homology
`H_*(M, ∂M)` with the homology of `M` relative to an open neighbourhood of the boundary use, for
instance to construct the fundamental class of a compact manifold relative to its boundary. A
smooth collar, a diffeomorphism onto its image, is a stronger statement not treated here.

## Main results

* `TauCeti.isLocallyCollared_subtypeVal_boundary_of_isCollared`: if the boundary of the model is
  collared, the boundary of every charted space over it is locally collared.
* `TauCeti.isCollared_subtypeVal_boundary_of_isLocallyCollared`,
  `TauCeti.isCollared_subtypeVal_boundary_of_isLocallyCollared_of_compactSpace`: a locally collared
  compact boundary of a Hausdorff charted space is collared.
* `TauCeti.IsProductCollarChart.exists_isCollar`: the boundary points of the source of a product
  collar chart have a collar meeting the boundary only at depth zero.
* `TauCeti.isLocallyCollared_subtypeVal_boundary`: the boundary of a charted space over the
  half-space is locally collared.
* `TauCeti.isCollared_subtypeVal_boundary`: a compact boundary of a Hausdorff charted space over the
  half-space is collared.
* `TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`: the boundary of a compact Hausdorff
  charted space over the half-space is collared.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. Connelly, *A new proof of Brown's collaring theorem*, Proceedings of the American Mathematical
  Society 27 (1971), 180–182.
-/

public section

open Set Topology
open scoped Manifold

namespace TauCeti

/-- The depth coordinate of a local collar: `t ∈ [0, 1)` is sent to the point of normal coordinate
`ε t` of the initial segment `[0, ε)` of the one-dimensional half-space model. -/
private noncomputable def depthHomeomorph {ε : ℝ} (hε : 0 < ε) :
    ↥(Ico (0 : ℝ) 1) ≃ₜ EuclideanHalfSpace.normalIioOpens ε :=
  ((icoScale hε).trans (EuclideanHalfSpace.homeomorphNormalIio ε).symm).trans
    (Homeomorph.setCongr (Set.ext fun _ ↦
      EuclideanHalfSpace.mem_normalIio.trans EuclideanHalfSpace.mem_normalIioOpens.symm))

private theorem depthHomeomorph_apply_coe_zero {ε : ℝ} (hε : 0 < ε) (t : ↥(Ico (0 : ℝ) 1)) :
    (depthHomeomorph hε t : EuclideanHalfSpace 1).val 0 = ε * t := by
  have ht : (depthHomeomorph hε t : EuclideanHalfSpace 1) =
      (EuclideanHalfSpace.homeomorphNormalIio ε).symm (icoScale hε t) :=
    rfl
  rw [ht, ← coe_icoScale hε, ← EuclideanHalfSpace.coe_homeomorphNormalIio,
    Homeomorph.apply_symm_apply]

section Model

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A chart `e` identifies the boundary points of `M` in its source read in `O ⊆ e.target` with the
boundary points of the model in `O`. -/
private noncomputable def chartBoundaryHomeomorph [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph M H) {O : Set H} (hO : O ⊆ e.target) :
    (Subtype.val ⁻¹' (e.source ∩ e ⁻¹' O) : Set (I.boundary M)) ≃ₜ
      (Subtype.val ⁻¹' O : Set (I.boundary H)) where
  toFun p := ⟨⟨e p.val.val, (e.isBoundaryPoint_iff I I rfl p.property.1).1 p.val.property⟩,
    p.property.2⟩
  invFun z := ⟨⟨e.symm z.val.val,
      (e.isBoundaryPoint_iff I I rfl (e.map_target (hO z.property))).2
        (by rw [e.right_inv (hO z.property)]; exact z.val.property)⟩,
    e.map_target (hO z.property), by
      rw [mem_preimage, e.right_inv (hO z.property)]
      exact z.property⟩
  left_inv p := Subtype.ext (Subtype.ext (e.left_inv p.property.1))
  right_inv z := Subtype.ext (Subtype.ext (e.right_inv (hO z.property)))
  continuous_toFun := ((e.continuousOn.comp_continuous
    (continuous_subtypeVal.comp continuous_subtypeVal) fun p ↦ p.property.1).subtype_mk
      _).subtype_mk _
  continuous_invFun := ((e.continuousOn_symm.comp_continuous
    (continuous_subtypeVal.comp continuous_subtypeVal) fun z ↦ hO z.property).subtype_mk
      _).subtype_mk _

/-- **Charts carry a collar of the model to local collars.** If the boundary of a
finite-dimensional model `H` is collared in `H`, then the boundary of every charted space `M` over
`H` is locally collared: every boundary point has an open neighbourhood in the boundary with a
collar in `M` whose points of positive collar depth are interior points. -/
theorem isLocallyCollared_subtypeVal_boundary_of_isCollared [FiniteDimensional ℝ E]
    (hH : IsCollared (Subtype.val : I.boundary H → H)) :
    IsLocallyCollared ((↑) : I.boundary M → M) := by
  obtain ⟨C, hC⟩ := isCollared_iff.1 hH
  refine isLocallyCollared_iff.2 fun x ↦ ?_
  set e := chartAt H (x : M)
  have hxe : (x : M) ∈ e.source := mem_chart_source _ _
  -- The collar of the model at small depth near `e x` stays in the target of `e`.
  have hT : IsOpen {q | C q ∈ e.target} := e.open_target.preimage hC.isOpenEmbedding.continuous
  obtain ⟨u, v, hu, hv, hxu, h0v, huv⟩ := isOpen_prod_iff.1 hT
    ⟨e x, (e.isBoundaryPoint_iff I I rfl hxe).1 x.property⟩ ⟨0, le_rfl, zero_lt_one⟩
    (by rw [mem_ofPred_eq, hC.apply_zero]; exact e.map_source hxe)
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hu
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.1 hv _ h0v
  have hε : min r 1 ∈ Ioc (0 : ℝ) 1 := ⟨lt_min hr one_pos, min_le_right _ _⟩
  have hεv (t : Ico (0 : ℝ) 1) : (⟨min r 1 * t, mul_nonneg hε.1.le t.property.1,
      (mul_le_of_le_one_left t.property.1 hε.2).trans_lt t.property.2⟩ : Ico (0 : ℝ) 1) ∈ v := by
    refine hrv ?_
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg hε.1.le t.property.1)]
    exact (mul_lt_of_lt_one_right hε.1 t.property.2).trans_le (min_le_left _ _)
  -- Restrict the collar of the model to `O ∩ e.target`, shrink its depth, read it in `M`.
  have hOt : IsOpen (Subtype.val ⁻¹' (O ∩ e.target) : Set (I.boundary H)) :=
    (hO.inter e.open_target).preimage continuous_subtypeVal
  set a := chartBoundaryHomeomorph (I := I) e (inter_subset_right : O ∩ e.target ⊆ e.target)
  have hc := (((hC.restrict hOt).scale _ hε).comp_homeomorph a).openPartialHomeomorph_comp e.symm
    (by
      rintro _ ⟨⟨p, t⟩, rfl⟩
      exact huv ⟨(a p).property.1, hεv t⟩)
  have hfa : ⇑e.symm ∘ (Subtype.val ∘ Subtype.val) ∘ ⇑a = ((↑) : I.boundary M → M) ∘
      ((↑) : (Subtype.val ⁻¹' (e.source ∩ e ⁻¹' (O ∩ e.target)) : Set (I.boundary M)) →
        I.boundary M) :=
    funext fun p ↦ e.left_inv p.property.1
  rw [hfa] at hc
  refine ⟨_, (e.isOpen_inter_preimage (hO.inter e.open_target)).preimage continuous_subtypeVal,
    ⟨hxe, hxu, e.map_source hxe⟩, _, hc, ?_⟩
  · -- A point of positive depth is read in `e` as a point of positive depth of the collar of the
    -- model, which is not a boundary point.
    rintro ⟨p, t⟩ ⟨y, hy⟩
    have hmem : C ((a p).val, _) ∈ e.target := huv ⟨(a p).property.1, hεv t⟩
    have hyB := (e.isBoundaryPoint_iff I I rfl
      (hy ▸ e.map_target hmem : (y : M) ∈ e.source)).1 y.property
    simp only [Function.comp_apply, Prod.map_apply, id_eq] at hy
    rw [hy, e.right_inv hmem] at hyB
    have h0 := congrArg Subtype.val (hC.preimage_range.subset ⟨⟨_, hyB⟩, rfl⟩).2
    exact (mul_eq_zero.1 h0).resolve_left hε.1.ne'

/-- **The collar of a compact, locally collared boundary.** If the boundary of a Hausdorff charted
space is locally collared and compact, then it is collared: there
is an open embedding `c : ∂M × [0, 1) → M` with `c (x, 0) = x`. This is Brown's collaring theorem
applied to the local collars. -/
theorem isCollared_subtypeVal_boundary_of_isLocallyCollared [T2Space M]
    (h : IsLocallyCollared ((↑) : I.boundary M → M)) (hK : IsCompact (I.boundary M)) :
    IsCollared ((↑) : I.boundary M → M) :=
  have := isCompact_iff_compactSpace.1 hK
  h.isCollared Subtype.val_injective

/-- **The boundary of a compact manifold is collared once it is locally collared.** For a compact
Hausdorff charted space over a finite-dimensional model whose boundary is locally collared, there is
an open embedding `c : ∂M × [0, 1) → M` with `c (x, 0) = x`. -/
theorem isCollared_subtypeVal_boundary_of_isLocallyCollared_of_compactSpace
    [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    (h : IsLocallyCollared ((↑) : I.boundary M → M)) :
    IsCollared ((↑) : I.boundary M → M) :=
  isCollared_subtypeVal_boundary_of_isLocallyCollared h
    (I.isClosed_boundary_of_finiteDimensional M).isCompact

end Model

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

namespace IsProductCollarChart

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)}
  {V : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ}

/-- The local collar of a product collar chart, as a homeomorphism from the boundary points of
its source times `[0, 1)` onto its source. -/
private noncomputable def collarHomeomorph (h : IsProductCollarChart k φ V ε) :
    h.sourceBoundaryOpens × ↥(Ico (0 : ℝ) 1) ≃ₜ h.sourceOpens :=
  ((Homeomorph.refl _).prodCongr (depthHomeomorph h.height_pos)).trans h.homeomorphProdOpens.symm

/-- The chart value of a point of the local collar has normal coordinate `ε t` at depth `t`. -/
private theorem snd_collarHomeomorph (h : IsProductCollarChart k φ V ε)
    (p : h.sourceBoundaryOpens × ↥(Ico (0 : ℝ) 1)) :
    (φ (h.collarHomeomorph p)).2.val 0 = ε * p.2 := by
  rw [← h.coe_homeomorphProdOpens_snd, collarHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply]
  exact depthHomeomorph_apply_coe_zero h.height_pos p.2

/-- The local collar sends a boundary point at depth zero to itself. -/
private theorem collarHomeomorph_zero (h : IsProductCollarChart k φ V ε)
    (y : h.sourceBoundaryOpens) :
    (h.collarHomeomorph (y, ⟨0, le_rfl, zero_lt_one⟩) : M) = y := by
  -- Both points have the same tangential coordinate, and normal coordinate zero.
  set z := h.collarHomeomorph (y, ⟨0, le_rfl, zero_lt_one⟩)
  have hy : φ y = ((φ z).1, 0) := by
    have hz : h.homeomorphProdOpens z =
        (y, depthHomeomorph h.height_pos ⟨0, le_rfl, zero_lt_one⟩) :=
      h.homeomorphProdOpens.apply_symm_apply _
    simpa [hz] using h.map_homeomorphProdOpens_fst z
  have hz0 : (φ z).2 = 0 := by
    rw [EuclideanHalfSpace.eq_zero_iff, h.snd_collarHomeomorph, mul_zero]
  exact φ.injOn (h.mem_sourceOpens.1 z.property) (h.mem_sourceBoundaryOpens.1 y.property)
    ((show φ z = ((φ z).1, 0) from Prod.ext rfl hz0).trans hy.symm)

/-- **The local collar of a product collar chart.** The boundary points of the source of a product
collar chart have a collar in `M`, an open embedding of their product with `[0, 1)` whose zero
slice is the inclusion, and whose points of positive depth are not boundary points of `M`. -/
theorem exists_isCollar (h : IsProductCollarChart k φ V ε) :
    ∃ c : h.sourceBoundaryOpens × ↥(Ico (0 : ℝ) 1) → M,
      IsCollar (((↑) : (𝓡∂ (n + 1)).boundary M → M) ∘ (↑)) c ∧
        ∀ p, c p ∈ (𝓡∂ (n + 1)).boundary M → (p.2 : ℝ) = 0 := by
  refine ⟨fun p ↦ h.collarHomeomorph p,
    ⟨h.sourceOpens.isOpen.isOpenEmbedding_subtypeVal.comp h.collarHomeomorph.isOpenEmbedding,
      h.collarHomeomorph_zero⟩, fun p hp ↦ ?_⟩
  have hp0 := (h.mem_boundary_iff _ (h.mem_sourceOpens.1 (h.collarHomeomorph p).property)).1 hp
  rw [h.snd_collarHomeomorph] at hp0
  exact (mul_eq_zero.1 hp0).resolve_left h.height_pos.ne'

end IsProductCollarChart

/-- **The boundary of a manifold is locally collared.** For a charted space over the half-space,
every boundary point has an open neighbourhood in the boundary with a collar in `M` whose
points of positive depth are interior points: the local collar of a product collar chart. -/
theorem isLocallyCollared_subtypeVal_boundary :
    IsLocallyCollared ((↑) : (𝓡∂ (n + 1)).boundary M → M) := by
  refine isLocallyCollared_iff.2 fun x ↦ ?_
  obtain ⟨φ, V, ε, hxφ, h⟩ := exists_isProductCollarChart_of_mem_boundary (k := 0) x.property
  obtain ⟨c, hc, hc0⟩ := h.exists_isCollar
  exact ⟨h.sourceBoundaryOpens, h.sourceBoundaryOpens.isOpen, h.mem_sourceBoundaryOpens.2 hxφ,
    c, hc,
    fun p ⟨y, hy⟩ ↦ hc0 p (hy ▸ y.property)⟩

/-- **The collar of a compact boundary.** If the boundary of a Hausdorff charted space over the
half-space is compact, then it is collared: there is an open embedding `c : ∂M × [0, 1) → M` with
`c (x, 0) = x`. This is Brown's collaring theorem applied to the local collars. -/
theorem isCollared_subtypeVal_boundary [T2Space M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    IsCollared ((↑) : (𝓡∂ (n + 1)).boundary M → M) :=
  isCollared_subtypeVal_boundary_of_isLocallyCollared isLocallyCollared_subtypeVal_boundary hK

/-- **The boundary of a compact manifold is collared.** For a compact Hausdorff charted space over
the half-space, there is an open embedding `c : ∂M × [0, 1) → M` with `c (x, 0) = x`. -/
theorem isCollared_subtypeVal_boundary_of_compactSpace [CompactSpace M] [T2Space M] :
    IsCollared ((↑) : (𝓡∂ (n + 1)).boundary M → M) :=
  isCollared_subtypeVal_boundary_of_isLocallyCollared_of_compactSpace
    isLocallyCollared_subtypeVal_boundary

end TauCeti
