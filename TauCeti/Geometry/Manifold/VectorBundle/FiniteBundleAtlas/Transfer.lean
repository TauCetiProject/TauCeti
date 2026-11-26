/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Transfer domains of a finite bundle atlas

Let `A` be a finite bundle atlas of a manifold `M` modelled on `E` for a fibre bundle `V → M`. The
chart data of a section in chart `j` are compared with those in chart `i` on the transfer domain
`A.transferDomain i j`: the chart-`j` coordinates whose preimage lies in the source of chart `i` and
in the base sets of the bundle charts `i` and `j`. This file collects the geometry of transfer
domains used to move chart data between charts.

For an open `Q` in chart `i`, the localized image `A.localizedImage i j Q` is the part of the image
of chart `j` read in chart `i` inside `Q`: data supported over the points of `Q` live there in chart
`j`. If the closure of `Q` lies in the image of chart `i`, the closure of the localized image lies
in the transfer domain.

For a `C^n` vector bundle over a `C^n` manifold without boundary modelled on a real normed space,
the coordinate change of the bundle, read in chart `j`, is `C^n` on the transfer domain.

If `M` and `E` are Hausdorff, the image of each chart is covered by finitely many open pieces with
compact closure in a transfer domain, each mapped by the chart coordinate change
`(A.chart j).symm ≫ₕ A.chart i` into an open set with compact closure in the image of another chart.
These pieces are built from the shrinking
`TauCeti.FiniteBundleAtlas.exists_isOpen_closure_subset_dom` of the chart domains, and the charts
they are mapped into may be restricted to any family of charts whose domains still cover the
manifold.

## Main definitions

* `TauCeti.FiniteBundleAtlas.transferDomain`: the chart-`j` coordinates on which chart `i` and the
  bundle charts `i` and `j` are defined.
* `TauCeti.FiniteBundleAtlas.localizedImage`: the part of the image of chart `j` read in chart `i`
  inside a given open set.

## Main results

* `TauCeti.FiniteBundleAtlas.mem_transferDomain`,
  `TauCeti.FiniteBundleAtlas.overlap_subset_transferDomain`: membership in transfer domains, which
  contain the overlaps of chart domains.
* `TauCeti.FiniteBundleAtlas.exists_transfer_cover`: the transfer cover of the chart images, and
  `TauCeti.FiniteBundleAtlas.exists_transfer_cover_of_iUnion_dom_eq` for transfers from a family of
  charts whose domains cover the manifold, and
  `TauCeti.FiniteBundleAtlas.exists_transfer_cover_append` for transfers from the charts of one
  atlas to those of another.
* `TauCeti.FiniteBundleAtlas.exists_transfer_piece`: for a compact set inside the domain of chart
  `i`, the image of chart `j` is covered by a transfer piece from chart `i` and an open set avoiding
  the compact set.
* `TauCeti.FiniteBundleAtlas.closure_localizedImage_subset_transferDomain`: the localized image of
  an open set with closure in the image of chart `i` lies, with its closure, in the transfer domain.
* `TauCeti.FiniteBundleAtlas.contDiffOn_coordChangeL_transferDomain`: the coordinate change of the
  bundle, read in chart `j`, is `C^n` on the transfer domain.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped Manifold Topology

universe u

namespace TauCeti

section Geometry
variable {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-! ### Transfer domains and the transfer cover -/

/-- The chart-`j` coordinates on which the transfer of chart data from chart `i` is defined: points
of the target of chart `j` whose preimage lies in the source of chart `i` and in the base sets of
the bundle charts `i` and `j`. -/
def transferDomain (i j : Fin A.n) : Set E :=
  (A.chart j).target ∩
    (A.chart j).symm ⁻¹' ((A.chart i).source ∩ ((A.triv j).baseSet ∩ (A.triv i).baseSet))

theorem mem_transferDomain {i j : Fin A.n} {y : E} :
    y ∈ A.transferDomain i j ↔ y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ (A.chart i).source ∧
      (A.chart j).symm y ∈ (A.triv j).baseSet ∧ (A.chart j).symm y ∈ (A.triv i).baseSet :=
  Iff.rfl

/-- The overlap of the domains of charts `i` and `j`, read in chart `j`, lies in the transfer
domain. -/
theorem overlap_subset_transferDomain (i j : Fin A.n) : A.overlap i j ⊆ A.transferDomain i j := by
  intro _ hy
  obtain ⟨x, ⟨hxi, hxj⟩, rfl⟩ := A.mem_overlap.1 hy
  have hs := A.dom_subset_chart_source j hxj
  refine A.mem_transferDomain.2 ⟨(A.chart j).map_source hs, ?_⟩
  rw [(A.chart j).left_inv hs]
  exact ⟨A.dom_subset_chart_source i hxi, A.dom_subset_baseSet j hxj, A.dom_subset_baseSet i hxi⟩

/-- Transfer domains are open. -/
theorem isOpen_transferDomain (i j : Fin A.n) : IsOpen (A.transferDomain i j) :=
  (A.chart j).isOpen_inter_preimage_symm ((A.chart i).open_source.inter
    ((A.triv j).open_baseSet.inter (A.triv i).open_baseSet))

/-- The transfer domain lies in the source of the chart coordinate change from chart `j` to chart
`i`. -/
theorem transferDomain_subset_source (i j : Fin A.n) :
    A.transferDomain i j ⊆ ((A.chart j).symm ≫ₕ A.chart i).source := fun _ hy ↦ by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  exact ⟨hy.1, hy.2.1⟩

/-- **Transfer cover from a covering family of charts.** Let `σ` pick finitely many charts of a
finite bundle atlas of a Hausdorff manifold whose domains still cover `M`. Then the image of each
chart `j` is covered by finitely many open pieces `P l j`, one for each chart `σ l` of the family.
The piece `P l j` lies in the overlap of the domains of charts `σ l` and `j`, has compact closure
in the transfer domain, and is mapped by the chart coordinate change into an open set `Q l` with
compact closure inside the image of chart `σ l`. Chart-`j` data can thus be transferred from the
charts of the family alone. -/
theorem exists_transfer_cover_of_iUnion_dom_eq [T2Space E] [T2Space M] {ι : Type*} [Finite ι]
    (σ : ι → Fin A.n) (hσ : ⋃ l, A.dom (σ l) = univ) :
    ∃ (P : ι → Fin A.n → Opens E) (Q : ι → Opens E),
      (∀ l j, (P l j : Set E) ⊆ A.overlap (σ l) j) ∧
      (∀ l j, IsCompact (closure (P l j : Set E))) ∧
      (∀ l j, closure (P l j : Set E) ⊆ A.transferDomain (σ l) j) ∧
      (∀ l, IsCompact (closure (Q l : Set E))) ∧ (∀ l, closure (Q l : Set E) ⊆ A.image (σ l)) ∧
      (∀ l j, MapsTo ((A.chart j).symm ≫ₕ A.chart (σ l)) (P l j) (Q l)) ∧
      ∀ j, A.image j ≤ ⨆ l, P l j := by
  -- A shrinking `D l` of the chart domains of the family, still covering `M`.
  obtain ⟨D, hDo, hD, hcov⟩ := A.exists_isOpen_closure_subset_dom σ hσ
  have hDdom (l : ι) : D l ⊆ A.dom (σ l) := subset_closure.trans (hD l)
  have hKc (l : ι) (j : Fin A.n) :
      IsCompact (A.chart j '' (closure (A.dom j) ∩ closure (D l))) :=
    ((A.isCompact_closure_dom j).inter_right isClosed_closure).image_of_continuousOn
      ((A.chart j).continuousOn.mono (inter_subset_left.trans (A.closure_dom_subset_source j)))
  have hPK (l : ι) (j : Fin A.n) : A.chart j '' (A.dom j ∩ D l) ⊆
      A.chart j '' (closure (A.dom j) ∩ closure (D l)) :=
    image_mono (inter_subset_inter subset_closure subset_closure)
  have hQc (l : ι) : IsCompact (A.chart (σ l) '' closure (D l)) :=
    ((A.isCompact_closure_dom (σ l)).of_isClosed_subset isClosed_closure
      ((hD l).trans subset_closure)).image_of_continuousOn
      ((A.chart (σ l)).continuousOn.mono ((hD l).trans (A.dom_subset_chart_source (σ l))))
  refine ⟨fun l j ↦ ⟨A.chart j '' (A.dom j ∩ D l), (A.chart j).isOpen_image_of_subset_source
      ((A.isOpen_dom j).inter (hDo l)) (inter_subset_left.trans (A.dom_subset_chart_source j))⟩,
    fun l ↦ ⟨A.chart (σ l) '' D l, (A.chart (σ l)).isOpen_image_of_subset_source (hDo l)
      ((hDdom l).trans (A.dom_subset_chart_source (σ l)))⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro l j _ ⟨x, hx, rfl⟩
    exact A.mem_overlap.2 ⟨x, ⟨hDdom l hx.2, hx.1⟩, rfl⟩
  · exact fun l j ↦ (hKc l j).closure_of_subset (hPK l j)
  · intro l j
    refine (closure_minimal (hPK l j) (hKc l j).isClosed).trans ?_
    rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    have hs := A.closure_dom_subset_source j hx₁
    refine ⟨(A.chart j).map_source hs, ?_⟩
    rw [mem_preimage, (A.chart j).left_inv hs]
    exact ⟨A.dom_subset_chart_source (σ l) (hD l hx₂), A.closure_dom_subset_baseSet j hx₁,
      A.dom_subset_baseSet (σ l) (hD l hx₂)⟩
  · exact fun l ↦ (hQc l).closure_of_subset (image_mono subset_closure)
  · intro l y hy
    exact A.mem_image.2
      (image_mono (hD l) (closure_minimal (image_mono subset_closure) (hQc l).isClosed hy))
  · rintro l j _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨x, hx₂, ?_⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart j).left_inv (A.dom_subset_chart_source j hx₁)]
  · intro j y hy
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    obtain ⟨l, hl⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨l, ⟨x, ⟨hx, hl⟩, rfl⟩⟩

/-- **Transfer cover.** For a finite bundle atlas of a Hausdorff manifold, the image of each chart
`j` is covered by finitely many open pieces `P i j`. The piece `P i j` lies in the overlap of the
domains of charts `i` and `j`, has compact closure in the transfer domain, and is mapped by the
chart coordinate change into an open set `Q i` with compact closure inside the image of chart `i`.
-/
theorem exists_transfer_cover [T2Space E] [T2Space M] :
    ∃ (P : Fin A.n → Fin A.n → Opens E) (Q : Fin A.n → Opens E),
      (∀ i j, (P i j : Set E) ⊆ A.overlap i j) ∧ (∀ i j, IsCompact (closure (P i j : Set E))) ∧
      (∀ i j, closure (P i j : Set E) ⊆ A.transferDomain i j) ∧
      (∀ i, IsCompact (closure (Q i : Set E))) ∧ (∀ i, closure (Q i : Set E) ⊆ A.image i) ∧
      (∀ i j, MapsTo ((A.chart j).symm ≫ₕ A.chart i) (P i j) (Q i)) ∧
      ∀ j, A.image j ≤ ⨆ i, P i j :=
  A.exists_transfer_cover_of_iUnion_dom_eq id A.iUnion_dom

/-- **Transfer cover between two atlases.** For two finite bundle atlases `A` and `B` of a
Hausdorff manifold, the image of each chart `j` of `B` is covered by finitely many open pieces
`P i j`, one for each chart `i` of `A`. In the union atlas `A.append B`, the piece `P i j` lies in
the overlap of the domains of the charts `i` of `A` and `j` of `B`, has compact closure in their
transfer domain, and is mapped by the chart coordinate change into an open set `Q i` inside the
image of chart `i` of `A`. Chart data for `B` can thus be transferred from chart data for `A`. -/
theorem exists_transfer_cover_append [T2Space E] [T2Space M] (B : FiniteBundleAtlas E M F V) :
    ∃ (P : Fin A.n → Fin B.n → Opens E) (Q : Fin A.n → Opens E),
      (∀ i j, (P i j : Set E) ⊆ (A.append B).overlap (Fin.castAdd B.n i) (Fin.natAdd A.n j)) ∧
      (∀ i j, IsCompact (closure (P i j : Set E))) ∧
      (∀ i j, closure (P i j : Set E) ⊆
        (A.append B).transferDomain (Fin.castAdd B.n i) (Fin.natAdd A.n j)) ∧
      (∀ i, Q i ≤ A.image i) ∧
      (∀ i j, MapsTo (((A.append B).chart (Fin.natAdd A.n j)).symm ≫ₕ
        (A.append B).chart (Fin.castAdd B.n i)) (P i j) (Q i)) ∧
      (∀ i j, P i j ≤ B.image j) ∧ ∀ j, B.image j ≤ ⨆ i, P i j := by
  obtain ⟨P, Q, hP, hPc, hPD, -, hQ, hPQ, hcov⟩ :=
    (A.append B).exists_transfer_cover_of_iUnion_dom_eq (Fin.castAdd B.n)
      (by simpa using A.iUnion_dom)
  refine ⟨fun i j ↦ P i (Fin.natAdd A.n j), Q, fun i j ↦ hP i _, fun i j ↦ hPc i _,
    fun i j ↦ hPD i _, fun i ↦ ?_, fun i j ↦ hPQ i _, fun i j ↦ ?_, fun j ↦ ?_⟩
  · have h := subset_closure.trans (hQ i)
    rw [image_append_castAdd] at h
    exact SetLike.coe_subset_coe.1 h
  · have h := (hP i (Fin.natAdd A.n j)).trans ((A.append B).overlap_subset_image _ _)
    rw [image_append_natAdd] at h
    exact SetLike.coe_subset_coe.1 h
  · simpa using hcov (Fin.natAdd A.n j)

/-- **Transfer piece of a compact set.** Let `K` be compact, and `U` an open neighbourhood of `K`
whose closure lies in the domain of chart `i`. In chart `j` there are open sets `P` and `R` covering
the image of chart `j` such that `P` lies in the overlap of the domains of charts `i` and `j`, has
compact closure in the transfer domain and is mapped by the chart coordinate change into the image
of chart `i`, while `R` lies in the image of chart `j` and avoids the points of `K`. Chart-`j` data
of a section vanishing outside `K` are thus transferred from chart `i` on `P` and vanish on `R`. -/
theorem exists_transfer_piece [T2Space E] {K U : Set M} {i : Fin A.n} (hKU : K ⊆ U)
    (hU : IsOpen U) (hUi : closure U ⊆ A.dom i) (hK : IsCompact K) (j : Fin A.n) :
    ∃ P R : Opens E, (P : Set E) ⊆ A.overlap i j ∧ IsCompact (closure (P : Set E)) ∧
      closure (P : Set E) ⊆ A.transferDomain i j ∧
      MapsTo ((A.chart j).symm ≫ₕ A.chart i) P (A.image i) ∧ R ≤ A.image j ∧
      A.image j ≤ P ⊔ R ∧ ∀ y ∈ (R : Set E), (A.chart j).symm y ∉ K := by
  have hsj := A.closure_dom_subset_source j
  have hUi' : closure U ⊆ (A.chart i).source := hUi.trans (A.dom_subset_chart_source i)
  -- The image of the compact set `closure U ∩ closure (dom j)` under chart `j` is compact.
  have hLc : IsCompact (A.chart j '' (closure U ∩ closure (A.dom j))) :=
    ((A.isCompact_closure_dom j).inter_left isClosed_closure).image_of_continuousOn
      ((A.chart j).continuousOn.mono (inter_subset_right.trans hsj))
  have hKc : IsCompact (A.chart j '' (K ∩ closure (A.dom j))) :=
    (hK.inter_right isClosed_closure).image_of_continuousOn
      ((A.chart j).continuousOn.mono (inter_subset_right.trans hsj))
  let P : Opens E := ⟨A.chart j '' (U ∩ A.dom j), (A.chart j).isOpen_image_of_subset_source
    (hU.inter (A.isOpen_dom j)) (inter_subset_right.trans (A.dom_subset_chart_source j))⟩
  let R : Opens E := ⟨(A.image j : Set E) \ A.chart j '' (K ∩ closure (A.dom j)),
    (A.image j).isOpen.sdiff hKc.isClosed⟩
  have hPL : closure (P : Set E) ⊆ A.chart j '' (closure U ∩ closure (A.dom j)) :=
    closure_minimal (image_mono (inter_subset_inter subset_closure subset_closure))
      hLc.isClosed
  refine ⟨P, R, ?_, hLc.of_isClosed_subset isClosed_closure hPL, hPL.trans ?_, ?_, sdiff_subset,
    ?_, ?_⟩
  · rintro _ ⟨x, ⟨hxU, hxj⟩, rfl⟩
    exact A.mem_overlap.2 ⟨x, ⟨hUi (subset_closure hxU), hxj⟩, rfl⟩
  · rintro _ ⟨x, ⟨hxU, hxj⟩, rfl⟩
    have hx := hsj hxj
    refine A.mem_transferDomain.2 ⟨(A.chart j).map_source hx, ?_⟩
    rw [(A.chart j).left_inv hx]
    exact ⟨hUi' hxU, A.closure_dom_subset_baseSet j hxj,
      A.dom_subset_baseSet i (hUi hxU)⟩
  · rintro _ ⟨x, ⟨hxU, hxj⟩, rfl⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart j).left_inv (A.dom_subset_chart_source j hxj)]
    exact A.mem_image.2 ⟨x, hUi (subset_closure hxU), rfl⟩
  · intro y hy
    obtain ⟨x, hxj, rfl⟩ := A.mem_image.1 hy
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨x, ⟨hKU hxK, hxj⟩, rfl⟩
    · refine Or.inr ⟨hy, ?_⟩
      rintro ⟨x', ⟨hx'K, hx'j⟩, hx'⟩
      exact hxK ((A.chart j).injOn (hsj hx'j) (A.dom_subset_chart_source j hxj) hx' ▸ hx'K)
  · rintro y ⟨hy, hyK⟩ hK'
    obtain ⟨x, hxj, rfl⟩ := A.mem_image.1 hy
    rw [(A.chart j).left_inv (A.dom_subset_chart_source j hxj)] at hK'
    exact hyK ⟨x, ⟨hK', subset_closure hxj⟩, rfl⟩

/-! ### Localized images -/

/-- The points of the image of chart `j` whose preimage lies in the domain of chart `i` and is
read in chart `i` inside `Q`: the part of chart `j` that sees data supported over `Q`. -/
def localizedImage (i j : Fin A.n) (Q : Opens E) : Opens E :=
  ⟨(A.image j : Set E) ∩ (A.chart j).symm ⁻¹' (A.dom i ∩ A.chart i ⁻¹' Q), by
    refine (A.continuousOn_chart_symm j).isOpen_inter_preimage (A.image j).isOpen ?_
    exact ((A.chart i).continuousOn.mono (A.dom_subset_chart_source i)).isOpen_inter_preimage
      (A.isOpen_dom i) Q.isOpen⟩

variable {A}

@[simp]
theorem mem_localizedImage {i j : Fin A.n} {Q : Opens E} {y : E} :
    y ∈ A.localizedImage i j Q ↔ y ∈ A.image j ∧ (A.chart j).symm y ∈ A.dom i ∧
      A.chart i ((A.chart j).symm y) ∈ Q :=
  Iff.rfl

theorem localizedImage_le_image (i j : Fin A.n) (Q : Opens E) :
    A.localizedImage i j Q ≤ A.image j :=
  fun _ hy ↦ hy.1

theorem mapsTo_localizedImage (i j : Fin A.n) (Q : Opens E) :
    MapsTo ((A.chart j).symm ≫ₕ A.chart i) (A.localizedImage i j Q) Q :=
  fun _ hy ↦ hy.2.2

theorem localizedImage_subset_overlap [T2Space E] (i j : Fin A.n) (Q : Opens E) :
    (A.localizedImage i j Q : Set E) ⊆ A.overlap i j := by
  rintro y ⟨hy, hi, -⟩
  refine A.mem_overlap.2 ⟨(A.chart j).symm y, ⟨hi, A.symm_mem_dom hy⟩, ?_⟩
  exact (A.chart j).right_inv (A.closure_image_subset_target j (subset_closure hy))

theorem isCompact_closure_localizedImage [T2Space E] (i j : Fin A.n) (Q : Opens E) :
    IsCompact (closure (A.localizedImage i j Q : Set E)) :=
  (A.isCompact_closure_image j).of_isClosed_subset isClosed_closure
    (closure_mono (A.localizedImage_le_image i j Q))

/-- If the closure of `Q` lies in the image of chart `i`, the closure of the localized image lies
in the domain on which data are transferred from chart `i` to chart `j`. -/
theorem closure_localizedImage_subset_transferDomain [T2Space E] [T2Space M] {i j : Fin A.n}
    {Q : Opens E} (hQi : closure (Q : Set E) ⊆ A.image i) :
    closure (A.localizedImage i j Q : Set E) ⊆ A.transferDomain i j := by
  have hQc : IsCompact (closure (Q : Set E)) :=
    (A.isCompact_closure_image i).of_isClosed_subset isClosed_closure (hQi.trans subset_closure)
  -- The points of `M` read in chart `i` inside `closure Q` form a compact subset of `dom i`.
  set K := (A.chart i).symm '' closure (Q : Set E)
  have hK : IsCompact K := hQc.image_of_continuousOn ((A.continuousOn_chart_symm i).mono hQi)
  have hKi : K ⊆ A.dom i := by
    rintro _ ⟨z, hz, rfl⟩
    exact A.symm_mem_dom (hQi hz)
  have hS : IsClosed (closure (A.image j : Set E) ∩ (A.chart j).symm ⁻¹' K) :=
    ((A.chart j).continuousOn_symm.mono
      (A.closure_image_subset_target j)).preimage_isClosed_of_isClosed isClosed_closure hK.isClosed
  have hPS : (A.localizedImage i j Q : Set E) ⊆
      closure (A.image j : Set E) ∩ (A.chart j).symm ⁻¹' K := by
    intro y hy
    obtain ⟨hyj, hyi, hyQ⟩ := mem_localizedImage.1 hy
    refine ⟨subset_closure hyj, A.chart i ((A.chart j).symm y), subset_closure hyQ, ?_⟩
    exact (A.chart i).left_inv (A.dom_subset_chart_source i hyi)
  refine (closure_minimal hPS hS).trans fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := A.closure_image_subset_chart_image_closure_dom j hy.1
  have hxs : x ∈ (A.chart j).source := A.closure_dom_subset_source j hx
  have hxK := hy.2
  rw [mem_preimage, (A.chart j).left_inv hxs] at hxK
  refine A.mem_transferDomain.2 ⟨(A.chart j).map_source hxs, ?_⟩
  rw [(A.chart j).left_inv hxs]
  exact ⟨A.dom_subset_chart_source i (hKi hxK), A.closure_dom_subset_baseSet j hx,
    A.dom_subset_baseSet i (hKi hxK)⟩

/-- A point of the image of chart `j` outside the localized image does not come from a point of
`K ⊆ Q` read in chart `i`. -/
theorem symm_notMem_image_of_notMem_localizedImage [T2Space E] {i j : Fin A.n} {Q : Opens E}
    {K : Set E} (hKQ : K ⊆ Q) (hQi : (Q : Set E) ⊆ A.image i) {y : E} (hy : y ∈ A.image j)
    (hyP : y ∉ A.localizedImage i j Q) : (A.chart j).symm y ∉ (A.chart i).symm '' K := by
  rintro ⟨z, hz, hzy⟩
  have hzi : z ∈ A.image i := hQi (hKQ hz)
  -- The point is `(A.chart i).symm z`, which chart `i` reads as `z ∈ Q`.
  refine hyP (mem_localizedImage.2 ⟨hy, ?_, ?_⟩)
  · rw [← hzy]
    exact A.symm_mem_dom hzi
  · rw [← hzy, (A.chart i).right_inv (A.closure_image_subset_target i (subset_closure hzi))]
    exact hKQ hz

end FiniteBundleAtlas

end Geometry

section Bundle

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-- The coordinate change from bundle chart `i` to bundle chart `j`, read in chart `j`, is `C^n` on
the transfer domain. -/
theorem contDiffOn_coordChangeL_transferDomain (i j : Fin A.n) :
    ContDiffOn ℝ n
      (fun y ↦ ((A.triv i).coordChangeL ℝ (A.triv j) ((A.chart j).symm y) : F →L[ℝ] F))
      (A.transferDomain i j) := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiffOn_coordChangeL (IB := 𝓘(ℝ, E)) (A.triv i) (A.triv j)).comp
    (contMDiffOn_chart_symm.mono inter_subset_left) fun _ hy ↦ ⟨hy.2.2.2, hy.2.2.1⟩

end FiniteBundleAtlas

end Bundle

end TauCeti
