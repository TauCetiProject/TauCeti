/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# The side of a bicollared hypersurface is a manifold with boundary

Let `M` be a topological `(n + 1)`-manifold and `f : N → M` an `n`-manifold with a bicollar
`b : N × ℝ → M` (`TauCeti.IsBicollar`). A *side* of the bicollar is a set `C ⊆ M` which meets the
bicollar exactly in its half `b (N × [0, ∞))`, and which is open in `M` away from the image of `f`.
Cutting `M` along the image of `f` and keeping `C` produces a topological manifold with boundary:
this file equips `C` with charts in the Euclidean half-space `EuclideanHalfSpace (n + 1)` and shows
that its manifold boundary is exactly the image of `f`.

The charts are of two kinds.

* At a point of the image of `f`, the chart reads the bicollar backwards: a point `b (y, t)` with
  `t ≥ 0` goes to the chart coordinates of `y` in `N` together with the normal coordinate `t`,
  assembled into a point of the half-space by `TauCeti.EuclideanHalfSpace.collarDiffeomorph`. The
  image of `f` is sent to the boundary hyperplane.
* At any other point of `C`, the chart is a chart of `M`, followed by a fixed homeomorphism of
  `ℝⁿ⁺¹` onto the open half-space `{x | 0 < x 0}` (exponentiating the zeroth coordinate). These
  points are therefore interior points.

This is how the manifolds with boundary of geometric topology arise from closed manifolds: the
exterior of a knot is the side of the boundary torus of a solid torus neighbourhood, and the
complement of an open ball, deleted for a connected sum, is a side of the boundary sphere.

When `M` and `N` are `C^k` manifolds and the bicollar is a `C^k` local diffeomorphism of `N × ℝ`
into `M`, these charts have `C^k` transition maps, so the side is a `C^k` manifold with boundary.
Between two collar charts the transition is a chart change of `N` times the identity of the
normal coordinate, and between two interior charts it is a chart change of `M`. Between a collar
chart and an interior chart it is the bicollar, or its inverse, read in charts: it is only defined
at positive normal coordinate, where the truncation of the normal coordinate at `0` plays no role.

## Main definitions

* `TauCeti.IsBicollar.sideChartedSpace`: the charted-space structure on a side of a bicollar,
  modelled on `EuclideanHalfSpace (n + 1)`. Every charted space is a `C⁰` manifold, so this is a
  topological manifold with boundary, and it is a smooth one when the bicollar is smooth.

## Main results

* `TauCeti.IsBicollar.boundary_sideChartedSpace`: the manifold boundary of the side is the image
  of `f`.
* `TauCeti.IsBicollar.interior_sideChartedSpace`: its manifold interior is the rest of the side.
* `TauCeti.IsBicollar.isManifold_sideChartedSpace`: the side of a smooth bicollar is a smooth
  manifold with boundary.
* `TauCeti.IsBicollar.contMDiff_subtypeVal_sideChartedSpace`: its inclusion into `M` is smooth.

## Implementation notes

The charted-space structure depends on the chosen bicollar: a set `C` may be a side of several
bicollars, so `sideChartedSpace` is a definition rather than an instance.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341, for bicollared hypersurfaces.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 9F, for knot exteriors as
  manifolds with boundary.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  {f : N → M} {b : N × ℝ → M} {C : Set M}

namespace IsBicollar

/-- The nonnegative half of a bicollar, read in the half-space model of the normal direction and
viewed in the side `C`. -/
private def collarPiece (hC : b ⁻¹' C = univ ×ˢ Ici 0) : N × EuclideanHalfSpace 1 → C :=
  codRestrict (fun p => b (p.1, p.2.val 0)) C fun p => by
    have hp : (p.1, p.2.val 0) ∈ b ⁻¹' C := by
      rw [hC]
      exact ⟨mem_univ _, p.2.property⟩
    exact hp

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem coe_collarPiece (hC : b ⁻¹' C = univ ×ˢ Ici 0) (p : N × EuclideanHalfSpace 1) :
    (collarPiece hC p : M) = b (p.1, p.2.val 0) :=
  (rfl)

private theorem isOpenEmbedding_collarPiece (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) : IsOpenEmbedding (collarPiece hC) := by
  have hcoord : IsEmbedding fun s : EuclideanHalfSpace 1 => s.val 0 :=
    Function.LeftInverse.isEmbedding EuclideanHalfSpace.normalRay_normalCoord
      EuclideanHalfSpace.continuous_normalRay (by fun_prop)
  refine ⟨((hb.isOpenEmbedding.isEmbedding.comp (IsEmbedding.id.prodMap hcoord)).codRestrict
    C _), ?_⟩
  have hrange : range (collarPiece hC) = Subtype.val ⁻¹' range b := by
    ext x
    refine ⟨?_, fun ⟨p, hp⟩ => ?_⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, (coe_collarPiece hC p).symm⟩
    · have hp' : p ∈ b ⁻¹' C := by
        rw [mem_preimage, hp]
        exact x.property
      rw [hC] at hp'
      refine ⟨(p.1, EuclideanHalfSpace.normalRay p.2), Subtype.ext ?_⟩
      rw [coe_collarPiece, EuclideanHalfSpace.normalRay_coe_apply, max_eq_left hp'.2, ← hp]
  rw [hrange]
  exact hb.isOpenEmbedding.isOpen_range.preimage continuous_subtypeVal

private theorem collarPiece_apply_zero (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (y : N) : (collarPiece hC (y, 0) : M) = f y := by
  rw [coe_collarPiece, EuclideanHalfSpace.val_zero_apply, hb.apply_zero]

/-- The chart of a side of a bicollar at a point `f y`: read the point through the bicollar, take
the chart of `N` at `y` on the first coordinate, and assemble the result with the normal
coordinate into a point of the half-space. -/
private def collarChart (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hb : IsBicollar f b) (y : N) :
    OpenPartialHomeomorph C (EuclideanHalfSpace (n + 1)) :=
  haveI : Nonempty (N × EuclideanHalfSpace 1) := ⟨(y, 0)⟩
  ((isOpenEmbedding_collarPiece hb hC).toOpenPartialHomeomorph _).symm.trans
    (((chartAt (EuclideanSpace ℝ (Fin n)) y).prod (OpenPartialHomeomorph.refl _)).trans
      (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).toHomeomorph.toOpenPartialHomeomorph)

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
private theorem collarChart_spec (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0) (y : N)
    {x : C} (hx : (x : M) = f y) :
    x ∈ (collarChart (n := n) hC hb y).source ∧ (collarChart (n := n) hC hb y x).val 0 = 0 := by
  have : Nonempty (N × EuclideanHalfSpace 1) := ⟨(y, 0)⟩
  have hxy : x = collarPiece hC (y, 0) := Subtype.ext (by rw [hx, collarPiece_apply_zero hb])
  have hsymm : ((isOpenEmbedding_collarPiece hb hC).toOpenPartialHomeomorph _).symm x = (y, 0) := by
    rw [hxy, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  refine ⟨?_, ?_⟩
  · simp only [collarChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.prod_source,
      OpenPartialHomeomorph.refl_source, Homeomorph.toOpenPartialHomeomorph_source, preimage_univ,
      inter_univ, mem_inter_iff, mem_preimage, hsymm, mem_prod, mem_univ, and_true]
    exact ⟨⟨_, hxy.symm⟩, mem_chart_source _ y⟩
  · simp only [collarChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, id_eq,
      Homeomorph.toOpenPartialHomeomorph_apply, Diffeomorph.coe_toHomeomorph,
      EuclideanHalfSpace.collarDiffeomorph_apply_zero, EuclideanHalfSpace.val_zero_apply]

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
private theorem isOpenEmbedding_inclusion_sdiff (hCo : IsOpen (C \ range f)) :
    IsOpenEmbedding (inclusion (sdiff_subset : C \ range f ⊆ C)) :=
  IsOpenEmbedding.inclusion sdiff_subset (hCo.preimage continuous_subtypeVal)

/-- The chart of a side of a bicollar at a point `x` off the image of `f`: a chart of `M` at `x`,
followed by a homeomorphism of `ℝⁿ⁺¹` onto the open half-space. -/
private def interiorChart (hCo : IsOpen (C \ range f)) (x : C) (hx : (x : M) ∉ range f) :
    OpenPartialHomeomorph C (EuclideanHalfSpace (n + 1)) :=
  haveI : Nonempty ↥(C \ range f) := ⟨⟨x, x.property, hx⟩⟩
  ((isOpenEmbedding_inclusion_sdiff hCo).toOpenPartialHomeomorph _).symm.trans
    ((hCo.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _).trans
      ((chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).trans
        ((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph _)))

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
private theorem interiorChart_spec (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) :
    x ∈ (interiorChart (n := n) hCo x hx).source ∧ 0 < (interiorChart (n := n) hCo x hx x).val 0
        := by
  have : Nonempty ↥(C \ range f) := ⟨⟨x, x.property, hx⟩⟩
  have hinc := isOpenEmbedding_inclusion_sdiff hCo
  have hsymm : (hinc.toOpenPartialHomeomorph _).symm x = ⟨x, x.property, hx⟩ := by
    have h := hinc.toOpenPartialHomeomorph_left_inv (x := (⟨x, x.property, hx⟩ : ↥(C \ range f)))
    exact h
  refine ⟨?_, ?_⟩
  · simp only [interiorChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, IsOpenEmbedding.toOpenPartialHomeomorph_apply,
      preimage_univ, inter_univ, univ_inter, mem_inter_iff, mem_preimage, hsymm]
    refine ⟨⟨⟨x, x.property, hx⟩, rfl⟩, mem_chart_source _ _⟩
  · simp only [interiorChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    rw [EuclideanHalfSpace.interiorEmbedding_coe_apply_zero]
    exact Real.exp_pos _

open Classical in
/-- The preferred chart of a side of a bicollar: a collar chart on the image of `f`, and an
interior chart elsewhere. -/
private def sideChart (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) (x : C) : OpenPartialHomeomorph C (EuclideanHalfSpace (n + 1)) :=
  if h : (x : M) ∈ range f then collarChart hC hb h.choose else interiorChart hCo x h

private theorem sideChart_spec (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) (x : C) :
    x ∈ (sideChart (n := n) hb hC hCo x).source ∧
      ((sideChart (n := n) hb hC hCo x x).val 0 = 0 ↔ (x : M) ∈ range f) := by
  by_cases h : (x : M) ∈ range f
  · rw [sideChart, dite_eq_left h]
    exact (collarChart_spec hb hC _ h.choose_spec.symm).imp_right fun h0 => iff_of_true h0 h
  · rw [sideChart, dite_eq_right h]
    exact (interiorChart_spec hCo x h).imp_right fun h0 => iff_of_false h0.ne' h

/-- A side `C` of a bicollar `b` of `f : N → M` — a set meeting the bicollar exactly in its
nonnegative half and open away from the image of `f` — is charted on the Euclidean half-space
`EuclideanHalfSpace (n + 1)`. The image of `f` is its manifold boundary
(`TauCeti.IsBicollar.boundary_sideChartedSpace`). -/
@[instance_reducible]
def sideChartedSpace (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) : ChartedSpace (EuclideanHalfSpace (n + 1)) C where
  atlas := range (sideChart hb hC hCo)
  chartAt := sideChart hb hC hCo
  mem_chart_source x := (sideChart_spec hb hC hCo x).1
  chart_mem_atlas x := mem_range_self x

/-- The manifold boundary of a side of a bicollar of `f` is the image of `f`. -/
theorem boundary_sideChartedSpace (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    (𝓡∂ (n + 1)).boundary C = Subtype.val ⁻¹' range f := by
  let := hb.sideChartedSpace (n := n) hC hCo
  ext x
  simp only [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint, extChartAt_coe,
    Function.comp_apply, frontier_range_modelWithCornersEuclideanHalfSpace,
    modelWithCornersEuclideanHalfSpace_apply, mem_ofPred_eq, mem_preimage, eq_comm (a := (0 : ℝ))]
  exact (sideChart_spec hb hC hCo x).2

/-- The manifold interior of a side of a bicollar of `f` is the part of the side off the image
of `f`. -/
theorem interior_sideChartedSpace (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    (𝓡∂ (n + 1)).interior C = Subtype.val ⁻¹' (range f)ᶜ := by
  let := hb.sideChartedSpace (n := n) hC hCo
  rw [← ModelWithCorners.compl_boundary, hb.boundary_sideChartedSpace hC hCo, preimage_compl]

/-! ### Smoothness of the side -/

section Smooth

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
private theorem collarChart_apply_collarPiece (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (y : N) (q : N × EuclideanHalfSpace 1) :
    collarChart (n := n) hC hb y (collarPiece hC q) =
      EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
        (chartAt (EuclideanSpace ℝ (Fin n)) y q.1, q.2) := by
  have : Nonempty (N × EuclideanHalfSpace 1) := ⟨(y, 0)⟩
  simp only [collarChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, OpenPartialHomeomorph.prod_apply,
    OpenPartialHomeomorph.refl_apply, id_eq, Homeomorph.toOpenPartialHomeomorph_apply,
    Diffeomorph.coe_toHomeomorph]

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
private theorem collarChart_symm_apply (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (y : N) (z : EuclideanHalfSpace (n + 1)) :
    (collarChart (n := n) hC hb y).symm z = collarPiece hC
      ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm
          ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1,
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).2) := by
  simp [collarChart]

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
private theorem mem_collarChart_target (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (y : N) {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ (collarChart (n := n) hC hb y).target) :
    ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) y).target := by
  simpa [collarChart] using hz

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
private theorem exists_of_mem_collarChart_source (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (y : N) {c : C}
    (hc : c ∈ (collarChart (n := n) hC hb y).source) :
    ∃ q, collarPiece hC q = c ∧ q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source := by
  simp only [collarChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source, mem_prod] at hc
  obtain ⟨⟨q, rfl⟩, ⟨hq, -⟩, -⟩ := hc
  have : Nonempty (N × EuclideanHalfSpace 1) := ⟨q⟩
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv] at hq
  exact ⟨q, rfl, hq⟩

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
private theorem interiorChart_apply (hCo : IsOpen (C \ range f)) (x : C) (hx : (x : M) ∉ range f)
    {c : C} (hc : (c : M) ∉ range f) :
    interiorChart (n := n) hCo x hx c = EuclideanHalfSpace.interiorEmbedding n
      (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M) c) := by
  have : Nonempty ↥(C \ range f) := ⟨⟨x, x.property, hx⟩⟩
  have hsymm : ((isOpenEmbedding_inclusion_sdiff hCo).toOpenPartialHomeomorph _).symm c =
      ⟨c, c.property, hc⟩ :=
    (isOpenEmbedding_inclusion_sdiff hCo).toOpenPartialHomeomorph_left_inv
      (x := (⟨c, c.property, hc⟩ : ↥(C \ range f)))
  simp only [interiorChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply]

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
private theorem mem_interiorChart_source (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) {c : C} (hc : c ∈ (interiorChart (n := n) hCo x hx).source) :
    (c : M) ∉ range f ∧ (c : M) ∈ (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).source := by
  have hcf : (c : M) ∉ range f := by
    rintro ⟨y, hy⟩
    simp only [interiorChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      mem_inter_iff] at hc
    obtain ⟨⟨c', hc'⟩, -⟩ := hc
    rw [← hc'] at hy
    exact c'.property.2 ⟨y, hy⟩
  have : Nonempty ↥(C \ range f) := ⟨⟨x, x.property, hx⟩⟩
  have hsymm : ((isOpenEmbedding_inclusion_sdiff hCo).toOpenPartialHomeomorph _).symm c =
      ⟨c, c.property, hcf⟩ :=
    (isOpenEmbedding_inclusion_sdiff hCo).toOpenPartialHomeomorph_left_inv
      (x := (⟨c, c.property, hcf⟩ : ↥(C \ range f)))
  have hc' : (∀ y, f y ≠ c) ∧ (c : M) ∈ (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).source :=
    by simpa [interiorChart, hsymm] using hc
  exact ⟨hcf, hc'.2⟩

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
private theorem mem_interiorChart_target (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (interiorChart (n := n) hCo x hx).target) :
    0 < z.val 0 ∧
      ((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph _).symm z ∈
        (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).target ∧
      ((interiorChart (n := n) hCo x hx).symm z : M) =
        (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).symm
          (((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
            _).symm z) := by
  have : Nonempty ↥(C \ range f) := ⟨⟨x, x.property, hx⟩⟩
  let ie := (EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
    (EuclideanHalfSpace.interiorEmbedding n)
  let e := chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)
  have hz' : ((∃ v, EuclideanHalfSpace.interiorEmbedding n v = z) ∧ ie.symm z ∈ e.target) ∧
      e.symm (ie.symm z) ∈ C ∧ ∀ y, f y ≠ e.symm (ie.symm z) := by
    simpa [interiorChart, ie, e] using hz
  obtain ⟨⟨⟨v, rfl⟩, hv⟩, hC', hf'⟩ := hz'
  refine ⟨by rw [EuclideanHalfSpace.interiorEmbedding_coe_apply_zero]; exact Real.exp_pos _,
    hv, ?_⟩
  have hm : e.symm (ie.symm (EuclideanHalfSpace.interiorEmbedding n v)) ∈
      range (Subtype.val : ↥(C \ range f) → M) :=
    ⟨⟨_, hC', fun ⟨y, hy⟩ ↦ hf' y hy⟩, rfl⟩
  simpa [interiorChart] using hCo.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_right_inv _ hm

/-- A point of the source of a chart transition `e.symm ≫ₕ e'` lies in the target of `e`, and
`e.symm` sends it into the source of `e'`. -/
private theorem mem_target_and_mem_source_of_mem_symm_trans_source {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {e e' : OpenPartialHomeomorph α β} {w : β}
    (hw : w ∈ (e.symm ≫ₕ e').source) : w ∈ e.target ∧ e.symm w ∈ e'.source :=
  hw

variable {k : WithTop ℕ∞}

/-- Read through the inverse of a collar chart, the point of `N × [0, ∞)` depends smoothly on
the chart coordinates. -/
private theorem contMDiffAt_collarChart_symm_pair [IsManifold (𝓡 n) k N] (y : N)
    {z : EuclideanHalfSpace (n + 1)}
    (hz : ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) y).target) :
    ContMDiffAt (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k (fun z ↦
      ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm
          ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1,
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).2)) z := by
  have hcd : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm :=
    (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm.contMDiff.of_le le_top
  exact ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y) hz).comp z
    (contMDiff_fst.comp hcd).contMDiffAt).prodMk (contMDiff_snd.comp hcd).contMDiffAt

/-- Read through the inverse of a collar chart, the point of `M` depends smoothly on the chart
coordinates. -/
private theorem contMDiffAt_collarChart_symm_coe [IsManifold (𝓡 n) k N]
    (hbd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b) (y : N)
    {z : EuclideanHalfSpace (n + 1)}
    (hz : ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) y).target) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) k (fun z ↦ b
      ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm
          ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1,
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).2.val 0)) z := by
  have hp := contMDiffAt_collarChart_symm_pair (k := k) y hz
  have hq : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod 𝓘(ℝ)) k
      (fun p : N × EuclideanHalfSpace 1 ↦ (p.1, p.2.val 0)) :=
    contMDiff_fst.prodMk ((contDiff_piLp_apply 2).contMDiff.comp
      ((𝓡∂ 1).contMDiff.comp contMDiff_snd))
  -- Elaborated without the expected type, which would unify the pair map with `collarDiffeomorph`.
  have h := hbd.contMDiff.contMDiffAt.comp z (hq.contMDiffAt.comp z hp)
  exact h

/-- In an interior chart, the point of `M` depends smoothly on the chart coordinates. -/
private theorem contMDiffAt_interiorChart_symm_coe [IsManifold (𝓡 (n + 1)) k M] (x : M)
    {z : EuclideanHalfSpace (n + 1)}
    (hz : 0 < z.val 0)
    (hz' : ((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
      _).symm z ∈ (chartAt (EuclideanSpace ℝ (Fin (n + 1))) x).target) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) k (fun z ↦
      (chartAt (EuclideanSpace ℝ (Fin (n + 1))) x).symm
        (((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
          _).symm z)) z :=
  (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hz').comp z
    ((EuclideanHalfSpace.contMDiffOn_interiorEmbedding_symm n).contMDiffAt
      ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hz))

/-- Reading a smooth family of points of `N × [0, ∞)` in a collar chart is smooth. -/
private theorem contMDiffAt_collarDiffeomorph_chartAt [IsManifold (𝓡 n) k N] (y : N)
    {g : EuclideanHalfSpace (n + 1) → N × EuclideanHalfSpace 1} {z : EuclideanHalfSpace (n + 1)}
    (hg : ContMDiffAt (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k g z)
    (hgz : (g z).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k (fun z ↦ EuclideanHalfSpace.collarDiffeomorph
      (k := ⊤) n (chartAt (EuclideanSpace ℝ (Fin n)) y (g z).1, (g z).2)) z :=
  ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).contMDiff.of_le le_top).contMDiffAt.comp z
    (((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y) hgz).comp z
      (contMDiffAt_fst.comp z hg)).prodMk (contMDiffAt_snd.comp z hg))

/-- Reading a smooth family of points of `M` in an interior chart is smooth. -/
private theorem contMDiffAt_interiorEmbedding_chartAt [IsManifold (𝓡 (n + 1)) k M] (x : M)
    {σ : EuclideanHalfSpace (n + 1) → M} {z : EuclideanHalfSpace (n + 1)}
    (hσ : ContMDiffAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) k σ z)
    (hσz : σ z ∈ (chartAt (EuclideanSpace ℝ (Fin (n + 1))) x).source) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k (fun z ↦ EuclideanHalfSpace.interiorEmbedding n
      (chartAt (EuclideanSpace ℝ (Fin (n + 1))) x (σ z))) z :=
  (EuclideanHalfSpace.contMDiff_interiorEmbedding n).contMDiffAt.comp z
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hσz).comp z hσ)

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
/-- A point of a collar chart's target read in a second collar chart. -/
private theorem collarChart_symm_mem_collarChart_source (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (y y' : N) {z : EuclideanHalfSpace (n + 1)}
    (hz : (collarChart (n := n) hC hb y).symm z ∈ (collarChart (n := n) hC hb y').source) :
    (chartAt (EuclideanSpace ℝ (Fin n)) y).symm
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm z).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) y').source := by
  obtain ⟨q, hq, hq'⟩ := exists_of_mem_collarChart_source (n := n) hb hC y' hz
  rw [collarChart_symm_apply] at hq
  rwa [(isOpenEmbedding_collarPiece hb hC).injective hq] at hq'

omit [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] in
/-- Transitions between two collar charts are smooth. -/
private theorem contMDiffOn_collarChart_symm_trans_collarChart [IsManifold (𝓡 n) k N]
    (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0) (y y' : N) :
    ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      ((collarChart (n := n) hC hb y).symm ≫ₕ collarChart (n := n) hC hb y')
      ((collarChart (n := n) hC hb y).symm ≫ₕ collarChart (n := n) hC hb y').source := by
  rintro z ⟨hzt, hzs⟩
  have hF : ⇑((collarChart (n := n) hC hb y).symm ≫ₕ collarChart (n := n) hC hb y') = fun w ↦
      EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
        (chartAt (EuclideanSpace ℝ (Fin n)) y' ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm
          ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm w).1),
          ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm w).2) := by
    ext1 w
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, collarChart_symm_apply,
      collarChart_apply_collarPiece]
  rw [hF]
  exact (contMDiffAt_collarDiffeomorph_chartAt y'
    (contMDiffAt_collarChart_symm_pair y (mem_collarChart_target hb hC y hzt))
    (collarChart_symm_mem_collarChart_source hb hC y y' hzs)).contMDiffWithinAt

/-- Transitions from a collar chart to an interior chart are smooth. -/
private theorem contMDiffOn_collarChart_symm_trans_interiorChart [IsManifold (𝓡 (n + 1)) k M]
    [IsManifold (𝓡 n) k N] (hb : IsBicollar f b)
    (hbd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hCo : IsOpen (C \ range f)) (y : N) (x : C)
    (hx : (x : M) ∉ range f) :
    ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      ((collarChart (n := n) hC hb y).symm ≫ₕ interiorChart (n := n) hCo x hx)
      ((collarChart (n := n) hC hb y).symm ≫ₕ interiorChart (n := n) hCo x hx).source := by
  have hF : ∀ w ∈ ((collarChart (n := n) hC hb y).symm ≫ₕ interiorChart (n := n) hCo x hx).source,
      ((collarChart (n := n) hC hb y).symm ≫ₕ interiorChart (n := n) hCo x hx) w =
        EuclideanHalfSpace.interiorEmbedding n (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)
          (b ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm
            ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm w).1,
            ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm w).2.val 0))) := by
    intro w hw
    replace hw := (mem_target_and_mem_source_of_mem_symm_trans_source hw).2
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      interiorChart_apply hCo x hx (mem_interiorChart_source hCo x hx hw).1,
      collarChart_symm_apply, coe_collarPiece]
  refine ContMDiffOn.congr ?_ hF
  intro z hz
  obtain ⟨hzt, hzs⟩ := mem_target_and_mem_source_of_mem_symm_trans_source hz
  have hzs' := (mem_interiorChart_source hCo x hx hzs).2
  rw [collarChart_symm_apply, coe_collarPiece] at hzs'
  exact (contMDiffAt_interiorEmbedding_chartAt (x : M)
    (contMDiffAt_collarChart_symm_coe hbd y (mem_collarChart_target hb hC y hzt))
    hzs').contMDiffWithinAt

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
/-- Transitions between two interior charts are smooth. -/
private theorem contMDiffOn_interiorChart_symm_trans_interiorChart [IsManifold (𝓡 (n + 1)) k M]
    (hCo : IsOpen (C \ range f)) (x : C) (hx : (x : M) ∉ range f) (x' : C)
    (hx' : (x' : M) ∉ range f) :
    ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      ((interiorChart (n := n) hCo x hx).symm ≫ₕ interiorChart (n := n) hCo x' hx')
      ((interiorChart (n := n) hCo x hx).symm ≫ₕ interiorChart (n := n) hCo x' hx').source := by
  have hF : ∀ w ∈ ((interiorChart (n := n) hCo x hx).symm ≫ₕ
      interiorChart (n := n) hCo x' hx').source,
      ((interiorChart (n := n) hCo x hx).symm ≫ₕ interiorChart (n := n) hCo x' hx') w =
        EuclideanHalfSpace.interiorEmbedding n (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x' : M)
          ((chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).symm
            (((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
              _).symm w))) := by
    intro w hw
    obtain ⟨hwt, hw⟩ := mem_target_and_mem_source_of_mem_symm_trans_source hw
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      interiorChart_apply hCo x' hx' (mem_interiorChart_source hCo x' hx' hw).1,
      (mem_interiorChart_target hCo x hx hwt).2.2]
  refine ContMDiffOn.congr ?_ hF
  intro z hz
  obtain ⟨hzt, hzs⟩ := mem_target_and_mem_source_of_mem_symm_trans_source hz
  obtain ⟨hz0, hzt', hzeq⟩ := mem_interiorChart_target hCo x hx hzt
  have hzs' := (mem_interiorChart_source hCo x' hx' hzs).2
  rw [hzeq] at hzs'
  exact (contMDiffAt_interiorEmbedding_chartAt (x' : M)
    (contMDiffAt_interiorChart_symm_coe (x : M) hz0 hzt') hzs').contMDiffWithinAt

/-- A point in the source of a transition from an interior chart to a collar chart is a point of
the collar at positive depth. -/
private theorem exists_collarPiece_eq_interiorChart_symm (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) (y : N) {w : EuclideanHalfSpace (n + 1)}
    (hw : w ∈ ((interiorChart (n := n) hCo x hx).symm ≫ₕ collarChart (n := n) hC hb y).source) :
    ∃ q, collarPiece hC q = (interiorChart (n := n) hCo x hx).symm w ∧
      q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source ∧ 0 < q.2.val 0 ∧
      (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).symm
          (((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
            _).symm w) = b (q.1, q.2.val 0) := by
  obtain ⟨hwt, hws⟩ := mem_target_and_mem_source_of_mem_symm_trans_source hw
  obtain ⟨q, hq, hq1⟩ := exists_of_mem_collarChart_source (n := n) hb hC y hws
  refine ⟨q, hq, hq1, lt_of_le_of_ne q.2.property fun h ↦ ?_,
    (mem_interiorChart_target hCo x hx hwt).2.2.symm.trans (by rw [← hq, coe_collarPiece])⟩
  -- Interior charts avoid the image of `f`, which is the collar at depth zero.
  refine (mem_interiorChart_source hCo x hx
    ((interiorChart (n := n) hCo x hx).map_target hwt)).1 ⟨q.1, ?_⟩
  rw [← hq, coe_collarPiece, ← h, hb.apply_zero]

open Function in
/-- Transitions from an interior chart to a collar chart are smooth. -/
private theorem contMDiffOn_interiorChart_symm_trans_collarChart [IsManifold (𝓡 (n + 1)) k M]
    [IsManifold (𝓡 n) k N] (hb : IsBicollar f b)
    (hbd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) (y : N) :
    ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      ((interiorChart (n := n) hCo x hx).symm ≫ₕ collarChart (n := n) hC hb y)
      ((interiorChart (n := n) hCo x hx).symm ≫ₕ collarChart (n := n) hC hb y).source := by
  have : Nonempty (N × ℝ) := ⟨(y, 0)⟩
  have hbinv (q : N × ℝ) : invFunOn b univ (b q) = q :=
    hb.isOpenEmbedding.injective.injOn.leftInvOn_invFunOn (mem_univ q)
  -- The point of `M` with interior-chart coordinates `w`.
  let σ : EuclideanHalfSpace (n + 1) → M := fun w ↦
    (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).symm
      (((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph _).symm w)
  have hF : ∀ w ∈ ((interiorChart (n := n) hCo x hx).symm ≫ₕ
      collarChart (n := n) hC hb y).source,
      ((interiorChart (n := n) hCo x hx).symm ≫ₕ collarChart (n := n) hC hb y) w =
        EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
          (chartAt (EuclideanSpace ℝ (Fin n)) y (invFunOn b univ (σ w)).1,
            EuclideanHalfSpace.normalRay (invFunOn b univ (σ w)).2) := by
    intro w hw
    obtain ⟨q, hq, -, -, hσ⟩ := exists_collarPiece_eq_interiorChart_symm hb hC hCo x hx y hw
    replace hσ : σ w = b (q.1, q.2.val 0) := hσ
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, ← hq, collarChart_apply_collarPiece,
      hσ, hbinv, EuclideanHalfSpace.normalRay_normalCoord]
  refine ContMDiffOn.congr ?_ hF
  intro z hz
  obtain ⟨q, -, hq1, hq2, hσz⟩ := exists_collarPiece_eq_interiorChart_symm hb hC hCo x hx y hz
  replace hσz : σ z = b (q.1, q.2.val 0) := hσz
  obtain ⟨hzt, -⟩ := mem_target_and_mem_source_of_mem_symm_trans_source hz
  obtain ⟨hz0, hzt', -⟩ := mem_interiorChart_target hCo x hx hzt
  have hB : ContMDiffAt (𝓡∂ (n + 1)) ((𝓡 n).prod 𝓘(ℝ)) k (fun w ↦ invFunOn b univ (σ w)) z := by
    refine ContMDiffAt.comp z ((IsLocalDiffeomorphOn.contMDiffOn_invFunOn
      (hbd.isLocalDiffeomorphOn univ) isOpen_univ
      hb.isOpenEmbedding.injective.injOn).contMDiffAt ?_)
      (contMDiffAt_interiorChart_symm_coe (x : M) hz0 hzt')
    rw [image_univ]
    exact hb.isOpenEmbedding.isOpen_range.mem_nhds ⟨_, hσz.symm⟩
  refine (contMDiffAt_collarDiffeomorph_chartAt y (g := fun w ↦
    ((invFunOn b univ (σ w)).1, EuclideanHalfSpace.normalRay (invFunOn b univ (σ w)).2))
    ((contMDiffAt_fst.comp z hB).prodMk ?_) (by simpa [hσz, hbinv] using hq1)).contMDiffWithinAt
  refine (EuclideanHalfSpace.contMDiffOn_normalRay.contMDiffAt (Ici_mem_nhds ?_)).comp z
    (contMDiffAt_snd.comp z hB)
  simpa [hσz, hbinv] using hq2

/-- **The side of a smooth bicollar is a smooth manifold with boundary.** Let `M` be a `C^k`
`(n + 1)`-manifold and `N` a `C^k` `n`-manifold. If the bicollar `b : N × ℝ → M` of `f` is a `C^k`
local diffeomorphism, then the charts of `TauCeti.IsBicollar.sideChartedSpace` on a side `C` have
`C^k` transition maps, so `C` is a `C^k` manifold with boundary, its boundary being the image of
`f` (`TauCeti.IsBicollar.boundary_sideChartedSpace`). -/
theorem isManifold_sideChartedSpace [IsManifold (𝓡 (n + 1)) k M] [IsManifold (𝓡 n) k N]
    (hb : IsBicollar f b) (hbd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hCo : IsOpen (C \ range f)) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    IsManifold (𝓡∂ (n + 1)) k C := by
  let := hb.sideChartedSpace (n := n) hC hCo
  have key (x x' : C) : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      ((sideChart (n := n) hb hC hCo x).symm ≫ₕ sideChart (n := n) hb hC hCo x')
      ((sideChart (n := n) hb hC hCo x).symm ≫ₕ sideChart (n := n) hb hC hCo x').source := by
    unfold sideChart
    split_ifs
    · exact contMDiffOn_collarChart_symm_trans_collarChart hb hC _ _
    · exact contMDiffOn_collarChart_symm_trans_interiorChart hb hbd hC hCo _ _ _
    · exact contMDiffOn_interiorChart_symm_trans_collarChart hb hbd hC hCo _ _ _
    · exact contMDiffOn_interiorChart_symm_trans_interiorChart hCo _ _ _ _
  refine { compatible := ?_ }
  rintro _ _ ⟨x, rfl⟩ ⟨x', rfl⟩
  have hsymm : ((sideChart (n := n) hb hC hCo x).symm ≫ₕ sideChart (n := n) hb hC hCo x').symm =
      (sideChart (n := n) hb hC hCo x').symm ≫ₕ sideChart hb hC hCo x := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  have hrefl : OpenPartialHomeomorph.refl (EuclideanHalfSpace (n + 1)) ∈
      IsManifold.maximalAtlas (𝓡∂ (n + 1)) k (EuclideanHalfSpace (n + 1)) :=
    IsManifold.chart_mem_maximalAtlas (0 : EuclideanHalfSpace (n + 1))
  simpa using symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn hrefl hrefl (key x x')
    (by rw [← OpenPartialHomeomorph.symm_source, hsymm]; exact key x' x)

/-- The inclusion of a side of a smooth bicollar into the ambient manifold is `C^k`, for the
manifold structure of `TauCeti.IsBicollar.isManifold_sideChartedSpace`. -/
theorem contMDiff_subtypeVal_sideChartedSpace [IsManifold (𝓡 (n + 1)) k M]
    [IsManifold (𝓡 n) k N] (hb : IsBicollar f b)
    (hbd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hCo : IsOpen (C \ range f)) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    ContMDiff (𝓡∂ (n + 1)) (𝓡 (n + 1)) k (Subtype.val : C → M) := by
  let := hb.sideChartedSpace (n := n) hC hCo
  intro c
  have hc := (sideChart (n := n) hb hC hCo c).map_source (sideChart_spec hb hC hCo c).1
  have key : ContMDiffAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) k
      (fun z ↦ ((sideChart (n := n) hb hC hCo c).symm z : M)) (sideChart hb hC hCo c c) := by
    revert hc
    unfold sideChart
    split_ifs
    · intro hc
      refine (contMDiffAt_collarChart_symm_coe hbd _
        (mem_collarChart_target hb hC _ hc)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z ↦ ?_)
      simp only [collarChart_symm_apply, coe_collarPiece]
    · intro hc
      obtain ⟨hz0, hzt, -⟩ := mem_interiorChart_target hCo c _ hc
      refine (contMDiffAt_interiorChart_symm_coe (c : M) hz0 hzt).congr_of_eventuallyEq
        (Filter.eventually_of_mem ((OpenPartialHomeomorph.open_target _).mem_nhds hc)
          fun z hz ↦ ?_)
      exact (mem_interiorChart_target hCo c _ hz).2.2
  rw [contMDiffAt_iff_source]
  exact key.comp_contMDiffWithinAt_of_eq ((𝓡∂ (n + 1)).contMDiffOn_symm _ (mem_range_self _))
    ((𝓡∂ (n + 1)).left_inv _)

end Smooth

end IsBicollar

end TauCeti
