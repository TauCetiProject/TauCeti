/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

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

## Main definitions

* `TauCeti.IsBicollar.sideChartedSpace`: the charted-space structure on a side of a bicollar,
  modelled on `EuclideanHalfSpace (n + 1)`. Every charted space is a `C⁰` manifold, so this is a
  topological manifold with boundary.

## Main results

* `TauCeti.IsBicollar.boundary_sideChartedSpace`: the manifold boundary of the side is the image
  of `f`.
* `TauCeti.IsBicollar.interior_sideChartedSpace`: its manifold interior is the rest of the side.

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
  codRestrict (fun p => b (p.1, p.2.1 0)) C fun p => by
    have hp : (p.1, p.2.1 0) ∈ b ⁻¹' C := by
      rw [hC]
      exact ⟨mem_univ _, p.2.2⟩
    exact hp

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem coe_collarPiece (hC : b ⁻¹' C = univ ×ˢ Ici 0) (p : N × EuclideanHalfSpace 1) :
    (collarPiece hC p : M) = b (p.1, p.2.1 0) :=
  (rfl)

private theorem isOpenEmbedding_collarPiece (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) : IsOpenEmbedding (collarPiece hC) := by
  have hcoord : IsEmbedding fun s : EuclideanHalfSpace 1 => s.1 0 :=
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
        exact x.2
      rw [hC] at hp'
      refine ⟨(p.1, EuclideanHalfSpace.normalRay p.2), Subtype.ext ?_⟩
      rw [coe_collarPiece, EuclideanHalfSpace.normalRay_coe_apply, max_eq_left hp'.2, ← hp]
  rw [hrange]
  exact hb.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val

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
    x ∈ (collarChart (n := n) hC hb y).source ∧ (collarChart (n := n) hC hb y x).1 0 = 0 := by
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
  IsOpenEmbedding.inclusion sdiff_subset (hCo.preimage continuous_subtype_val)

/-- The chart of a side of a bicollar at a point `x` off the image of `f`: a chart of `M` at `x`,
followed by a homeomorphism of `ℝⁿ⁺¹` onto the open half-space. -/
private def interiorChart (hCo : IsOpen (C \ range f)) (x : C) (hx : (x : M) ∉ range f) :
    OpenPartialHomeomorph C (EuclideanHalfSpace (n + 1)) :=
  haveI : Nonempty ↥(C \ range f) := ⟨⟨x, x.2, hx⟩⟩
  ((isOpenEmbedding_inclusion_sdiff hCo).toOpenPartialHomeomorph _).symm.trans
    ((hCo.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _).trans
      ((chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)).trans
        ((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph _)))

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
private theorem interiorChart_spec (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) :
    x ∈ (interiorChart (n := n) hCo x hx).source ∧ 0 < (interiorChart (n := n) hCo x hx x).1 0 := by
  have : Nonempty ↥(C \ range f) := ⟨⟨x, x.2, hx⟩⟩
  have hinc := isOpenEmbedding_inclusion_sdiff hCo
  have hsymm : (hinc.toOpenPartialHomeomorph _).symm x = ⟨x, x.2, hx⟩ := by
    have h := hinc.toOpenPartialHomeomorph_left_inv (x := (⟨x, x.2, hx⟩ : ↥(C \ range f)))
    exact h
  refine ⟨?_, ?_⟩
  · simp only [interiorChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, IsOpenEmbedding.toOpenPartialHomeomorph_apply,
      preimage_univ, inter_univ, univ_inter, mem_inter_iff, mem_preimage, hsymm]
    refine ⟨⟨⟨x, x.2, hx⟩, rfl⟩, mem_chart_source _ _⟩
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
      ((sideChart (n := n) hb hC hCo x x).1 0 = 0 ↔ (x : M) ∈ range f) := by
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

end IsBicollar

end TauCeti
