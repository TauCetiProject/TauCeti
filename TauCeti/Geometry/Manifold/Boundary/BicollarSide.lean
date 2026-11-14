/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
public import TauCeti.Geometry.Manifold.IsManifold.Ambient
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
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

If `M` and `N` are `C^k` manifolds and the bicollar is a `C^k` local diffeomorphism, these charts
are `C^k` compatible, so the side is a `C^k` manifold with boundary and its inclusion into `M` is
`C^k`. The comparison runs through `M`: an interior chart is a chart of `M` up to the exponential
of one coordinate, and a collar chart reads the inverse of the bicollar in a chart of `N`; the two
are compared by `TauCeti.isManifold_of_forall_mem_atlas_exists_contMDiffOn`.

## Main definitions

* `TauCeti.IsBicollar.sideChartedSpace`: the charted-space structure on a side of a bicollar,
  modelled on `EuclideanHalfSpace (n + 1)`. Every charted space is a `C⁰` manifold, so this is a
  topological manifold with boundary.

## Main results

* `TauCeti.IsBicollar.boundary_sideChartedSpace`: the manifold boundary of the side is the image
  of `f`.
* `TauCeti.IsBicollar.interior_sideChartedSpace`: its manifold interior is the rest of the side.
* `TauCeti.IsBicollar.isManifold_sideChartedSpace`: the side of a `C^k` bicollar is a `C^k`
  manifold with boundary.
* `TauCeti.IsBicollar.contMDiff_subtype_val_sideChartedSpace`: its inclusion into `M` is `C^k`.

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

/-! ### Smooth bicollars

If `M` and `N` are `C^k` manifolds and the bicollar `b` is a `C^k` local diffeomorphism, the side
charts read smoothly through the inclusion of the side into `M`: an interior chart is a chart of
`M` followed by `interiorEmbedding`, and a collar chart reads the inverse of `b` in a chart of `N`.
The criterion `TauCeti.isManifold_of_forall_mem_atlas_exists_contMDiffOn` then makes the side a
`C^k` manifold with boundary. -/

section Smooth

variable {k : WithTop ℕ∞}

variable [IsManifold (𝓡 (n + 1)) k M]

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
/-- An interior chart of a side is read smoothly through the inclusion into `M`: by
`interiorEmbedding` after the chart of `M`, and back by `EuclideanHalfSpace.interiorCoord` before
its inverse. -/
private theorem interiorChart_exists_contMDiffOn (hCo : IsOpen (C \ range f)) (x : C)
    (hx : (x : M) ∉ range f) :
    ∃ (F : M → EuclideanSpace ℝ (Fin (n + 1))) (G : EuclideanSpace ℝ (Fin (n + 1)) → M)
      (U : Set M) (V : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ContMDiffOn (𝓡 (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) k F U ∧
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 (n + 1)) k G V ∧
        ∀ z ∈ (interiorChart (n := n) hCo x hx).source, (z : M) ∈ U ∧
          (𝓡∂ (n + 1)) (interiorChart hCo x hx z) ∈ V ∧
          F z = (𝓡∂ (n + 1)) (interiorChart hCo x hx z) ∧
          G ((𝓡∂ (n + 1)) (interiorChart hCo x hx z)) = z := by
  have : Nonempty ↥(C \ range f) := ⟨⟨x, x.2, hx⟩⟩
  set c := chartAt (EuclideanSpace ℝ (Fin (n + 1))) (x : M)
  refine ⟨fun m => (EuclideanHalfSpace.interiorEmbedding n (c m)).1,
    fun w => c.symm (EuclideanHalfSpace.interiorCoord w), c.source,
    {w | 0 < w 0 ∧ EuclideanHalfSpace.interiorCoord w ∈ c.target},
    (EuclideanHalfSpace.contDiff_coe_interiorEmbedding n).contMDiff.comp_contMDiffOn
      contMDiffOn_chart,
    contMDiffOn_chart_symm.comp
      (EuclideanHalfSpace.contDiffOn_interiorCoord.contMDiffOn.mono fun _ hw => hw.1)
      fun _ hw => hw.2, fun z hz => ?_⟩
  -- A point of the source is the inclusion of a point of `C \ range f` lying in the source of `c`,
  -- and the chart sends it to `interiorEmbedding` of its coordinates in `c`.
  have hinc := isOpenEmbedding_inclusion_sdiff (f := f) hCo
  simp only [interiorChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, univ_inter, mem_inter_iff, mem_preimage,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply] at hz
  obtain ⟨⟨w, rfl⟩, hw⟩ := hz
  have hsymm : (hinc.toOpenPartialHomeomorph _).symm (inclusion sdiff_subset w) = w :=
    hinc.toOpenPartialHomeomorph_left_inv
  rw [hsymm] at hw
  have happ : interiorChart (n := n) hCo x hx (inclusion sdiff_subset w) =
      EuclideanHalfSpace.interiorEmbedding n (c w) := by
    simp only [interiorChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply, c]
  rw [happ, modelWithCornersEuclideanHalfSpace_apply, coe_inclusion]
  simp only [mem_ofPred_eq, EuclideanHalfSpace.interiorCoord_coe_interiorEmbedding, c.left_inv hw,
    EuclideanHalfSpace.interiorEmbedding_coe_apply_zero, Real.exp_pos, c.map_source hw, and_self,
    and_true]
  exact hw

variable [IsManifold (𝓡 n) k N]

omit [IsManifold (𝓡 (n + 1)) k M] in
/-- A collar chart of a side is read smoothly through the inclusion into `M`, when the bicollar is
a `C^k` local diffeomorphism: by the chart of `N` after the inverse of `b`, and back by `b` after
the inverse chart of `N`. -/
private theorem collarChart_exists_contMDiffOn (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b) (y : N) :
    ∃ (F : M → EuclideanSpace ℝ (Fin (n + 1))) (G : EuclideanSpace ℝ (Fin (n + 1)) → M)
      (U : Set M) (V : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ContMDiffOn (𝓡 (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) k F U ∧
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 (n + 1)) k G V ∧
        ∀ z ∈ (collarChart (n := n) hC hb y).source, (z : M) ∈ U ∧
          (𝓡∂ (n + 1)) (collarChart hC hb y z) ∈ V ∧
          F z = (𝓡∂ (n + 1)) (collarChart hC hb y z) ∧
          G ((𝓡∂ (n + 1)) (collarChart hC hb y z)) = z := by
  have : Nonempty (N × ℝ) := ⟨(y, 0)⟩
  have : Nonempty (N × EuclideanHalfSpace 1) := ⟨(y, 0)⟩
  set c := chartAt (EuclideanSpace ℝ (Fin n)) y
  set S := euclideanHalfSpaceBoundaryNormalEquiv n
  set binv := Function.invFunOn b univ
  have hinv : ∀ q, binv (b q) = q := fun q =>
    hb.isOpenEmbedding.injective.injOn.leftInvOn_invFunOn (mem_univ q)
  have hbinv : ContMDiffOn (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ)) k binv (range b) := by
    rw [← image_univ]
    exact (hd.isLocalDiffeomorphOn univ).contMDiffOn_invFunOn isOpen_univ
      hb.isOpenEmbedding.injective.injOn
  refine ⟨fun m => S (c (binv m).1, (binv m).2), fun w => b (c.symm (S.symm w).1, (S.symm w).2),
    {m | m ∈ range b ∧ (binv m).1 ∈ c.source}, {w | (S.symm w).1 ∈ c.target},
    S.contDiff.contMDiff.comp_contMDiffOn (ContMDiffOn.prodMk_space
      (contMDiffOn_chart.comp (contMDiff_fst.comp_contMDiffOn (hbinv.mono fun _ hm => hm.1))
        fun _ hm => hm.2)
      (contMDiff_snd.comp_contMDiffOn (hbinv.mono fun _ hm => hm.1))),
    hd.contMDiff.comp_contMDiffOn ((contMDiffOn_chart_symm.comp
      S.symm.contDiff.fst.contMDiff.contMDiffOn fun _ hw => hw).prodMk
        S.symm.contDiff.snd.contMDiff.contMDiffOn), fun z hz => ?_⟩
  -- A point of the source is the image `b (p.1, p.2 0)` of a point `p` of `N × [0, ∞)` with `p.1`
  -- in the source of `c`, and the chart sends it to the collar identification of `(c p.1, p.2)`.
  have hpiece := isOpenEmbedding_collarPiece hb hC
  simp only [collarChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, Homeomorph.toOpenPartialHomeomorph_source, preimage_univ,
    inter_univ, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true] at hz
  obtain ⟨⟨p, rfl⟩, hp⟩ := hz
  have hsymm : (hpiece.toOpenPartialHomeomorph _).symm (collarPiece hC p) = p :=
    hpiece.toOpenPartialHomeomorph_left_inv
  rw [hsymm] at hp
  have happ : (𝓡∂ (n + 1)) (collarChart (n := n) hC hb y (collarPiece hC p)) =
      S (c p.1, p.2.1 0) := by
    simp only [collarChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, id_eq,
      Homeomorph.toOpenPartialHomeomorph_apply, Diffeomorph.coe_toHomeomorph,
      modelWithCornersEuclideanHalfSpace_apply, EuclideanHalfSpace.coe_collarDiffeomorph_apply,
      EuclideanHalfSpace.collarAmbientEquiv_apply, S, c]
  rw [happ, coe_collarPiece]
  simp only [mem_ofPred_eq]
  rw [hinv, ContinuousLinearEquiv.symm_apply_apply, c.left_inv hp]
  exact ⟨⟨mem_range_self _, hp⟩, c.map_source hp, rfl, rfl⟩

omit [IsManifold (𝓡 (n + 1)) k M] [IsManifold (𝓡 n) k N] in
/-- Every chart of a side of a `C^k` bicollar is read smoothly through the inclusion into `M`. -/
private theorem forall_mem_atlas_exists_contMDiffOn [IsManifold (𝓡 (n + 1)) k M]
    [IsManifold (𝓡 n) k N] (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) (hd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    ∀ e ∈ atlas (EuclideanHalfSpace (n + 1)) C,
      ∃ (F : M → EuclideanSpace ℝ (Fin (n + 1))) (G : EuclideanSpace ℝ (Fin (n + 1)) → M)
        (U : Set M) (V : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        ContMDiffOn (𝓡 (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) k F U ∧
          ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 (n + 1)) k G V ∧
          ∀ z ∈ e.source, (z : M) ∈ U ∧ (𝓡∂ (n + 1)) (e z) ∈ V ∧ F z = (𝓡∂ (n + 1)) (e z) ∧
            G ((𝓡∂ (n + 1)) (e z)) = z := by
  rintro _ ⟨x, rfl⟩
  by_cases h : (x : M) ∈ range f
  · rw [sideChart, dite_eq_left h]
    exact collarChart_exists_contMDiffOn hb hC hd _
  · rw [sideChart, dite_eq_right h]
    exact interiorChart_exists_contMDiffOn hCo x h

/-- **The side of a smooth bicollar is a smooth manifold with boundary.** If `M` and `N` are `C^k`
manifolds and the bicollar `b : N × ℝ → M` is a `C^k` local diffeomorphism, then the charts of
`TauCeti.IsBicollar.sideChartedSpace` make the side `C` a `C^k` manifold modelled on the
half-space `EuclideanHalfSpace (n + 1)`, with boundary the image of `f`
(`TauCeti.IsBicollar.boundary_sideChartedSpace`). -/
theorem isManifold_sideChartedSpace (hb : IsBicollar f b) (hC : b ⁻¹' C = univ ×ˢ Ici 0)
    (hCo : IsOpen (C \ range f)) (hd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    IsManifold (𝓡∂ (n + 1)) k C :=
  letI := hb.sideChartedSpace (n := n) hC hCo
  isManifold_of_forall_mem_atlas_exists_contMDiffOn (I' := 𝓡 (n + 1)) (Subtype.val : C → M)
    (forall_mem_atlas_exists_contMDiffOn hb hC hCo hd)

/-- The inclusion of the side of a smooth bicollar into `M` is `C^k`. -/
theorem contMDiff_subtype_val_sideChartedSpace (hb : IsBicollar f b)
    (hC : b ⁻¹' C = univ ×ˢ Ici 0) (hCo : IsOpen (C \ range f))
    (hd : IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k b) :
    letI := hb.sideChartedSpace (n := n) hC hCo
    ContMDiff (𝓡∂ (n + 1)) (𝓡 (n + 1)) k (Subtype.val : C → M) :=
  letI := hb.sideChartedSpace (n := n) hC hCo
  contMDiff_of_forall_mem_atlas_exists_contMDiffOn (Subtype.val : C → M)
    (forall_mem_atlas_exists_contMDiffOn hb hC hCo hd)

end Smooth

end IsBicollar

end TauCeti
