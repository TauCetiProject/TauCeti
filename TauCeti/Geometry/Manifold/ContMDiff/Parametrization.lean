/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless

/-!
# Globally defined differentiable local parametrizations

Every point of a finite-dimensional boundaryless real `C^n` manifold lies in the image of a
`C^n` parametrization defined on an entire Cartesian space, with `C^n` inverse on its image,
for every finite order or smoothness order `n ≤ ∞`.
These parametrizations allow continuity and smoothness to be tested on globally defined plots,
without requiring a chart inverse to extend beyond its domain.
In particular, every point of a finite-dimensional boundaryless real manifold, on any boundaryless
model, has an open neighbourhood homeomorphic to `ℝᵐ`
(`TauCeti.exists_isOpen_mem_nonempty_homeomorph_euclideanSpace`).

The construction uses Mathlib's `OpenPartialHomeomorph.univBall` and `toEuclidean` to shrink
an ordinary manifold chart.

When the model space `F` is itself a real inner product space, no change of coordinates is needed:
every point of a boundaryless `C^n` manifold modelled on `F` is the centre of a coordinate ball, an
open embedding `F → N` which is a `C^n` local diffeomorphism
(`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`).

For an arbitrary model with corners, every interior point of a finite-dimensional real `C^n`
manifold has an open neighbourhood `C^n`-diffeomorphic to the Euclidean space of the same
dimension (`TauCeti.exists_opens_diffeomorph_euclideanSpace`). Such Euclidean neighbourhoods let
invariants computed on `ℝⁿ` be transported to small open subsets of a manifold.
-/

public noncomputable section

open Set Function Metric
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ∞} [IsManifold 𝓘(ℝ, E) n M]

/-- A point of a finite-dimensional boundaryless real `C^n` manifold, for `n ≤ ∞`, has `C^n`
local coordinates parametrized by an entire Cartesian space, with a `C^n` inverse on their
open image. -/
theorem exists_contMDiff_parametrization (x : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M,
      e.source = univ ∧ x ∈ e.target ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ, E) n e ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        n e.symm e.target := by
  let L := toEuclidean (E := E)
  let c := (chartAt E x).trans L.toHomeomorph.toOpenPartialHomeomorph
  have hc : c x ∈ c.target := c.map_source (by simp [c, mem_chart_source])
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) hc
  let b := OpenPartialHomeomorph.univBall (c x) r
  have hb : b.target ⊆ c.target := by
    simpa [b, OpenPartialHomeomorph.univBall_target _ hr] using hball
  have hbc : ∀ z, b z ∈ c.target := fun z => hb (b.map_source (by simp [b]))
  let e := b.trans c.symm
  have hs : e.source = univ := by
    apply eq_univ_of_forall
    intro z
    simp [e, hbc, b]
  have ht : x ∈ e.target := by
    simp [e, c, b, mem_chart_source,
      OpenPartialHomeomorph.univBall_target _ hr, hr]
  have hcs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      𝓘(ℝ, E) n c.symm c.target := by
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).comp
      (L.symm.contDiff.contMDiff.contMDiffOn (s := c.target)) (fun z hz => hz.2)
  have hcf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      n c c.source := by
    exact L.contDiff.contMDiff.comp_contMDiffOn
      ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := x)).mono inter_subset_left)
  refine ⟨e, hs, ht, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans]
    exact hcs.comp_contMDiff OpenPartialHomeomorph.contDiff_univBall.contMDiff
      hbc
  · rw [OpenPartialHomeomorph.coe_trans_symm]
    exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn.comp
      (hcf.mono inter_subset_left) (fun z hz => by
        simpa only [b, OpenPartialHomeomorph.univBall_target _ hr] using hz.2)

/-- Every point of a finite-dimensional boundaryless real manifold has an open neighbourhood
homeomorphic to `ℝᵐ`, where `m` is the dimension of the model vector space. The neighbourhood is
the image of a global parametrization of the copy of the manifold modelled on `E`. -/
theorem exists_isOpen_mem_nonempty_homeomorph_euclideanSpace {H N : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    (x : N) : ∃ U : Set N, IsOpen U ∧ x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  set e := BoundarylessModel.homeomorph I N
  -- Every charted space is a `C⁰` manifold; state it at the order used by the parametrization.
  have : IsManifold 𝓘(ℝ, E) ((0 : ℕ∞) : ℕ∞ω) (BoundarylessModel I N) :=
    inferInstanceAs (IsManifold 𝓘(ℝ, E) 0 _)
  obtain ⟨φ, hφ, hx, -⟩ :=
    exists_contMDiff_parametrization (E := E) (M := BoundarylessModel I N) (n := 0) (e x)
  exact ⟨e ⁻¹' φ.target, φ.open_target.preimage e.continuous, hx,
    ⟨(e.sets rfl).trans <| φ.toHomeomorphSourceTarget.symm.trans <|
      (Homeomorph.setCongr hφ).trans (Homeomorph.Set.univ _)⟩⟩

section CoordinateBall

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) n N]

/-- **Coordinate balls exist.** Every point `x` of a `C^n` manifold without boundary modelled on a
real inner product space `F` is the centre `e 0` of an open embedding `e : F → N` which is a `C^n`
local diffeomorphism: a chart inverse precomposed with a diffeomorphism of `F` onto a small
ball. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph (x : N) :
    ∃ e : F → N, e 0 = x ∧ Topology.IsOpenEmbedding e ∧
      IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) n e := by
  set c := chartAt F x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x)
    (c.map_source (mem_chart_source F x))
  -- A diffeomorphism of `F` onto a ball about `c x` inside the chart target.
  let b := OpenPartialHomeomorph.univBall (c x) r
  have hb (v : F) : b v ∈ c.target := hball <| by
    rw [← OpenPartialHomeomorph.univBall_target (c x) hr]
    exact b.map_source (by simp [b])
  let φ := b.trans c.symm
  have hφ : φ.source = univ := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.symm_source, univ_inter]
    exact eq_univ_of_forall hb
  refine ⟨φ, ?_, φ.isOpenEmbedding hφ, fun v ↦ ?_⟩
  · simp [φ, b, c]
  · let Φ := PartialDiffeomorph.ofOpenPartialHomeomorph (n := n) b
      OpenPartialHomeomorph.contDiff_univBall.contDiffOn
      (by rw [OpenPartialHomeomorph.univBall_target _ hr]
          exact OpenPartialHomeomorph.contDiffOn_univBall_symm)
    have hΦ : Φ.toPartialEquiv = b.toPartialEquiv :=
      PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv _ _ _
    have hbv : IsLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, F) n b v :=
      isLocalDiffeomorphAt_of_eqOn (Φ := Φ) (by simp [hΦ, b]) fun y _ ↦ by
        rw [hΦ, OpenPartialHomeomorph.coe_toPartialEquiv]
    exact hbv.comp (hg := c.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas x) (hb v))

end CoordinateBall

section EuclideanNeighbourhood

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I n N]

/-- **Euclidean neighbourhoods.** An interior point `x` of a finite-dimensional real `C^n` manifold
with corners, for `n ≤ ∞`, has an open neighbourhood which is `C^n`-diffeomorphic to the Euclidean
space of the same dimension. -/
theorem exists_opens_diffeomorph_euclideanSpace {x : N} (hx : I.IsInteriorPoint x) :
    ∃ U : TopologicalSpace.Opens N, x ∈ U ∧
      Nonempty (U ≃ₘ^n⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  -- The extended chart at `x`, followed by a linear equivalence with Euclidean space, maps a
  -- neighbourhood of `x` onto a ball, which `univBall` identifies with the whole space.
  let L := toEuclidean (E := E)
  set c := extChartAt I x
  -- A ball about `L (c x)` whose preimage under `L` lies in the target of the chart.
  have hT : L.symm ⁻¹' c.target ∈ 𝓝 (L (c x)) := by
    refine L.symm.continuous.continuousAt.preimage_mem_nhds ?_
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp hx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hT
  let b := OpenPartialHomeomorph.univBall (L (c x)) r
  have hb (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : b v ∈ ball (L (c x)) r := by
    rw [← OpenPartialHomeomorph.univBall_target _ hr]
    exact b.map_source (by simp [b])
  have hbT (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : L.symm (b v) ∈ c.target :=
    hball (hb v)
  let U : TopologicalSpace.Opens N :=
    ⟨c.source ∩ c ⁻¹' (L ⁻¹' ball (L (c x)) r),
      (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
        (isOpen_ball.preimage L.continuous)⟩
  have hU (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : c.symm (L.symm (b v)) ∈ U := by
    refine ⟨c.map_target (hbT v), ?_⟩
    simp only [mem_preimage, c.right_inv (hbT v), ContinuousLinearEquiv.apply_symm_apply]
    exact hb v
  refine ⟨U, ⟨mem_extChartAt_source x, mem_ball_self hr⟩, ⟨
    { toFun := fun u ↦ b.symm (L (c u))
      invFun := fun v ↦ ⟨c.symm (L.symm (b v)), hU v⟩
      left_inv := fun u ↦ Subtype.ext ?_
      right_inv := fun v ↦ ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }⟩⟩
  · have hu : L (c u) ∈ b.target := by
      rw [OpenPartialHomeomorph.univBall_target _ hr]
      exact u.2.2
    simp only [b.right_inv hu, ContinuousLinearEquiv.symm_apply_apply]
    exact c.left_inv u.2.1
  · simp only [c.right_inv (hbT v), ContinuousLinearEquiv.apply_symm_apply]
    exact b.left_inv (by simp [b])
  · have hf : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) n
        (fun y ↦ b.symm (L (c y))) U :=
      OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn.comp
        (L.contDiff.contMDiff.comp_contMDiffOn
          ((contMDiffOn_extChartAt (x := x)).mono fun y hy ↦ by
            rw [← extChartAt_source I]
            exact hy.1))
        fun y hy ↦ hy.2
    exact hf.comp_contMDiff contMDiff_subtype_val fun u ↦ u.2
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiffOn_extChartAt_symm x).comp_contMDiff
      (L.symm.contDiff.comp OpenPartialHomeomorph.contDiff_univBall).contMDiff hbT

end EuclideanNeighbourhood

end TauCeti
