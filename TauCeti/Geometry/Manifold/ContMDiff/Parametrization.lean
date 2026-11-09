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

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
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
For arbitrary models with corners, each interior point has an open domain diffeomorphic to the
entire model vector space (`TauCeti.exists_opens_diffeomorph_normedSpace`), including dimension
zero.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1, coordinate balls.
-/

public noncomputable section

open Set Function
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

section InteriorPoint

variable {H P : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I n P]

/-- An interior point has an open coordinate domain diffeomorphic to the entire model space,
including when the model has dimension zero. -/
theorem exists_opens_diffeomorph_normedSpace (x : P) (hx : I.IsInteriorPoint x) :
    ∃ U : TopologicalSpace.Opens P, x ∈ U ∧ Nonempty (E ≃ₘ^n⟮𝓘(ℝ, E), I⟯ U) := by
  let L := toEuclidean (E := E)
  have hLs : (L.toPartialDiffeomorph (n := n)).source = univ := by
    simp only [ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv,
      Equiv.toPartialEquiv_source]
  have hLt : (L.toPartialDiffeomorph (n := n)).target = univ := by
    simp only [ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv,
      Equiv.toPartialEquiv_target]
  let c := (extChartPartialDiffeomorph I n x).trans L.toPartialDiffeomorph
  have hxc : x ∈ c.source := by
    simp only [c, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph, PartialEquiv.trans_source,
      hLs, preimage_univ, inter_univ]
    exact (mem_extChartPartialDiffeomorph_source (I := I) (n := n) x).mpr hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x)
    (c.toPartialEquiv.map_source hxc)
  let b₀ := OpenPartialHomeomorph.univBall (c x) r
  let b := PartialDiffeomorph.ofOpenPartialHomeomorph (n := n) b₀
    OpenPartialHomeomorph.contDiff_univBall.contDiffOn
    (by rw [OpenPartialHomeomorph.univBall_target _ hr]
        exact OpenPartialHomeomorph.contDiffOn_univBall_symm)
  have hbs : b.source = univ := by
    rw [PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
    exact OpenPartialHomeomorph.univBall_source _ _
  have hbt : b.target = Metric.ball (c x) r := by
    rw [PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
    exact OpenPartialHomeomorph.univBall_target _ hr
  have hb (v) : b v ∈ c.target :=
    hball (hbt ▸ b.toPartialEquiv.map_source (hbs ▸ mem_univ v))
  let Q := L.toPartialDiffeomorph.trans (b.trans c.symm)
  -- The linear map and ball parametrization are total, and the ball lies in the chart target.
  have hs : Q.source = univ := by
    simp only [Q, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph, PartialEquiv.trans_source,
      PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source, hLs, hbs, univ_inter]
    exact eq_univ_of_forall fun v ↦ hb _
  -- The chart sends x to the centre of the ball; the outer linear map has full target.
  have ht : x ∈ Q.target := by
    simp only [Q, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph, PartialEquiv.trans_target,
      PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
      PartialEquiv.symm_symm, hLt, preimage_univ, inter_univ, hbt, mem_inter_iff,
      mem_preimage]
    exact ⟨hxc, Metric.mem_ball_self hr⟩
  let U : TopologicalSpace.Opens P := ⟨Q.target, Q.open_target⟩
  refine ⟨U, ht, ⟨{
    toFun := fun v ↦ ⟨Q v, Q.toPartialEquiv.map_source (hs ▸ mem_univ v)⟩
    invFun := fun y ↦ Q.toPartialEquiv.symm y
    left_inv := fun v ↦ Q.toPartialEquiv.left_inv (hs ▸ mem_univ v)
    right_inv := fun y ↦ Subtype.ext (Q.toPartialEquiv.right_inv y.property)
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }⟩⟩
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    have hf := Q.contMDiffOn_toFun
    rw [hs, contMDiffOn_univ] at hf
    exact hf.congr (fun _ ↦ rfl)
  · intro y
    exact ((Q.contMDiffOn_invFun y y.property).contMDiffAt
      (Q.open_target.mem_nhds y.property)).comp y contMDiff_subtype_val.contMDiffAt

end InteriorPoint

end CoordinateBall

end TauCeti
