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

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Globally defined differentiable local parametrizations

Every point of a finite-dimensional boundaryless real `C^n` manifold lies in the image of a
`C^n` parametrization defined on an entire Cartesian space, with `C^n` inverse on its image,
for every finite order or smoothness order `n ≤ ∞`.
These parametrizations allow continuity and smoothness to be tested on globally defined plots,
without requiring a chart inverse to extend beyond its domain.

The construction uses Mathlib's `OpenPartialHomeomorph.univBall` and `toEuclidean` to shrink
an ordinary manifold chart.

When the model space `F` is itself a real inner product space, no change of coordinates is needed:
every point of a boundaryless `C^n` manifold modelled on `F` is the centre of a coordinate ball, an
open embedding `F → N` which is a `C^n` local diffeomorphism
(`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`).
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

end TauCeti
