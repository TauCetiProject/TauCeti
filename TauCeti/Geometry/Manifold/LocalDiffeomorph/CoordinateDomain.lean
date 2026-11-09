/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Euclidean coordinate domains

Every interior point of a finite-dimensional real manifold has an open neighbourhood
diffeomorphic to its entire model vector space. This includes dimension zero and arbitrary
models with corners: only the specified point must be an interior point.

The construction shrinks an extended chart using Mathlib's smooth parametrization of an
open ball by Euclidean space. Such domains are useful for local-to-global arguments in
compactly supported cohomology.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1,
  coordinate balls.
-/

public noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞} [IsManifold I n M]

/-- An interior point has an open coordinate domain diffeomorphic to the entire model space,
including when the model has dimension zero. -/
theorem exists_opens_diffeomorph_normedSpace (x : M) (hx : I.IsInteriorPoint x) :
    ∃ U : Opens M, x ∈ U ∧ Nonempty (E ≃ₘ^n⟮𝓘(ℝ, E), I⟯ U) := by
  let L := toEuclidean (E := E)
  let c := (extChartPartialDiffeomorph I n x).trans L.toPartialDiffeomorph
  have hxc : x ∈ c.source := by
    simpa [c] using (mem_extChartPartialDiffeomorph_source (I := I) (n := n) x).mpr hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x)
    (c.toPartialEquiv.map_source hxc)
  let b₀ := OpenPartialHomeomorph.univBall (c x) r
  let b := PartialDiffeomorph.ofOpenPartialHomeomorph (n := n) b₀
    OpenPartialHomeomorph.contDiff_univBall.contDiffOn
    (by rw [OpenPartialHomeomorph.univBall_target _ hr]
        exact OpenPartialHomeomorph.contDiffOn_univBall_symm)
  have hb (v) : b v ∈ c.target := hball <| by
    rw [← OpenPartialHomeomorph.univBall_target (c x) hr]
    simpa only [b, PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv,
      OpenPartialHomeomorph.coe_toPartialEquiv] using b₀.map_source (by simp [b₀])
  let P := L.toPartialDiffeomorph.trans (b.trans c.symm)
  have hs : P.source = univ := by
    simpa [P, b, b₀, range_subset_iff] using hb
  have ht : x ∈ P.target := by
    simpa [P, b, b₀, hxc, OpenPartialHomeomorph.univBall_target _ hr] using
      (Metric.mem_ball_self hr : c x ∈ Metric.ball (c x) r)
  let U : Opens M := ⟨P.target, P.open_target⟩
  refine ⟨U, ht, ⟨{
    toFun := fun v ↦ ⟨P v, P.toPartialEquiv.map_source (hs ▸ mem_univ v)⟩
    invFun := fun y ↦ P.toPartialEquiv.symm y
    left_inv := fun v ↦ P.toPartialEquiv.left_inv (hs ▸ mem_univ v)
    right_inv := fun y ↦ Subtype.ext (P.toPartialEquiv.right_inv y.property)
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }⟩⟩
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    have hf := P.contMDiffOn_toFun
    rw [hs, contMDiffOn_univ] at hf
    exact hf.congr (fun _ ↦ rfl)
  · intro y
    exact ((P.contMDiffOn_invFun y y.property).contMDiffAt
      (P.open_target.mem_nhds y.property)).comp y contMDiff_subtype_val.contMDiffAt

end TauCeti
