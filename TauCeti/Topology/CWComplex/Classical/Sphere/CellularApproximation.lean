/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Topology.CWComplex.Classical.CellularApproximation
import TauCeti.AlgebraicTopology.Disk
import TauCeti.Topology.CWComplex.Classical.Sphere.Basic

/-!
# Cellular approximation of maps of spheres

Every map of the boundary sphere `∂Dᵐ` of the `m`-disk into a CW complex `W` is homotopic to a map
into the skeleton `skeletonLT W m`, the union of the cells of `W` of dimension less than `m`
(`ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary`). This is cellular approximation
(`TauCeti.exists_isCellular_homotopic`) for the CW structure on the sphere with one `0`-cell and
one top cell (`TauCeti.sphereCWComplex`). It is used to move attaching maps of cells into the
skeleta of a CW complex.

## Main results

* `ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary`: a map of `∂Dᵐ` into a CW
  complex is homotopic to a map into `skeletonLT W m`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.8 (cellular approximation).
-/

public section

noncomputable section

universe u

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

variable {W : Type u} [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]

/-- **Cellular approximation of a map of a sphere.** Every map of the boundary sphere `∂Dᵐ` of the
`m`-disk into a CW complex `W` is homotopic to a map into the skeleton `skeletonLT W m`, the union
of the cells of `W` of dimension less than `m`. -/
theorem _root_.ContinuousMap.exists_homotopic_mapsTo_skeletonLT_diskBoundary {m : ℕ}
    (f : C(TopCat.diskBoundary.{u} m, W)) :
    ∃ g : C(TopCat.diskBoundary.{u} m, W), f.Homotopic g ∧
      ∀ x, g x ∈ (skeletonLT (univ : Set W) m : Set W) := by
  obtain _ | k := m
  · -- The boundary of the `0`-disk is empty.
    exact ⟨f, .refl f, isEmptyElim⟩
  -- Cellular approximation for the CW structure on `Sᵏ` with one `0`-cell and one `k`-cell,
  -- indexed by `ULift (Fin (k + 1))` so that the sphere lives in the universe of `W`.
  let ι := ULift.{u} (Fin (k + 1))
  have hι : Fintype.card ι = k + 1 := by simp [ι]
  let _ := sphereCWComplex hι
  let S := sphere (0 : EuclideanSpace ℝ ι) 1
  let E := diskBoundaryHomeomorph.{u} (k + 1)
  let down : C(TopCat.diskBoundary.{u} (k + 1), S) := E
  let val : C((univ : Set W), W) := ⟨Subtype.val, continuous_subtype_val⟩
  let φ : C(S, (univ : Set W)) := ⟨fun y ↦ ⟨f (E.symm y), mem_univ _⟩, by fun_prop⟩
  have hf : f = val.comp (φ.comp down) := by
    ext x
    simp [val, φ, down]
  obtain ⟨g, hg, hφg⟩ := exists_isCellular_homotopic (TopCat.ofHom φ)
  refine ⟨val.comp (g.hom.comp down), hf ▸ (ContinuousMap.Homotopic.refl val).comp
    (hφg.comp (ContinuousMap.Homotopic.refl down)), fun x ↦ hg (k + 1) ?_⟩
  -- Every point of `Sᵏ` lies in an open cell of dimension at most `k`.
  obtain ⟨l, -, j, hj⟩ := CWComplex.mem_skeletonLT_iff.1
    (by rw [← SetLike.mem_coe, skeletonLT_top]; exact (down x).2 :
      (down x : EuclideanSpace ℝ ι) ∈ skeletonLT S ⊤)
  have hl : l < k + 1 := by
    by_contra! hl
    exact (isEmpty_cell_sphereCWComplex hι hl).elim j
  exact CWComplex.mem_skeletonLT_iff.2 ⟨l, by exact_mod_cast hl, j, hj⟩

end TauCeti
