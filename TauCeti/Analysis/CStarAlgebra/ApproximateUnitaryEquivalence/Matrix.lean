/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
import Mathlib.Analysis.Matrix.Normed
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Matrix amplification of approximate unitary equivalence

Approximate unitary equivalence is preserved by finite matrix amplification.
-/

public section

open scoped CStarAlgebra Matrix.Norms.Elementwise

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
  {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- Entrywise finite matrix amplification preserves approximate unitary equivalence. -/
theorem matrix_map (h : ApproximatelyUnitarilyEquivalent φ ψ) (n : Type*)
    [Fintype n] [DecidableEq n] [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B] :
    ApproximatelyUnitarilyEquivalent (A := CStarMatrix n n A) (B := CStarMatrix n n B)
      (CStarMatrix.mapₙₐ (n := n) φ)
      (CStarMatrix.mapₙₐ (n := n) ψ) := by
  classical
  rw [approximatelyUnitarilyEquivalent_def]
  intro F ε hε
  -- The matrix norm induces the product topology, so a common entrywise tolerance suffices.
  obtain ⟨δ, hδ, hδε⟩ := (Metric.continuousAt_iff
    (α := Matrix n n B) (β := CStarMatrix n n B)).mp
    ((CStarMatrix.ofMatrixL (m := n) (n := n) (A := B)).continuous.continuousAt
      (x := (0 : Matrix n n B))) ε hε
  let S : Finset A := F.biUnion fun M ↦ Finset.univ.image fun ij : n × n ↦ M ij.1 ij.2
  obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp h S δ hδ
  -- A diagonal matrix of copies of the same target unitary implements the amplification.
  let U : CStarMatrix n n B := CStarMatrix.ofMatrix (Matrix.diagonal fun _ ↦ (u : B))
  have hU : U ∈ unitary (CStarMatrix n n B) := by
    rw [CStarMatrix.ofMatrix_mem_unitary_iff, Matrix.diagonal_mem_unitary,
      Pi.mem_unitary_iff]
    exact fun _ ↦ u.prop
  refine ⟨⟨U, hU⟩, fun M hM ↦ ?_⟩
  let D : Matrix n n B := fun i j ↦ (u : B) * φ (M i j) * star (u : B) - ψ (M i j)
  have hD : dist D 0 < δ := by
    rw [dist_zero_right, Matrix.norm_lt_iff hδ]
    intro i j
    exact hu (M i j) (Finset.mem_biUnion.mpr ⟨M, hM,
      Finset.mem_image_of_mem (fun ij : n × n ↦ M ij.1 ij.2) (Finset.mem_univ (i, j))⟩)
  have hnorm := hδε hD
  have hconj : U * CStarMatrix.mapₙₐ φ M * star U - CStarMatrix.mapₙₐ ψ M =
      CStarMatrix.ofMatrix D := by
    ext i j
    simp only [CStarMatrix.sub_apply, CStarMatrix.ofMatrix_apply]
    simp [U, D, CStarMatrix.mul_apply, Matrix.diagonal_apply, CStarMatrix.star_apply,
      CStarMatrix.ofMatrix_apply, CStarMatrix.mapₙₐ_apply, CStarMatrix.mapₗ_apply,
      CStarMatrix.map_apply, apply_ite]
  rw [hconj]
  simpa only [← CStarMatrix.ofMatrix_eq_ofMatrixL, map_zero, dist_zero_right] using hnorm

end TauCeti.ApproximatelyUnitarilyEquivalent
