/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero
import Mathlib.Analysis.Matrix.Normed
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation

/-!
# Approximate unitary equivalence and projection K-theory

Approximate unitary equivalence is preserved by finite matrix amplification. Consequently,
approximately unitarily equivalent maps into a unital C⋆-algebra induce the same map on the
projection monoid and on its Grothendieck group `ProjectionKZero`.

The source algebra and the homomorphisms may be nonunital. For unital source algebras,
`ProjectionKZero` is operator `K₀`. The nonunital operator `K₀` construction uses unitization.
-/

public section

open scoped CStarAlgebra Matrix.Norms.Elementwise

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
  {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- Entrywise finite matrix amplification preserves approximate unitary equivalence, with a
diagonal matrix of copies of the same target unitary as an implementing unitary. -/
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
    simp [U, D, CStarMatrix.mul_apply, Matrix.diagonal_apply, CStarMatrix.star_apply,
      CStarMatrix.ofMatrix_apply, apply_ite]
    rfl
  rw [hconj]
  simpa only [← CStarMatrix.ofMatrix_eq_ofMatrixL, map_zero, dist_zero_right] using hnorm

/-- Approximately unitarily equivalent maps induce equal maps on the projection monoid. -/
theorem projectionMonoid_map_eq (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    ProjectionMonoid.map (NonUnitalStarRingHom.ofClass φ) =
      ProjectionMonoid.map (NonUnitalStarRingHom.ofClass ψ) := by
  classical
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  let _ := CStarAlgebra.spectralOrder B
  let _ := CStarAlgebra.spectralOrderedRing B
  ext x
  induction x using ProjectionMonoid.ind with
  | mk n p hp =>
    rw [ProjectionMonoid.map_mk, ProjectionMonoid.map_mk]
    let P := CStarMatrix.ofMatrix p
    let Φ := CStarMatrix.mapₙₐ (n := Fin n) φ
    let Ψ := CStarMatrix.mapₙₐ (n := Fin n) ψ
    have hP : IsStarProjection P := CStarMatrix.isStarProjection_ofMatrix_iff.mpr hp
    have hφP := hP.map Φ
    have hψP := hP.map Ψ
    obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp
      (h.matrix_map (Fin n)) {P} 1 zero_lt_one
    have hclose := hu P (Finset.mem_singleton_self P)
    have hconj : IsStarProjection ((u : CStarMatrix (Fin n) (Fin n) B) * Φ P *
        star (u : CStarMatrix (Fin n) (Fin n) B)) := by
      simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply,
        Unitary.conjStarAlgAut_apply] using
        hφP.map (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom
    obtain ⟨v, hv, heq, -⟩ :=
      hconj.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one hψP hclose
    have huM := CStarMatrix.ofMatrix_symm_mem_unitary_iff.mpr u.prop
    have hvM := CStarMatrix.ofMatrix_symm_mem_unitary_iff.mpr hv
    have hpφ := hp.matrix_map (NonUnitalStarRingHom.ofClass φ)
    have h₁ := hpφ.isMurrayVonNeumannEquivalent_mul_mul_star huM
    have h₂ := h₁.isStarProjection_right.isMurrayVonNeumannEquivalent_mul_mul_star hvM
    -- Both presentations of matrix amplification apply the homomorphism to each entry.
    have hmap (f : A →⋆ₙₐ[ℂ] B) :
        CStarMatrix.ofMatrix.symm (CStarMatrix.mapₙₐ f P) =
          p.map (NonUnitalStarRingHom.ofClass f) := rfl
    have heqM := congrArg CStarMatrix.ofMatrix.symm heq
    simp only [CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_star,
      ← Matrix.star_eq_conjTranspose, Φ, Ψ, hmap] at heqM
    rw [heqM] at h₂
    exact ProjectionMonoid.mk_eq_mk (h₁.trans h₂)

/-- Approximately unitarily equivalent maps induce equal maps on the projection `K₀`-group.
For unital source algebras this is the induced map on operator `K₀`. -/
theorem projectionKZero_map_eq (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    ProjectionKZero.map (NonUnitalStarRingHom.ofClass φ) =
      ProjectionKZero.map (NonUnitalStarRingHom.ofClass ψ) := by
  apply Algebra.GrothendieckAddGroup.addHom_ext
  intro x
  rw [ProjectionKZero.map_of, ProjectionKZero.map_of, h.projectionMonoid_map_eq]

end TauCeti.ApproximatelyUnitarilyEquivalent
