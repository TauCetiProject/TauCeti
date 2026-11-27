/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Matrix
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation

/-!
# Approximate unitary equivalence and projection K-theory

Approximately unitarily equivalent maps into a unital C⋆-algebra induce the same map on the
projection monoid and on its Grothendieck group `ProjectionKZero`, by finite matrix amplification
and perturbation of close projections.

The source algebra and the homomorphisms may be nonunital. For unital source algebras,
`ProjectionKZero` is operator `K₀`. The nonunital operator `K₀` construction uses unitization.
-/

public section

open scoped CStarAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
  {φ ψ : A →⋆ₙₐ[ℂ] B}

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
    have heqM := congrArg CStarMatrix.ofMatrix.symm heq
    simp only [CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_star,
      ← Matrix.star_eq_conjTranspose, Φ, Ψ, CStarMatrix.ofMatrix_symm_mapₙₐ, P,
      Equiv.symm_apply_apply] at heqM
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
