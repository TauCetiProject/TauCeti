/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ProjectionKZero
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Stability
public import Mathlib.Analysis.Complex.Basic

/-!
# Checks: rank-one and rank-two corners of `ℂ` in `K₀`

Matrix stability of `K₀` (`TauCeti.ProjectionKZero.cornerEquiv`) uses a rank-one corner
`λ ↦ λ eᵢᵢ`. For `A = ℂ` and `M₂(ℂ)`, identify `K₀(M₂(ℂ))` with `K₀(ℂ)` through the stability
isomorphism of the corner `e₀₀`, and `K₀(ℂ)` with `ℤ` by the rank
(`TauCeti.ProjectionKZero.rankAddEquiv`).

* The corner `λ ↦ λ e₀₀` sends the class `[1]` of `K₀(ℂ)` to the class of the projection `e₀₀`,
  which corresponds to the generator `1` of `ℤ`.
* The corner `λ ↦ λ (e₀₀ + e₁₁) = λ 1` of the rank-two projection `1 = e₀₀ + e₁₁` of `M₂(ℂ)`
  sends `[1]` to `2`, so it induces multiplication by `2` on `ℤ` and is not an isomorphism: the
  stability isomorphism needs a rank-one corner.

These are finite-matrix analogues of the corresponding statements for the compact operators.
-/

public section

open Matrix Algebra

namespace TauCeti.CornerKZeroExample

/-- The class `[1]` of `K₀(ℂ)`, of the `1 × 1` identity matrix. -/
noncomputable abbrev classOne : ProjectionKZero ℂ :=
  GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _))

/-- `[1]` corresponds to `1` under the rank. -/
theorem rankAddEquiv_classOne : ProjectionKZero.rankAddEquiv ℂ classOne = 1 := by
  rw [ProjectionKZero.rankAddEquiv_of_mk_one, Nat.cast_one]

/-- The `1 × 1` matrix over `M₂(ℂ)` with entry `e₀₀`, the image of `1` under the corner. -/
noncomputable abbrev cornerOne : Matrix (Fin 1) (Fin 1) (Matrix (Fin 2) (Fin 2) ℂ) :=
  (1 : Matrix (Fin 1) (Fin 1) ℂ).map (singleNonUnitalStarRingHom ℂ (0 : Fin 2))

/-- The entry of `cornerOne` is `e₀₀`. -/
theorem cornerOne_apply (i j : Fin 1) : cornerOne i j = single 0 0 1 := by
  simp [Subsingleton.elim i j]

/-- `cornerOne` is a projection. -/
theorem isStarProjection_cornerOne : IsStarProjection cornerOne :=
  (IsStarProjection.one _).matrix_map _

/-- **The rank-one corner sends `[1]` to `[e₀₀]`.** -/
example : ProjectionKZero.map (singleNonUnitalStarRingHom ℂ (0 : Fin 2)) classOne =
    GrothendieckAddGroup.of (ProjectionMonoid.mk cornerOne isStarProjection_cornerOne) :=
  ProjectionKZero.map_of_mk _ _

/-- **The rank-one corner induces the identity of `ℤ`.** Under the stability isomorphism of the
corner `e₀₀` and the rank, the image `[e₀₀]` of `[1]` corresponds to the generator `1`. -/
example : ProjectionKZero.rankAddEquiv ℂ ((ProjectionKZero.cornerEquiv (0 : Fin 2)).symm
    (GrothendieckAddGroup.of (ProjectionMonoid.mk cornerOne isStarProjection_cornerOne))) = 1 := by
  rw [ProjectionKZero.cornerEquiv_symm_of, ProjectionMonoid.cornerEquiv_symm_mk,
    ProjectionKZero.rankAddEquiv_of_mk]
  have h : comp (Fin 1) (Fin 1) (Fin 2) (Fin 2) ℂ cornerOne = single (0, 0) (0, 0) 1 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [Subsingleton.elim i 0, Subsingleton.elim j 0, single_apply]
  rw [h, ← diagonal_single, rank_diagonal]
  simp

/-- The unital corner `λ ↦ λ 1` of the rank-two projection `1 = e₀₀ + e₁₁` of `M₂(ℂ)`. -/
noncomputable def rankTwoCorner : ℂ →⋆ₙ+* Matrix (Fin 2) (Fin 2) ℂ :=
  NonUnitalStarRingHom.ofClass (StarAlgHom.ofId ℂ (Matrix (Fin 2) (Fin 2) ℂ))

/-- The rank-two corner is `λ ↦ λ 1`. -/
theorem rankTwoCorner_apply (c : ℂ) : rankTwoCorner c = c • 1 :=
  Algebra.algebraMap_eq_smul_one c

/-- The rank-two corner, read through the stability isomorphism of the corner `e₀₀` and the
rank, as an endomorphism of `ℤ`. -/
noncomputable def rankTwoCornerInt : ℤ →+ ℤ :=
  (ProjectionKZero.rankAddEquiv ℂ).toAddMonoidHom.comp <|
    (ProjectionKZero.cornerEquiv (0 : Fin 2)).symm.toAddMonoidHom.comp <|
      (ProjectionKZero.map rankTwoCorner).comp (ProjectionKZero.rankAddEquiv ℂ).symm.toAddMonoidHom

/-- **The rank-two corner sends `[1]` to `2`.** -/
theorem rankTwoCornerInt_one : rankTwoCornerInt 1 = 2 := by
  have h : (ProjectionKZero.rankAddEquiv ℂ).symm 1 = classOne := by
    rw [AddEquiv.symm_apply_eq, rankAddEquiv_classOne]
  simp only [rankTwoCornerInt, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, h, ProjectionKZero.map_of_mk, ProjectionKZero.cornerEquiv_symm_of,
    ProjectionMonoid.cornerEquiv_symm_mk, ProjectionKZero.rankAddEquiv_of_mk]
  have h1 : comp (Fin 1) (Fin 1) (Fin 2) (Fin 2) ℂ
      ((1 : Matrix (Fin 1) (Fin 1) ℂ).map rankTwoCorner) = 1 := by
    rw [Matrix.map_one rankTwoCorner (map_zero _) (map_one (StarAlgHom.ofId ℂ _)), comp_one]
  rw [h1, rank_one]
  simp

/-- **The rank-two corner induces multiplication by `2` on `ℤ`.** -/
theorem rankTwoCornerInt_apply (n : ℤ) : rankTwoCornerInt n = 2 * n := by
  have h := map_zsmul rankTwoCornerInt n 1
  rw [zsmul_one, Int.cast_id, rankTwoCornerInt_one, smul_eq_mul] at h
  rw [h, mul_comm]

/-- **The rank-two corner is not an isomorphism on `K₀`**: its image misses the class
corresponding to `1`. -/
example : ¬ Function.Surjective (ProjectionKZero.map rankTwoCorner) := by
  intro h
  obtain ⟨x, hx⟩ := h ((ProjectionKZero.cornerEquiv (0 : Fin 2))
    ((ProjectionKZero.rankAddEquiv ℂ).symm 1))
  have h2 := rankTwoCornerInt_apply (ProjectionKZero.rankAddEquiv ℂ x)
  simp only [rankTwoCornerInt, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply] at h2
  omega

end TauCeti.CornerKZeroExample
