/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Completely positive maps are completely bounded

The amplification `φₙ : M_n(A) → M_n(B)` of a completely positive map `φ : A → B` is again
completely positive (`CompletelyPositiveMap.mapCStarMatrix`). When `A` is unital, the bound
`‖ψ a‖ ≤ ‖ψ 1‖ ‖a‖` for the `2`-positive map `ψ = φₙ` on the unital C⋆-algebra `M_n(A)`,
together with `‖φₙ 1‖ = ‖diag(φ 1, …, φ 1)‖ ≤ ‖φ 1‖`
(`CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le`), gives the matrix bound `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`
at every level. Hence `φ` is completely bounded and
`‖φ‖_cb = ‖φ‖ = ‖φ 1‖`.

## Main declarations

* `CompletelyPositiveMapClass.norm_map_cstarMatrix_le`: the matrix bound `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`
  for a completely positive map with unital domain.
* `CompletelyPositiveMapClass.isCompletelyBounded` and
  `CompletelyPositiveMapClass.cbNorm_eq_norm_map_one`: such a map is completely bounded with
  `‖φ‖_cb = ‖φ 1‖`, and `CompletelyPositiveMapClass.cbNorm_eq_opNorm_ofClass`: `‖φ‖_cb = ‖φ‖`.

## References

* B. Blackadar, *Operator Algebras*, II.6.9.4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 3.6.
-/

public section

open scoped CStarAlgebra

namespace CompletelyPositiveMapClass

open LinearMap

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [FunLike F A B]
  [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B]

/-- The matrix bound for a completely positive map with unital domain: every amplification of
`φ` is bounded by `‖φ 1‖`, so `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`. -/
theorem norm_map_cstarMatrix_le (φ : F) {n : Type*} [Fintype n] (x : CStarMatrix n n A) :
    ‖x.map φ‖ ≤ ‖φ 1‖ * ‖x‖ := by
  classical
  let ψ := CompletelyPositiveMap.mapCStarMatrix (φ : A →CP B) n
  have hψ (y : CStarMatrix n n A) : ψ y = y.map φ := CompletelyPositiveMap.mapCStarMatrix_apply _ y
  have h1 : ψ 1 = CStarMatrix.diagonalNonUnitalStarAlgHom ℂ n B (φ 1) := by
    ext i j
    rw [hψ, CStarMatrix.map_apply, CStarMatrix.diagonalNonUnitalStarAlgHom_apply]
    by_cases h : i = j <;> simp [CStarMatrix.one_apply, h]
  calc ‖x.map φ‖ = ‖ψ x‖ := by rw [hψ]
    _ ≤ ‖ψ 1‖ * ‖x‖ := norm_apply_le ψ x
    _ ≤ ‖φ 1‖ * ‖x‖ := by
      rw [h1]
      gcongr
      exact CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le _

/-- A completely positive map with unital domain is completely bounded. -/
theorem isCompletelyBounded (φ : F) : (φ : A →ₗ[ℂ] B).IsCompletelyBounded :=
  isCompletelyBounded_iff_exists_bound.mpr ⟨‖φ 1‖, fun _ x => norm_map_cstarMatrix_le φ x⟩

/-- The cb norm of a completely positive map with unital domain is `‖φ 1‖`. -/
theorem cbNorm_eq_norm_map_one (φ : F) : (φ : A →ₗ[ℂ] B).cbNorm = ‖φ 1‖ := by
  refine le_antisymm (cbNorm_le_of_bound (norm_nonneg _) fun _ x =>
    norm_map_cstarMatrix_le φ x) ?_
  rcases subsingleton_or_nontrivial A with hA | hA
  · simp [Subsingleton.elim (1 : A) 0]
  simpa using norm_apply_le_cbNorm_mul (isCompletelyBounded φ) (1 : A)

/-- The cb norm of a completely positive map with unital domain is its operator norm, for the
continuous linear map `PositiveContinuousLinearMap.ofClass φ`. -/
theorem cbNorm_eq_opNorm_ofClass (φ : F) :
    (φ : A →ₗ[ℂ] B).cbNorm =
      ‖((PositiveContinuousLinearMap.ofClass φ : A →P[ℂ] B) : A →L[ℂ] B)‖ := by
  rw [cbNorm_eq_norm_map_one, opNorm_ofClass_eq_norm_map_one]

end CompletelyPositiveMapClass
