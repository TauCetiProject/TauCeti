/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Unitization

/-!
# Completely positive maps are completely bounded

The amplification `φₙ : M_n(A) → M_n(B)` of a completely positive map `φ : A → B` is again
completely positive (`CompletelyPositiveMap.mapCStarMatrix`). When `A` is unital, the bound
`‖ψ a‖ ≤ ‖ψ 1‖ ‖a‖` for the `2`-positive map `ψ = φₙ` on the unital C⋆-algebra `M_n(A)`,
together with `‖φₙ 1‖ = ‖diag(φ 1, …, φ 1)‖ ≤ ‖φ 1‖`
(`CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le`), gives the matrix bound `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`
at every level. Hence `φ` is completely bounded and
`‖φ‖_cb = ‖φ‖ = ‖φ 1‖`.

For nonunital `A`, a bound `‖φ a‖ ≤ c ‖a‖` passes to every amplification. For a contraction,
the amplification of `φ` is the restriction of the amplification of the unital extension
`φ⁺ : A⁺¹ → B⁺¹` to `M_n(A) ⊆ M_n(A⁺¹)`, and `M_n(A) → M_n(A⁺¹)` and `M_n(B) → M_n(B⁺¹)` are
isometric; the general case scales `φ` to a contraction.

## Main declarations

* `CompletelyPositiveMapClass.norm_map_cstarMatrix_le`: the matrix bound `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`
  for a completely positive map with unital domain.
* `CompletelyPositiveMapClass.isCompletelyBounded` and
  `CompletelyPositiveMapClass.cbNorm_eq_norm_map_one`: such a map is completely bounded with
  `‖φ‖_cb = ‖φ 1‖`, and `CompletelyPositiveMapClass.cbNorm_eq_opNorm_ofClass`: `‖φ‖_cb = ‖φ‖`.
* `CompletelyPositiveMap.norm_mapCStarMatrix_apply_le`: the matrix bound `‖φₙ x‖ ≤ c ‖x‖` for a
  completely positive map with possibly nonunital domain and `‖φ a‖ ≤ c ‖a‖`.

## References

* B. Blackadar, *Operator Algebras*, II.6.9.4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 3.6.
* B. Blackadar, *Operator Algebras*, II.6.9.5 (unitization of completely positive contractions).
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal

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

namespace CompletelyPositiveMap

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The matrix bound for a completely positive map with possibly nonunital domain: if
`‖φ a‖ ≤ c ‖a‖` for every `a`, then every amplification satisfies `‖φₙ x‖ ≤ c ‖x‖`. -/
theorem norm_mapCStarMatrix_apply_le (φ : A →CP B) {c : ℝ≥0} (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖)
    {n : Type*} [Fintype n] (x : CStarMatrix n n A) : ‖φ.mapCStarMatrix n x‖ ≤ c * ‖x‖ := by
  -- The contraction case: restrict the amplification of the unital extension `ψ⁺`.
  have key (ψ : A →CP B) (hψ : ∀ a, ‖ψ a‖ ≤ ‖a‖) : ‖ψ.mapCStarMatrix n x‖ ≤ ‖x‖ := by
    let ιA := CStarMatrix.mapₙₐ (n := n) (Unitization.inrNonUnitalStarAlgHom ℂ A)
    let ιB := CStarMatrix.mapₙₐ (n := n) (Unitization.inrNonUnitalStarAlgHom ℂ B)
    have hιA : Function.Injective ιA := CStarMatrix.map_injective Unitization.inr_injective
    have hιB : Function.Injective ιB := CStarMatrix.map_injective Unitization.inr_injective
    have h1 : ‖ψ.unitization hψ 1‖ ≤ 1 := by
      rw [unitization_apply_one]
      exact CStarRing.norm_one_le
    have hfac : ιB (ψ.mapCStarMatrix n x) = (ιA x).map (ψ.unitization hψ) :=
      CStarMatrix.ext fun i j ↦ by
        simp [ιA, ιB, CStarMatrix.mapₗ_apply, CStarMatrix.map_apply]
    rw [← NonUnitalStarAlgHom.norm_map ιB hιB, hfac, ← NonUnitalStarAlgHom.norm_map ιA hιA x]
    calc ‖(ιA x).map (ψ.unitization hψ)‖ ≤ ‖ψ.unitization hψ 1‖ * ‖ιA x‖ :=
          CompletelyPositiveMapClass.norm_map_cstarMatrix_le _ _
      _ ≤ 1 * ‖ιA x‖ := by gcongr
      _ = ‖ιA x‖ := one_mul _
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : φ.mapCStarMatrix n x = 0 := CStarMatrix.ext fun i j ↦ by
      simpa [CStarMatrix.map_apply] using hφ (x i j)
    simp [h0]
  have hc' : (0 : ℝ) < c := by positivity
  have hψ (a : A) : ‖(c⁻¹ • φ) a‖ ≤ ‖a‖ := by
    simpa [NNReal.smul_def, norm_smul, inv_mul_le_iff₀ hc'] using hφ a
  have hφc : φ = c • (c⁻¹ • φ) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [hφc, mapCStarMatrix_smul, smul_apply]
  simpa [NNReal.smul_def, norm_smul] using mul_le_mul_of_nonneg_left (key _ hψ) hc'.le

end CompletelyPositiveMap
