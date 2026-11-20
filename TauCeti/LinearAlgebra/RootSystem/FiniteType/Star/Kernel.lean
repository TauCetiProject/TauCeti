/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

/-!
# The null equations of a simply-laced star

Prescribing the coefficient at the centre determines the solution to the null equations along
all arms: on each arm, the coefficients interpolate linearly between the centre and zero one
step after the tip. The remaining equation at the centre tests whether the sum of reciprocal
arm sizes (counting the centre) equals the number of arms minus two. The calculation uses
`TauCeti.starMark` and its row identities, the same linear weights as in the finite-type fork
bound (Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, step (7)).
-/

public section

open scoped Matrix
open Finset Matrix

namespace TauCeti

variable {α : Type*} [DecidableEq α] {ℓ : α → ℕ}

/-- The principal submatrix on one arm, with the centre omitted, is a type `A` chain. -/
@[simp] theorem starCartanMatrix_submatrix_arm (i : α) :
    (starCartanMatrix ℓ).submatrix (fun t ↦ some ⟨i, t⟩) (fun t ↦ some ⟨i, t⟩) =
      CartanMatrix.A (ℓ i) := by
  ext t s
  simp [← chainEntry_eq_cartanMatrix_A, chainEntry_def]

variable [Fintype α]

/-- If the centre coefficient is zero, the row at an arm vertex depends only on the restriction
of the vector to that arm. -/
theorem starCartanMatrix_mulVec_some_of_none_eq_zero {R : Type*} [NonAssocRing R]
    {x : StarIndex ℓ → R} (hx : x none = 0) (i : α) (t : Fin (ℓ i)) :
    (((starCartanMatrix ℓ).map (Int.cast : ℤ → R)) *ᵥ x) (some ⟨i, t⟩) =
      (((CartanMatrix.A (ℓ i)).map (Int.cast : ℤ → R)) *ᵥ fun s ↦ x (some ⟨i, s⟩)) t := by
  simp only [mulVec, dotProduct, map_apply, Fintype.sum_option, hx, mul_zero, zero_add,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← starCartanMatrix_submatrix_arm (ℓ := ℓ) i]
    rfl
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Solving the null equations at every arm vertex determines all coefficients from the
coefficient at the centre, whether or not the centre itself satisfies its null equation. -/
theorem eq_smul_starMark_of_mulVec_some_eq_zero {x : StarIndex ℓ → ℚ}
    (hx : ∀ v, (((starCartanMatrix ℓ).map (Int.cast : ℤ → ℚ)) *ᵥ x) (some v) = 0) :
    x = (x none / starMark ℓ none) • starMark ℓ := by
  let c := x none / starMark ℓ none
  suffices x - c • starMark ℓ = 0 by exact sub_eq_zero.mp this
  have hc : (x - c • starMark ℓ) none = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c,
      div_mul_cancel₀ _ (starMark_pos none).ne', sub_self]
  funext v
  cases v with
  | none => exact hc
  | some v =>
    rcases v with ⟨i, t⟩
    have hchain : ((CartanMatrix.A (ℓ i)).map (Int.cast : ℤ → ℚ)) *ᵥ
        (fun s ↦ (x - c • starMark ℓ) (some ⟨i, s⟩)) = 0 := by
      funext s
      have hmark : (((starCartanMatrix ℓ).map (Int.cast : ℤ → ℚ)) *ᵥ starMark ℓ)
          (some ⟨i, s⟩) = 0 := by
        simpa only [mulVec, dotProduct, map_apply] using
          sum_starCartanMatrix_mul_starMark_some_eq_zero ⟨i, s⟩
      rw [← starCartanMatrix_mulVec_some_of_none_eq_zero hc, mulVec_sub, mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, hx, hmark, smul_zero, sub_zero, Pi.zero_apply]
    exact congrFun ((posDef_map_intCast_cartanMatrix_A (ℓ i)).mulVec_injective
      (hchain.trans (mulVec_zero _).symm)) t

/-- At the centre, the Cartan image of the star marks is the centre mark times the difference
between the reciprocal sum and `Fintype.card α - 2` (in `ℚ`). An empty arm contributes `1`. -/
theorem starCartanMatrix_mulVec_starMark_none :
    (((starCartanMatrix ℓ).map (Int.cast : ℤ → ℚ)) *ᵥ starMark ℓ) none =
      (∑ i, ((ℓ i : ℚ) + 1)⁻¹ - ((Fintype.card α : ℚ) - 2)) * starMark ℓ none := by
  simp only [mulVec, dotProduct, map_apply, sum_starCartanMatrix_mul_starMark_none, sub_mul,
    Finset.sum_mul, starMark_none]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.compl_singleton, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    inv_mul_cancel_left₀ (by positivity)]

/-- The rational kernel of a simply-laced star is nonzero exactly at equality in the fork bound.
In that case its positive star marks span the kernel. -/
theorem exists_ne_zero_mulVec_starCartanMatrix_eq_zero_iff :
    (∃ x : StarIndex ℓ → ℚ, x ≠ 0 ∧ ((starCartanMatrix ℓ).map (Int.cast : ℤ → ℚ)) *ᵥ x = 0) ↔
      ∑ i, ((ℓ i : ℚ) + 1)⁻¹ = (Fintype.card α : ℚ) - 2 := by
  constructor
  · rintro ⟨x, hx₀, hx⟩
    have he := eq_smul_starMark_of_mulVec_some_eq_zero fun v ↦ congrFun hx (some v)
    have hc : x none / starMark ℓ none ≠ 0 := by
      intro hc
      exact hx₀ (by simpa only [hc, zero_smul] using he)
    rw [he, mulVec_smul] at hx
    have h := congrFun hx none
    rw [Pi.smul_apply, smul_eq_mul, starCartanMatrix_mulVec_starMark_none, Pi.zero_apply] at h
    have hcentre := (mul_eq_zero.mp h).resolve_left hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hcentre).resolve_right (starMark_pos none).ne')
  · intro h
    refine ⟨starMark ℓ, fun hz ↦ (starMark_pos none).ne' (congrFun hz none), ?_⟩
    funext v
    cases v with
    | none => simp [starCartanMatrix_mulVec_starMark_none, h]
    | some v => simpa [mulVec, dotProduct] using sum_starCartanMatrix_mul_starMark_some_eq_zero v

end TauCeti
