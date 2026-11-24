/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic
public import TauCeti.Analysis.CStarAlgebra.Lift

/-!
# Complete quotient maps between C⋆-algebras

A linear map `φ : A → B` between C⋆-algebras is a **complete quotient map** when every matrix
amplification `φₙ : M_n(A) → M_n(B)` maps the open unit ball of `M_n(A)` onto the open unit ball
of `M_n(B)`, for the C⋆-norms of `CStarMatrix`. Complete quotient maps compose, the identity is
one, and they are complete contractions (`LinearMap.IsCompleteQuotient.norm_map_le`).

A surjective star homomorphism of C⋆-algebras is a complete quotient map
(`NonUnitalStarAlgHom.isCompleteQuotient`): its amplifications are surjective star
homomorphisms, so they are contractive and every element of their range has a preimage of the same
norm (`NonUnitalStarAlgHom.exists_apply_eq_norm_eq`).

## Main declarations

* `LinearMap.IsCompleteQuotient`: complete quotient maps.
* `LinearMap.IsCompleteQuotient.comp`, `LinearMap.isCompleteQuotient_id`: composition and the
  identity.
* `LinearMap.IsCompleteQuotient.norm_map_le`: a complete quotient map is a complete contraction.
* `NonUnitalStarAlgHom.isCompleteQuotient`: a surjective star homomorphism is a complete quotient
  map.

## References

* G. Pisier, *Introduction to Operator Space Theory*, §1.2.
-/

public section

open scoped ComplexOrder

namespace LinearMap

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A linear map between C⋆-algebras is a **complete quotient map** when each matrix
amplification maps the open unit ball onto the open unit ball, for the C⋆-norms of
`CStarMatrix`. -/
def IsCompleteQuotient (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ n : ℕ, (fun x : CStarMatrix (Fin n) (Fin n) A ↦ x.map φ) '' Metric.ball 0 1 = Metric.ball 0 1

theorem isCompleteQuotient_def {φ : A →ₗ[ℂ] B} :
    IsCompleteQuotient φ ↔ ∀ n : ℕ,
      (fun x : CStarMatrix (Fin n) (Fin n) A ↦ x.map φ) '' Metric.ball 0 1 = Metric.ball 0 1 :=
  (Iff.rfl)

/-- The identity is a complete quotient map. -/
theorem isCompleteQuotient_id : IsCompleteQuotient (LinearMap.id : A →ₗ[ℂ] A) := by
  intro n
  have : (fun x : CStarMatrix (Fin n) (Fin n) A ↦ x.map (LinearMap.id : A →ₗ[ℂ] A)) =
      _root_.id := by
    ext x i j
    simp [CStarMatrix.map_apply]
  rw [this, Set.image_id]

/-- A composite of complete quotient maps is a complete quotient map. -/
theorem IsCompleteQuotient.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompleteQuotient ψ)
    (hφ : IsCompleteQuotient φ) : IsCompleteQuotient (ψ ∘ₗ φ) := by
  intro n
  have : (fun x : CStarMatrix (Fin n) (Fin n) A ↦ x.map (ψ ∘ₗ φ)) =
      (fun y : CStarMatrix (Fin n) (Fin n) B ↦ y.map ψ) ∘ fun x ↦ x.map φ := by
    ext x i j
    simp [CStarMatrix.map_apply]
  rw [this, Set.image_comp, hφ n, hψ n]

/-- A complete quotient map is a complete contraction: each amplification is contractive. -/
theorem IsCompleteQuotient.norm_map_le {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) : ‖x.map φ‖ ≤ ‖x‖ := by
  refine le_of_forall_gt fun t ht ↦ ?_
  have ht₀ : 0 < t := (norm_nonneg x).trans_lt ht
  have hx : (t⁻¹ : ℂ) • x ∈ Metric.ball 0 1 := by
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht₀.le,
      inv_mul_lt_one₀ ht₀]
    exact ht
  have hmem : ((t⁻¹ : ℂ) • x).map φ ∈ Metric.ball 0 1 := h n ▸ Set.mem_image_of_mem _ hx
  have hmap : ((t⁻¹ : ℂ) • x).map φ = (t⁻¹ : ℂ) • x.map φ := by
    ext i j
    simp [CStarMatrix.map_apply]
  rw [hmap, mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg ht₀.le, inv_mul_lt_one₀ ht₀] at hmem
  exact hmem

end LinearMap

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **A surjective star homomorphism of C⋆-algebras is a complete quotient map.** Its
amplifications are surjective star homomorphisms, hence contractive, and every element of their
range has a preimage of the same norm. -/
theorem isCompleteQuotient (π : F) (hπ : Function.Surjective π) :
    (π : A →ₗ[ℂ] B).IsCompleteQuotient := by
  intro n
  let πₙ := CStarMatrix.mapₙₐ (n := Fin n) (ofClass π)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff] at hx ⊢
    exact (norm_apply_le πₙ x).trans_lt hx
  · intro hy
    have hrange : y ∈ Set.range πₙ := ⟨CStarMatrix.ofMatrix fun i j ↦ (hπ (y i j)).choose, by
      ext i j
      exact (hπ (y i j)).choose_spec⟩
    obtain ⟨x, hxy, hxn⟩ := exists_apply_eq_norm_eq πₙ hrange
    refine ⟨x, ?_, hxy⟩
    rw [mem_ball_zero_iff] at hy ⊢
    rwa [hxn]

end NonUnitalStarAlgHom
