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
one, and they are complete contractions (`LinearMap.IsCompleteQuotient.norm_map_le`,
`LinearMap.IsCompleteQuotient.cbNorm_le_one`).

A surjective star homomorphism of C⋆-algebras is a complete quotient map
(`NonUnitalStarAlgHom.isCompleteQuotient`): its amplifications are surjective star
homomorphisms, so they are contractive and every element of their range has a preimage of the same
norm (`NonUnitalStarAlgHom.exists_apply_eq_norm_eq`).

## Main declarations

* `LinearMap.IsCompleteQuotient`: complete quotient maps.
* `LinearMap.IsCompleteQuotient.comp`, `LinearMap.isCompleteQuotient_id`: composition and the
  identity.
* `LinearMap.IsCompleteQuotient.norm_map_le`, `LinearMap.IsCompleteQuotient.cbNorm_le_one`: a
  complete quotient map is a complete contraction.
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
@[simp, grind .]
theorem isCompleteQuotient_id : IsCompleteQuotient (LinearMap.id : A →ₗ[ℂ] A) := fun n ↦ by
  rw [show (fun x : CStarMatrix (Fin n) (Fin n) A ↦ x.map (LinearMap.id : A →ₗ[ℂ] A)) =
    _root_.id from funext CStarMatrix.map_id, Set.image_id]

/-- A composite of complete quotient maps is a complete quotient map. -/
@[grind ←]
theorem IsCompleteQuotient.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompleteQuotient ψ)
    (hφ : IsCompleteQuotient φ) : IsCompleteQuotient (ψ ∘ₗ φ) := fun n ↦ by
  rw [show (fun x : CStarMatrix (Fin n) (Fin n) A ↦ x.map (ψ ∘ₗ φ)) =
      (fun y : CStarMatrix (Fin n) (Fin n) B ↦ y.map ψ) ∘ fun x ↦ x.map φ from
    funext fun _ ↦ CStarMatrix.map_map.symm, Set.image_comp, hφ n, hψ n]

/-- Rescaling by `t⁻¹` puts `z` in the open unit ball exactly when `‖z‖ < t`. -/
private theorem inv_smul_mem_ball_iff {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {t : ℝ} (ht : 0 < t) (z : E) : (t⁻¹ : ℂ) • z ∈ Metric.ball 0 1 ↔ ‖z‖ < t := by
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le,
    inv_mul_lt_one₀ ht]

/-- A complete quotient map is contractive on the amplifications at the levels `Fin n`. -/
private theorem IsCompleteQuotient.norm_map_le_fin {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ)
    {n : ℕ} (x : CStarMatrix (Fin n) (Fin n) A) : ‖x.map φ‖ ≤ ‖x‖ := by
  refine le_of_forall_gt fun t ht ↦ ?_
  have ht₀ : 0 < t := (norm_nonneg x).trans_lt ht
  have hmem := h n ▸ Set.mem_image_of_mem (fun y : CStarMatrix (Fin n) (Fin n) A ↦ y.map φ)
    ((inv_smul_mem_ball_iff ht₀ x).mpr ht)
  rwa [← CStarMatrix.mapₗ_apply, map_smul, CStarMatrix.mapₗ_apply,
    inv_smul_mem_ball_iff ht₀] at hmem

/-- A complete quotient map is completely bounded. -/
theorem IsCompleteQuotient.isCompletelyBounded {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ) :
    IsCompletelyBounded φ :=
  isCompletelyBounded_def.mpr ⟨1, zero_le_one, fun _ x ↦ (one_mul ‖x‖).symm ▸ h.norm_map_le_fin x⟩

/-- A complete quotient map has cb norm at most `1`. -/
theorem IsCompleteQuotient.cbNorm_le_one {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ) :
    cbNorm φ ≤ 1 :=
  cbNorm_le_of_bound zero_le_one fun _ x ↦ (one_mul ‖x‖).symm ▸ h.norm_map_le_fin x

/-- A complete quotient map is a complete contraction: each amplification is contractive, for
matrices over any finite index type. -/
theorem IsCompleteQuotient.norm_map_le {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ) {κ : Type*}
    [Fintype κ] (x : CStarMatrix κ κ A) : ‖x.map φ‖ ≤ ‖x‖ :=
  (norm_map_le_cbNorm_mul h.isCompletelyBounded x).trans
    (mul_le_of_le_one_left (norm_nonneg x) h.cbNorm_le_one)

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
  have hπₙ (x : CStarMatrix (Fin n) (Fin n) A) : πₙ x = x.map (π : A →ₗ[ℂ] B) := by simp [πₙ]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff] at hx ⊢
    dsimp only
    rw [← hπₙ]
    exact (norm_apply_le πₙ x).trans_lt hx
  · intro hy
    have hrange : y ∈ Set.range πₙ := ⟨CStarMatrix.ofMatrix fun i j ↦ (hπ (y i j)).choose, by
      ext i j
      rw [hπₙ, CStarMatrix.map_apply]
      exact (hπ (y i j)).choose_spec⟩
    obtain ⟨x, hxy, hxn⟩ := exists_apply_eq_norm_eq πₙ hrange
    refine ⟨x, ?_, (hπₙ x).symm.trans hxy⟩
    rw [mem_ball_zero_iff] at hy ⊢
    rwa [hxn]

end NonUnitalStarAlgHom
