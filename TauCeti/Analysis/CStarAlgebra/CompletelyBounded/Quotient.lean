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
* `LinearMap.IsCompleteQuotient.of_norm_map_le_of_exists_map_eq`: a linear map whose
  amplifications are contractive and lift the open unit ball is a complete quotient map.
* `LinearMap.IsCompleteQuotient.comp`, `LinearMap.isCompleteQuotient_id`: composition and the
  identity.
* `LinearMap.IsCompleteQuotient.norm_map_le`, `LinearMap.IsCompleteQuotient.cbNorm_le_one`: a
  complete quotient map is a complete contraction.
* `LinearMap.IsCompleteQuotient.exists_map_eq`: a complete quotient map lifts the open unit ball.
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

/-- A linear map whose amplifications at the levels `Fin n` are contractive and lift the open unit
ball is a complete quotient map. -/
theorem IsCompleteQuotient.of_norm_map_le_of_exists_map_eq {φ : A →ₗ[ℂ] B}
    (hle : ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ ‖x‖)
    (hlift : ∀ (n : ℕ) (y : CStarMatrix (Fin n) (Fin n) B), ‖y‖ < 1 →
      ∃ x : CStarMatrix (Fin n) (Fin n) A, ‖x‖ < 1 ∧ x.map φ = y) :
    IsCompleteQuotient φ := fun n ↦ by
  ext y
  simp only [Set.mem_image, mem_ball_zero_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hle n x).trans_lt hx
  · exact hlift n y

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

/-- A complete quotient map is contractive on the amplifications at the levels `Fin n`. -/
private theorem IsCompleteQuotient.norm_map_le_fin {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ)
    {n : ℕ} (x : CStarMatrix (Fin n) (Fin n) A) : ‖x.map φ‖ ≤ ‖x‖ := by
  refine le_of_forall_gt fun t ht ↦ ?_
  have ht₀ : 0 < t := (norm_nonneg x).trans_lt ht
  have key (r : ℝ) : ‖(t⁻¹ : ℂ)‖ * r < 1 ↔ r < t := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg ht₀.le, inv_mul_lt_one₀ ht₀]
  have hx : (t⁻¹ : ℂ) • x ∈ Metric.ball 0 1 := by
    rwa [mem_ball_zero_iff, norm_smul, key]
  have hmem := h n ▸ Set.mem_image_of_mem (fun y : CStarMatrix (Fin n) (Fin n) A ↦ y.map φ) hx
  rwa [← CStarMatrix.mapₗ_apply, map_smul, CStarMatrix.mapₗ_apply, mem_ball_zero_iff, norm_smul,
    key] at hmem

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

/-- A complete quotient map lifts the open unit ball: every matrix of norm `< 1` over `B` is the
amplification of a matrix of norm `< 1` over `A`, for matrices over any finite index type. -/
theorem IsCompleteQuotient.exists_map_eq {φ : A →ₗ[ℂ] B} (h : IsCompleteQuotient φ) {κ : Type*}
    [Fintype κ] {y : CStarMatrix κ κ B} (hy : ‖y‖ < 1) :
    ∃ x : CStarMatrix κ κ A, ‖x‖ < 1 ∧ x.map φ = y := by
  classical
  let e := Fintype.equivFin κ
  have hy' : CStarMatrix.reindexₐ ℂ B e y ∈
      (fun x : CStarMatrix (Fin (Fintype.card κ)) (Fin (Fintype.card κ)) A ↦ x.map φ) ''
        Metric.ball 0 1 := by
    rw [h, mem_ball_zero_iff, StarAlgEquiv.norm_map]
    exact hy
  obtain ⟨x', hx', hxy⟩ := hy'
  refine ⟨(CStarMatrix.reindexₐ ℂ A e).symm x', ?_,
    EquivLike.injective (CStarMatrix.reindexₐ ℂ B e) ?_⟩
  · rwa [StarAlgEquiv.norm_map, ← mem_ball_zero_iff]
  · rw [← hxy, CStarMatrix.reindexₐ_map, StarAlgEquiv.apply_symm_apply]

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
  have hπₙ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A) :
      CStarMatrix.mapₙₐ (ofClass π) x = x.map (π : A →ₗ[ℂ] B) := by simp
  refine .of_norm_map_le_of_exists_map_eq (fun n x ↦ hπₙ n x ▸ norm_apply_le _ x)
    fun n y hy ↦ ?_
  have hrange : y ∈ Set.range (CStarMatrix.mapₙₐ (n := Fin n) (ofClass π)) :=
    ⟨CStarMatrix.ofMatrix fun i j ↦ (hπ (y i j)).choose, by
      ext i j
      rw [hπₙ, CStarMatrix.map_apply]
      exact (hπ (y i j)).choose_spec⟩
  obtain ⟨x, hxy, hxn⟩ := exists_apply_eq_norm_eq _ hrange
  exact ⟨x, hxn ▸ hy, (hπₙ n x).symm.trans hxy⟩

end NonUnitalStarAlgHom
