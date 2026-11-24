/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Maps
import Mathlib.Algebra.Order.Star.Unitization
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Complete contractions, complete isometries and `CB(ℂ, B) ≃ B`

A linear map `φ : A → B` between C⋆-algebras is a **complete contraction** when every matrix
amplification `φₙ : M_n(A) → M_n(B)` is contractive, and a **complete isometry** when every
amplification is isometric, for the C⋆-norms of `CStarMatrix`. A complete contraction is the same
as a completely bounded map of cb norm at most `1`, and a complete isometry is a complete
contraction.

An injective star homomorphism of C⋆-algebras is a complete isometry: its amplifications are
injective star homomorphisms, hence isometric.

For `E = ℂ`, evaluation at `1` is an isometric isomorphism `CB(ℂ, B) ≃ₗᵢ B` for every C⋆-algebra
`B`, with inverse `b ↦ (z ↦ z • b)`. The amplification of `z ↦ z • b` sends a scalar matrix `x` to
`[xᵢⱼ • b]`; in matrices over the unitization of `B` this is the product of the scalar matrix `x`
and the diagonal matrix `diag(b, …, b)`, so its norm is at most `‖x‖ ‖b‖`.

## Main declarations

* `LinearMap.IsCompleteContraction`, `LinearMap.isCompleteContraction_iff`: complete contractions
  are the completely bounded maps of cb norm at most `1`.
* `LinearMap.IsCompleteIsometry`, `LinearMap.IsCompleteIsometry.isCompleteContraction`.
* `LinearMap.IsCompleteContraction.comp`, `LinearMap.IsCompleteIsometry.comp`: both classes are
  closed under composition and contain the identity.
* `NonUnitalStarAlgHom.isCompleteIsometry`: an injective star homomorphism is a complete isometry.
* `LinearMap.cbNorm_toSpanSingleton`: `‖z ↦ z • b‖_cb = ‖b‖`.
* `LinearMap.completelyBounded.evalOneEquiv`: `CB(ℂ, B) ≃ₗᵢ[ℂ] B`, `u ↦ u 1`.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3.
* G. Pisier, *Introduction to Operator Space Theory*, §1.2.
-/

public section

open scoped ComplexOrder

namespace LinearMap

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A linear map between C⋆-algebras is a **complete contraction** when all of its matrix
amplifications are contractive, for the C⋆-norms of `CStarMatrix`. -/
def IsCompleteContraction (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ ‖x‖

/-- A linear map between C⋆-algebras is a **complete isometry** when all of its matrix
amplifications are isometric, for the C⋆-norms of `CStarMatrix`. -/
def IsCompleteIsometry (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ = ‖x‖

theorem isCompleteContraction_def {φ : A →ₗ[ℂ] B} :
    IsCompleteContraction φ ↔ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ ‖x‖ :=
  (Iff.rfl)

theorem isCompleteIsometry_def {φ : A →ₗ[ℂ] B} :
    IsCompleteIsometry φ ↔ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ = ‖x‖ :=
  (Iff.rfl)

/-- A complete contraction is a completely bounded map of cb norm at most `1`. -/
theorem isCompleteContraction_iff {φ : A →ₗ[ℂ] B} :
    IsCompleteContraction φ ↔ IsCompletelyBounded φ ∧ cbNorm φ ≤ 1 := by
  refine ⟨fun h ↦ ⟨isCompletelyBounded_def.2 ⟨1, zero_le_one, fun n x ↦ by simpa using h n x⟩,
    cbNorm_le_of_bound zero_le_one fun n x ↦ by simpa using h n x⟩, fun ⟨hφ, h⟩ n x ↦ ?_⟩
  simpa using (cbNorm_le_iff hφ zero_le_one).1 h n x

/-- A complete isometry is a complete contraction. -/
@[grind →]
theorem IsCompleteIsometry.isCompleteContraction {φ : A →ₗ[ℂ] B} (hφ : IsCompleteIsometry φ) :
    IsCompleteContraction φ :=
  fun n x ↦ (hφ n x).le

/-- A complete isometry is completely bounded. -/
@[grind →]
theorem IsCompleteIsometry.isCompletelyBounded {φ : A →ₗ[ℂ] B} (hφ : IsCompleteIsometry φ) :
    IsCompletelyBounded φ :=
  (isCompleteContraction_iff.1 hφ.isCompleteContraction).1

section Comp

variable {C : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- The identity map is a complete contraction. -/
@[simp, grind .]
theorem isCompleteContraction_id : IsCompleteContraction (LinearMap.id : A →ₗ[ℂ] A) :=
  fun n x ↦ by simp

/-- The identity map is a complete isometry. -/
@[simp, grind .]
theorem isCompleteIsometry_id : IsCompleteIsometry (LinearMap.id : A →ₗ[ℂ] A) :=
  fun n x ↦ by simp

/-- The composite of complete contractions is a complete contraction. -/
@[grind ←]
theorem IsCompleteContraction.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B}
    (hψ : IsCompleteContraction ψ) (hφ : IsCompleteContraction φ) :
    IsCompleteContraction (ψ ∘ₗ φ) := fun n x ↦ by
  have : x.map (ψ ∘ₗ φ) = (x.map φ).map ψ := by ext; simp
  exact this ▸ (hψ n _).trans (hφ n x)

/-- The composite of complete isometries is a complete isometry. -/
@[grind ←]
theorem IsCompleteIsometry.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B}
    (hψ : IsCompleteIsometry ψ) (hφ : IsCompleteIsometry φ) :
    IsCompleteIsometry (ψ ∘ₗ φ) := fun n x ↦ by
  have : x.map (ψ ∘ₗ φ) = (x.map φ).map ψ := by ext; simp
  exact this ▸ (hψ n _).trans (hφ n x)

end Comp

end LinearMap

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- A star homomorphism of C⋆-algebras is a complete contraction. -/
@[grind .]
theorem isCompleteContraction (π : F) : (π : A →ₗ[ℂ] B).IsCompleteContraction :=
  LinearMap.isCompleteContraction_iff.2 ⟨isCompletelyBounded π, cbNorm_le_one π⟩

/-- An injective star homomorphism of C⋆-algebras is a complete isometry: its matrix
amplifications are injective star homomorphisms, hence isometric. -/
theorem isCompleteIsometry (π : F) (hπ : Function.Injective π) :
    (π : A →ₗ[ℂ] B).IsCompleteIsometry := fun n x ↦ by
  have hinj : Function.Injective (CStarMatrix.mapₙₐ (n := Fin n) (ofClass π : A →⋆ₙₐ[ℂ] B)) :=
    CStarMatrix.map_injective hπ
  simpa using norm_map (CStarMatrix.mapₙₐ (n := Fin n) (ofClass π : A →⋆ₙₐ[ℂ] B)) hinj x

end NonUnitalStarAlgHom

namespace LinearMap

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The amplification of `z ↦ z • b` has norm at most `‖x‖ ‖b‖` at the scalar matrix `x`. In
matrices over the unitization of `B` it is the product of `x` and `diag(b, …, b)`, and the
inclusion of `B` in its unitization is isometric on matrices. -/
private theorem norm_map_toSpanSingleton_le (b : B) {n : ℕ} (x : CStarMatrix (Fin n) (Fin n) ℂ) :
    ‖x.map (toSpanSingleton ℂ B b)‖ ≤ ‖x‖ * ‖b‖ := by
  let ι : B →⋆ₙₐ[ℂ] Unitization ℂ B := Unitization.inrNonUnitalStarAlgHom ℂ B
  let ιₙ := CStarMatrix.mapₙₐ (n := Fin n) ι
  have hιₙ : Function.Injective ιₙ := CStarMatrix.map_injective Unitization.inr_injective
  let α := CStarMatrix.mapₙₐ (n := Fin n)
    ((StarAlgHom.ofId ℂ (Unitization ℂ B)).toNonUnitalStarAlgHom)
  have hfac : ιₙ (x.map (toSpanSingleton ℂ B b)) =
      α x * CStarMatrix.diagonalNonUnitalStarAlgHom ℂ (Fin n) _ (ι b) := by
    refine CStarMatrix.ext fun i j ↦ ?_
    simp [ιₙ, α, ι, CStarMatrix.mul_apply, Unitization.algebraMap_eq_inl,
      Unitization.inl_mul_inr, Unitization.inr_smul]
  rw [← NonUnitalStarAlgHom.norm_map ιₙ hιₙ, hfac]
  refine (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le α x) ?_
    (norm_nonneg _) (norm_nonneg _))
  exact (CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le _).trans (Unitization.norm_inr b).le

/-- The map `z ↦ z • b` from `ℂ` to a C⋆-algebra is completely bounded. -/
@[simp, grind .]
theorem isCompletelyBounded_toSpanSingleton (b : B) :
    (toSpanSingleton ℂ B b).IsCompletelyBounded :=
  isCompletelyBounded_def.2
    ⟨‖b‖, norm_nonneg b, fun _ x ↦ (norm_map_toSpanSingleton_le b x).trans_eq (mul_comm _ _)⟩

/-- The map `z ↦ z • b` from `ℂ` to a C⋆-algebra has cb norm `‖b‖`. -/
@[simp, grind =]
theorem cbNorm_toSpanSingleton (b : B) : (toSpanSingleton ℂ B b).cbNorm = ‖b‖ :=
  le_antisymm
    (cbNorm_le_of_bound (norm_nonneg b) fun _ x ↦
      (norm_map_toSpanSingleton_le b x).trans_eq (mul_comm _ _)) <| by
    simpa using norm_apply_le_cbNorm_mul (isCompletelyBounded_toSpanSingleton b) 1

namespace completelyBounded

/-- **`CB(ℂ, B) ≃ B`.** Evaluation at `1` is an isometric isomorphism from the completely bounded
maps `ℂ → B` onto the C⋆-algebra `B`, with inverse `b ↦ (z ↦ z • b)`. -/
noncomputable def evalOneEquiv : completelyBounded ℂ B ≃ₗᵢ[ℂ] B where
  toFun u := (u : ℂ →ₗ[ℂ] B) 1
  invFun b :=
    ⟨toSpanSingleton ℂ B b, mem_completelyBounded.2 (isCompletelyBounded_toSpanSingleton b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := Subtype.ext (ext_ring (by simp))
  right_inv b := by simp
  norm_map' u := by
    rw [norm_def, show (u : ℂ →ₗ[ℂ] B) = toSpanSingleton ℂ B ((u : ℂ →ₗ[ℂ] B) 1) from
      ext_ring (by simp), cbNorm_toSpanSingleton]
    -- the left side is `‖u 1‖` by definition of `toFun`
    rfl

@[simp]
theorem evalOneEquiv_apply (u : completelyBounded ℂ B) :
    evalOneEquiv u = (u : ℂ →ₗ[ℂ] B) 1 :=
  (rfl)

@[simp]
theorem coe_evalOneEquiv_symm_apply (b : B) :
    (evalOneEquiv.symm b : ℂ →ₗ[ℂ] B) = toSpanSingleton ℂ B b :=
  (rfl)

end completelyBounded

end LinearMap
