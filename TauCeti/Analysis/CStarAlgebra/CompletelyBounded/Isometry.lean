/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Maps
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Complete contractions, complete isometries and `CB(ℂ, B) ≃ B`

A linear map `φ : A → B` between C⋆-algebras is a **complete contraction** when every matrix
amplification `φₙ : M_n(A) → M_n(B)` is contractive, and a **complete isometry** when every
amplification is isometric, for the C⋆-norms of `CStarMatrix`. A complete contraction is the same
as a completely bounded map of cb norm at most `1`, and a complete isometry is a complete
contraction.

An injective star homomorphism of C⋆-algebras is a complete isometry: its amplifications are
injective star homomorphisms, hence isometric.

For `E = ℂ`, the map `b ↦ (z ↦ z • b)` is an isometric isomorphism `B ≃ₗᵢ CB(ℂ, B)` for every
C⋆-algebra `B`, with inverse evaluation at `1`. The amplification of `z ↦ z • b` sends a scalar
matrix `x` to `[xᵢⱼ • b]`; in matrices over the unitization of `B` this is the product of the
scalar matrix `x` and the diagonal matrix `diag(b, …, b)`, so its norm is at most `‖x‖ ‖b‖`
(`CStarMatrix.norm_map_toSpanSingleton_le`).

## Main declarations

* `LinearMap.IsCompleteContraction`, `LinearMap.isCompleteContraction_iff`: complete contractions
  are the completely bounded maps of cb norm at most `1`.
* `LinearMap.IsCompleteIsometry`, `LinearMap.IsCompleteIsometry.isCompleteContraction`.
* `LinearMap.IsCompleteContraction.norm_map_le`, `LinearMap.IsCompleteIsometry.norm_map`: the
  defining bounds for matrices over any finite index type; `norm_apply_le`, `norm_apply` and
  `LinearMap.IsCompleteIsometry.isometry` give the level-one consequences.
* `LinearMap.IsCompleteContraction.comp`, `LinearMap.IsCompleteIsometry.comp`: both classes are
  closed under composition and contain the identity.
* `NonUnitalStarAlgHom.isCompleteIsometry`: an injective star homomorphism is a complete isometry.
* `LinearMap.cbNorm_toSpanSingleton`: `‖z ↦ z • b‖_cb = ‖b‖`.
* `LinearMap.completelyBounded.toSpanSingletonLIE`: `B ≃ₗᵢ[ℂ] CB(ℂ, B)`, `b ↦ (z ↦ z • b)`.

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

/-- A complete contraction is contractive on matrices over any finite index type. -/
theorem IsCompleteContraction.norm_map_le {φ : A →ₗ[ℂ] B} (hφ : IsCompleteContraction φ)
    {κ : Type*} [Fintype κ] (x : CStarMatrix κ κ A) : ‖x.map φ‖ ≤ ‖x‖ := by
  obtain ⟨hcb, h⟩ := isCompleteContraction_iff.1 hφ
  exact (norm_map_le_cbNorm_mul hcb x).trans (mul_le_of_le_one_left (norm_nonneg x) h)

/-- A complete contraction is contractive. -/
theorem IsCompleteContraction.norm_apply_le {φ : A →ₗ[ℂ] B} (hφ : IsCompleteContraction φ)
    (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  obtain ⟨hcb, h⟩ := isCompleteContraction_iff.1 hφ
  exact (norm_apply_le_cbNorm_mul hcb a).trans (mul_le_of_le_one_left (norm_nonneg a) h)

/-- A complete isometry is isometric on matrices over any finite index type. -/
theorem IsCompleteIsometry.norm_map {φ : A →ₗ[ℂ] B} (hφ : IsCompleteIsometry φ)
    {κ : Type*} [Fintype κ] (x : CStarMatrix κ κ A) : ‖x.map φ‖ = ‖x‖ := by
  classical
  let e := Fintype.equivFin κ
  rw [← CStarMatrix.norm_map_reindexₐ_linearMap x e φ,
    ← StarAlgEquiv.norm_map (CStarMatrix.reindexₐ ℂ A e) x]
  exact hφ _ _

/-- A complete isometry is isometric. -/
theorem IsCompleteIsometry.norm_apply {φ : A →ₗ[ℂ] B} (hφ : IsCompleteIsometry φ) (a : A) :
    ‖φ a‖ = ‖a‖ := by
  rw [← CStarMatrix.norm_map_toOneByOne_linearMap (ι := Fin 1) a φ,
    ← CStarMatrix.norm_toOneByOne (ι := Fin 1) a]
  exact hφ 1 _

/-- A complete isometry is an isometry. -/
theorem IsCompleteIsometry.isometry {φ : A →ₗ[ℂ] B} (hφ : IsCompleteIsometry φ) :
    Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ hφ.norm_apply

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
  rw [coe_comp, ← CStarMatrix.map_map]
  exact (hψ n _).trans (hφ n x)

/-- The composite of complete isometries is a complete isometry. -/
@[grind ←]
theorem IsCompleteIsometry.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B}
    (hψ : IsCompleteIsometry ψ) (hφ : IsCompleteIsometry φ) :
    IsCompleteIsometry (ψ ∘ₗ φ) := fun n x ↦ by
  rw [coe_comp, ← CStarMatrix.map_map]
  exact (hψ n _).trans (hφ n x)

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

section toSpanSingleton

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace LinearMap

/-- The map `z ↦ z • b` from `ℂ` to a C⋆-algebra is completely bounded. -/
@[simp, grind .]
theorem isCompletelyBounded_toSpanSingleton (b : B) :
    (toSpanSingleton ℂ B b).IsCompletelyBounded :=
  isCompletelyBounded_def.2
    ⟨‖b‖, norm_nonneg b, fun _ x ↦
      (CStarMatrix.norm_map_toSpanSingleton_le b x).trans_eq (mul_comm _ _)⟩

/-- The map `z ↦ z • b` from `ℂ` to a C⋆-algebra has cb norm `‖b‖`. -/
@[simp, grind =]
theorem cbNorm_toSpanSingleton (b : B) : (toSpanSingleton ℂ B b).cbNorm = ‖b‖ :=
  le_antisymm
    (cbNorm_le_of_bound (norm_nonneg b) fun _ x ↦
      (CStarMatrix.norm_map_toSpanSingleton_le b x).trans_eq (mul_comm _ _)) <| by
    simpa using norm_apply_le_cbNorm_mul (isCompletelyBounded_toSpanSingleton b) 1

namespace completelyBounded

/-- **`CB(ℂ, B) ≃ B`.** The map `b ↦ (z ↦ z • b)` is an isometric isomorphism from the
C⋆-algebra `B` onto the completely bounded maps `ℂ → B`, with inverse evaluation at `1`. This is
the completely bounded analogue of `ContinuousLinearMap.toSpanSingletonLIE`. -/
noncomputable def toSpanSingletonLIE : B ≃ₗᵢ[ℂ] completelyBounded ℂ B where
  toFun b :=
    ⟨toSpanSingleton ℂ B b, mem_completelyBounded.2 (isCompletelyBounded_toSpanSingleton b)⟩
  invFun u := (u : ℂ →ₗ[ℂ] B) 1
  map_add' _ _ := Subtype.ext (ext_ring (by simp))
  map_smul' _ _ := Subtype.ext (ext_ring (by simp))
  left_inv b := by simp
  right_inv u := Subtype.ext (ext_ring (by simp))
  norm_map' b := (norm_def _).trans (cbNorm_toSpanSingleton b)

@[simp]
theorem coe_toSpanSingletonLIE_apply (b : B) :
    (toSpanSingletonLIE b : ℂ →ₗ[ℂ] B) = toSpanSingleton ℂ B b :=
  (rfl)

@[simp]
theorem toSpanSingletonLIE_symm_apply (u : completelyBounded ℂ B) :
    toSpanSingletonLIE.symm u = (u : ℂ →ₗ[ℂ] B) 1 :=
  (rfl)

end completelyBounded

end LinearMap

end toSpanSingleton
