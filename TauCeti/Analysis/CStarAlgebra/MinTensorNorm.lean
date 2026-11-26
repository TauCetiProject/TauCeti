/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Norm
import TauCeti.Analysis.CStarAlgebra.SpatialNorm.Independence

/-!
# The minimal C*-norm on an algebraic tensor product of abstract C*-algebras

Let `A` and `B` be (possibly non-unital) C*-algebras. A **pair of representations** of `A` and
`B` (`TauCeti.RepresentationPair A B`) is a pair of star homomorphisms `π : A → B(E)` and
`ρ : B → B(F)` on Hilbert spaces `E` and `F` in the universes of `A` and `B`. Each pair gives the
spatial tensor homomorphism `A ⊗[ℂ] B → B(E ⊗₂ F)`, `a ⊗ b ↦ π a ⊗ ρ b`
(`NonUnitalStarAlgHom.spatialTensorHom`). The **minimal norm** of `x : A ⊗[ℂ] B` is the supremum
of `‖(π ⊗ ρ) x‖` over all pairs (`TauCeti.minTensorNorm`).

The spatial tensor homomorphism of a pair is the integrated form of the commuting spatial pair
`a ↦ π a ⊗ 1`, `b ↦ 1 ⊗ ρ b` (`TauCeti.CommutingRepresentationPair.spatial`), so the minimal norm
is the supremum of the norms defining `TauCeti.maxTensorNorm` over a subfamily of the commuting
pairs (`TauCeti.supTensorNorm`). Hence `‖x‖_min ≤ ‖x‖_max`
(`TauCeti.minTensorNorm_le_maxTensorNorm`), and the norm properties of the minimal norm are those
of `TauCeti.supTensorNorm`. The minimal norm is a submultiplicative star norm with the
C*-identity `‖x⋆ x‖_min = ‖x‖_min ^ 2` (`TauCeti.minTensorNorm_star_mul_self`), it vanishes
only at `0` (a pair of faithful representations, which exists by the Gelfand–Naimark theorem,
has injective spatial tensor homomorphism), and it is a cross norm, `‖a ⊗ b‖_min = ‖a‖ ‖b‖`
(`TauCeti.minTensorNorm_tmul`). For closed concrete operator algebras it dominates the spatial
norm of the given representations (`NonUnitalStarSubalgebra.spatialNorm_le_minTensorNorm`), hence
so does the maximal norm (`NonUnitalStarSubalgebra.spatialNorm_le_maxTensorNorm`).

By representation independence of the spatial norm (Takesaki I, Theorem IV.4.9;
`TauCeti.norm_spatialTensorLinearMap_map_le`), a pair of faithful representations attains the
supremum: the minimal norm is the norm of `(π ⊗ ρ) x` for **every** pair of faithful
representations, on Hilbert spaces in any universes
(`TauCeti.minTensorNorm_eq_norm_spatialTensorHom`), and it bounds `‖(π ⊗ ρ) x‖` for every pair of
representations (`TauCeti.norm_spatialTensorHom_le_minTensorNorm`). For closed concrete operator
algebras it is the spatial norm (`NonUnitalStarSubalgebra.minTensorNorm_eq_spatialNorm`). Hence
the minimal norm is **functorial**: star homomorphisms `φ : A → A'` and `ψ : B → B'` give
`‖(φ ⊗ ψ) x‖_min ≤ ‖x‖_min` (`TauCeti.minTensorNorm_mapNonUnitalStarAlgHom_le`), with equality for
injective `φ` and `ψ` (`TauCeti.minTensorNorm_mapNonUnitalStarAlgHom`), and it is invariant under
the flip `A ⊗[ℂ] B ≃ B ⊗[ℂ] A` (`TauCeti.minTensorNorm_comm`).

The completion `A ⊗min B` is `TauCeti.MinTensorProduct`. That every C*-norm on `A ⊗[ℂ] B`
dominates the minimal norm is not in this file.

## Main declarations

* `TauCeti.minTensorNorm A B`: the minimal C*-norm on `A ⊗[ℂ] B`, with
  `TauCeti.norm_spatialTensorHom_le_minTensorNorm` and `TauCeti.minTensorNorm_le_maxTensorNorm`.
* `TauCeti.minTensorNorm_eq_norm_spatialTensorHom`: the minimal norm is the spatial norm through
  any pair of faithful representations.
* `TauCeti.minTensorNorm_mapNonUnitalStarAlgHom_le`, `TauCeti.minTensorNorm_mapNonUnitalStarAlgHom`,
  `TauCeti.minTensorNorm_comm`: functoriality and flip invariance.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3.
* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4.
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

open RepresentationPair

/-- The **minimal C*-norm** `‖x‖_min` on `A ⊗[ℂ] B`: the supremum of `‖(π ⊗ ρ) x‖` over all
pairs of representations `π` of `A` and `ρ` of `B` on Hilbert spaces in the universes of `A` and
`B`, where `π ⊗ ρ : A ⊗[ℂ] B → B(E ⊗₂ F)` is the spatial tensor homomorphism, written as the
integrated form of the commuting spatial pair
(`TauCeti.CommutingRepresentationPair.tensorHom_spatial`). -/
def minTensorNorm (x : A ⊗[ℂ] B) : ℝ :=
  supTensorNorm (RepresentationPair.spatial (A := A) (B := B)) x

/-- Unfolding `TauCeti.minTensorNorm`. -/
theorem minTensorNorm_def (x : A ⊗[ℂ] B) :
    minTensorNorm A B x = ⨆ p : RepresentationPair A B, ‖p.left.spatialTensorHom p.right x‖ := by
  simp_rw [minTensorNorm, supTensorNorm_def, CommutingRepresentationPair.tensorHom_spatial]

variable {A B}

/-- The minimal norm dominates the spatial norm of every pair of representations, on Hilbert
spaces in any universes. -/
theorem norm_spatialTensorHom_le_minTensorNorm {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (x : A ⊗[ℂ] B) :
    ‖π.spatialTensorHom ρ x‖ ≤ minTensorNorm A B x := by
  obtain ⟨E', _, _, _, σ, hσ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A
  obtain ⟨F', _, _, _, τ, hτ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B
  calc ‖π.spatialTensorHom ρ x‖ ≤ ‖σ.spatialTensorHom τ x‖ := by
        rw [NonUnitalStarAlgHom.spatialTensorHom_apply,
          NonUnitalStarAlgHom.spatialTensorHom_apply]
        exact norm_spatialTensorLinearMap_map_le π ρ σ τ hσ hτ x
    _ ≤ minTensorNorm A B x := by
        rw [← CommutingRepresentationPair.tensorHom_spatial]
        exact norm_tensorHom_le_supTensorNorm RepresentationPair.spatial ⟨E', F', σ, τ⟩ x

/-- To bound the minimal norm it suffices to bound every pair of representations. -/
theorem minTensorNorm_le_of_forall {x : A ⊗[ℂ] B} {c : ℝ}
    (h : ∀ p : RepresentationPair A B, ‖p.left.spatialTensorHom p.right x‖ ≤ c) :
    minTensorNorm A B x ≤ c := by
  rw [minTensorNorm_def]
  exact ciSup_le h

/-- **The minimal norm is at most the maximal norm**: `‖x‖_min ≤ ‖x‖_max`. -/
theorem minTensorNorm_le_maxTensorNorm (x : A ⊗[ℂ] B) :
    minTensorNorm A B x ≤ maxTensorNorm A B x :=
  supTensorNorm_le_maxTensorNorm _ x

theorem minTensorNorm_nonneg (x : A ⊗[ℂ] B) : 0 ≤ minTensorNorm A B x :=
  supTensorNorm_nonneg _ x

/-- The minimal norm of `Σ aᵢ ⊗ bᵢ` is at most `Σ ‖aᵢ‖ ‖bᵢ‖`. -/
theorem minTensorNorm_le_sum {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → B) :
    minTensorNorm A B (∑ i ∈ s, a i ⊗ₜ b i) ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ :=
  supTensorNorm_le_sum _ s a b

theorem minTensorNorm_tmul_le (a : A) (b : B) : minTensorNorm A B (a ⊗ₜ b) ≤ ‖a‖ * ‖b‖ :=
  supTensorNorm_tmul_le _ a b

@[simp]
theorem minTensorNorm_zero : minTensorNorm A B 0 = 0 :=
  supTensorNorm_zero _

theorem minTensorNorm_add_le (x y : A ⊗[ℂ] B) :
    minTensorNorm A B (x + y) ≤ minTensorNorm A B x + minTensorNorm A B y :=
  supTensorNorm_add_le _ x y

theorem minTensorNorm_smul (c : ℂ) (x : A ⊗[ℂ] B) :
    minTensorNorm A B (c • x) = ‖c‖ * minTensorNorm A B x :=
  supTensorNorm_smul _ c x

@[simp]
theorem minTensorNorm_neg (x : A ⊗[ℂ] B) : minTensorNorm A B (-x) = minTensorNorm A B x :=
  supTensorNorm_neg _ x

@[simp]
theorem minTensorNorm_star (x : A ⊗[ℂ] B) : minTensorNorm A B (star x) = minTensorNorm A B x :=
  supTensorNorm_star _ x

theorem minTensorNorm_mul_le (x y : A ⊗[ℂ] B) :
    minTensorNorm A B (x * y) ≤ minTensorNorm A B x * minTensorNorm A B y :=
  supTensorNorm_mul_le _ x y

/-- **The C*-identity** for the minimal norm. -/
theorem minTensorNorm_star_mul_self (x : A ⊗[ℂ] B) :
    minTensorNorm A B (star x * x) = minTensorNorm A B x ^ 2 :=
  supTensorNorm_star_mul_self _ x

/-- The minimal norm is definite: it vanishes only at `0`. -/
@[simp]
theorem minTensorNorm_eq_zero_iff {x : A ⊗[ℂ] B} : minTensorNorm A B x = 0 ↔ x = 0 :=
  supTensorNorm_eq_zero_iff _
    ((exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul A B).imp fun _ h ↦ h.1)

/-- The minimal norm is a **cross norm**: `‖a ⊗ b‖_min = ‖a‖ ‖b‖`. -/
@[simp]
theorem minTensorNorm_tmul (a : A) (b : B) : minTensorNorm A B (a ⊗ₜ b) = ‖a‖ * ‖b‖ :=
  supTensorNorm_tmul _
    ((exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul A B).imp fun _ h ↦ h.2 a b)

/-- **The minimal norm is the spatial norm through any faithful pair** (representation
independence, Takesaki I, Theorem IV.4.9): for injective star homomorphisms `π : A → B(E)` and
`ρ : B → B(F)`, on Hilbert spaces in any universes, `‖x‖_min = ‖(π ⊗ ρ) x‖`. -/
theorem minTensorNorm_eq_norm_spatialTensorHom {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)} {ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)}
    (hπ : Function.Injective π) (hρ : Function.Injective ρ) (x : A ⊗[ℂ] B) :
    minTensorNorm A B x = ‖π.spatialTensorHom ρ x‖ := by
  refine le_antisymm (minTensorNorm_le_of_forall fun p ↦ ?_)
    (norm_spatialTensorHom_le_minTensorNorm π ρ x)
  rw [NonUnitalStarAlgHom.spatialTensorHom_apply, NonUnitalStarAlgHom.spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_le p.left p.right π ρ hπ hρ x

/-- The spatial tensor homomorphism of composites is that of the factors composed with
`φ ⊗ ψ`. -/
theorem spatialTensorHom_comp_mapNonUnitalStarAlgHom {A' B' E F : Type*}
    [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B'] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (π : A' →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B' →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    (π.comp φ).spatialTensorHom (ρ.comp ψ) x =
      π.spatialTensorHom ρ (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [Algebra.TensorProduct.coe_mapNonUnitalStarAlgHom] at hx hy ⊢
    rw [map_add, map_add, map_add, hx, hy]
  | tmul a b => simp

/-- **Functoriality of the minimal norm**: star homomorphisms `φ : A → A'` and `ψ : B → B'` give
`‖(φ ⊗ ψ) x‖_min ≤ ‖x‖_min`. -/
theorem minTensorNorm_mapNonUnitalStarAlgHom_le {A' B' : Type*} [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B'] (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    minTensorNorm A' B' (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ x) ≤
      minTensorNorm A B x := by
  obtain ⟨E, _, _, _, π, hπ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A'
  obtain ⟨F, _, _, _, ρ, hρ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B'
  rw [minTensorNorm_eq_norm_spatialTensorHom hπ hρ,
    ← spatialTensorHom_comp_mapNonUnitalStarAlgHom]
  exact norm_spatialTensorHom_le_minTensorNorm _ _ x

/-- **Injective star homomorphisms are isometric for the minimal norm**: for injective
`φ : A → A'` and `ψ : B → B'`, `‖(φ ⊗ ψ) x‖_min = ‖x‖_min`. -/
theorem minTensorNorm_mapNonUnitalStarAlgHom {A' B' : Type*} [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B'] {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (x : A ⊗[ℂ] B) :
    minTensorNorm A' B' (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ x) =
      minTensorNorm A B x := by
  obtain ⟨E, _, _, _, π, hπ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A'
  obtain ⟨F, _, _, _, ρ, hρ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B'
  rw [minTensorNorm_eq_norm_spatialTensorHom hπ hρ,
    minTensorNorm_eq_norm_spatialTensorHom (π := π.comp φ) (ρ := ρ.comp ψ) (hπ.comp hφ)
      (hρ.comp hψ), spatialTensorHom_comp_mapNonUnitalStarAlgHom]

/-- **Flip invariance of the minimal norm**: `‖τ(x)‖_min = ‖x‖_min` for the flip
`τ : A ⊗[ℂ] B ≃ B ⊗[ℂ] A`. -/
@[simp]
theorem minTensorNorm_comm (x : A ⊗[ℂ] B) :
    minTensorNorm B A (TensorProduct.comm ℂ A B x) = minTensorNorm A B x := by
  obtain ⟨E, _, _, _, π, hπ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A
  obtain ⟨F, _, _, _, ρ, hρ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B
  rw [minTensorNorm_eq_norm_spatialTensorHom hρ hπ, minTensorNorm_eq_norm_spatialTensorHom hπ hρ,
    NonUnitalStarAlgHom.spatialTensorHom_apply, NonUnitalStarAlgHom.spatialTensorHom_apply,
    TensorProduct.map_comm, norm_spatialTensorLinearMap_comm]

end TauCeti

namespace NonUnitalStarSubalgebra

open TauCeti

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)) (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F))
  [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

/-- For closed concrete operator algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal norm is the
spatial norm relative to the given representations. -/
theorem minTensorNorm_eq_spatialNorm (x : A ⊗[ℂ] B) : minTensorNorm A B x = A.spatialNorm B x := by
  rw [spatialNorm_def, spatialTensorHom_def]
  exact minTensorNorm_eq_norm_spatialTensorHom Subtype.val_injective Subtype.val_injective x

/-- For closed concrete operator algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal norm dominates
the spatial norm relative to the given representations. -/
theorem spatialNorm_le_minTensorNorm (x : A ⊗[ℂ] B) : A.spatialNorm B x ≤ minTensorNorm A B x :=
  (minTensorNorm_eq_spatialNorm A B x).ge

/-- **The spatial norm is at most the maximal norm**: for closed concrete operator algebras
`A ⊆ B(E)` and `B ⊆ B(F)`, the spatial norm `A.spatialNorm B x` is at most `‖x‖_max`. -/
theorem spatialNorm_le_maxTensorNorm (x : A ⊗[ℂ] B) : A.spatialNorm B x ≤ maxTensorNorm A B x :=
  (spatialNorm_le_minTensorNorm A B x).trans (minTensorNorm_le_maxTensorNorm x)

end NonUnitalStarSubalgebra
