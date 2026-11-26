/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensorNorm

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
pairs. Hence `‖x‖_min ≤ ‖x‖_max` (`TauCeti.minTensorNorm_le_maxTensorNorm`). The minimal norm is a
submultiplicative star norm with the C*-identity `‖x⋆ x‖_min = ‖x‖_min ^ 2`
(`TauCeti.minTensorNorm_star_mul_self`), it vanishes only at `0` (a pair of faithful
representations, which exists by the Gelfand–Naimark theorem, has injective spatial tensor
homomorphism), and it is a cross norm, `‖a ⊗ b‖_min = ‖a‖ ‖b‖` (`TauCeti.minTensorNorm_tmul`).
For closed concrete operator algebras it dominates the spatial norm of the given representations
(`NonUnitalStarSubalgebra.spatialNorm_le_minTensorNorm`).

Representation independence of the spatial norm (Takesaki I, Theorem IV.4.9) says that a pair of
faithful representations attains the supremum, so that the minimal norm is the spatial norm
through any faithful pair. That identification, the completion `A ⊗min B`, and the fact that
every C*-norm on `A ⊗[ℂ] B` dominates the minimal norm are not in this file.

## Main declarations

* `TauCeti.RepresentationPair A B`: pairs of representations of `A` and `B`, with the commuting
  pair `TauCeti.RepresentationPair.toCommutingRepresentationPair`.
* `TauCeti.minTensorNorm A B`: the minimal C*-norm on `A ⊗[ℂ] B`, with
  `TauCeti.minTensorNorm_le_maxTensorNorm`.

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

/-- A **pair of representations** of `A` and `B`: star homomorphisms `left : A → B(E)` and
`right : B → B(F)` on complex Hilbert spaces `E` and `F` in the universes of `A` and `B`. -/
structure RepresentationPair where
  /-- The Hilbert space of the representation of `A`. -/
  E : Type u
  /-- The Hilbert space of the representation of `B`. -/
  F : Type v
  /-- The norm of `E`. -/
  [instNormedAddCommGroupE : NormedAddCommGroup E]
  /-- The inner product of `E`. -/
  [instInnerProductSpaceE : InnerProductSpace ℂ E]
  /-- `E` is complete. -/
  [instCompleteSpaceE : CompleteSpace E]
  /-- The norm of `F`. -/
  [instNormedAddCommGroupF : NormedAddCommGroup F]
  /-- The inner product of `F`. -/
  [instInnerProductSpaceF : InnerProductSpace ℂ F]
  /-- `F` is complete. -/
  [instCompleteSpaceF : CompleteSpace F]
  /-- The representation of `A`. -/
  left : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)
  /-- The representation of `B`. -/
  right : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)

attribute [instance] RepresentationPair.instNormedAddCommGroupE
  RepresentationPair.instInnerProductSpaceE RepresentationPair.instCompleteSpaceE
  RepresentationPair.instNormedAddCommGroupF RepresentationPair.instInnerProductSpaceF
  RepresentationPair.instCompleteSpaceF

namespace RepresentationPair

variable {A B}

/-- The commuting spatial pair `a ↦ π a ⊗ 1`, `b ↦ 1 ⊗ ρ b` on `E ⊗₂ F` of a pair of
representations. -/
abbrev toCommutingRepresentationPair (p : RepresentationPair A B) :
    CommutingRepresentationPair A B :=
  CommutingRepresentationPair.spatial p.left p.right

/-- The integrated form of the commuting spatial pair of `p` is the spatial tensor homomorphism
of `p`. -/
theorem tensorHom_toCommutingRepresentationPair (p : RepresentationPair A B) :
    p.toCommutingRepresentationPair.tensorHom = p.left.spatialTensorHom p.right :=
  CommutingRepresentationPair.tensorHom_spatial p.left p.right

variable (A B) in
/-- There is a pair of representations whose spatial tensor homomorphism is injective and has
norm `‖a‖ ‖b‖` at every `a ⊗ b`: a pair of faithful representations. -/
theorem exists_injective_and_norm_tmul :
    ∃ p : RepresentationPair A B, Function.Injective p.toCommutingRepresentationPair.tensorHom ∧
      ∀ a b, ‖p.toCommutingRepresentationPair.tensorHom (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  obtain ⟨E, _, _, _, π, hπ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A
  obtain ⟨F, _, _, _, ρ, hρ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B
  refine ⟨⟨E, F, π, ρ⟩, CommutingRepresentationPair.tensorHom_spatial_injective hπ hρ,
    fun a b ↦ ?_⟩
  rw [CommutingRepresentationPair.norm_tensorHom_spatial_tmul, NonUnitalStarAlgHom.norm_map π hπ,
    NonUnitalStarAlgHom.norm_map ρ hρ]

instance : Nonempty (RepresentationPair A B) :=
  (exists_injective_and_norm_tmul A B).nonempty

/-- For each `x`, the norms `‖(π ⊗ ρ) x‖` over all pairs of representations are bounded. -/
theorem bddAbove_range_norm_tensorHom (x : A ⊗[ℂ] B) :
    BddAbove (Set.range fun p : RepresentationPair A B ↦
      ‖p.toCommutingRepresentationPair.tensorHom x‖) := by
  obtain ⟨c, hc⟩ := CommutingRepresentationPair.bddAbove_range_norm_tensorHom x
  exact ⟨c, by rintro _ ⟨p, rfl⟩; exact hc ⟨_, rfl⟩⟩

end RepresentationPair

open RepresentationPair

/-- The **minimal C*-norm** `‖x‖_min` on `A ⊗[ℂ] B`: the supremum of `‖(π ⊗ ρ) x‖` over all
pairs of representations `π` of `A` and `ρ` of `B` on Hilbert spaces in the universes of `A` and
`B`, where `π ⊗ ρ : A ⊗[ℂ] B → B(E ⊗₂ F)` is the spatial tensor homomorphism, written as the
integrated form of the commuting spatial pair
(`TauCeti.RepresentationPair.tensorHom_toCommutingRepresentationPair`). -/
def minTensorNorm (x : A ⊗[ℂ] B) : ℝ :=
  ⨆ p : RepresentationPair A B, ‖p.toCommutingRepresentationPair.tensorHom x‖

/-- Unfolding `TauCeti.minTensorNorm`. -/
theorem minTensorNorm_def (x : A ⊗[ℂ] B) :
    minTensorNorm A B x =
      ⨆ p : RepresentationPair A B, ‖p.toCommutingRepresentationPair.tensorHom x‖ :=
  (rfl)

variable {A B}

/-- The minimal norm dominates the spatial norm of every pair of representations. -/
theorem norm_tensorHom_le_minTensorNorm (p : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ‖p.toCommutingRepresentationPair.tensorHom x‖ ≤ minTensorNorm A B x :=
  le_ciSup (bddAbove_range_norm_tensorHom x) p

/-- To bound the minimal norm it suffices to bound every pair of representations. -/
theorem minTensorNorm_le_of_forall {x : A ⊗[ℂ] B} {c : ℝ}
    (h : ∀ p : RepresentationPair A B, ‖p.toCommutingRepresentationPair.tensorHom x‖ ≤ c) :
    minTensorNorm A B x ≤ c :=
  ciSup_le h

/-- **The minimal norm is at most the maximal norm**: `‖x‖_min ≤ ‖x‖_max`. -/
theorem minTensorNorm_le_maxTensorNorm (x : A ⊗[ℂ] B) :
    minTensorNorm A B x ≤ maxTensorNorm A B x :=
  minTensorNorm_le_of_forall fun _ ↦ norm_tensorHom_le_maxTensorNorm _ x

theorem minTensorNorm_nonneg (x : A ⊗[ℂ] B) : 0 ≤ minTensorNorm A B x :=
  (norm_nonneg _).trans (norm_tensorHom_le_minTensorNorm (Classical.arbitrary _) x)

/-- The minimal norm of `Σ aᵢ ⊗ bᵢ` is at most `Σ ‖aᵢ‖ ‖bᵢ‖`. -/
theorem minTensorNorm_le_sum {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → B) :
    minTensorNorm A B (∑ i ∈ s, a i ⊗ₜ b i) ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ :=
  (minTensorNorm_le_maxTensorNorm _).trans (maxTensorNorm_le_sum s a b)

theorem minTensorNorm_tmul_le (a : A) (b : B) : minTensorNorm A B (a ⊗ₜ b) ≤ ‖a‖ * ‖b‖ :=
  (minTensorNorm_le_maxTensorNorm _).trans (maxTensorNorm_tmul_le a b)

@[simp]
theorem minTensorNorm_zero : minTensorNorm A B 0 = 0 :=
  le_antisymm (minTensorNorm_le_of_forall fun p ↦ by simp) (minTensorNorm_nonneg 0)

theorem minTensorNorm_add_le (x y : A ⊗[ℂ] B) :
    minTensorNorm A B (x + y) ≤ minTensorNorm A B x + minTensorNorm A B y :=
  minTensorNorm_le_of_forall fun p ↦ by
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (norm_tensorHom_le_minTensorNorm p x)
      (norm_tensorHom_le_minTensorNorm p y))

theorem minTensorNorm_smul (c : ℂ) (x : A ⊗[ℂ] B) :
    minTensorNorm A B (c • x) = ‖c‖ * minTensorNorm A B x := by
  simp_rw [minTensorNorm, map_smul, norm_smul]
  exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

@[simp]
theorem minTensorNorm_neg (x : A ⊗[ℂ] B) : minTensorNorm A B (-x) = minTensorNorm A B x := by
  simpa using minTensorNorm_smul (-1) x

@[simp]
theorem minTensorNorm_star (x : A ⊗[ℂ] B) : minTensorNorm A B (star x) = minTensorNorm A B x := by
  simp_rw [minTensorNorm, map_star, norm_star]

theorem minTensorNorm_mul_le (x y : A ⊗[ℂ] B) :
    minTensorNorm A B (x * y) ≤ minTensorNorm A B x * minTensorNorm A B y :=
  minTensorNorm_le_of_forall fun p ↦ by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_tensorHom_le_minTensorNorm p x)
      (norm_tensorHom_le_minTensorNorm p y) (norm_nonneg _) (minTensorNorm_nonneg x))

/-- **The C*-identity** for the minimal norm. -/
theorem minTensorNorm_star_mul_self (x : A ⊗[ℂ] B) :
    minTensorNorm A B (star x * x) = minTensorNorm A B x ^ 2 := by
  have hp (p : RepresentationPair A B) :
      ‖p.toCommutingRepresentationPair.tensorHom (star x * x)‖ =
        ‖p.toCommutingRepresentationPair.tensorHom x‖ ^ 2 := by
    rw [map_mul, map_star, CStarRing.norm_star_mul_self, sq]
  refine le_antisymm (minTensorNorm_le_of_forall fun p ↦ ?_) ?_
  · rw [hp]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_tensorHom_le_minTensorNorm p x) 2
  · have h : minTensorNorm A B x ≤ √(minTensorNorm A B (star x * x)) :=
      minTensorNorm_le_of_forall fun p ↦ by
        rw [← Real.sqrt_sq (norm_nonneg (p.toCommutingRepresentationPair.tensorHom x)), ← hp]
        exact Real.sqrt_le_sqrt (norm_tensorHom_le_minTensorNorm p _)
    calc minTensorNorm A B x ^ 2 ≤ √(minTensorNorm A B (star x * x)) ^ 2 :=
          pow_le_pow_left₀ (minTensorNorm_nonneg x) h 2
      _ = minTensorNorm A B (star x * x) := Real.sq_sqrt (minTensorNorm_nonneg _)

/-- The minimal norm is definite: it vanishes only at `0`. -/
@[simp]
theorem minTensorNorm_eq_zero_iff {x : A ⊗[ℂ] B} : minTensorNorm A B x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ minTensorNorm_zero⟩
  obtain ⟨p, hp, -⟩ := exists_injective_and_norm_tmul A B
  refine hp ?_
  rw [map_zero, ← norm_eq_zero]
  exact le_antisymm (hx ▸ norm_tensorHom_le_minTensorNorm p x) (norm_nonneg _)

/-- The minimal norm is a **cross norm**: `‖a ⊗ b‖_min = ‖a‖ ‖b‖`. -/
@[simp]
theorem minTensorNorm_tmul (a : A) (b : B) : minTensorNorm A B (a ⊗ₜ b) = ‖a‖ * ‖b‖ := by
  refine le_antisymm (minTensorNorm_tmul_le a b) ?_
  obtain ⟨p, -, hp⟩ := exists_injective_and_norm_tmul A B
  exact hp a b ▸ norm_tensorHom_le_minTensorNorm p (a ⊗ₜ b)

end TauCeti

namespace NonUnitalStarSubalgebra

open TauCeti

/-- For closed concrete operator algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal norm dominates
the spatial norm relative to the given representations. -/
theorem spatialNorm_le_minTensorNorm {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E))
    (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F)) [IsClosed (A : Set (E →L[ℂ] E))]
    [IsClosed (B : Set (F →L[ℂ] F))] (x : A ⊗[ℂ] B) :
    A.spatialNorm B x ≤ minTensorNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_def, ← CommutingRepresentationPair.tensorHom_spatial]
  exact norm_tensorHom_le_minTensorNorm
    ⟨E, F, NonUnitalStarSubalgebraClass.subtype A, NonUnitalStarSubalgebraClass.subtype B⟩ x

end NonUnitalStarSubalgebra
