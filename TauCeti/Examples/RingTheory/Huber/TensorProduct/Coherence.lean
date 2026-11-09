/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Coherence
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks for integral completed tensor associativity

The two-term checks fix the factor order in both directions. The two-adic check uses a
proper plus ring: reassociation does not turn the nonintegral scalar `1/2` into an integral
element. Multiplication into `ℚ₂` detects this obstruction. A zero middle factor is also
permitted.
-/

public section

open TensorProduct TauCeti.Huber

namespace TauCeti.Huber.CompletedTensorCoherenceChecks

section General

variable (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsTopologicalRing D]
  [IsHuberRing B] [IsHuberRing C] [IsHuberRing D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A D)]

/-- *associator_two_terms*: the two summands retain the order of all three factors. -/
example (b₁ b₂ : B) (c₁ c₂ : C) (d₁ d₂ : D) :
    CompletedTensor.assoc A B C D
      (CompletedTensor.toCompletion A (CompletedTensor A B C) D
          (CompletedTensor.toCompletion A B C (b₁ ⊗ₜ[A] c₁) ⊗ₜ[A] d₁) +
        CompletedTensor.toCompletion A (CompletedTensor A B C) D
          (CompletedTensor.toCompletion A B C (b₂ ⊗ₜ[A] c₂) ⊗ₜ[A] d₂)) =
      CompletedTensor.toCompletion A B (CompletedTensor A C D)
          (b₁ ⊗ₜ[A] CompletedTensor.toCompletion A C D (c₁ ⊗ₜ[A] d₁)) +
        CompletedTensor.toCompletion A B (CompletedTensor A C D)
          (b₂ ⊗ₜ[A] CompletedTensor.toCompletion A C D (c₂ ⊗ₜ[A] d₂)) := by
  simp only [map_add, CompletedTensor.assoc_tmul]

/-- *associator_inverse_two_terms*: inverse reassociation keeps the same factor order. -/
example (b₁ b₂ : B) (c₁ c₂ : C) (d₁ d₂ : D) :
    (CompletedTensor.assoc A B C D).symm
      (CompletedTensor.toCompletion A B (CompletedTensor A C D)
          (b₁ ⊗ₜ[A] CompletedTensor.toCompletion A C D (c₁ ⊗ₜ[A] d₁)) +
        CompletedTensor.toCompletion A B (CompletedTensor A C D)
          (b₂ ⊗ₜ[A] CompletedTensor.toCompletion A C D (c₂ ⊗ₜ[A] d₂))) =
      CompletedTensor.toCompletion A (CompletedTensor A B C) D
          (CompletedTensor.toCompletion A B C (b₁ ⊗ₜ[A] c₁) ⊗ₜ[A] d₁) +
        CompletedTensor.toCompletion A (CompletedTensor A B C) D
          (CompletedTensor.toCompletion A B C (b₂ ⊗ₜ[A] c₂) ⊗ₜ[A] d₂) := by
  simp only [map_add, CompletedTensor.assoc_symm_tmul]

/-- *associator_zero_factor*: a zero middle factor gives a zero ring on both sides. -/
example [Subsingleton C] (S : Pair B) (T : Pair C) (U : Pair D)
    (x : CompletedTensor A (CompletedTensor A B C) D) :
    CompletedTensor.assoc A B C D x = 0 ∧
      CompletedTensor.assoc A B C D x ∈ (S.completedTensor A (T.completedTensor A U)).plus := by
  have := (CompletedTensor.inl A C D).codomain_trivial
  have := (CompletedTensor.inr A B (CompletedTensor A C D)).codomain_trivial
  have hzero : CompletedTensor.assoc A B C D x = 0 := Subsingleton.elim _ _
  exact ⟨hzero, hzero ▸ zero_mem _⟩

end General

local instance : IsAdicHom (algebraMap ℚ_[2] ℚ_[2]) := by
  simpa using (IsAdicHom.id (A := ℚ_[2]))

/-- Reassociation preserves the obstruction to integrality of the two-adic scalar `1/2`. -/
example :
    let P := Pair.powerBounded ℚ_[2]
    let x := CompletedTensor.inl ℚ_[2] (CompletedTensor ℚ_[2] ℚ_[2] ℚ_[2]) ℚ_[2]
      (CompletedTensor.inl ℚ_[2] ℚ_[2] ℚ_[2] (2 : ℚ_[2])⁻¹)
    ¬ CompletedTensor.assoc ℚ_[2] ℚ_[2] ℚ_[2] ℚ_[2] x ∈
      (P.completedTensor ℚ_[2] (P.completedTensor ℚ_[2] P)).plus := by
  intro P x hx
  have hx' := (Pair.completedTensor.assoc_mem_plus_iff ℚ_[2] P P P x).mp hx
  let m := Pair.completedTensor.lift (A := ℚ_[2]) (Pair.Hom.id P) (Pair.Hom.id P) (by simp)
  let n := Pair.completedTensor.lift (A := ℚ_[2]) m (Pair.Hom.id P)
    (by ext; simp [m, CompletedTensor.algebraMap_eq_inl])
  have h := n.map_mem_plus x hx'
  have hnorm : ‖(2 : ℚ_[2])⁻¹‖ ≤ 1 := by
    apply isPowerBounded_iff_norm_le_one.mp
    apply mem_powerBoundedSubring.mp
    simpa [n, m, x, P, Pair.powerBounded_plus] using h
  have hp := _root_.Padic.norm_p (p := 2)
  norm_num only [Nat.cast_ofNat] at hp
  rw [norm_inv, hp] at hnorm
  norm_num at hnorm

end TauCeti.Huber.CompletedTensorCoherenceChecks
