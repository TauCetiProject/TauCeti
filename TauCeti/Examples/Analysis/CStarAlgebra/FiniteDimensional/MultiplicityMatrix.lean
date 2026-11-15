/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.MultiplicityMatrix

/-!
# Concrete examples of multiplicity matrices of finite-dimensional `⋆`-homomorphisms

Low-dimensional calculations illustrating the multiplicity-matrix classification of unital and
non-unital `⋆`-homomorphisms between finite direct sums of complex matrix C⋆-algebras:

* **Embeddings `M₂(ℂ) × M₃(ℂ) → M₇(ℂ)`**: injective unital `⋆`-homomorphisms realize a unique
  multiplicity vector `(2, 1)` (since `2 m₂ + 3 m₃ = 7` with `m₂, m₃ ≥ 1`), whereas injective
  non-unital `⋆`-homomorphisms realize both `(1, 1)` and `(2, 1)`.
* **Unital obstruction vs. non-unital embedding `M₂(ℂ) → M₃(ℂ)`**: no unital `⋆`-homomorphism
  exists because `2 ∤ 3`, whereas a nonzero non-unital `⋆`-homomorphism exists with multiplicity
  `1`.
* **Corner embeddings `ℂ ≅ M₁(ℂ) → M₂(ℂ)`**: the upper-left and lower-right rank-one corner
  embeddings both have multiplicity `1`, and are therefore unitarily conjugate in `M₂(ℂ)`.
-/

public section

noncomputable section

namespace TauCeti.MultiplicityMatrixExample

/-- The direct-sum block sizes `n false = Fin 2` and `n true = Fin 3` for `M₂(ℂ) × M₃(ℂ)`. -/
abbrev twoThreeSize (b : Bool) : Type := Fin (if b then 3 else 2)

/-- An injective unital `⋆`-homomorphism `M₂(ℂ) × M₃(ℂ) → M₇(ℂ)` realizes multiplicities
`(m₂, m₃)` if and only if `(m₂, m₃) = (2, 1)`. -/
theorem exists_injective_starAlgHom_two_three_seven_iff (m₂ m₃ : ℕ) :
    (∃ φ : (∀ b : Bool, CStarMatrix (twoThreeSize b) (twoThreeSize b) ℂ) →⋆ₐ[ℂ]
        (Unit → CStarMatrix (Fin 7) (Fin 7) ℂ),
      Function.Injective φ ∧
        φ.toNonUnitalStarAlgHom.multiplicityMatrix = Matrix.of fun _ b ↦ if b then m₃ else m₂) ↔
      m₂ = 2 ∧ m₃ = 1 := by
  refine ⟨fun ⟨φ, hinj, hM⟩ ↦ ?_, fun ⟨hm₂, hm₃⟩ ↦ ?_⟩
  · have hinj' := (φ.toNonUnitalStarAlgHom
      |>.injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero).mp hinj
    obtain ⟨⟨⟩, h₂⟩ := hinj' false ⟨0⟩
    obtain ⟨⟨⟩, h₃⟩ := hinj' true ⟨0⟩
    have hsum := φ.sum_multiplicityMatrix_mul_card_eq ()
    simp [twoThreeSize, hM] at h₂ h₃ hsum; omega
  · rw [hm₂, hm₃]
    obtain ⟨φ, hM⟩ := (TauCeti.exists_starAlgHom_multiplicityMatrix_eq_iff
      (n := twoThreeSize) (m := fun _ : Unit ↦ Fin 7)
      (Matrix.of fun _ b ↦ if b then 1 else 2)).mpr fun ⟨⟩ ↦ by simp [twoThreeSize]
    exact ⟨φ, (φ.toNonUnitalStarAlgHom
      |>.injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero).mpr
      fun b _ ↦ ⟨(), by cases b <;> simp [hM]⟩, hM⟩

/-- An injective non-unital `⋆`-homomorphism `M₂(ℂ) × M₃(ℂ) → M₇(ℂ)` realizes multiplicities
`(m₂, m₃)` if and only if `(m₂, m₃) = (1, 1)` or `(m₂, m₃) = (2, 1)`. -/
theorem exists_injective_nonUnitalStarAlgHom_two_three_seven_iff (m₂ m₃ : ℕ) :
    (∃ φ : (∀ b : Bool, CStarMatrix (twoThreeSize b) (twoThreeSize b) ℂ) →⋆ₙₐ[ℂ]
        (Unit → CStarMatrix (Fin 7) (Fin 7) ℂ),
      Function.Injective φ ∧
        φ.multiplicityMatrix = Matrix.of fun _ b ↦ if b then m₃ else m₂) ↔
      (m₂ = 1 ∧ m₃ = 1) ∨ (m₂ = 2 ∧ m₃ = 1) := by
  refine ⟨fun ⟨φ, hinj, hM⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [NonUnitalStarAlgHom.injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero] at hinj
    obtain ⟨⟨⟩, h₂⟩ := hinj false ⟨0⟩
    obtain ⟨⟨⟩, h₃⟩ := hinj true ⟨0⟩
    have hle := φ.sum_multiplicityMatrix_mul_card_le ()
    simp [twoThreeSize, hM] at h₂ h₃ hle; omega
  · obtain ⟨φ, hM⟩ := (TauCeti.exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff
      (n := twoThreeSize) (m := fun _ : Unit ↦ Fin 7)
      (Matrix.of fun _ b ↦ if b then m₃ else m₂)).mpr fun ⟨⟩ ↦ by simp [twoThreeSize]; omega
    exact ⟨φ, φ.injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero.mpr
      fun b _ ↦ ⟨(), by cases b <;> simp [hM] <;> omega⟩, hM⟩

/-- No unital `⋆`-homomorphism `M₂(ℂ) → M₃(ℂ)` exists, whereas a nonzero non-unital
`⋆`-homomorphism does exist. -/
theorem isEmpty_starAlgHom_two_three_and_exists_nonUnital :
    ¬ Nonempty (CStarMatrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] CStarMatrix (Fin 3) (Fin 3) ℂ) ∧
      ∃ φ : (Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) →⋆ₙₐ[ℂ]
        (Unit → CStarMatrix (Fin 3) (Fin 3) ℂ), φ ≠ 0 := by
  refine ⟨by rw [TauCeti.nonempty_starAlgHom_cstarMatrix_iff]; decide, ?_⟩
  obtain ⟨φ, hφ⟩ := (TauCeti.exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff
    (n := fun _ : Unit ↦ Fin 2) (m := fun _ : Unit ↦ Fin 3) (Matrix.of fun _ _ ↦ 1)).mpr
    fun ⟨⟩ ↦ by simp
  exact ⟨φ, fun h0 ↦ by simpa [h0] using congrArg (fun M ↦ M () ()) hφ⟩

/-- The `1 × 1` multiplicity matrix with single entry `1`. -/
def oneByOneMultiplicity : Matrix Unit Unit ℕ := Matrix.of fun _ _ ↦ 1

/-- The upper-left and lower-right rank-one corner embeddings `M₁(ℂ) → M₂(ℂ)`, indexed by
`c : Fin 2`. -/
def cornerEmbedding (c : Fin 2) :
    (Unit → CStarMatrix (Fin 1) (Fin 1) ℂ) →⋆ₙₐ[ℂ] (Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) :=
  TauCeti.cstarMatrixPiBlockHom oneByOneMultiplicity fun ⟨⟩ ↦
    ⟨fun _ ↦ c, fun ⟨⟨⟩, a, b⟩ ⟨⟨⟩, d, e⟩ _ ↦ by
      simp [Subsingleton.elim a d, Subsingleton.elim (α := Fin 1) b e]⟩

/-- The upper-left (`c = 0`) and lower-right (`c = 1`) corner embeddings `M₁(ℂ) → M₂(ℂ)` are
unitarily conjugate in `M₂(ℂ)`. -/
theorem exists_unitary_conj_cornerEmbedding :
    ∃ u : unitary (Unit → CStarMatrix (Fin 2) (Fin 2) ℂ), ∀ x,
      (u : Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) * cornerEmbedding 0 x *
        star (u : Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) = cornerEmbedding 1 x :=
  ((cornerEmbedding 0).exists_unitary_conj_iff_multiplicityMatrix_eq (cornerEmbedding 1)).mpr
    ((TauCeti.multiplicityMatrix_cstarMatrixPiBlockHom oneByOneMultiplicity _).trans
      (TauCeti.multiplicityMatrix_cstarMatrixPiBlockHom oneByOneMultiplicity _).symm)

end TauCeti.MultiplicityMatrixExample

end
