/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.MultiplicityMatrix.Basic
import TauCeti.Algebra.Star.Pi
import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.MultiplicityMatrix.Classification

/-!
# Concrete examples of multiplicity matrices of finite-dimensional `⋆`-homomorphisms

Low-dimensional calculations illustrating the multiplicity-matrix classification of unital and
non-unital `⋆`-homomorphisms between finite direct sums of complex matrix C⋆-algebras:

* **Embeddings `M₂(ℂ) × M₃(ℂ) → M₇(ℂ)`**: injective unital `⋆`-homomorphisms realize a unique
  multiplicity vector `(2, 1)` (since `2 m₂ + 3 m₃ = 7` with `m₂, m₃ ≥ 1`), whereas injective
  non-unital `⋆`-homomorphisms realize both `(1, 1)` and `(2, 1)`.
* **Unital obstruction vs. non-unital embedding `M₂(ℂ) → M₃(ℂ)`**: no unital `⋆`-homomorphism
  exists because `2 ∤ 3`, whereas an injective non-unital `⋆`-homomorphism does exist.
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
    obtain ⟨φ, hM⟩ := (TauCeti.exists_starAlgHom_multiplicityMatrix_eq_iff_of_nonempty
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
  · obtain ⟨φ, hM⟩ := (TauCeti.exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff_of_nonempty
      (n := twoThreeSize) (m := fun _ : Unit ↦ Fin 7)
      (Matrix.of fun _ b ↦ if b then m₃ else m₂)).mpr fun ⟨⟩ ↦ by simp [twoThreeSize]; omega
    exact ⟨φ, φ.injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero.mpr
      fun b _ ↦ ⟨(), by cases b <;> simp [hM] <;> omega⟩, hM⟩

/-- No unital `⋆`-homomorphism `M₂(ℂ) → M₃(ℂ)` exists, whereas an injective non-unital
`⋆`-homomorphism `M₂(ℂ) → M₃(ℂ)` does exist. -/
theorem isEmpty_starAlgHom_two_three_and_exists_injective_nonUnitalStarAlgHom :
    IsEmpty (CStarMatrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] CStarMatrix (Fin 3) (Fin 3) ℂ) ∧
      ∃ φ : CStarMatrix (Fin 2) (Fin 2) ℂ →⋆ₙₐ[ℂ] CStarMatrix (Fin 3) (Fin 3) ℂ,
        Function.Injective φ := by
  refine ⟨not_nonempty_iff.mp (by rw [TauCeti.nonempty_starAlgHom_cstarMatrix_iff]; decide), ?_⟩
  obtain ⟨φ, hφ⟩ := (TauCeti.exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff_of_nonempty
    (n := fun _ : Unit ↦ Fin 2) (m := fun _ : Unit ↦ Fin 3) 1).mpr fun ⟨⟩ ↦ by simp
  have hinj : Function.Injective φ :=
    φ.injective_iff_forall_exists_multiplicityMatrix_ne_zero.mpr fun ⟨⟩ ↦ ⟨(), by simp [hφ]⟩
  exact ⟨NonUnitalStarAlgHom.funUniqueEquiv ℂ Unit Unit _ _ φ,
    (NonUnitalStarAlgHom.funUniqueEquiv_injective_iff φ).mpr hinj⟩

private def cornerIndexEmbedding (c : Fin 2) :
    (Σ _ : Unit, Fin 1 × Fin ((Matrix.of fun _ _ : Unit ↦ 1) () ())) ↪ Fin 2 :=
  ⟨fun _ ↦ c, fun ⟨⟨⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨⟩, ⟨d, hd⟩, ⟨e, he⟩⟩ _ ↦ by
    simp only [Matrix.of_apply] at hb he
    grind⟩

private theorem cornerIndexEmbedding_apply (c : Fin 2)
    (a : Σ _ : Unit, Fin 1 × Fin ((Matrix.of fun _ _ : Unit ↦ 1) () ())) :
    cornerIndexEmbedding c a = c :=
  rfl

/-- The upper-left and lower-right rank-one corner embeddings `M₁(ℂ) → M₂(ℂ)`, indexed by
`c : Fin 2`. -/
def cornerEmbedding (c : Fin 2) :
    (Unit → CStarMatrix (Fin 1) (Fin 1) ℂ) →⋆ₙₐ[ℂ] (Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) :=
  TauCeti.cstarMatrixPiBlockHom (Matrix.of fun _ _ ↦ 1) fun ⟨⟩ ↦ cornerIndexEmbedding c

/-- Entrywise action of `cornerEmbedding c`: it places the single entry `x () 0 0` at the diagonal
corner `(c, c)` and zeros elsewhere. -/
@[simp]
theorem cornerEmbedding_apply (c : Fin 2) (x : Unit → CStarMatrix (Fin 1) (Fin 1) ℂ)
    (i j : Fin 2) :
    cornerEmbedding c x () i j = if i = c ∧ j = c then x () 0 0 else 0 := by
  rw [cornerEmbedding, TauCeti.cstarMatrixPiBlockHom_apply]
  by_cases hi : c = i
  · subst hi
    by_cases hj : c = j
    · subst hj
      have h := TauCeti.cstarMatrixBlockHom_apply_same ((Matrix.of fun _ _ : Unit ↦ 1) ())
        (cornerIndexEmbedding c) x () 0 0 ⟨0, Nat.zero_lt_one⟩
      rw [cornerIndexEmbedding_apply] at h
      simpa using h
    · have hj' : j ∉ Set.range (cornerIndexEmbedding c) := by
        rintro ⟨_, h⟩; exact hj h
      rw [TauCeti.cstarMatrixBlockHom_apply_of_notMem_range_right _ _ _ _ hj']
      simp [Ne.symm hj]
  · have hi' : i ∉ Set.range (cornerIndexEmbedding c) := by
      rintro ⟨_, h⟩; exact hi h
    rw [TauCeti.cstarMatrixBlockHom_apply_of_notMem_range_left _ _ _ hi']
    simp [Ne.symm hi]

/-- Both corner embeddings have multiplicity matrix `1`. -/
@[simp]
theorem multiplicityMatrix_cornerEmbedding (c : Fin 2) :
    (cornerEmbedding c).multiplicityMatrix = 1 := by
  rw [cornerEmbedding, TauCeti.multiplicityMatrix_cstarMatrixPiBlockHom]
  ext ⟨⟩ ⟨⟩
  simp

/-- The upper-left (`c = 0`) and lower-right (`c = 1`) corner embeddings `M₁(ℂ) → M₂(ℂ)` are
unitarily conjugate in `M₂(ℂ)`. -/
theorem exists_unitary_conj_cornerEmbedding :
    ∃ u : unitary (Unit → CStarMatrix (Fin 2) (Fin 2) ℂ), ∀ x,
      (u : Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) * cornerEmbedding 0 x *
        star (u : Unit → CStarMatrix (Fin 2) (Fin 2) ℂ) = cornerEmbedding 1 x := by
  rw [NonUnitalStarAlgHom.exists_unitary_conj_iff_multiplicityMatrix_eq]
  simp

end TauCeti.MultiplicityMatrixExample

end
