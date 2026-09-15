/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.HermitianForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Hermitian duals of linear codes

A code is a submodule of a finite coordinate space. Its Hermitian dual uses the form
`h(x,y) = ∑ i, x i * σ (y i)`, with a specified semiring automorphism `σ`. A generator
matrix becomes a parity-check matrix for the dual after applying `σ.symm` entrywise;
for involutive `σ`, this is `σ` itself. Over a field, the dimensions of a code and its dual
add to the length, and taking the dual twice recovers the code when `σ` is involutive.
The field need not be finite.

The matrix convention is row generators (`range G.vecMulLinear`) and column syndromes
(`ker H.mulVecLin`). In particular, omitting the conjugation computes a different dual.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*,
§§1.3–1.4. The Hermitian-duality statements and pairing orientation follow the
[formal prototype in `AlgebraicCodingTheory/Suggested.lean`][hermitian-prototype].

[hermitian-prototype]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/368157aaeaf6d07617b20f935b6c7b1367b1aee0/TauCetiRoadmap/AlgebraicCodingTheory/Suggested.lean#L65-L100
-/

public section

namespace TauCeti

open Module Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The Hermitian dual of a code, with the automorphism acting on the second argument.
Double duality requires the automorphism to be involutive. -/
noncomputable def hermitianDual (σ : R ≃+* R) (C : Submodule R (ι → R)) :
    Submodule R (ι → R) := C.orthogonalBilin (hermitianForm σ)

/-- The Hermitian dual is the orthogonal submodule for the standard Hermitian form. -/
theorem hermitianDual_def (σ : R ≃+* R) (C : Submodule R (ι → R)) :
    hermitianDual σ C = C.orthogonalBilin (hermitianForm σ) := by
  rfl

/-- Membership in the Hermitian dual means being Hermitian-orthogonal to every codeword. -/
@[simp]
theorem mem_hermitianDual (σ : R ≃+* R) (C : Submodule R (ι → R)) (y : ι → R) :
    y ∈ hermitianDual σ C ↔ ∀ x ∈ C, ∑ i, x i * σ (y i) = 0 := by
  simp [hermitianDual]

@[simp]
theorem hermitianDual_bot (σ : R ≃+* R) :
    hermitianDual σ (⊥ : Submodule R (ι → R)) = ⊤ := by
  simp [hermitianDual]

@[simp]
theorem hermitianDual_top (σ : R ≃+* R) :
    hermitianDual σ (⊤ : Submodule R (ι → R)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  exact (nondegenerate_hermitianForm σ).2 y (fun x ↦ hy x (Submodule.mem_top))

/-- Hermitian duality reverses inclusion. -/
theorem hermitianDual_antitone (σ : R ≃+* R) :
    Antitone (hermitianDual σ (ι := ι)) := Submodule.orthogonalBilin_antitone

/-- The Hermitian dual of a sum is the intersection of the Hermitian duals. -/
@[simp]
theorem hermitianDual_sup (σ : R ≃+* R) (C D : Submodule R (ι → R)) :
    hermitianDual σ (C ⊔ D) = hermitianDual σ C ⊓ hermitianDual σ D :=
  Submodule.orthogonalBilin_sup C D

/-- Every code is contained in its double Hermitian dual for an involutive automorphism. -/
theorem le_hermitianDual_hermitianDual (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (C : Submodule R (ι → R)) : C ≤ hermitianDual σ (hermitianDual σ C) := by
  apply Submodule.le_orthogonalBilin_orthogonalBilin
  intro x y h
  rw [hermitianForm_swap σ hσ, h, map_zero]

/-- The Hermitian dual of a row space is the kernel of the matrix obtained by applying
the inverse automorphism entrywise. -/
theorem hermitianDual_range_vecMulLinear (σ : R ≃+* R)
    {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι R) :
    hermitianDual σ (LinearMap.range G.vecMulLinear) =
      LinearMap.ker (G.map σ.symm).mulVecLin := by
  ext y
  rw [hermitianDual, range_vecMulLinear]
  simp only [Submodule.mem_orthogonalBilin_span, Set.forall_mem_range]
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
  apply forall_congr'
  intro i
  rw [← σ.symm.map_eq_zero_iff]
  simp [hermitianForm_apply, Matrix.mulVec, dotProduct]

/-- For an involutive automorphism, the Hermitian dual of a row space is the kernel of
the entrywise-conjugate matrix. -/
theorem hermitianDual_range_vecMulLinear_of_involutive (σ : R ≃+* R)
    (hσ : Function.Involutive σ) {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι R) :
    hermitianDual σ (LinearMap.range G.vecMulLinear) =
      LinearMap.ker (G.map σ).mulVecLin := by
  have hsymm : σ.symm = σ := by
    ext x
    exact σ.injective (by simp [hσ x])
  simpa only [hsymm] using hermitianDual_range_vecMulLinear σ G

section Field

variable {K : Type*} [Field K]

/-- The dimensions of a code and its Hermitian dual add to the length. -/
theorem finrank_add_finrank_hermitianDual (σ : K ≃+* K) (C : Submodule K (ι → K)) :
    finrank K C + finrank K (hermitianDual σ C) = Fintype.card ι := by
  have hd : finrank K (hermitianDual σ C) = finrank K C.dualAnnihilator := by
    rw [hermitianDual, ← Submodule.comap_dualAnnihilator_eq_orthogonalBilin]
    let f := (hermitianForm σ (ι := ι)).flip
    have hf := hermitianForm_flip_bijective σ (ι := ι)
    let g := f.submoduleComap C.dualAnnihilator
    have hg : Function.Bijective g := by
      constructor
      · intro x y h
        apply Subtype.ext
        exact hf.1 (congrArg Subtype.val h)
      · exact f.submoduleComap_surjective_of_surjective _ hf.2
    let e := AddEquiv.ofBijective g.toAddHom hg
    exact congrArg Cardinal.toNat
      (rank_eq_of_equiv_equiv σ e σ.bijective (fun r x ↦ g.map_smulₛₗ r x))
  rw [hd, Subspace.finrank_add_finrank_dualAnnihilator_eq, Module.finrank_pi]

/-- Taking the Hermitian dual twice recovers the code. -/
@[simp]
theorem hermitianDual_hermitianDual (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (C : Submodule K (ι → K)) : hermitianDual σ (hermitianDual σ C) = C := by
  apply (Submodule.eq_of_le_of_finrank_le (le_hermitianDual_hermitianDual σ hσ C) _).symm
  have h₁ := finrank_add_finrank_hermitianDual σ C
  have h₂ := finrank_add_finrank_hermitianDual σ (hermitianDual σ C)
  omega

/-- For an involutive automorphism, the Hermitian dual of an intersection is the sum
of the Hermitian duals. -/
@[simp]
theorem hermitianDual_inf (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (C D : Submodule K (ι → K)) :
    hermitianDual σ (C ⊓ D) = hermitianDual σ C ⊔ hermitianDual σ D := by
  have h := hermitianDual_sup σ (hermitianDual σ C) (hermitianDual σ D)
  simpa only [hermitianDual_hermitianDual σ hσ] using
    (congrArg (hermitianDual σ) h).symm

/-- A matrix generates a code exactly when its conjugate checks the Hermitian dual. -/
theorem range_vecMulLinear_eq_iff_ker_map_eq_hermitianDual (σ : K ≃+* K)
    (hσ : Function.Involutive σ) {ρ : Type*} [Fintype ρ]
    (G : Matrix ρ ι K) (C : Submodule K (ι → K)) :
    LinearMap.range G.vecMulLinear = C ↔
      LinearMap.ker (G.map σ).mulVecLin = hermitianDual σ C := by
  rw [← hermitianDual_range_vecMulLinear_of_involutive σ hσ]
  exact ⟨congrArg (hermitianDual σ), fun h ↦ by
    simpa only [hermitianDual_hermitianDual σ hσ] using congrArg (hermitianDual σ) h⟩

end Field

end TauCeti
