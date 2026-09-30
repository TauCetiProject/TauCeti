/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Galois duals of linear codes

A code is a submodule of a finite coordinate space. Its Galois dual uses the form
`h(x,y) = ∑ i, x i * σ (y i)`, with a specified semiring automorphism `σ`. A generator
matrix becomes a parity-check matrix for the dual after applying `σ.symm` entrywise;
for involutive `σ`, this is `σ` itself. Over a field, the dimensions of a code and its dual
add to the length. Taking duals with `σ` and then `σ.symm` recovers the code; for
involutive `σ`, this is Hermitian double duality.
The field need not be finite.

The API is in `RingEquiv`: use `σ.galoisDual C`, or `RingEquiv.galoisDual σ C`.

The matrix convention is row generators (`range G.vecMulLinear`) and column syndromes
(`ker H.mulVecLin`). In particular, omitting the conjugation can compute a different dual.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*,
§§1.3–1.4.
-/

public section

namespace RingEquiv

open Module Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The Galois dual of a code, with the automorphism acting on the second argument.
For an involutive automorphism, this is the Hermitian dual. -/
noncomputable def galoisDual (σ : R ≃+* R) (C : Submodule R (ι → R)) :
    Submodule R (ι → R) := C.orthogonalBilin (sesquilinearForm σ)

/-- The Galois dual is the orthogonal submodule for the standard sesquilinear form. -/
theorem galoisDual_def (σ : R ≃+* R) (C : Submodule R (ι → R)) :
    galoisDual σ C = C.orthogonalBilin (sesquilinearForm σ) := by
  rfl

/-- Membership in the Galois dual means being orthogonal to every codeword with respect
to the standard sesquilinear form. -/
@[simp]
theorem mem_galoisDual (σ : R ≃+* R) (C : Submodule R (ι → R)) (y : ι → R) :
    y ∈ galoisDual σ C ↔ ∀ x ∈ C, ∑ i, x i * σ (y i) = 0 := by
  simp [galoisDual]

@[simp]
theorem galoisDual_bot (σ : R ≃+* R) :
    galoisDual σ (⊥ : Submodule R (ι → R)) = ⊤ := by
  simp [galoisDual]

@[simp]
theorem galoisDual_top (σ : R ≃+* R) :
    galoisDual σ (⊤ : Submodule R (ι → R)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  exact (nondegenerate_sesquilinearForm σ).2 y (fun x ↦ hy x (Submodule.mem_top))

/-- Galois duality reverses inclusion. -/
theorem galoisDual_antitone (σ : R ≃+* R) :
    Antitone (galoisDual σ (ι := ι)) := Submodule.orthogonalBilin_antitone

/-- The Galois dual of a sum is the intersection of the Galois duals. -/
@[simp]
theorem galoisDual_sup (σ : R ≃+* R) (C D : Submodule R (ι → R)) :
    galoisDual σ (C ⊔ D) = galoisDual σ C ⊓ galoisDual σ D :=
  Submodule.orthogonalBilin_sup C D

/-- Every code is contained in the inverse-automorphism dual of its Galois dual. -/
theorem le_galoisDual_symm_galoisDual (σ : R ≃+* R)
    (C : Submodule R (ι → R)) : C ≤ galoisDual σ.symm (galoisDual σ C) := by
  intro x hx y hy
  rw [sesquilinearForm_symm_swap, hy x hx, map_zero]

/-- Every code is contained in its double Hermitian dual for an involutive automorphism. -/
theorem le_galoisDual_galoisDual (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (C : Submodule R (ι → R)) : C ≤ galoisDual σ (galoisDual σ C) := by
  have hsymm : σ.symm = σ := DFunLike.coe_injective (hσ.leftInverse_iff.mp σ.left_inv)
  simpa only [hsymm] using le_galoisDual_symm_galoisDual σ C

/-- The Galois dual of a row space is the kernel of the matrix obtained by applying
the inverse automorphism entrywise. -/
theorem galoisDual_range_vecMulLinear (σ : R ≃+* R)
    {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι R) :
    galoisDual σ (LinearMap.range G.vecMulLinear) =
      LinearMap.ker (G.map σ.symm).mulVecLin := by
  ext y
  rw [galoisDual, range_vecMulLinear]
  simp only [Submodule.mem_orthogonalBilin_span, Set.forall_mem_range]
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
  apply forall_congr'
  intro i
  rw [← σ.symm.map_eq_zero_iff]
  simp [sesquilinearForm_apply, Matrix.mulVec, dotProduct]

/-- For an involutive automorphism, the Galois dual of a row space is the kernel of
the entrywise-conjugate matrix. -/
theorem galoisDual_range_vecMulLinear_of_involutive (σ : R ≃+* R)
    (hσ : Function.Involutive σ) {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι R) :
    galoisDual σ (LinearMap.range G.vecMulLinear) =
      LinearMap.ker (G.map σ).mulVecLin := by
  have hsymm : σ.symm = σ := DFunLike.coe_injective (hσ.leftInverse_iff.mp σ.left_inv)
  simpa only [hsymm] using galoisDual_range_vecMulLinear σ G

section Field

variable {K : Type*} [Field K]

/-- The dimensions of a code and its Galois dual add to the length. -/
theorem finrank_add_finrank_galoisDual (σ : K ≃+* K) (C : Submodule K (ι → K)) :
    finrank K C + finrank K (galoisDual σ C) = Fintype.card ι := by
  have hd : finrank K (galoisDual σ C) = finrank K C.dualAnnihilator := by
    rw [galoisDual, ← Submodule.comap_dualAnnihilator_eq_orthogonalBilin]
    let f := (sesquilinearForm σ (ι := ι)).flip
    have hf := sesquilinearForm_flip_bijective σ (ι := ι)
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

/-- Taking Galois duals with inverse automorphisms recovers the code. -/
@[simp]
theorem galoisDual_symm_galoisDual (σ : K ≃+* K)
    (C : Submodule K (ι → K)) : galoisDual σ.symm (galoisDual σ C) = C := by
  apply (Submodule.eq_of_le_of_finrank_le (le_galoisDual_symm_galoisDual σ C) _).symm
  have h₁ := finrank_add_finrank_galoisDual σ C
  have h₂ := finrank_add_finrank_galoisDual σ.symm (galoisDual σ C)
  omega

/-- Taking the Hermitian dual twice recovers the code for an involutive automorphism. -/
@[simp]
theorem galoisDual_galoisDual (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (C : Submodule K (ι → K)) : galoisDual σ (galoisDual σ C) = C := by
  have hsymm : σ.symm = σ := DFunLike.coe_injective (hσ.leftInverse_iff.mp σ.left_inv)
  simpa only [hsymm] using galoisDual_symm_galoisDual σ C

/-- The Galois dual of an intersection is the sum of the Galois duals. -/
@[simp]
theorem galoisDual_inf (σ : K ≃+* K) (C D : Submodule K (ι → K)) :
    galoisDual σ (C ⊓ D) = galoisDual σ C ⊔ galoisDual σ D := by
  apply (Submodule.eq_of_le_of_finrank_le
    (sup_le (galoisDual_antitone σ inf_le_left)
      (galoisDual_antitone σ inf_le_right)) _).symm
  have hC := finrank_add_finrank_galoisDual σ C
  have hD := finrank_add_finrank_galoisDual σ D
  have hsup := finrank_add_finrank_galoisDual σ (C ⊔ D)
  have hinf := finrank_add_finrank_galoisDual σ (C ⊓ D)
  have hCD := Submodule.finrank_sup_add_finrank_inf_eq C D
  have hdual := Submodule.finrank_sup_add_finrank_inf_eq (galoisDual σ C) (galoisDual σ D)
  rw [galoisDual_sup] at hsup
  omega

/-- A matrix generates a code exactly when its inverse-automorphism image checks the
Galois dual. -/
theorem range_vecMulLinear_eq_iff_ker_map_eq_galoisDual (σ : K ≃+* K)
    {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι K) (C : Submodule K (ι → K)) :
    LinearMap.range G.vecMulLinear = C ↔
      LinearMap.ker (G.map σ.symm).mulVecLin = galoisDual σ C := by
  rw [← galoisDual_range_vecMulLinear]
  exact ⟨congrArg (galoisDual σ), fun h ↦ by
    simpa only [galoisDual_symm_galoisDual] using congrArg (galoisDual σ.symm) h⟩

/-- For an involutive automorphism, a matrix generates a code exactly when its conjugate
checks the Hermitian dual. -/
theorem range_vecMulLinear_eq_iff_ker_map_eq_galoisDual_of_involutive (σ : K ≃+* K)
    (hσ : Function.Involutive σ) {ρ : Type*} [Fintype ρ]
    (G : Matrix ρ ι K) (C : Submodule K (ι → K)) :
    LinearMap.range G.vecMulLinear = C ↔
      LinearMap.ker (G.map σ).mulVecLin = galoisDual σ C := by
  have hsymm : σ.symm = σ := DFunLike.coe_injective (hσ.leftInverse_iff.mp σ.left_inv)
  simpa only [hsymm] using range_vecMulLinear_eq_iff_ker_map_eq_galoisDual σ G C

end Field

end RingEquiv
