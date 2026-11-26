/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Parity
public import TauCeti.Geometry.Symplectic.ConleyZehnder

import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# The parity of the Conley–Zehnder index of linear symplectic maps

Let `(V, ω)` be a symplectic vector space of dimension `2n`. A path `Ψ` of linear maps of `V`
preserving `ω`, from the identity to a map `B` without the eigenvalue `1`, has an integer
Conley–Zehnder index `k` (`TauCeti.SymplecticForm.conleyZehnderIndex`), and its parity is the sign
of the determinant of `1 - B`:

`(-1) ^ (n - k) = sign det (1 - B)`

(`TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq_of_one`). For a path between two maps
`A` and `B` without the eigenvalue `1`, the index is an integer `k` with
`(-1) ^ k = sign (det (1 - A) det (1 - B))`
(`TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq`).

The linearized flow along a nondegenerate one-periodic orbit of a Hamiltonian is a path of the
first kind, so its index is an integer; this is what makes the Conley–Zehnder grading of the
generators of a Floer complex integer valued. The statements are those of the matrix index
(`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one`,
`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq`), read in a symplectic basis: the matrix of
`1 - B` in a basis has the determinant of `1 - B`, and its eigenvalue `1` is that of `B`
(`TauCeti.SymplecticForm.det_one_sub_toGLSymplectic`,
`TauCeti.SymplecticForm.det_one_sub_toGLSymplectic_ne_zero_iff`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Section 2.4 (the parity of the Conley–Zehnder index).
-/

public section

open Matrix Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- **The parity of the Conley–Zehnder index**, for paths from the identity. For a path `Ψ` of
linear maps of a symplectic vector space `(V, ω)` of dimension `2n` preserving `ω`, from the
identity to a map `B` without the eigenvalue `1`, the Conley–Zehnder index is an integer `k`
with `(-1) ^ (n - k) = sign det (1 - B)`. -/
theorem exists_int_conleyZehnderIndex_eq_of_one {B : V →L[ℝ] V} (Ψ : Path 1 B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (hB : End.eigenspace (B : V →ₗ[ℝ] V) 1 = ⊥) :
    ∃ k : ℤ, ω.conleyZehnderIndex Ψ hΨ = k ∧
      ((((finrank ℝ V / 2 : ℕ) : ℤ) - k).negOnePow : ℤ) =
        SignType.sign (LinearMap.det (1 - (B : V →ₗ[ℝ] V))) := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  -- The basis has `2 m` elements, so `m = dim V / 2`.
  have hm : m = finrank ℝ V / 2 := by
    have := finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  -- In the basis `b` the path of matrices starts at the identity matrix.
  have h₁ : (1 : GLSymplectic (Fin m) ℝ) =
      ω.toGLSymplectic hb ((1 : V →L[ℝ] V) : V →ₗ[ℝ] V) (by simp) :=
    (ω.toGLSymplectic_id hb fun _ _ ↦ rfl).symm
  have hB' : ∀ u v, ω (B u) (B v) = ω u v := by simpa using hΨ 1
  obtain ⟨k, hk, hsign⟩ := GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one
    ((ω.matrixPath hb Ψ hΨ).cast h₁ rfl) ((ω.det_one_sub_toGLSymplectic_ne_zero_iff hb _ hB').2 hB)
  refine ⟨k, ?_, ?_⟩
  · rw [ω.conleyZehnderIndex_eq hb, ← hk]
    exact GLSymplectic.conleyZehnderIndex_congr _ _ fun _ ↦ rfl
  · rw [← hm, ← ω.det_one_sub_toGLSymplectic hb _ hB', ← hsign, Fintype.card_fin]

/-- **The parity of the Conley–Zehnder index.** For a path `Ψ` of linear maps of a symplectic
vector space `(V, ω)` preserving `ω`, between two maps `A` and `B` without the eigenvalue `1`, the
Conley–Zehnder index is an integer `k` with `(-1) ^ k = sign (det (1 - A) det (1 - B))`. -/
theorem exists_int_conleyZehnderIndex_eq {A B : V →L[ℝ] V} (Ψ : Path A B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (hA : End.eigenspace (A : V →ₗ[ℝ] V) 1 = ⊥)
    (hB : End.eigenspace (B : V →ₗ[ℝ] V) 1 = ⊥) :
    ∃ k : ℤ, ω.conleyZehnderIndex Ψ hΨ = k ∧
      (k.negOnePow : ℤ) = SignType.sign (LinearMap.det (1 - (A : V →ₗ[ℝ] V)) *
        LinearMap.det (1 - (B : V →ₗ[ℝ] V))) := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  have hA' : ∀ u v, ω (A u) (A v) = ω u v := by simpa using hΨ 0
  have hB' : ∀ u v, ω (B u) (B v) = ω u v := by simpa using hΨ 1
  rw [ω.conleyZehnderIndex_eq hb, ← ω.det_one_sub_toGLSymplectic hb _ hA',
    ← ω.det_one_sub_toGLSymplectic hb _ hB']
  exact GLSymplectic.exists_int_conleyZehnderIndex_eq _
    ((ω.det_one_sub_toGLSymplectic_ne_zero_iff hb _ hA').2 hA)
    ((ω.det_one_sub_toGLSymplectic_ne_zero_iff hb _ hB').2 hB)

end TauCeti.SymplecticForm
