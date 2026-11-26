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

Let `(V, ω)` be a symplectic vector space of dimension `2n`. For a path `Ψ` of linear maps of `V`
preserving `ω` from the identity to a map `B` without the eigenvalue `1`, the Conley–Zehnder index
`TauCeti.SymplecticForm.conleyZehnderIndex` is an integer `k`, and its parity is the sign of
`det (1 - B)`:

`(-1) ^ (n - k) = sign det (1 - B)`

(`TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq_of_one`). For a path between two maps
`A` and `B` without the eigenvalue `1`, the index is an integer `k` with
`(-1) ^ k = sign (det (1 - A) det (1 - B))`
(`TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq`).

These are the statements `TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one` and
`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq` for symplectic matrices, read in a
symplectic basis: the determinant of `1 - B` is that of `1` minus its matrix
(`TauCeti.SymplecticForm.det_one_sub_coe_toGLSymplectic`). This is the form needed for the
linearized flow `dφ_t` along a periodic orbit of a Hamiltonian, read in a symplectic frame. At a
nondegenerate orbit the return map `dφ_1` has no eigenvalue `1`, so the index of the orbit is an
integer, and its parity, the sign of the orbit in the Lefschetz count of fixed points, does not
depend on the frame.

## Main results

* `TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq`: integrality and parity of the index
  of a path between two maps without the eigenvalue `1`.
* `TauCeti.SymplecticForm.exists_int_conleyZehnderIndex_eq_of_one`: integrality and parity of the
  index of a path from the identity to a map without the eigenvalue `1`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Section 2.4 (the parity of the Conley–Zehnder index).
-/

public section

noncomputable section

open Matrix Module
open scoped unitInterval

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

omit [FiniteDimensional ℝ V] in
/-- In a symplectic basis `b`, the determinant of `1` minus the symplectic matrix of a linear map
`A` preserving `ω` is the determinant of `1 - A`. -/
theorem det_one_sub_coe_toGLSymplectic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : Basis (ι ⊕ ι) ℝ V} (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ)
    (A : V →ₗ[ℝ] V) (hA : ∀ u v, ω (A u) (A v) = ω u v) :
    (1 - ((ω.toGLSymplectic hb A hA : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)).det =
      LinearMap.det (1 - A) := by
  rw [coe_toGLSymplectic, ← LinearMap.toMatrix_one b, ← map_sub, LinearMap.det_toMatrix]

/-- **The parity of the Conley–Zehnder index.** For a path `Ψ` of linear maps preserving `ω` from
`A` to `B`, both without the eigenvalue `1`, the Conley–Zehnder index is an integer `k` with
`(-1) ^ k = sign (det (1 - A) det (1 - B))`. -/
theorem exists_int_conleyZehnderIndex_eq {A B : V →L[ℝ] V} (Ψ : Path A B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v)
    (hA : LinearMap.det ((1 - A : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hB : LinearMap.det ((1 - B : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ k : ℤ, ω.conleyZehnderIndex Ψ hΨ = k ∧
      (k.negOnePow : ℤ) = SignType.sign (LinearMap.det ((1 - A : V →L[ℝ] V) : V →ₗ[ℝ] V) *
        LinearMap.det ((1 - B : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one] at hA hB ⊢
  rw [ω.conleyZehnderIndex_eq hb]
  rw [← ω.det_one_sub_coe_toGLSymplectic hb _ (by simpa using hΨ 0)] at hA ⊢
  rw [← ω.det_one_sub_coe_toGLSymplectic hb _ (by simpa using hΨ 1)] at hB ⊢
  exact GLSymplectic.exists_int_conleyZehnderIndex_eq _ hA hB

/-- **The parity of the Conley–Zehnder index, from the identity.** For a path `Ψ` of linear maps
of a symplectic vector space `(V, ω)` of dimension `2n` preserving `ω`, from the identity to a map
`B` without the eigenvalue `1`, the Conley–Zehnder index is an integer `k` with
`(-1) ^ (n - k) = sign det (1 - B)`. -/
theorem exists_int_conleyZehnderIndex_eq_of_one {B : V →L[ℝ] V} (Ψ : Path 1 B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v)
    (hB : LinearMap.det ((1 - B : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ k : ℤ, ω.conleyZehnderIndex Ψ hΨ = k ∧
      ((((finrank ℝ V / 2 : ℕ) : ℤ) - k).negOnePow : ℤ) =
        SignType.sign (LinearMap.det ((1 - B : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  have hm : finrank ℝ V / 2 = m := by
    have := finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  -- The matrix path starts at the identity matrix.
  have h₁ : ω.toGLSymplectic hb ((1 : V →L[ℝ] V) : V →ₗ[ℝ] V) (by simp) = 1 :=
    (ω.toGLSymplectic_congr hb (ContinuousLinearMap.toLinearMap_one.trans Module.End.one_eq_id) _
      fun _ _ ↦ rfl).trans (ω.toGLSymplectic_id hb _)
  let Ψ' := (ω.matrixPath hb Ψ hΨ).cast h₁.symm rfl
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one] at hB ⊢
  rw [ω.conleyZehnderIndex_eq hb, hm,
    GLSymplectic.conleyZehnderIndex_congr (ω.matrixPath hb Ψ hΨ) Ψ' fun _ ↦ rfl]
  rw [← ω.det_one_sub_coe_toGLSymplectic hb _ (by simpa using hΨ 1)] at hB ⊢
  simpa using GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one Ψ' hB

end TauCeti.SymplecticForm
