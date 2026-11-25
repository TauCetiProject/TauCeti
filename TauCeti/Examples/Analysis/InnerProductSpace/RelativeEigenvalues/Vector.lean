/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Vector
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Examples: eigenvalue vectors relative to a non-standard metric on `ℂ²`

On `ℂ²` take the Hermitian forms `h = diag(2, 1)` and `a = diag(2, 3)`, that is
`h(u, v) = 2 ū₁ v₁ + ū₂ v₂` and `a(u, v) = 2 ū₁ v₁ + 3 ū₂ v₂`. The family `(e₁/√2, e₂)` is
`h`-orthonormal, with `a(b₁, b₁) = 1` and `a(b₂, b₂) = 3`, so `μ = (1, 3)` and its reordering
`(3, 1)` are eigenvalue vectors of `a` relative to `h`, and the decreasingly sorted one is
`(3, 1)`. The Euclidean basis `(e₁, e₂)` has `h(e₁, e₁) = 2` and is not `h`-orthonormal: the
Euclidean eigenvalues `(2, 3)` of `a` are not an eigenvalue vector relative to `h`.
-/

public section

open Module

namespace TauCeti.RelEigenvalueVectorExamples

local notation "ℂ²" => EuclideanSpace ℂ (Fin 2)

/-- The diagonal Hermitian form `(u, v) ↦ ∑ᵢ dᵢ ūᵢ vᵢ` on `ℂ²`. -/
noncomputable abbrev diagForm (d : Fin 2 → ℝ) : ℂ² →ₗ⋆[ℂ] ℂ² →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun u v ↦ ∑ i, (starRingEnd ℂ) (u i) * (d i * v i))
    (fun _ _ _ ↦ by simp [Fin.sum_univ_two]; ring)
    (fun _ _ _ ↦ by simp [Fin.sum_univ_two]; ring)
    (fun _ _ _ ↦ by simp [Fin.sum_univ_two]; ring)
    (fun _ _ _ ↦ by simp [Fin.sum_univ_two]; ring)

/-- The diagonal form in coordinates. -/
theorem diagForm_apply (d : Fin 2 → ℝ) (u v : ℂ²) :
    diagForm d u v = (starRingEnd ℂ) (u 0) * (d 0 * v 0) +
      (starRingEnd ℂ) (u 1) * (d 1 * v 1) := by
  simp [diagForm, Fin.sum_univ_two]

/-- The reindexing of `Fin (finrank ℂ ℂ²)` by `Fin 2`. -/
noncomputable abbrev e : Fin (finrank ℂ ℂ²) ≃ Fin 2 := finCongr finrank_euclideanSpace_fin

/-- **`μ = (1, 3)` is an eigenvalue vector of `diag(2, 3)` relative to `diag(2, 1)`**, through
the `h`-orthonormal family `(e₁/√2, e₂)`. -/
theorem isRelEigenvalueVector_one_three :
    IsRelEigenvalueVector (diagForm ![2, 1] · ·) (diagForm ![2, 3] · ·) (![1, 3] ∘ e) := by
  refine (isRelEigenvalueVector_def _ _ _).2
    ⟨![EuclideanSpace.single 0 ((Real.sqrt 2)⁻¹ : ℂ), EuclideanSpace.single 1 1] ∘ e,
      fun i j ↦ ?_⟩
  obtain ⟨i, rfl⟩ := e.symm.surjective i
  obtain ⟨j, rfl⟩ := e.symm.surjective j
  have hs (c : ℂ) : ((Real.sqrt 2 : ℂ))⁻¹ * c * (Real.sqrt 2 : ℂ)⁻¹ = c / 2 := by
    rw [mul_comm _ c, mul_assoc, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
    ring
  fin_cases i <;> fin_cases j <;>
    simp [← mul_assoc, Complex.conj_ofReal, hs]

/-- Eigenvalue vectors are closed under reordering: `(3, 1)` qualifies too. -/
theorem isRelEigenvalueVector_three_one :
    IsRelEigenvalueVector (diagForm ![2, 1] · ·) (diagForm ![2, 3] · ·) (![3, 1] ∘ e) := by
  have h := isRelEigenvalueVector_one_three.comp_perm (e.trans ((Equiv.swap 0 1).trans e.symm))
  convert h using 1
  ext i
  obtain ⟨i, rfl⟩ := e.symm.surjective i
  fin_cases i <;> rfl

/-- **The sorted eigenvalue vector is `(3, 1)`**: it is the only decreasing eigenvalue vector of
`diag(2, 3)` relative to `diag(2, 1)`. -/
example {μ : Fin (finrank ℂ ℂ²) → ℝ}
    (hμ : IsRelEigenvalueVector (diagForm ![2, 1] · ·) (diagForm ![2, 3] · ·) μ)
    (hμa : Antitone μ) : μ = ![3, 1] ∘ e := by
  refine hμ.eq_of_antitone hμa isRelEigenvalueVector_three_one fun i j hij ↦ ?_
  obtain ⟨i, rfl⟩ := e.symm.surjective i
  obtain ⟨j, rfl⟩ := e.symm.surjective j
  fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]

/-- **The Euclidean eigenvalues do not qualify.** The Euclidean basis is not `h`-orthonormal, and
`(2, 3)` is not a reordering of `(1, 3)`, so it is not an eigenvalue vector relative to `h`. -/
example :
    ¬ IsRelEigenvalueVector (diagForm ![2, 1] · ·) (diagForm ![2, 3] · ·) (![2, 3] ∘ e) := by
  intro h23
  obtain ⟨σ, hσ⟩ := isRelEigenvalueVector_one_three.exists_perm_eq h23
  have h := congrFun hσ (e.symm 0)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  obtain ⟨k, hk⟩ := e.symm.surjective (σ (e.symm 0))
  rw [← hk, Equiv.apply_symm_apply] at h
  fin_cases k <;> norm_num at h

end TauCeti.RelEigenvalueVectorExamples
