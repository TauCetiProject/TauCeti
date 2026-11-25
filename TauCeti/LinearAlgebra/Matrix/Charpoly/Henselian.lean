/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Diagonalizing matrices with residually distinct eigenvalues over a henselian ring

Let `A → K` be an injective map from a henselian local ring with residue field `k` to a field. A
`2 × 2` matrix `M` over `K` whose characteristic polynomial comes from some `P` over `A`, with
reduction `(X - u) (X - v)` for distinct `u v ∈ k`, has two residually simple roots. Hensel's lemma
lifts them to roots `α β ∈ A` of `P`, which are distinct eigenvalues of `M`, so `M` is conjugate in
`GL₂(K)` to `diag(α, β)`.

## Main results

* `TauCeti.exists_conj_eq_diagonal_of_henselian_fin_two`: a `2 × 2` matrix with integral
  characteristic polynomial and residually distinct eigenvalues is conjugate to a diagonal matrix
  whose entries are integral lifts of the residual eigenvalues.
-/

public section

open Polynomial IsLocalRing Matrix

namespace TauCeti

variable {A K : Type*} [CommRing A] [IsLocalRing A] [HenselianRing A (maximalIdeal A)] [Field K]
  [Algebra A K] [FaithfulSMul A K]

/-- A `2 × 2` matrix whose characteristic polynomial is integral with residually distinct roots
`u ≠ v` is conjugate to a diagonal matrix whose entries are integral, with residues `u` and `v`. -/
theorem exists_conj_eq_diagonal_of_henselian_fin_two
    {M : Matrix (Fin 2) (Fin 2) K} {P : A[X]} {u v : ResidueField A} (huv : u ≠ v)
    (hP : P.map (algebraMap A K) = M.charpoly)
    (hPr : P.map (residue A) = (X - C u) * (X - C v)) :
    ∃ (Q : (Matrix (Fin 2) (Fin 2) K)ˣ) (α β : A),
      ((Q⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) * M * Q =
        diagonal ![algebraMap A K α, algebraMap A K β] ∧
      residue A α = u ∧ residue A β = v := by
  have hinj := FaithfulSMul.algebraMap_injective A K
  have hmon : P.Monic := monic_of_injective hinj (hP ▸ charpoly_monic M)
  -- Hensel's lemma lifts the residually simple roots `u` and `v` of `P`.
  have hroot {u v : ResidueField A} (huv : u ≠ v)
      (hPr : P.map (residue A) = (X - C u) * (X - C v)) :
      ∃ α : A, P.IsRoot α ∧ residue A α = u := by
    obtain ⟨a₀, rfl⟩ := residue_surjective u
    obtain ⟨α, hα, hα'⟩ := HenselianRing.is_henselian P hmon a₀
      (by rw [← residue_eq_zero_iff, ← eval_map_apply, hPr]; simp)
      (((residue_ne_zero_iff_isUnit _).mp (by
        rw [← eval_map_apply, ← derivative_map, hPr]
        simpa [derivative_mul, sub_eq_zero] using huv)).map _)
    exact ⟨α, hα, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩
  obtain ⟨α, hα, hαu⟩ := hroot huv hPr
  obtain ⟨β, hβ, hβv⟩ := hroot huv.symm (by rw [hPr, mul_comm])
  have heig (γ : A) (hγ : P.IsRoot γ) :
      ∃ w, Module.End.HasEigenvector (toLin' M) (algebraMap A K γ) w :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr (by
      rw [IsRoot, Matrix.charpoly_toLin', ← hP, eval_map_apply, hγ.eq_zero, map_zero])
      ).exists_hasEigenvector
  obtain ⟨w₁, hw₁⟩ := heig α hα
  obtain ⟨w₂, hw₂⟩ := heig β hβ
  have hMw₁ : M *ᵥ w₁ = algebraMap A K α • w₁ := hw₁.apply_eq_smul
  have hMw₂ : M *ᵥ w₂ = algebraMap A K β • w₂ := hw₂.apply_eq_smul
  have hαβ : algebraMap A K α ≠ algebraMap A K β := fun h => huv (by rw [← hαu, ← hβv, hinj h])
  set Q₀ : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => ![w₁, w₂] j i
  have hli : LinearIndependent K Q₀.col := by
    rw [show Q₀.col = ![w₁, w₂] by ext j i; fin_cases j <;> simp [Q₀]]
    refine Module.End.eigenvectors_linearIndependent' (toLin' M)
      ![algebraMap A K α, algebraMap A K β] ?_ _ (Fin.forall_fin_two.mpr ⟨hw₁, hw₂⟩)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hQ : IsUnit Q₀ := linearIndependent_col_iff_isUnit.mp hli
  refine ⟨hQ.unit, α, β, ?_, hαu, hβv⟩
  have hMQ : M * Q₀ = Q₀ * diagonal ![algebraMap A K α, algebraMap A K β] := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_two]
    fin_cases j
    · simpa [Q₀, mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using congrFun hMw₁ i
    · simpa [Q₀, mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using congrFun hMw₂ i
  rw [Matrix.mul_assoc, hQ.unit_spec, hMQ, ← Matrix.mul_assoc, hQ.val_inv_mul, Matrix.one_mul]

end TauCeti
