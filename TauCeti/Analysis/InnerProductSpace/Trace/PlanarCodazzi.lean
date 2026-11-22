/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.Ring

/-!
# Hilbert–Schmidt contractions and planar Codazzi tensors

The Hilbert–Schmidt pairing on finite-dimensional real endomorphisms is the trace of an adjoint
composition. Contracting it with the source metric gives the squared tensor norm of a linear
endomorphism-valued map. These definitions retain the ordinary topology on continuous linear
maps and do not identify its operator norm with a tensor norm.

For a symmetric trace-free endomorphism on a real plane, contracting it with a fully symmetric
trace-free cubic tensor gives the exact two-dimensional Kato identity. The contraction is
expressed by `planar_codazzi_identity` using the Hilbert–Schmidt pairing and tensor energy.
-/

public noncomputable section

open Module
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Hilbert–Schmidt pairing of real endomorphisms. -/
def endomorphismHilbertSchmidtForm (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : LinearMap.BilinForm ℝ (V →L[ℝ] V) :=
  LinearMap.mk₂ ℝ
    (fun A B ↦ LinearMap.trace ℝ V (A.toLinearMap.adjoint.comp B.toLinearMap))
    (fun A B C ↦ by simp [LinearMap.add_comp])
    (fun c A B ↦ by simp [LinearMap.smul_comp])
    (fun A B C ↦ by simp [LinearMap.comp_add])
    (fun c A B ↦ by simp [LinearMap.comp_smul])

/-- The Hilbert–Schmidt pairing evaluates as a trace of an adjoint composition. -/
theorem endomorphismHilbertSchmidtForm_apply (A B : V →L[ℝ] V) :
    endomorphismHilbertSchmidtForm V A B =
      LinearMap.trace ℝ V (A.toLinearMap.adjoint.comp B.toLinearMap) := (rfl)

/-- In an orthonormal basis the pairing is the sum of its column pairings. -/
theorem endomorphismHilbertSchmidtForm_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) :
    endomorphismHilbertSchmidtForm V A B = ∑ i, inner ℝ (A (b i)) (B (b i)) := by
  rw [endomorphismHilbertSchmidtForm_apply, LinearMap.trace_eq_sum_inner _ b]
  exact Finset.sum_congr rfl fun i _ ↦ LinearMap.adjoint_inner_right A.toLinearMap _ _

/-- The Hilbert–Schmidt pairing is the sum of products of matrix coefficients. -/
theorem endomorphismHilbertSchmidtForm_eq_sum_inner_mul {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) :
    endomorphismHilbertSchmidtForm V A B =
      ∑ i, ∑ j, inner ℝ (A (b i)) (b j) * inner ℝ (B (b i)) (b j) := by
  rw [endomorphismHilbertSchmidtForm_eq_sum b]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [real_inner_comm (B (b i))] using
    (b.sum_inner_mul_inner (A (b i)) (B (b i))).symm

/-- The pairing with a symmetric endomorphism is its ordinary composition trace. -/
theorem endomorphismHilbertSchmidtForm_apply_of_isSymmetric (A B : V →L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) :
    endomorphismHilbertSchmidtForm V A B =
      LinearMap.trace ℝ V (A.toLinearMap.comp B.toLinearMap) := by
  rw [endomorphismHilbertSchmidtForm_apply, hA.adjoint_eq]

/-- The diagonal Hilbert–Schmidt pairing is nonnegative. -/
theorem endomorphismHilbertSchmidtForm_self_nonneg (A : V →L[ℝ] V) :
    0 ≤ endomorphismHilbertSchmidtForm V A A := by
  rw [endomorphismHilbertSchmidtForm_eq_sum (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_nonneg fun _ _ ↦ real_inner_self_nonneg

/-- The squared tensor norm of an endomorphism-valued linear map. -/
def endomorphismDerivativeEnergy (D : V →L[ℝ] (V →L[ℝ] V)) : ℝ :=
  bilinFormTrace ((endomorphismHilbertSchmidtForm V).compl₁₂ D.toLinearMap D.toLinearMap)

/-- The derivative energy contracts the Hilbert–Schmidt pairing with the source metric. -/
theorem endomorphismDerivativeEnergy_def (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D =
      bilinFormTrace ((endomorphismHilbertSchmidtForm V).compl₁₂ D.toLinearMap D.toLinearMap) :=
  (rfl)

/-- In an orthonormal basis the energy is the sum of the squared Hilbert–Schmidt norms. -/
theorem endomorphismDerivativeEnergy_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D =
      ∑ i, endomorphismHilbertSchmidtForm V (D (b i)) (D (b i)) := by
  rw [endomorphismDerivativeEnergy_def, bilinFormTrace_eq_sum _ b]
  exact (rfl)

/-- The energy is the squared norm summed over its first two orthonormal slots. -/
theorem endomorphismDerivativeEnergy_eq_sum_sum_norm_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D = ∑ i, ∑ j, ‖D (b i) (b j)‖ ^ 2 := by
  simp only [endomorphismDerivativeEnergy_eq_sum b, endomorphismHilbertSchmidtForm_eq_sum b,
    real_inner_self_eq_norm_sq]

/-- The energy is the sum of squares of all its coefficients in an orthonormal basis. -/
theorem endomorphismDerivativeEnergy_eq_sum_inner_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D =
      ∑ i, ∑ j, ∑ k, inner ℝ (D (b i) (b j)) (b k) ^ 2 := by
  simp only [endomorphismDerivativeEnergy_eq_sum_sum_norm_sq b, b.sum_sq_inner_left]

/-- A squared tensor norm is nonnegative. -/
theorem endomorphismDerivativeEnergy_nonneg (D : V →L[ℝ] (V →L[ℝ] V)) :
    0 ≤ endomorphismDerivativeEnergy D := by
  rw [endomorphismDerivativeEnergy_eq_sum_sum_norm_sq (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The zero endomorphism-valued map has zero energy. -/
@[simp]
theorem endomorphismDerivativeEnergy_zero :
    endomorphismDerivativeEnergy (0 : V →L[ℝ] (V →L[ℝ] V)) = 0 := by
  simp [endomorphismDerivativeEnergy_eq_sum_sum_norm_sq (stdOrthonormalBasis ℝ V)]

private theorem planar_coefficient_identity (a : Fin 2 → Fin 2 → ℝ)
    (t : Fin 2 → Fin 2 → Fin 2 → ℝ) (ha : ∀ i j, a i j = a j i)
    (hatrace : a 0 0 + a 1 1 = 0) (htlast : ∀ i j k, t i j k = t i k j)
    (htfirst : ∀ i j k, t i j k = t j i k) (httrace : ∀ i, t i 0 0 + t i 1 1 = 0) :
    (∑ i, (2 * ∑ j, ∑ k, a j k * t i j k) ^ 2) =
      2 * (∑ i, ∑ j, a i j ^ 2) * (∑ i, ∑ j, ∑ k, t i j k ^ 2) := by
  have ha10 : a 1 0 = a 0 1 := ha 1 0
  have ha11 : a 1 1 = -a 0 0 := eq_neg_of_add_eq_zero_right hatrace
  have ht010 : t 0 1 0 = t 0 0 1 := htlast 0 1 0
  have ht011 : t 0 1 1 = -t 0 0 0 := eq_neg_of_add_eq_zero_right (httrace 0)
  have ht100 : t 1 0 0 = t 0 0 1 := (htfirst 1 0 0).trans ht010
  have ht101 : t 1 0 1 = -t 0 0 0 := (htfirst 1 0 1).trans ht011
  have ht110 : t 1 1 0 = -t 0 0 0 := (htlast 1 1 0).trans ht101
  have ht111 : t 1 1 1 = -t 0 0 1 := by
    rw [eq_neg_of_add_eq_zero_right (httrace 1), ht100]
  simp only [Fin.sum_univ_two, ha10, ha11, ht010, ht011, ht100, ht101, ht110, ht111]
  ring

/-- In dimension two, a symmetric trace-free Codazzi cubic has the exact Kato contraction. -/
theorem planar_codazzi_identity (b : OrthonormalBasis (Fin 2) ℝ V)
    (S : V →L[ℝ] V) (D : V →L[ℝ] (V →L[ℝ] V)) (hS : S.toLinearMap.IsSymmetric)
    (hStrace : LinearMap.trace ℝ V S.toLinearMap = 0)
    (hD : ∀ w, (D w).toLinearMap.IsSymmetric)
    (hDtrace : ∀ w, LinearMap.trace ℝ V (D w).toLinearMap = 0)
    (hCodazzi : ∀ u v, D u v = D v u) :
    (∑ i, (2 * endomorphismHilbertSchmidtForm V S (D (b i))) ^ 2) =
      2 * endomorphismHilbertSchmidtForm V S S * endomorphismDerivativeEnergy D := by
  have htrace (A : V →L[ℝ] V) :
      inner ℝ (A (b 0)) (b 0) + inner ℝ (A (b 1)) (b 1) =
        LinearMap.trace ℝ V A.toLinearMap := by
    rw [LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_two]
    simp only [ContinuousLinearMap.coe_coe, real_inner_comm (A (b 0)),
      real_inner_comm (A (b 1))]
  have h := planar_coefficient_identity
    (fun i j ↦ inner ℝ (S (b i)) (b j))
    (fun i j k ↦ inner ℝ (D (b i) (b j)) (b k))
    (fun i j ↦ (hS (b i) (b j)).trans (real_inner_comm _ _))
    ((htrace S).trans hStrace)
    (fun i j k ↦ (hD (b i) (b j) (b k)).trans (real_inner_comm _ _))
    (fun i j k ↦ congrArg (fun v ↦ inner ℝ v (b k)) (hCodazzi (b i) (b j)))
    (fun i ↦ (htrace (D (b i))).trans (hDtrace (b i)))
  simpa only [endomorphismHilbertSchmidtForm_eq_sum_inner_mul b,
    endomorphismDerivativeEnergy_eq_sum_inner_sq b, pow_two] using h

end TauCeti
