/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.Ring

/-!
# Hilbert–Schmidt contractions and planar Codazzi tensors

Contracting `ContinuousLinearMap.hilbertSchmidtInner` with the source metric gives the squared
tensor norm of a linear endomorphism-valued map. This definition retains the ordinary topology
on continuous linear maps and does not identify its operator norm with a tensor norm.

For a symmetric trace-free endomorphism on a real plane, contracting it with a fully symmetric
trace-free cubic tensor gives the exact two-dimensional Kato identity. The contraction is
expressed by `planar_codazzi_identity` using the Hilbert–Schmidt pairing and tensor energy.
-/

public noncomputable section

open Module
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The squared tensor norm of an endomorphism-valued linear map. -/
def endomorphismDerivativeEnergy (D : V →L[ℝ] (V →L[ℝ] V)) : ℝ :=
  bilinFormTrace
    ((ContinuousLinearMap.hilbertSchmidtBilinForm V V).compl₁₂ D.toLinearMap D.toLinearMap)

/-- The derivative energy contracts the Hilbert–Schmidt pairing with the source metric. -/
theorem endomorphismDerivativeEnergy_def (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D =
      bilinFormTrace
        ((ContinuousLinearMap.hilbertSchmidtBilinForm V V).compl₁₂ D.toLinearMap D.toLinearMap) :=
  (rfl)

/-- In an orthonormal basis the energy is the sum of the squared Hilbert–Schmidt norms. -/
theorem endomorphismDerivativeEnergy_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D =
      ∑ i, (D (b i)).hilbertSchmidtInner (D (b i)) := by
  rw [endomorphismDerivativeEnergy_def, bilinFormTrace_eq_sum _ b]
  simp only [LinearMap.compl₁₂_apply, ContinuousLinearMap.hilbertSchmidtBilinForm_apply,
    ContinuousLinearMap.coe_coe]

/-- The energy is the squared norm summed over its first two orthonormal slots. -/
theorem endomorphismDerivativeEnergy_eq_sum_sum_norm_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] (V →L[ℝ] V)) :
    endomorphismDerivativeEnergy D = ∑ i, ∑ j, ‖D (b i) (b j)‖ ^ 2 := by
  simp only [endomorphismDerivativeEnergy_eq_sum b,
    ContinuousLinearMap.hilbertSchmidtInner_eq_sum _ _ b, real_inner_self_eq_norm_sq]

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
    (∑ i, (2 * S.hilbertSchmidtInner (D (b i))) ^ 2) =
      2 * S.hilbertSchmidtInner S * endomorphismDerivativeEnergy D := by
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
  simpa only [ContinuousLinearMap.hilbertSchmidtInner_eq_sum_inner_mul _ _ b b,
    endomorphismDerivativeEnergy_eq_sum_inner_sq b, pow_two] using h

end TauCeti
