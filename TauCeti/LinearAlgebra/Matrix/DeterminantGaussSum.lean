/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.GaussSum
public import TauCeti.Analysis.Fourier.FiniteAbelian.ModuleDual
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Determinant Gauss sums over finite commutative rings

The trace pairing defines a Fourier transform on square matrices over a finite ring.
A function transforming under left multiplication by invertible matrices through a primitive
character of the determinant has a Fourier transform proportional to the inverse character of
the determinant. The constant for the character itself has squared norm equal to the number of
matrices.

The singular case uses a rank-one perturbation of the identity in the right stabilizer of a
singular matrix. Primitivity gives such a perturbation on which the determinant character is
nontrivial. The size of the constant follows from orthogonality for the trace pairing.
-/

@[expose] public section

namespace Matrix

open Finset AddChar

variable {R n : Type*} [CommRing R] [Fintype R] [Fintype n] [DecidableEq n]

/-- The unnormalized Fourier transform on square matrices using the trace pairing. -/
noncomputable def traceFourier (ψ : AddChar R ℂ) (f : Matrix n n R → ℂ)
    (y : Matrix n n R) : ℂ :=
  ψ.fourierTransform f ((Matrix.traceLinearMap n R R).comp (LinearMap.mulLeft R y))

/-- The value of the matrix Fourier transform is the sum against the trace character. -/
theorem traceFourier_apply (ψ : AddChar R ℂ) (f : Matrix n n R → ℂ) (y : Matrix n n R) :
    traceFourier ψ f y = ∑ x, f x * ψ (y * x).trace := by
  simp [traceFourier, AddChar.fourierTransform_apply]

/-- A primitive additive character gives orthogonality for the matrix trace pairing. -/
private theorem sum_addChar_trace_mul_of_ne_zero {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    {y : Matrix n n R} (hy : y ≠ 0) : ∑ x : Matrix n n R, ψ (y * x).trace = 0 := by
  classical
  let κ : AddChar (Matrix n n R) ℂ :=
    ψ.compAddMonoidHom (Matrix.traceAddMonoidHom n R |>.comp (AddMonoidHom.mulLeft y))
  change ∑ x, κ x = 0
  apply AddChar.sum_eq_zero_of_ne_one
  intro hκ
  obtain ⟨i, j, hij⟩ : ∃ i j, y i j ≠ 0 := by
    by_contra! h
    exact hy (Matrix.ext h)
  apply hψ hij
  apply AddChar.eq_one_iff.mpr
  intro r
  simpa [κ, AddChar.mulShift_apply, Matrix.trace_mul_single, mul_comm] using
    (AddChar.eq_one_iff.mp hκ) (Matrix.single j i r)

/-- A determinant-equivariant function transforms through the inverse character, including at
singular matrices, provided the multiplicative character is nontrivial on the units congruent
to one modulo each nonzero principal ideal. The additive character is arbitrary. -/
theorem traceFourier_eq_inv_det_mul {χ : MulChar R ℂ} (ψ : AddChar R ℂ)
    (hχ : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ χ (1 + c * a) ≠ 1)
    (f : Matrix n n R → ℂ)
    (hf : ∀ (g : (Matrix n n R)ˣ) (x : Matrix n n R), f (g.val * x) = χ g.val.det * f x)
    (y : Matrix n n R) : traceFourier ψ f y = χ⁻¹ y.det * traceFourier ψ f 1 := by
  have hshift (g : (Matrix n n R)ˣ) (z : Matrix n n R) :
      χ g.val.det * traceFourier ψ f (z * g.val) = traceFourier ψ f z := by
    calc
      _ = ∑ x, f (g.val * x) * ψ (z * (g.val * x)).trace := by
        simp [traceFourier_apply, hf, mul_sum, mul_assoc]
      _ = _ := by
        rw [traceFourier_apply]
        exact g.mulLeft_bijective.sum_comp fun x ↦ f x * ψ (z * x).trace
  by_cases hy : IsUnit y
  · obtain ⟨g, rfl⟩ := hy
    simpa [χ.inv_apply] using (hshift g⁻¹ g.val).symm
  · obtain ⟨D, hD, i, j, hij⟩ : ∃ D : Matrix n n R, y * D = 0 ∧ ∃ i j, D i j ≠ 0 := by
      by_contra! h
      exact hy (isLeftRegular_iff_right_eq_zero_of_mul.mpr
        fun D hD ↦ Matrix.ext (h D hD)).isUnit_of_finite
    obtain ⟨c, hc, hc'⟩ := hχ (D i j) hij
    let g : Matrix n n R := 1 + D * single j () (1 : R) * single () i c
    have hdet : g.det = 1 + c * D i j := by
      simp [g, det_one_add_mul_comm, ← Matrix.mul_assoc]
    have hfix : y * g = y := by simp [g, mul_add, ← Matrix.mul_assoc, hD]
    have hg : IsUnit g.det := hdet ▸ hc
    have h := hshift (GeneralLinearGroup.mk'' g hg) y
    have hzero : traceFourier ψ f y = 0 :=
      (mul_left_eq_self₀.mp (by simpa [hdet, hfix] using h)).resolve_left hc'
    rw [hzero, χ⁻¹.map_nonunit (by rwa [← isUnit_iff_isUnit_det]), zero_mul]

/-- Pairing the transform of a determinant-equivariant function with the transform of the
determinant character recovers the value of the function at the identity. -/
theorem star_traceFourier_det_mul {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) {χ : MulChar R ℂ}
    (hχ : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ χ (1 + c * a) ≠ 1)
    (f : Matrix n n R → ℂ)
    (hf : ∀ (g : (Matrix n n R)ˣ) (x : Matrix n n R), f (g.val * x) = χ g.val.det * f x) :
    star (traceFourier ψ (fun x : Matrix n n R ↦ χ x.det) 1) * traceFourier ψ f 1 =
      f 1 * Fintype.card (Matrix n n R) := by
  classical
  calc
    _ = ∑ y : Matrix n n R, traceFourier ψ f y * ψ (-y.trace) := by
      rw [Finset.sum_congr rfl fun y _ ↦ congrArg (· * ψ (-y.trace))
        (traceFourier_eq_inv_det_mul ψ hχ f hf y)]
      have hconj : star (traceFourier ψ (fun x : Matrix n n R ↦ χ x.det) 1) =
          ∑ y : Matrix n n R, χ⁻¹ y.det * ψ (-y.trace) := by
        simp only [traceFourier_apply, Matrix.one_mul, star_sum, star_mul, MulChar.star_apply']
        exact Finset.sum_congr rfl fun y _ ↦ by
          rw [ψ.map_neg_eq_conj, starRingEnd_apply, mul_comm]
      rw [hconj, sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_right_comm _ _ _
    _ = ∑ x : Matrix n n R, f x * ∑ y : Matrix n n R, ψ ((x - 1) * y).trace := by
      simp only [traceFourier_apply, sum_mul, mul_assoc, ← map_add_eq_mul]
      rw [Finset.sum_comm]
      simp only [mul_sum]
      exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by
        rw [Matrix.trace_mul_comm y x, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
          sub_eq_add_neg]
    _ = _ := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro x _ hx
        rw [sum_addChar_trace_mul_of_ne_zero hψ (sub_ne_zero.mpr hx), mul_zero]
      · simp

/-- For primitive characters, the transform of a determinant-equivariant function at any matrix
is the determinant Gauss sum times the inverse character of the determinant times the value of
the function at the identity. The squared norm of the Gauss sum is the number of matrices. -/
theorem exists_traceFourier_eq_mul_inv_det {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    {χ : MulChar R ℂ}
    (hχ : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ χ (1 + c * a) ≠ 1) :
    ∃ γ : ℂ, ‖γ‖ ^ 2 = (Fintype.card (Matrix n n R) : ℝ) ∧
      ∀ f : Matrix n n R → ℂ,
        (∀ (g : (Matrix n n R)ˣ) (x : Matrix n n R), f (g.val * x) = χ g.val.det * f x) →
        ∀ y : Matrix n n R, traceFourier ψ f y = γ * χ⁻¹ y.det * f 1 := by
  let γ := traceFourier ψ (fun x : Matrix n n R ↦ χ x.det) 1
  have hγ : star γ * γ = Fintype.card (Matrix n n R) := by
    simpa [γ] using star_traceFourier_det_mul hψ hχ (fun x : Matrix n n R ↦ χ x.det) (by simp)
  have hne : star γ ≠ 0 := left_ne_zero_of_mul (hγ.trans_ne (by simp))
  refine ⟨γ, ?_, fun f hf y ↦ ?_⟩
  · simpa [sq] using congrArg norm hγ
  have hone : traceFourier ψ f 1 = γ * f 1 := by
    apply mul_left_cancel₀ hne
    rw [star_traceFourier_det_mul hψ hχ f hf, ← mul_assoc, hγ, mul_comm]
  rw [traceFourier_eq_inv_det_mul ψ hχ f hf, hone, mul_left_comm, mul_assoc]

end Matrix
