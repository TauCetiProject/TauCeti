/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.LinearAlgebra.Matrix.Trace.Fourier
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Determinant Gauss sums over finite commutative rings

Let `R` be a finite commutative ring, `ψ` an additive character of `R`, and `χ` a multiplicative
character of `R` that is primitive in the sense that for every `a ≠ 0` some unit `1 + c a` has
`χ (1 + c a) ≠ 1`. A function `f` on `n × n` matrices over `R` is determinant-equivariant if
`f (g x) = χ (det g) f x` for every invertible matrix `g`.

These results evaluate the trace Fourier transform `AddChar.traceFourier` of a
determinant-equivariant function everywhere from its value at the identity matrix.

* `AddChar.traceFourier_eq_inv_det_mul`: for every additive character, the transform at `y` is
  `χ⁻¹ (det y)` times the transform at the identity, singular `y` included.
* `AddChar.IsPrimitive.exists_traceFourier_eq_mul_inv_det`: if moreover `ψ` is primitive and the
  characters are complex valued, the transform at `y` is `γ χ⁻¹ (det y) f 1` for a determinant
  Gauss sum `γ` with `‖γ‖ ^ 2` equal to the number of matrices. Without primitivity of `ψ` this
  norm formula fails: for the trivial additive character and the quadratic character of `𝔽₃` in
  size one, the Gauss sum is zero.

## Provenance

These results adapt `New.Exchange.matrixFourier_eq_inv_det_mul`,
`New.Exchange.star_matrixFourier_det_mul` and `New.Exchange.exists_matrixFourier_eq_mul_inv_det`
(file `src/Lib/General/Analysis/FiniteFourier.lean`) of L. Alpöge's Lean formalization of the
Riemann hypothesis for Dirichlet L-functions,
https://github.com/leanprover-community/riemann-hypothesis (commit
`af5639fc3c5697fd8050d3fb58515e2efc606139`). Here the twisting identity is stated for characters
with values in any domain and the primitivity condition on `χ` is unfolded.
-/

public section

namespace AddChar

open Finset

variable {R n : Type*} [CommRing R] [Fintype R] [Fintype n] [DecidableEq n]

/-- A determinant-equivariant function transforms through the inverse character, including at
singular matrices, provided the multiplicative character is nontrivial on the units congruent
to one modulo each nonzero principal ideal. The additive character is arbitrary. -/
theorem traceFourier_eq_inv_det_mul {Λ : Type*} [CommRing Λ] [IsDomain Λ] (ψ : AddChar R Λ)
    {χ : MulChar R Λ} (hχ : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ χ (1 + c * a) ≠ 1)
    (f : Matrix n n R → Λ)
    (hf : ∀ (g : (Matrix n n R)ˣ) (x : Matrix n n R), f (g.val * x) = χ g.val.det * f x)
    (y : Matrix n n R) : ψ.traceFourier f y = χ⁻¹ y.det * ψ.traceFourier f 1 := by
  have hshift (g : (Matrix n n R)ˣ) (z : Matrix n n R) :
      χ g.val.det * ψ.traceFourier f (z * g.val) = ψ.traceFourier f z := by
    calc
      _ = ∑ x, f (g.val * x) * ψ (z * (g.val * x)).trace := by
        simp [traceFourier_apply, hf, mul_sum, mul_assoc]
      _ = _ := by
        rw [traceFourier_apply]
        exact g.mulLeft_bijective.sum_comp fun x ↦ f x * ψ (z * x).trace
  by_cases hy : IsUnit y
  · obtain ⟨g, rfl⟩ := hy
    simpa [χ.inv_apply, Matrix.coe_units_inv, Matrix.det_nonsing_inv] using
      (hshift g⁻¹ g.val).symm
  · obtain ⟨D, hD, i, j, hij⟩ : ∃ D : Matrix n n R, y * D = 0 ∧ ∃ i j, D i j ≠ 0 := by
      by_contra! h
      exact hy (isLeftRegular_iff_right_eq_zero_of_mul.mpr
        fun D hD ↦ Matrix.ext (h D hD)).isUnit_of_finite
    obtain ⟨c, hc, hc'⟩ := hχ (D i j) hij
    let g : Matrix n n R := 1 + D * Matrix.single j () (1 : R) * Matrix.single () i c
    have hdet : g.det = 1 + c * D i j := by
      simp [g, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc]
    have hfix : y * g = y := by simp [g, mul_add, ← Matrix.mul_assoc, hD]
    have hg : IsUnit g.det := hdet ▸ hc
    have h := hshift (Matrix.GeneralLinearGroup.mk'' g hg) y
    have hzero : ψ.traceFourier f y = 0 :=
      (mul_left_eq_self₀.mp (by simpa [hdet, hfix] using h)).resolve_left hc'
    rw [hzero, χ⁻¹.map_nonunit (by rwa [← Matrix.isUnit_iff_isUnit_det]), zero_mul]

/-- Pairing the transform of a determinant-equivariant function with the transform of the
determinant character recovers the value of the function at the identity. -/
theorem IsPrimitive.star_traceFourier_det_mul {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    {χ : MulChar R ℂ} (hχ : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ χ (1 + c * a) ≠ 1)
    (f : Matrix n n R → ℂ)
    (hf : ∀ (g : (Matrix n n R)ˣ) (x : Matrix n n R), f (g.val * x) = χ g.val.det * f x) :
    star (ψ.traceFourier (fun x : Matrix n n R ↦ χ x.det) 1) * ψ.traceFourier f 1 =
      f 1 * Fintype.card (Matrix n n R) := by
  calc
    _ = ∑ y : Matrix n n R, ψ.traceFourier f y * ψ (-y.trace) := by
      rw [Finset.sum_congr rfl fun y _ ↦ congrArg (· * ψ (-y.trace))
        (traceFourier_eq_inv_det_mul ψ hχ f hf y)]
      have hconj : star (ψ.traceFourier (fun x : Matrix n n R ↦ χ x.det) 1) =
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
        rw [hψ.sum_trace_mul_eq_zero (sub_ne_zero.mpr hx), mul_zero]
      · simp

/-- For primitive characters, the transform of a determinant-equivariant function at any matrix
is the determinant Gauss sum times the inverse character of the determinant times the value of
the function at the identity. The squared norm of the Gauss sum is the number of matrices. -/
theorem IsPrimitive.exists_traceFourier_eq_mul_inv_det {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    {χ : MulChar R ℂ}
    (hχ : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ χ (1 + c * a) ≠ 1) :
    ∃ γ : ℂ, ‖γ‖ ^ 2 = (Fintype.card (Matrix n n R) : ℝ) ∧
      ∀ f : Matrix n n R → ℂ,
        (∀ (g : (Matrix n n R)ˣ) (x : Matrix n n R), f (g.val * x) = χ g.val.det * f x) →
        ∀ y : Matrix n n R, ψ.traceFourier f y = γ * χ⁻¹ y.det * f 1 := by
  let γ := ψ.traceFourier (fun x : Matrix n n R ↦ χ x.det) 1
  have hγ : star γ * γ = Fintype.card (Matrix n n R) := by
    simpa [γ] using hψ.star_traceFourier_det_mul hχ (fun x : Matrix n n R ↦ χ x.det) (by simp)
  have hne : star γ ≠ 0 := left_ne_zero_of_mul (hγ.trans_ne (by simp))
  refine ⟨γ, ?_, fun f hf y ↦ ?_⟩
  · simpa [sq] using congrArg norm hγ
  have hone : ψ.traceFourier f 1 = γ * f 1 := by
    apply mul_left_cancel₀ hne
    rw [hψ.star_traceFourier_det_mul hχ f hf, ← mul_assoc, hγ, mul_comm]
  rw [traceFourier_eq_inv_det_mul ψ hχ f hf, hone, mul_left_comm, mul_assoc]

end AddChar
