/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Normed.Algebra.Basic
public import TauCeti.Analysis.SpecialFunctions.Exponential.Map
public import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# The derivative of the exponential at Hermitian matrices

In a unitary eigenbasis of a Hermitian matrix with eigenvalues `d i`, the derivative of the
matrix exponential multiplies entry `(i,j)` by the positive divided difference
`dslope Real.exp (d i) (d j)`. Consequently the derivative is invertible, even on the full
matrix space. This is the analytic local-inverse step for smooth logarithms on positive
Hermitian matrices.

The proof uses the Duhamel integral `TauCeti.expFDeriv_apply_eq_integral` and Mathlib's unitary
spectral theorem. The continuous linear maps use the Euclidean operator norm, whose topology
is the native matrix topology.
-/

public section

noncomputable section

open NormedSpace
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- At a real diagonal matrix the derivative of the exponential is entrywise multiplication
by the divided differences of the real exponential. This is an explicit rewrite rule:
the general `TauCeti.expFDeriv_apply` simp rule expands the derivative into its series. -/
theorem expFDeriv_diagonal (d : n → ℝ) (Y : Matrix n n 𝕜) :
    TauCeti.expFDeriv 𝕜 (diagonal (fun k ↦ (d k : 𝕜))) Y =
      Matrix.of (fun i j ↦ ((dslope Real.exp (d i) (d j) : ℝ) : 𝕜) * Y i j) := by
  ext i j
  simp only [Matrix.of_apply]
  let : NormedAlgebra ℝ (Matrix n n 𝕜) :=
    { norm_smul_le r Z := by
        simpa only [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.norm_ofReal,
          Real.norm_eq_abs] using
          norm_smul_le (r : 𝕜) Z }
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  rw [TauCeti.expFDeriv_apply_eq_integral]
  let D : Matrix n n 𝕜 := diagonal (fun k ↦ (d k : 𝕜))
  have hi : IntervalIntegrable (fun t : ℝ ↦ exp ((1 - t) • D) * Y * exp (t • D))
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by fun_prop) _ _
  have heval := (entryLinearMap 𝕜 𝕜 i j).toContinuousLinearMap.intervalIntegral_comp_comm hi
  have hexp (x : ℝ) : exp (x : 𝕜) = (Real.exp x : 𝕜) := by
    simpa only [RCLike.algebraMap_eq_ofReal, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝔸 := 𝕜) x).symm
  have hint : (fun t : ℝ ↦ (exp ((1 - t) • D) * Y * exp (t • D)) i j) =
      fun t ↦ (Real.exp ((1 - t) * d i + t * d j) : 𝕜) * Y i j := by
    funext t
    simp only [D, ← diagonal_smul, exp_diagonal, diagonal_mul, mul_diagonal, Pi.coe_exp,
      Pi.smul_apply, RCLike.real_smul_eq_coe_mul]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, hexp, hexp,
      Real.exp_add, RCLike.ofReal_mul]
    ring
  calc
    _ = ∫ t in (0 : ℝ)..1, (exp ((1 - t) • D) * Y * exp (t • D)) i j := heval.symm
    _ = _ := by
      rw [hint, intervalIntegral.integral_mul_const, RCLike.intervalIntegral_ofReal,
        ← Real.dslope_exp_eq_integral]

/-- The derivative at a real diagonal matrix is bijective. Repeated eigenvalues cause no
singularity, since the corresponding divided difference is the positive exponential. -/
theorem bijective_expFDeriv_diagonal (d : n → ℝ) :
    Function.Bijective (TauCeti.expFDeriv 𝕜 (diagonal (fun k ↦ (d k : 𝕜)))) := by
  have hn (i j : n) : ((dslope Real.exp (d i) (d j) : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.dslope_exp_pos (d i) (d j))
  constructor
  · intro X Y h
    ext i j
    have h' := congrArg (fun Z : Matrix n n 𝕜 ↦ Z i j) h
    simpa only [expFDeriv_diagonal, Matrix.of_apply, mul_right_inj' (hn i j)] using h'
  · intro Y
    refine ⟨Matrix.of (fun i j ↦ Y i j / ((dslope Real.exp (d i) (d j) : ℝ) : 𝕜)), ?_⟩
    ext i j
    simp only [expFDeriv_diagonal, Matrix.of_apply]
    exact mul_div_cancel₀ _ (hn i j)

end Matrix

namespace Matrix.IsHermitian

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  {A : Matrix n n 𝕜}

/-- In a unitary eigenbasis, the derivative of the exponential is multiplication of each
entry by the positive divided difference of its two eigenvalues. -/
theorem expFDeriv_eigenbasis (hA : A.IsHermitian) (Y : Matrix n n 𝕜) :
    Unitary.conjStarAlgAut 𝕜 _ (star hA.eigenvectorUnitary) (TauCeti.expFDeriv 𝕜 A Y) =
      Matrix.of (fun i j ↦ ((dslope Real.exp (hA.eigenvalues i) (hA.eigenvalues j) : ℝ) : 𝕜) *
        Unitary.conjStarAlgAut 𝕜 _ (star hA.eigenvectorUnitary) Y i j) := by
  let e := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) (star hA.eigenvectorUnitary)
  let f : Matrix n n 𝕜 →A[𝕜] Matrix n n 𝕜 :=
    { e.toAlgEquiv.toAlgHom with
      cont := e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous }
  calc
    _ = TauCeti.expFDeriv 𝕜 (e A) (e Y) := f.map_expFDeriv A Y
    _ = _ := by
      rw [hA.conjStarAlgAut_star_eigenvectorUnitary]
      exact Matrix.expFDeriv_diagonal hA.eigenvalues _

/-- The derivative of the exponential at a Hermitian matrix is bijective on the full
matrix space, over either the real or complex scalars. -/
theorem bijective_expFDeriv (hA : A.IsHermitian) :
    Function.Bijective (TauCeti.expFDeriv 𝕜 A) := by
  let e := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) (star hA.eigenvectorUnitary)
  have heq : e ∘ TauCeti.expFDeriv 𝕜 A =
      TauCeti.expFDeriv 𝕜 (diagonal (fun i ↦ (hA.eigenvalues i : 𝕜))) ∘ e := by
    funext Y
    exact (hA.expFDeriv_eigenbasis Y).trans
      (Matrix.expFDeriv_diagonal hA.eigenvalues (e Y)).symm
  have hbij : Function.Bijective (e ∘ TauCeti.expFDeriv 𝕜 A) := by
    rw [heq]
    exact (Matrix.bijective_expFDeriv_diagonal hA.eigenvalues).comp e.bijective
  exact (e.bijective.of_comp_iff' _).mp hbij

/-- The derivative of the exponential at a Hermitian matrix is an invertible continuous
linear endomorphism. -/
theorem isUnit_expFDeriv (hA : A.IsHermitian) : IsUnit (TauCeti.expFDeriv 𝕜 A) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr hA.bijective_expFDeriv

end Matrix.IsHermitian
