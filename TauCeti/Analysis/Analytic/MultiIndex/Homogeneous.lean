/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.MultiIndex.Coeff

/-!
# Homogeneous analytic functions are polynomials

A function `f` of finitely many variables over a field of characteristic zero which is analytic
at the origin and homogeneous of degree `d`, in the sense that `f (t • v) = t ^ d * f v` for all
scalars `t` and vectors `v`, is a homogeneous polynomial of degree `d`
(`AnalyticAt.exists_isHomogeneous_eval_eq`). No growth condition and no analyticity away from the
origin is needed: the homogeneity identity is global.

The proof reads the degree-`d` term of the power series of `f` at `0` as a polynomial through its
multi-index coefficients (`FormalMultilinearSeries.exists_isHomogeneous_eval_eq`). Along the line
`t ↦ t • v` the function is `t ↦ t ^ d * f v`, whose `d`-th derivative at `0` is `d! * f v`, while
the `d`-th derivative of an analytic function at its centre is `d!` times the degree-`d` term of
its power series. So `f v` is the value at `v` of that degree-`d` term.

This is the step that turns the homogeneous functions on `ℂⁿ⁺¹ \ {0}` attached to holomorphic
sections of the line bundles `𝒪(d)` on projective space, once extended across the origin, into
homogeneous polynomials.

## Main declarations

* `FormalMultilinearSeries.exists_isHomogeneous_eval_eq`: the degree-`k` term of a scalar formal
  multilinear series on `ι → 𝕜` is a homogeneous polynomial function of degree `k`.
* `AnalyticAt.exists_isHomogeneous_eval_eq`: a function analytic at the origin and homogeneous of
  degree `d` is a homogeneous polynomial of degree `d`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1, for homogeneous
  holomorphic functions and the sections of the hyperplane bundle.
-/

public section

open Finset MvPolynomial
open scoped Nat

namespace FormalMultilinearSeries

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Finite ι]

/-- The degree-`k` term `z ↦ p k (fun _ ↦ z)` of a scalar formal multilinear series on `ι → 𝕜` is
the evaluation of a homogeneous polynomial of degree `k`: the one whose coefficient of
`∏ i, X i ^ α i` is the multi-index coefficient `p.mvCoeff α`. -/
theorem exists_isHomogeneous_eval_eq (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) 𝕜) (k : ℕ) :
    ∃ P : MvPolynomial ι 𝕜, P.IsHomogeneous k ∧ ∀ z, eval z P = p k fun _ ↦ z := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨∑ α ∈ univ.piAntidiag k, C (p.mvCoeff α) * ∏ i, X i ^ α i,
    IsHomogeneous.sum _ _ _ fun α hα ↦ ?_, fun z ↦ ?_⟩
  · rw [← (mem_piAntidiag.1 hα).1]
    exact (IsHomogeneous.prod _ _ _ fun i _ ↦ isHomogeneous_X_pow i (α i)).C_mul _
  · simp [apply_eq_sum_mvCoeff, mul_comm]

end FormalMultilinearSeries

/-- **Homogeneous analytic functions are homogeneous polynomials.** Over a complete nontrivially
normed field of characteristic zero, a function of finitely many variables which is analytic at
the origin and satisfies `f (t • v) = t ^ d * f v` for every scalar `t` and every vector `v` is the
evaluation of a homogeneous polynomial of degree `d`. -/
theorem AnalyticAt.exists_isHomogeneous_eval_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CharZero 𝕜] [CompleteSpace 𝕜] {ι : Type*} [Fintype ι] {f : (ι → 𝕜) → 𝕜} {d : ℕ}
    (hf : AnalyticAt 𝕜 f 0) (hhom : ∀ (t : 𝕜) v, f (t • v) = t ^ d * f v) :
    ∃ P : MvPolynomial ι 𝕜, P.IsHomogeneous d ∧ ∀ v, eval v P = f v := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨P, hP, hPeval⟩ := p.exists_isHomogeneous_eval_eq d
  refine ⟨P, hP, fun v ↦ ?_⟩
  -- Restrict `f` to the line through `v`, where it is `t ↦ t ^ d * f v`.
  let L : 𝕜 →L[𝕜] ι → 𝕜 := ContinuousLinearMap.toSpanSingleton 𝕜 v
  have hL : f ∘ L = fun t ↦ t ^ d * f v := funext fun t ↦ by
    simp [L, hhom]
  have hpL : HasFPowerSeriesOnBall (f ∘ L) (p.compContinuousLinearMap L) 0 (r / ‖L‖ₑ) :=
    HasFPowerSeriesOnBall.compContinuousLinearMap (x := 0) (by simpa using hp)
  -- Compare the two expressions for the `d`-th derivative of the restriction at `0`.
  have hpow : iteratedDeriv d (fun t : 𝕜 ↦ t ^ d * f v) 0 = d ! * f v := by
    simp [iteratedDeriv_mul_const_field, Nat.descFactorial_self]
  have hderiv : (d ! : 𝕜) * p d (fun _ ↦ v) = d ! * f v := by
    have h := hpL.factorial_smul 1 d
    rw [hL, ← iteratedDeriv_eq_iteratedFDeriv, hpow] at h
    simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def, L,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, nsmul_eq_mul] using h
  rw [hPeval]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 d.factorial_ne_zero) hderiv
