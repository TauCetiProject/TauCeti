/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.ZeroTemperature
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Zero-temperature limit of the Gibbs state of a Hermitian matrix

For a Hermitian matrix `K`, let `P₀ = cfc ({λ₀}.indicator 1) K` be its spectral projection at
its least eigenvalue `λ₀ = sInf (spectrum ℝ K)`. Its Euclidean operator is the orthogonal
projection onto the lowest eigenspace, `Matrix.IsHermitian.toEuclideanLin_cfc_indicator`.
As the inverse temperature `β` tends to `+∞`, the Gibbs functionals of `K` converge pointwise:
`Tr (exp (-βK) x) / Tr (exp (-βK)) → Tr (P₀ x) / Tr P₀`.

This spectral and Gibbs-state reading assumes `Nonempty m`, so that `K` has a least eigenvalue.
The theorem holds without that assumption: for empty `m` every trace is zero, so both sides are
the constant quotient `0 / 0 = 0`.

For nonempty `m`, this is the trace instance of the general limit
`TauCeti.tendsto_apply_exp_neg_smul_mul_div` for self-adjoint elements with finite spectrum;
the only matrix-specific input is that `Tr P₀ = Tr (P₀ᴴ P₀)` is nonzero.

## Main results

* `Matrix.IsHermitian.tendsto_trace_exp_neg_smul_mul_div`: the Gibbs functionals
  `x ↦ Tr (exp (-(β • K)) x) / Tr (exp (-(β • K)))` of a Hermitian matrix converge pointwise
  to `x ↦ Tr (P₀ x) / Tr P₀`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.3.1, for the Gibbs states of a finite quantum system and their zero-temperature
limits.
-/

public section

open Filter Topology NormedSpace

namespace Matrix

open TauCeti
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {m : Type*} [Fintype m] [DecidableEq m] {K : Matrix m m ℂ}

/-- **Zero-temperature limit of the Gibbs state.** For a Hermitian matrix `K`, let `P₀` be the
spectral projection of `K` at its least eigenvalue, the orthogonal projection onto the lowest
eigenspace. As `β → +∞`, the Gibbs functionals
`x ↦ Tr (exp (-(β • K)) x) / Tr (exp (-(β • K)))` converge pointwise to
`x ↦ Tr (P₀ x) / Tr P₀`.

This reading assumes `Nonempty m`; for empty `m` there is no eigenvalue or normalized state, and
the statement holds trivially since every trace is zero and both sides are `0 / 0 = 0`. -/
theorem IsHermitian.tendsto_trace_exp_neg_smul_mul_div (hK : K.IsHermitian) (x : Matrix m m ℂ) :
    Tendsto (fun β : ℝ ↦ (exp (-(β • K)) * x).trace / (exp (-(β • K))).trace) atTop
      (𝓝 ((cfc (Set.indicator {sInf (spectrum ℝ K)} 1) K * x).trace /
        (cfc (Set.indicator {sInf (spectrum ℝ K)} 1) K).trace)) := by
  cases isEmpty_or_nonempty m
  · simp [Matrix.trace]
  set P := cfc (Set.indicator {sInf (spectrum ℝ K)} 1) K
  -- `P` is a nonzero star projection, so its trace `Tr (Pᴴ P)` is nonzero
  have hP : P ≠ 0 := by
    intro h
    have hfin : (spectrum ℝ K).Finite := finite_real_spectrum
    have hspec := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) K hK.isSelfAdjoint
    have := eqOn_of_cfc_eq_cfc (h.trans (cfc_zero ℝ K).symm) (hfin.continuousOn _)
      (hfin.continuousOn _) hK.isSelfAdjoint (hspec.csInf_mem hfin)
    simp at this
  have htr : P.trace ≠ 0 := by
    have hPP : IsStarProjection P := isStarProjection_cfc_indicator K _
    have h : P.trace = (Pᴴ * P).trace := by
      rw [← star_eq_conjTranspose, hPP.isSelfAdjoint.star_eq, hPP.isIdempotentElem.eq]
    rwa [h, Ne, trace_conjTranspose_mul_self_eq_zero_iff]
  exact tendsto_apply_exp_neg_smul_mul_div hK.isSelfAdjoint finite_real_spectrum
    (LinearMap.toContinuousLinearMap ((traceLinearMap m ℂ ℂ).restrictScalars ℝ)) htr x

end Matrix
