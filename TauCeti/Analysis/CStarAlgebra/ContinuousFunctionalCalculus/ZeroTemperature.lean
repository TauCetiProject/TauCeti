/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Zero-temperature limits of Boltzmann weights

Let `a` be a self-adjoint element with finite spectrum of an algebra with a real continuous
functional calculus, for instance a Hermitian matrix, and let `λ₀ = sInf (spectrum ℝ a)` be its
least spectral value. The spectral projection of `a` at `λ₀` is `P₀ = cfc ({λ₀}.indicator 1) a`,
a star projection by `TauCeti.isStarProjection_cfc_indicator`; for a Hermitian matrix its
Euclidean operator is the orthogonal projection onto the lowest eigenspace,
`Matrix.IsHermitian.toEuclideanLin_cfc_indicator`.

As the inverse temperature `β` tends to `+∞`, the rescaled Boltzmann weights converge to `P₀`:
`exp (β λ₀) exp (-βa) → P₀`. Indeed `exp (β λ₀) exp (-βa)` is the functional calculus of
`t ↦ exp (-β (t - λ₀))`, which tends to `1` at `t = λ₀` and to `0` at every larger point of the
spectrum, and on a finite spectrum pointwise convergence passes to the functional calculus.

Consequently, for a continuous real-linear functional `φ` with `φ P₀ ≠ 0`, the normalised
functionals `x ↦ φ (exp (-βa) x) / φ (exp (-βa))` converge pointwise to
`x ↦ φ (P₀ x) / φ P₀`. For the trace of matrices this is the zero-temperature limit of the Gibbs
state of a matrix Hamiltonian `K`:
`Tr (exp (-βK) x) / Tr (exp (-βK)) → Tr (P₀ x) / Tr P₀`.

## Main results

* `TauCeti.tendsto_cfc_exp_neg_mul_sub_sInf`: `cfc (fun t ↦ exp (-β (t - λ₀))) a → P₀`;
* `TauCeti.tendsto_exp_mul_sInf_smul_exp_neg_smul`: `exp (β λ₀) • exp (-(β • a)) → P₀` in a
  normed algebra;
* `TauCeti.tendsto_apply_exp_neg_smul_mul_div`: `φ (exp (-(β • a)) x) / φ (exp (-(β • a)))`
  tends to `φ (P₀ x) / φ P₀`;
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

namespace TauCeti

section CFC

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A}

/-- On a finite spectrum, the functional calculi of the shifted Boltzmann weights
`t ↦ exp (-β (t - λ₀))`, with `λ₀` the least spectral value, converge as `β → +∞` to the
spectral projection at `λ₀`. -/
theorem tendsto_cfc_exp_neg_mul_sub_sInf (hfin : (spectrum ℝ a).Finite) :
    Tendsto (fun β : ℝ ↦ cfc (fun t ↦ Real.exp (-(β * (t - sInf (spectrum ℝ a))))) a) atTop
      (𝓝 (cfc (Set.indicator {sInf (spectrum ℝ a)} 1) a)) := by
  refine tendsto_cfc_fun_of_finite_spectrum hfin fun t ht ↦ ?_
  rcases (csInf_le hfin.bddBelow ht).eq_or_lt with h | h
  · simp [← h]
  · rw [Set.indicator_of_notMem (by simpa using h.ne')]
    refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
    exact tendsto_id.atTop_mul_const (sub_pos.mpr h)

end CFC

section Normed

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [StarModule ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A}

/-- The exponential `exp (-(β • a))` of a self-adjoint element, rescaled by `exp (β λ₀)` with
`λ₀` the least spectral value, converges as `β → +∞` to the spectral projection at `λ₀` when the
spectrum is finite. -/
theorem tendsto_exp_mul_sInf_smul_exp_neg_smul (ha : IsSelfAdjoint a)
    (hfin : (spectrum ℝ a).Finite) :
    Tendsto (fun β : ℝ ↦ Real.exp (β * sInf (spectrum ℝ a)) • exp (-(β • a))) atTop
      (𝓝 (cfc (Set.indicator {sInf (spectrum ℝ a)} 1) a)) := by
  refine (tendsto_cfc_exp_neg_mul_sub_sInf hfin).congr fun β ↦ ?_
  have hβa : IsSelfAdjoint (-(β • a)) := ((IsSelfAdjoint.all β).smul ha).neg
  rw [← CFC.real_exp_eq_normedSpace_exp hβa, ← cfc_comp_neg .., ← cfc_comp_smul ..,
    ← cfc_const_mul ..]
  refine cfc_congr fun t _ ↦ ?_
  rw [← Real.exp_add, smul_eq_mul]
  congr 1
  ring

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]

/-- **Zero-temperature limit.** Let `a` be self-adjoint with finite spectrum and spectral
projection `P₀` at its least spectral value. For a continuous real-linear functional `φ` with
`φ P₀ ≠ 0`, the normalised functionals `x ↦ φ (exp (-(β • a)) x) / φ (exp (-(β • a)))`
converge as `β → +∞` to `x ↦ φ (P₀ x) / φ P₀`. -/
theorem tendsto_apply_exp_neg_smul_mul_div (ha : IsSelfAdjoint a) (hfin : (spectrum ℝ a).Finite)
    (φ : A →L[ℝ] 𝕜) (hφ : φ (cfc (Set.indicator {sInf (spectrum ℝ a)} 1) a) ≠ 0) (x : A) :
    Tendsto (fun β : ℝ ↦ φ (exp (-(β • a)) * x) / φ (exp (-(β • a)))) atTop
      (𝓝 (φ (cfc (Set.indicator {sInf (spectrum ℝ a)} 1) a * x) /
        φ (cfc (Set.indicator {sInf (spectrum ℝ a)} 1) a))) := by
  have h := tendsto_exp_mul_sInf_smul_exp_neg_smul ha hfin
  refine ((φ.continuous.tendsto _ |>.comp (h.mul_const x)).div
    (φ.continuous.tendsto _ |>.comp h) hφ).congr fun β ↦ ?_
  -- the positive scalar `exp (β λ₀)` cancels between numerator and denominator
  have hc : algebraMap ℝ 𝕜 (Real.exp (β * sInf (spectrum ℝ a))) ≠ 0 := by
    simp [(Real.exp_pos _).ne']
  simp only [Pi.div_apply, Function.comp_apply, smul_mul_assoc, map_smul]
  rw [Algebra.smul_def (A := 𝕜), Algebra.smul_def (A := 𝕜), mul_div_mul_left _ _ hc]

end Normed

end TauCeti

namespace Matrix

open TauCeti
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {m : Type*} [Fintype m] [DecidableEq m] {K : Matrix m m ℂ}

/-- **Zero-temperature limit of the Gibbs state.** For a Hermitian matrix `K`, let `P₀` be the
spectral projection of `K` at its least eigenvalue, the orthogonal projection onto the lowest
eigenspace. As `β → +∞`, the Gibbs functionals
`x ↦ Tr (exp (-(β • K)) x) / Tr (exp (-(β • K)))` converge pointwise to
`x ↦ Tr (P₀ x) / Tr P₀`. -/
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
