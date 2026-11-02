/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Trace.Basic

import Mathlib.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.Normed.Module.Dual.Bounded

/-!
# Spectral bounds for the trace and linear functionals

The trace of a finite extension of an ultrametric normed field is bounded by the spectral
norm. If the extension is separable, every linear functional is bounded by that norm. The
field need not be complete: the spectral norm used here is Mathlib's power-multiplicative
algebra norm, which need not be multiplicative over an incomplete base.

These are Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §3.2.3, Proposition 2 and
§3.5.1, Proposition 3. The proofs adapt William Coram's `norm_trace_le_spectralNorm` and
`exists_bound_of_isSeparable` in `PhD/TauCeti/Code/RigidAnalyticGeometry/WeaklyStable.lean`
at commit `eefb3d91f34b27d0bc7822140fa85fecae029884` of
<https://github.com/WilliamCoram/PhD>.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The trace of a finite extension is bounded by its spectral norm, without completeness of
the base field or separability of the extension. -/
theorem norm_trace_le_spectralNorm (x : L) :
    ‖Algebra.trace K L x‖ ≤ spectralNorm K L x := by
  have hr := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := K) x)
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (IsUltrametricDist.norm_natCast_le_one K _)).trans ?_
  rw [Polynomial.nextCoeff_of_natDegree_pos hr]
  have h := le_ciSup (spectralValueTerms_bddAbove (minpoly K x))
    ((minpoly K x).natDegree - 1)
  rw [spectralValueTerms_of_lt_natDegree _ (Nat.sub_lt hr one_pos)] at h
  have hdegree : ((minpoly K x).natDegree : ℝ) -
      (((minpoly K x).natDegree - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub hr, Nat.cast_one, sub_sub_cancel]
  rw [hdegree, div_one, Real.rpow_one] at h
  simpa only [spectralNorm, spectralValue] using h

end TauCeti

namespace Module.Dual

/-- Every linear functional on a finite separable extension of an ultrametric normed field
is bounded by the spectral norm. Completeness and nontriviality of the valuation are not
required. -/
theorem exists_bound_spectralNorm_of_isSeparable {K : Type*} [NormedField K]
    [IsUltrametricDist K] {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (φ : Module.Dual K L) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := by
  refine φ.exists_bound_of_forall_exists_ne_zero (spectralNorm K L) fun x hx ↦ ?_
  obtain ⟨z, hz⟩ : ∃ z, Algebra.trace K L (x * z) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx ((traceForm_nondegenerate K L).1 x fun z ↦ by
      simpa only [Algebra.traceForm_apply] using h z)
  refine ⟨(Algebra.trace K L).comp (LinearMap.mulRight K z),
    ⟨spectralNorm K L z, fun y ↦ ?_⟩, by simpa using hz⟩
  exact (TauCeti.norm_trace_le_spectralNorm (y * z)).trans
    ((spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic y)
      (Algebra.IsAlgebraic.isAlgebraic z)).trans_eq (mul_comm _ _))

end Module.Dual
