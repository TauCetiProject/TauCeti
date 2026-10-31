/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompletelyContinuous
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Spectrum

/-!
# The Fredholm alternative and eigenvalues of row-compact operators

Let `u` be row compact on `C₀(I, K)` over a complete nontrivially normed ultrametric field.
Every operator `1 - a • u` is Fredholm in Mathlib's sense and has index zero. Thus its range is
closed, its kernel and cokernel are finite dimensional, and its kernel has a continuous
complement. The field need not be locally compact, discretely valued or spherically complete.

The general Fredholm alternative for completely continuous operators supplies these results.
Combining it with the Fredholm-series description of the spectrum shows that every zero `a` of
`H_u` gives the eigenvalue `a⁻¹`. The condition `a ≠ 0` is automatic because `H_u(0) = 1`.
This identifies actual eigenvalues, without asserting an algebraic multiplicity or a dimension
formula for a generalised eigenspace.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped ZeroAtInfty

namespace ContinuousLinearMap

variable {K I : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- Every scalar multiple of a row-compact operator is a Fredholm perturbation of the identity,
including at zeros of its Fredholm series. -/
theorem IsRowCompact.isFredholm_one_sub_smul (hu : u.IsRowCompact) (a : K) :
    IsFredholm (1 - a • u) :=
  (hu.isCompletelyContinuous.smul a).isFredholm_one_sub

/-- The Fredholm operator `1 - a • u` has index zero for every scalar `a`. -/
@[simp]
theorem IsRowCompact.index_one_sub_smul_eq_zero (hu : u.IsRowCompact) (a : K) :
    (1 - a • u).index = 0 :=
  (hu.isCompletelyContinuous.smul a).index_one_sub_eq_zero

/-- The zeros of the Fredholm series of a row-compact operator are exactly the inverses of its
nonzero eigenvalues. This conclusion concerns eigenvalues in the given coefficient field. -/
theorem IsRowCompact.evalAt_charPowerSeries_eq_zero_iff_hasEigenvalue (hu : u.IsRowCompact)
    {a : K} :
    u.matrixCoeff.charPowerSeries.evalAt a = 0 ↔
      a ≠ 0 ∧ Module.End.HasEigenvalue (u : Module.End K C₀(I, K)) a⁻¹ := by
  rw [hu.evalAt_charPowerSeries_eq_zero_iff]
  exact and_congr_right fun ha ↦
    (hu.isCompletelyContinuous.hasEigenvalue_iff_mem_spectrum (inv_ne_zero ha)).symm

end ContinuousLinearMap
