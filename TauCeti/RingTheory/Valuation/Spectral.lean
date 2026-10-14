/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.RingTheory.Valuation.Continuous.Basic

import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The spectral valuation of an algebraic extension

Let `K` be a complete nontrivially normed field with an ultrametric norm and `L` an algebraic
field extension of `K`. Mathlib's spectral norm `spectralNorm K L` is then the unique
power-multiplicative `K`-algebra norm on `L` extending the norm of `K` (`spectralNorm_unique`),
and it is multiplicative and nonarchimedean. So it is a rank-one valuation on `L`, the
*spectral valuation* `TauCeti.spectralValuation K L`: Mathlib's `NormedField.valuation` for the
normed field structure `spectralNorm.normedField K L`.

That normed field structure is not installed as an instance, because `L` often carries a
topology of its own. The typical case is a residue field `A ⧸ 𝔪` of a topological `K`-algebra,
with the quotient topology. When `L` is finite over `K` and that topology makes it a Hausdorff
topological `K`-vector space, the spectral valuation is continuous for it
(`TauCeti.isContinuous_spectralValuation`). This is how a maximal ideal with finite residue field
gives a point of an adic spectrum.

## Main definitions

* `TauCeti.spectralValuation`: the spectral norm of an algebraic extension, as a valuation with
  values in `ℝ≥0`.

## Main results

* `TauCeti.coe_spectralValuation`: the spectral valuation is the spectral norm.
* `TauCeti.spectralValuation_algebraMap`: it extends the norm of `K`.
* `TauCeti.isContinuous_spectralValuation`: on a finite extension it is continuous for every
  Hausdorff topological `K`-vector space structure.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L]

section IsAlgebraic

variable [Algebra.IsAlgebraic K L]

/-- **The spectral valuation** of an algebraic extension `L` of a complete ultrametric field `K`:
the spectral norm `spectralNorm K L`, which is multiplicative and nonarchimedean, as a valuation
with values in `ℝ≥0`. -/
def spectralValuation : Valuation L ℝ≥0 :=
  letI := spectralNorm.normedField K L
  haveI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  NormedField.valuation

variable {K L}

/-- The spectral valuation is the spectral norm. -/
@[simp]
theorem coe_spectralValuation (x : L) : (spectralValuation K L x : ℝ) = spectralNorm K L x :=
  (rfl)

/-- The spectral valuation extends the norm of `K`. -/
@[simp]
theorem spectralValuation_algebraMap (c : K) :
    spectralValuation K L (algebraMap K L c) = ‖c‖₊ :=
  NNReal.eq <| by rw [coe_spectralValuation, spectralNorm_extends, coe_nnnorm]

end IsAlgebraic

/-- **The spectral valuation is continuous** on a finite extension `L` of `K`, for every topology
making `L` a Hausdorff topological `K`-vector space. The spectral norm is a `K`-seminorm on `L`,
and every seminorm on a finite-dimensional Hausdorff topological vector space is continuous. -/
theorem isContinuous_spectralValuation [FiniteDimensional K L] [TopologicalSpace L]
    [IsTopologicalAddGroup L] [ContinuousSMul K L] [T2Space L] :
    (spectralValuation K L).IsContinuous := by
  have hcont : Continuous (spectralNorm K L) :=
    (spectralAlgNorm K L).toSeminorm.continuous_of_finiteDimensional
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  simpa [← NNReal.coe_lt_coe] using isOpen_lt hcont continuous_const

end TauCeti
