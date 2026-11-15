/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous operators of finite rank are compact

A continuous linear map `T : E →L[𝕜] F` with finite-dimensional range is compact whenever
`F` is a topological vector space over a locally compact nontrivially normed field. It factors
through its range, which is locally compact. No norm or compatibility between the topology and
module structure on `E` is needed.

In particular, operator-norm limits of finite-rank maps into a Banach space are compact, by
`isCompactOperator_of_tendsto`.

Finiteness of the rank is spelled with Mathlib's `LinearMap.HasFiniteRange`.

## Main declarations

* `LinearMap.HasFiniteRange.isCompactOperator`: over a locally compact nontrivially normed field, a
  continuous linear map of finite rank is a compact operator.

## Mathlib sources

Scalar completeness and finite-dimensional local compactness come from
`IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace` and
`LocallyCompactSpace.of_finiteDimensional_of_complete`, respectively. Compactness of maps into
the range is provided by `isCompactOperator_of_locallyCompactSpace_dom`.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]

/-- Over a locally compact nontrivially normed field, a continuous linear map into a topological
vector space with finite-dimensional range is a compact operator. -/
theorem LinearMap.HasFiniteRange.isCompactOperator {T : E →L[𝕜] F}
    (hT : (T : E →ₗ[𝕜] F).HasFiniteRange) : IsCompactOperator T := by
  have : CompleteSpace 𝕜 :=
    IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 T.range := .of_fg hT
  have : LocallyCompactSpace T.range :=
    .of_finiteDimensional_of_complete 𝕜 _
  simpa only [← ContinuousLinearMap.coe_comp, ContinuousLinearMap.subtypeL_comp_codRestrict] using
    (isCompactOperator_of_locallyCompactSpace_dom T.rangeRestrict).clm_comp T.range.subtypeL

end
