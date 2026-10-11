/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Bounded operators of finite rank are compact

A bounded linear map `T : E →L[𝕜] F` whose range is finite dimensional factors through that
range, which is a finite-dimensional normed space and hence locally compact when the scalar field
is. A continuous linear map into a locally compact space is compact, so `T` is a compact operator.
Since the compact operators into a Banach space are closed in operator norm
(`isCompactOperator_of_tendsto`), it follows that operator-norm limits of finite-rank operators
are compact.

Finiteness of the rank is spelled with Mathlib's `LinearMap.HasFiniteRange`.

## Main declarations

* `LinearMap.HasFiniteRange.isCompactOperator`: over a locally compact nontrivially normed field, a
  bounded linear map of finite rank is a compact operator.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a locally compact nontrivially normed field, a bounded linear map with finite-dimensional
range is a compact operator. -/
theorem LinearMap.HasFiniteRange.isCompactOperator {T : E →L[𝕜] F}
    (hT : (T : E →ₗ[𝕜] F).HasFiniteRange) : IsCompactOperator T := by
  have : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) := Module.Finite.iff_fg.mpr hT
  have : ProperSpace (LinearMap.range (T : E →ₗ[𝕜] F)) := FiniteDimensional.proper 𝕜 _
  have h := (isCompactOperator_of_locallyCompactSpace_dom
    (T.codRestrict _ (LinearMap.mem_range_self (T : E →ₗ[𝕜] F)))).clm_comp
    (LinearMap.range (T : E →ₗ[𝕜] F)).subtypeL
  rwa [← ContinuousLinearMap.coe_comp, ContinuousLinearMap.subtypeL_comp_codRestrict] at h

end
