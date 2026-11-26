/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Large shifts of bounded operators

A bounded operator `A` on a normed space whose endomorphism algebra has summable geometric series,
for instance a Banach space, has its spectrum in the closed ball of radius `‖A‖`. So every shift
`c • 1 - A` by a scalar with `‖A‖ < ‖c‖` is invertible
(`ContinuousLinearMap.isInvertible_smul_one_sub_of_norm_lt`), a restatement of Mathlib's
`mem_resolventSet_of_norm_lt` for operators.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [HasSummableGeomSeries (E →L[𝕜] E)]

/-- A bounded operator shifted by a scalar of larger norm is invertible. -/
theorem isInvertible_smul_one_sub_of_norm_lt {A : E →L[𝕜] E} {c : 𝕜} (h : ‖A‖ < ‖c‖) :
    (c • 1 - A).IsInvertible :=
  isInvertible_iff_isUnit.2 <| by
    simpa [Algebra.algebraMap_eq_smul_one] using
      spectrum.mem_resolventSet_iff.1 (mem_resolventSet_of_norm_lt h)

end ContinuousLinearMap
