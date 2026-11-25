/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.NumberField.HermitianBundle.DegreeDual

/-!
# Checks for the Arakelov degree of the dual of a hermitian line

ArakelovGeometryAndAbelianHeights §1.5 Check: over `ℚ`, the trivial line whose generator has norm
`e^(-a)` has degree `a` and its dual has degree `-a`.
-/

open scoped NumberField TensorProduct
open NumberField TauCeti

namespace TauCeti.ArakelovDualChecks

/-- Over `ℚ`, the trivial line with generator norm `e^(-a)` has degree `a`, its dual degree `-a`,
computed with the generator `1` and the identity functional. -/
example (a : ℝ) :
    ((HermitianMetric.trivial ℚ).rescale a).sectionDegree 1 = a ∧
      ((HermitianMetric.trivial ℚ).rescale a).dual.sectionDegree LinearMap.id = -a := by
  have h1 : ((HermitianMetric.trivial ℚ).rescale a).sectionDegree 1 = a := by
    rw [HermitianMetric.sectionDegree_rescale _ _ one_ne_zero,
      HermitianMetric.sectionDegree_trivial_one, Module.finrank_self]
    simp
  refine ⟨h1, ?_⟩
  rw [HermitianMetric.sectionDegree_dual_of_span_eq_top _ Ideal.span_singleton_one
    (LinearMap.id_apply 1), h1]

end TauCeti.ArakelovDualChecks
