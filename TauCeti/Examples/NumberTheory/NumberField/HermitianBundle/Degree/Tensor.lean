/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Tensor

/-!
# Checks for the degree of a tensor product of hermitian lines

Over `ℚ`, the trivial lines with generator norms `e^(−a)` and `e^(−b)` have degrees `a` and `b`,
and their tensor product has degree `a + b` (`TauCeti.HermitianMetric.sectionDegree_tmul`): the
line `Ō_ℚ` rescaled by `e^(−a)` has degree `a` computed with `1`, and the tensor product of the
two rescaled lines has degree `a + b` computed with `1 ⊗ 1`.
-/

public section

open scoped TensorProduct
open NumberField TauCeti TauCeti.HermitianMetric

namespace TauCeti.ArakelovDegreeTensorChecks

/-- The trivial line over `ℚ` with generator norm `e^(−a)` has degree `a`. -/
example (a : ℝ) : ((trivial ℚ).rescale a).sectionDegree (1 : 𝓞 ℚ) = a := by
  rw [sectionDegree_rescale _ _ one_ne_zero, sectionDegree_trivial_one, Module.finrank_self]
  simp

/-- Over `ℚ`, the tensor product of trivial lines with generator norms `e^(−a)` and `e^(−b)` has
degree `a + b`. -/
example (a b : ℝ) :
    (((trivial ℚ).rescale a).tmul ((trivial ℚ).rescale b)).sectionDegree
      ((1 : 𝓞 ℚ) ⊗ₜ[𝓞 ℚ] (1 : 𝓞 ℚ)) = a + b := by
  -- `1` spans `𝓞 ℚ`, so the quotient by its span is trivial, hence finite.
  have : Finite (𝓞 ℚ ⧸ Submodule.span (𝓞 ℚ) {(1 : 𝓞 ℚ)}) := by
    rw [(Submodule.span_singleton_eq_top_iff _ _).2 fun r ↦ ⟨r, mul_one r⟩]
    infer_instance
  rw [sectionDegree_tmul _ _ one_ne_zero one_ne_zero, sectionDegree_rescale _ _ one_ne_zero,
    sectionDegree_rescale _ _ one_ne_zero, sectionDegree_trivial_one, Module.finrank_self]
  simp

end TauCeti.ArakelovDegreeTensorChecks
