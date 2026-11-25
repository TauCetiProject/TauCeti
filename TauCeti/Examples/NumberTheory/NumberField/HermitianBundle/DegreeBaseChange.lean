/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.DegreeBaseChange
public import TauCeti.NumberTheory.NumberField.Quadratic.Model

/-!
# Checks for the Arakelov degree under base change

ArakelovGeometryAndAbelianHeights §1.6 Check: for `K = ℚ`, `L = ℚ(i)` and `M = (ℤ, 2 |·|)`,
`deg(M) = -log 2` and `deg(M_{𝓞 L}) = -2 log 2`, through
`TauCeti.HermitianMetric.sectionDegree_baseChange_of_span_eq_top`.

`ℚ(i)` is the model `QuadraticAlgebra ℚ (-1) 0`.
-/

public section

open scoped NumberField TensorProduct
open NumberField TauCeti

local instance TauCeti.ArakelovBaseChangeChecks.instFactNotIsSquareNegOne :
    Fact (¬ IsSquare (-1 : ℤ)) :=
  ⟨not_isSquare_of_neg (by norm_num)⟩

namespace TauCeti.ArakelovBaseChangeChecks

/-- The Gaussian rationals `ℚ(i)`. -/
abbrev K := QuadraticAlgebra ℚ ((-1 : ℤ) : ℚ) 0

/-- The hermitian line `M = (ℤ, 2 |·|)` over `ℚ`. -/
noncomputable abbrev M : HermitianMetric ℚ (𝓞 ℚ) :=
  (HermitianMetric.trivial ℚ).rescale (-Real.log 2)

/-- `deg(ℤ, 2 |·|) = -log 2` and `deg((ℤ, 2 |·|)_{𝓞 ℚ(i)}) = -2 log 2`. -/
example :
    M.sectionDegree 1 = -Real.log 2 ∧
      (M.baseChange (L := K)).sectionDegree ((1 : 𝓞 K) ⊗ₜ (1 : 𝓞 ℚ)) = -2 * Real.log 2 := by
  have h1 : M.sectionDegree 1 = -Real.log 2 := by
    rw [HermitianMetric.sectionDegree_rescale _ _ one_ne_zero,
      HermitianMetric.sectionDegree_trivial_one, Module.finrank_self]
    simp
  refine ⟨h1, ?_⟩
  rw [HermitianMetric.sectionDegree_baseChange_of_span_eq_top _ Ideal.span_singleton_one, h1,
    QuadraticAlgebra.finrank_eq_two]
  ring

end TauCeti.ArakelovBaseChangeChecks
