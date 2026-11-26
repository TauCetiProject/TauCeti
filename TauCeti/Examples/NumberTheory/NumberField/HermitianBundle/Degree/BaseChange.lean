/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.BaseChange
public import TauCeti.NumberTheory.NumberField.Quadratic.Model

import Mathlib.RingTheory.PicardGroup

/-!
# Checks for the Arakelov degree under base change

For `K = ℚ`, `L = ℚ(i)` and `M = (ℤ, 2 |·|)`, `deg(M) = -log 2` and `deg(M_{𝓞 L}) = -2 log 2`,
through `TauCeti.HermitianMetric.sectionDegree_baseChange`, computed with the generating section
`1` and with the non-generating section `2`.

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
abbrev L := QuadraticAlgebra ℚ ((-1 : ℤ) : ℚ) 0

/-- The hermitian line `M = (ℤ, 2 |·|)` over `ℚ`. -/
noncomputable abbrev M : HermitianMetric ℚ (𝓞 ℚ) :=
  (HermitianMetric.trivial ℚ).rescale (-Real.log 2)

/-- `deg(ℤ, 2 |·|) = -log 2`, computed with the generator `1`. -/
theorem sectionDegree_M_one : M.sectionDegree 1 = -Real.log 2 := by
  rw [HermitianMetric.sectionDegree_rescale _ _ one_ne_zero,
    HermitianMetric.sectionDegree_trivial_one, Module.finrank_self]
  simp

/-- `deg(ℤ, 2 |·|) = -log 2` and `deg((ℤ, 2 |·|)_{𝓞 ℚ(i)}) = -2 log 2`. -/
example :
    M.sectionDegree 1 = -Real.log 2 ∧
      (M.baseChange (L := L)).sectionDegree ((1 : 𝓞 L) ⊗ₜ (1 : 𝓞 ℚ)) = -2 * Real.log 2 := by
  refine ⟨sectionDegree_M_one, ?_⟩
  rw [HermitianMetric.sectionDegree_baseChange, sectionDegree_M_one,
    QuadraticAlgebra.finrank_eq_two]
  ring

/-- The same degrees computed with the non-generating section `2`, whose cokernel `ℤ / 2` is
nontrivial: `deg((ℤ, 2 |·|)_{𝓞 ℚ(i)}) = -2 log 2` with the section `1 ⊗ 2`. -/
example :
    M.sectionDegree 2 = -Real.log 2 ∧
      (M.baseChange (L := L)).sectionDegree ((1 : 𝓞 L) ⊗ₜ (2 : 𝓞 ℚ)) = -2 * Real.log 2 := by
  have h2 : M.sectionDegree 2 = -Real.log 2 := by
    have := M.sectionDegree_smul (Module.Invertible.finrank_eq_one ℚ (ℚ ⊗[𝓞 ℚ] 𝓞 ℚ))
      (a := 2) two_ne_zero 1
    rw [smul_eq_mul, mul_one] at this
    rw [this, sectionDegree_M_one]
  refine ⟨h2, ?_⟩
  rw [HermitianMetric.sectionDegree_baseChange, h2, QuadraticAlgebra.finrank_eq_two]
  ring

end TauCeti.ArakelovBaseChangeChecks
