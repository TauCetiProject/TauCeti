/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.Borel

/-!
# The matrix Cartan criterion needs closure under transpose

The matrix Cartan criterion `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose` applies to
real Lie subalgebras of `𝔤𝔩_n(𝕜)` closed under conjugate transpose. The upper triangular
trace-zero real `2 × 2` matrices, `TauCeti.upperTriangular ℝ (Fin 2) ⊓ sl (Fin 2) ℝ`, are not:
the raising matrix `E₀₁` lies in them while its transpose `E₁₀` does not, and neither does
`-E₁₀`, so `X ↦ -Xᵀ` does not even map this subalgebra to itself.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- The raising matrix `E₀₁` is upper triangular of trace zero. -/
theorem single_zero_one_mem_upperTriangular_inf_sl :
    single (0 : Fin 2) 1 (1 : ℝ) ∈ upperTriangular ℝ (Fin 2) ⊓ SpecialLinear.sl (Fin 2) ℝ := by
  refine ⟨single_mem_upperTriangular (by decide) 1, ?_⟩
  simp [SpecialLinear.sl, trace_single_eq_of_ne]

/-- The upper triangular trace-zero real `2 × 2` matrices are not closed under transpose. -/
theorem not_forall_transpose_mem_upperTriangular_inf_sl :
    ¬ ∀ X ∈ upperTriangular ℝ (Fin 2) ⊓ SpecialLinear.sl (Fin 2) ℝ,
      Xᵀ ∈ upperTriangular ℝ (Fin 2) ⊓ SpecialLinear.sl (Fin 2) ℝ := by
  intro h
  have := (h _ single_zero_one_mem_upperTriangular_inf_sl).1
  rw [transpose_single] at this
  exact absurd ((single_mem_upperTriangular_iff one_ne_zero).mp this) (by decide)

/-- `X ↦ -Xᵀ` does not map the upper triangular trace-zero real `2 × 2` matrices to themselves. -/
theorem not_forall_neg_transpose_mem_upperTriangular_inf_sl :
    ¬ ∀ X ∈ upperTriangular ℝ (Fin 2) ⊓ SpecialLinear.sl (Fin 2) ℝ,
      -Xᵀ ∈ upperTriangular ℝ (Fin 2) ⊓ SpecialLinear.sl (Fin 2) ℝ :=
  fun h ↦ not_forall_transpose_mem_upperTriangular_inf_sl fun X hX ↦ by
    simpa using neg_mem (h X hX)

end TauCeti
