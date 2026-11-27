/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Riesz
import TauCeti.NumberTheory.LFunctions.Continued.Dirichlet
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth

/-!
# Bounds for the first Riesz zero series of primitive Dirichlet characters

A zero-free half-plane for the Dirichlet L-function bounds the first Riesz sum over the zeros
of its entire completion. The bound is uniform in the threshold: its constant is the sum of the
norms of the Riesz coefficients. At conductor one, the zeros are those of Riemann's ξ-function,
with neither of the two cleared poles counted. This is the nontrivial-zero term in the bound
for the Riesz remainder in the first Riesz explicit formula.
-/

public section

namespace DirichletCharacter.IsPrimitive

open TauCeti TauCeti.LFunctions

/-- For a primitive Dirichlet character, if its L-function is zero-free right of `σ`, the norm
of its first Riesz zero series is bounded by `C * y ^ σ` on `y ≥ 1`. The same constant works for
all such `σ`. This also covers the primitive character of conductor one. -/
theorem exists_norm_rieszZeroSeries_le_of_zeroFreeRightOf {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ C ≥ 0, ∀ σ : ℝ, ZeroFreeRightOf σ χ.LFunction → ∀ y ≥ 1,
      ‖rieszZeroSeries (dirichletData χ hχ).entireCompletion y‖ ≤ C * y ^ σ := by
  rw [← dirichletData_continuedL χ hχ]
  have h := dirichletData_hasMeromorphicContinuation χ hχ
  exact h.exists_norm_rieszZeroSeries_le_of_zeroFreeRightOf
    (dirichletData_entireCompletion_orderLE_one χ hχ) (by norm_num)

end DirichletCharacter.IsPrimitive
