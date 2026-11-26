/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
import TauCeti.NumberTheory.LFunctions.Continued.Dirichlet
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.ZeroFree

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
  have h := dirichletData_hasMeromorphicContinuation χ hχ
  have hOrder := dirichletData_entireCompletion_orderLE_one χ hχ
  refine ⟨_, tsum_nonneg (fun _ ↦ norm_nonneg _), fun σ hσ y hy ↦
    hOrder.norm_rieszZeroSeries_le h.differentiable_entireCompletion (by norm_num) ?_ hy⟩
  intro ρ hρ
  have hρre := (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hρ).1
  have hγ : (dirichletData χ hχ).gammaFactor ρ ≠ 0 := by
    simpa only [dirichletData_gammaFactor] using χ.gammaFactor_ne_zero_of_re_pos hρre
  have hpos := (h.entireCompletion_eq_zero_iff_meromorphicOrderAt_continuedL_pos hγ).mp hρ
  rw [dirichletData_continuedL χ hχ] at hpos
  exact le_of_not_gt fun hlt ↦ hpos.not_ge ((zeroFreeRightOf_iff.mp hσ) ρ hlt)

end DirichletCharacter.IsPrimitive
