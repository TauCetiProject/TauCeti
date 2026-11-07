/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Comparing linear combinations by their Gram kernels

Two families with the same pairwise inner products give linear combinations with the same
pairwise inner products, hence of the same norm, when supplied with the same finitely supported
coefficients. This comparison applies in seminormed inner product spaces and is useful for
comparing realizations of a positive-definite kernel before constructing an isometry between
their closed spans.
-/

public section

open InnerProductSpace

namespace Finsupp

variable {𝕜 α E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Families with equal pairwise inner products give linear combinations with equal inner
products for the same finitely supported coefficients. -/
theorem inner_linearCombination_eq_of_inner_eq (f g : α →₀ 𝕜) {φ : α → E} {ψ : α → F}
    (h : ∀ a b, ⟪φ a, φ b⟫_𝕜 = ⟪ψ a, ψ b⟫_𝕜) :
    ⟪linearCombination 𝕜 φ f, linearCombination 𝕜 φ g⟫_𝕜 =
      ⟪linearCombination 𝕜 ψ f, linearCombination 𝕜 ψ g⟫_𝕜 := by
  simp only [linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left,
    inner_smul_right, h]

/-- Families with equal pairwise inner products give linear combinations of equal norm
for the same finitely supported coefficients. -/
theorem norm_linearCombination_eq_of_inner_eq (f : α →₀ 𝕜) {φ : α → E} {ψ : α → F}
    (h : ∀ a b, ⟪φ a, φ b⟫_𝕜 = ⟪ψ a, ψ b⟫_𝕜) :
    ‖linearCombination 𝕜 φ f‖ = ‖linearCombination 𝕜 ψ f‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜),
    inner_linearCombination_eq_of_inner_eq f f h]

end Finsupp
