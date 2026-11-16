/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Products of inner products

A product of inner products `∏ i ∈ s, ⟪m i, η⟫` against a fixed vector `η` is a homogeneous
polynomial of degree `#s` in `η`. This file records the Cauchy–Schwarz bound for it, the
estimate that controls the symbol `∏ i ∈ s, ⟪m i, η⟫` of an iterated directional derivative
`∂_{m i₁} ⋯ ∂_{m iₖ}` at frequency `η`.

## Main declarations

* `TauCeti.norm_prod_inner_le`: `‖∏ i ∈ s, ⟪m i, η⟫‖ ≤ (∏ i ∈ s, ‖m i‖) ‖η‖ ^ #s`.
-/

public section

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Cauchy–Schwarz for a product of inner products**: a product of `#s` inner products with
`η` is bounded by `(∏ i ∈ s, ‖m i‖) ‖η‖ ^ #s`. -/
theorem norm_prod_inner_le (s : Finset ι) (m : ι → E) (η : E) :
    ‖∏ i ∈ s, inner 𝕜 (m i) η‖ ≤ (∏ i ∈ s, ‖m i‖) * ‖η‖ ^ s.card := by
  rw [norm_prod, Finset.prod_mul_pow_card]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ norm_inner_le_norm _ _

end TauCeti
