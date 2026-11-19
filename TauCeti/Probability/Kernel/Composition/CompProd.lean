/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The second marginal of a composition-product of kernels

For kernels `κ : Kernel α β` and `η : Kernel (α × β) γ`, the second marginal of the
composition-product `κ ⊗ₖ η` is the composition of `η` with `Kernel.id ×ₖ κ`: drawing `b` from
`κ a` and then `c` from `η (a, b)`, and forgetting `b`, is the same as feeding the pair `(a, b)`
into `η`. Mathlib's `ProbabilityTheory.Kernel.snd_compProd_prodMkLeft` is the special case where
`η` ignores `a`.

## Main statements

* `ProbabilityTheory.Kernel.snd_compProd_eq_comp_id_prod` —
  `(κ ⊗ₖ η).snd = η ∘ₖ (Kernel.id ×ₖ κ)`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The second marginal of a composition-product `κ ⊗ₖ η` is `η ∘ₖ (Kernel.id ×ₖ κ)`. -/
theorem snd_compProd_eq_comp_id_prod (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    (κ ⊗ₖ η).snd = η ∘ₖ (Kernel.id ×ₖ κ) := by
  ext a s hs
  rw [snd_apply' _ _ hs, compProd_apply (measurable_snd hs), comp_apply' _ _ _ hs,
    lintegral_id_prod (Kernel.measurable_coe _ hs)]
  simp [← Set.preimage_comp]

end ProbabilityTheory.Kernel
