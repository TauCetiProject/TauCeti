/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The second marginal of a composition-product of kernels

Composing a kernel `κ` with the Dirac measure at `a` gives `κ a`.

For a kernel `κ : Kernel α β` and an s-finite kernel `η : Kernel (α × β) γ`, the second marginal
of the composition-product `κ ⊗ₖ η` is the composition of `η` with `Kernel.id ×ₖ κ`: integrating
`η (a, b)` against `κ a` and forgetting `b` is the same as integrating `η` against the measure
`Kernel.id ×ₖ κ` on pairs `(a, b)`. When `κ` is not s-finite both sides are `0`. For probability
kernels: drawing `b` from `κ a`, then `c` from `η (a, b)`, and keeping `c`. Mathlib's
`ProbabilityTheory.Kernel.snd_compProd_prodMkLeft` is the special case where `η` ignores `a`.

## Main statements

* `MeasureTheory.Measure.comp_dirac` — `κ ∘ₘ Measure.dirac a = κ a`.
* `ProbabilityTheory.Kernel.snd_compProd_eq_comp_id_prod` —
  `(κ ⊗ₖ η).snd = η ∘ₖ (Kernel.id ×ₖ κ)`.
-/

public section

open MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

namespace MeasureTheory.Measure

open ProbabilityTheory

/-- Composing a kernel with the Dirac measure at `a` gives the kernel's measure at `a`. -/
@[simp]
theorem comp_dirac (κ : Kernel α β) (a : α) : κ ∘ₘ Measure.dirac a = κ a :=
  Measure.dirac_bind κ.measurable a

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

/-- The second marginal of a composition-product `κ ⊗ₖ η` with `η` s-finite is
`η ∘ₖ (Kernel.id ×ₖ κ)`. When `κ` is not s-finite, both sides vanish. -/
@[simp low]
theorem snd_compProd_eq_comp_id_prod (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : (κ ⊗ₖ η).snd = η ∘ₖ (Kernel.id ×ₖ κ) := by
  by_cases hκ : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ, prod_of_not_isSFiniteKernel_right _ hκ]
  ext1 a
  -- Mathlib's `Measure.comp_compProd_comm` at the Dirac measure at `a`.
  have h := Measure.comp_compProd_comm (μ := Measure.dirac a) (κ := κ) (η := η)
  rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc] at h
  simp only [Measure.comp_dirac] at h
  rw [h, snd_apply, Measure.snd]

end ProbabilityTheory.Kernel
