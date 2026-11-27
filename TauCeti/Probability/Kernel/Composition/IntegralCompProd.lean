/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Bochner integrability against the composition-product of a measure and a kernel

This file provides measure-level Bochner integrability for the composition-product `μ ⊗ₘ κ` of an
s-finite measure `μ : Measure α` and an s-finite kernel `κ : Kernel α β`, complementing Mathlib's
`Mathlib/Probability/Kernel/Composition/IntegralCompProd.lean`.

## Main statements

* `MeasureTheory.Integrable.integral_measure_compProd`: if `f : α × β → E` is integrable with
  respect to `μ ⊗ₘ κ`, then `a ↦ ∫ b, f (a, b) ∂κ a` is integrable with respect to `μ`.
-/

public section

noncomputable section

open ProbabilityTheory

namespace MeasureTheory.Integrable

/-- If `f` is integrable with respect to `μ ⊗ₘ κ`, then the fiberwise integral
`a ↦ ∫ b, f (a, b) ∂κ a` is integrable with respect to `μ`.

This is the measure-level counterpart of Mathlib's `MeasureTheory.Integrable.integral_compProd`. -/
theorem integral_measure_compProd {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsSFiniteKernel κ] {f : α × β → E} (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun a ↦ ∫ b, f (a, b) ∂κ a) μ := by
  rw [← Kernel.const_compProd_prodMkLeft_apply Unit μ κ ()] at hf
  simpa [Kernel.prodMkLeft_apply, Kernel.const_apply] using hf.integral_compProd

end MeasureTheory.Integrable
