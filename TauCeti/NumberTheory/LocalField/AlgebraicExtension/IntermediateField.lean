/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# Valuative extensions through algebraic intermediate fields

If a valuative relation on an ambient field extends that of a nonarchimedean local field `K`,
then it also extends any compatible valuative relation on an algebraic intermediate field.
This follows from uniqueness of the valuation class on algebraic extensions of `K`.

## Main results

* `IntermediateField.valuativeExtension`: the ambient field is a valuative extension of a
  compatible algebraic intermediate field.
-/

public section

namespace IntermediateField

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- If the valuative relations on an ambient field `Ω` and an algebraic intermediate field `E`
both extend that of the nonarchimedean local field `K`, then `Ω` is a valuative extension of `E`.
The extension `Ω / K` need not be algebraic. -/
theorem valuativeExtension [ValuativeRel Ω] [ValuativeExtension K Ω]
    (E : IntermediateField K Ω) [Algebra.IsAlgebraic K E] [ValuativeRel E]
    [ValuativeExtension K E] : ValuativeExtension E Ω := by
  have h := E.val.valuativeExtension
  exact ⟨fun a b ↦ h.vle_iff_vle a b⟩

end IntermediateField
