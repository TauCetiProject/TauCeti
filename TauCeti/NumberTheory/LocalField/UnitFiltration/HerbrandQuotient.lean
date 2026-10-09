/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.TateCohomology
public import TauCeti.NumberTheory.LocalField.UnitFiltration.ValuationSequence

/-!
# The Herbrand quotient of the units of a local field

For a cyclic extension `L/K` of nonarchimedean local fields, the equivariant valuation sequence
expresses the Herbrand quotient of `Lˣ` as the product of `[L : K]` and the Herbrand quotient of
the valuation-zero units. The latter is one, so `h(Lˣ) = [L : K]`.

## Main results

* `TauCeti.herbrandQuotient_units_eq_finrank`: `h(Lˣ) = [L : K]` for cyclic `L/K`.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, §4 and Chapter IX, §3.
-/

public noncomputable section

open Module ValuativeRel

namespace TauCeti

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- **The Herbrand quotient of a cyclic local extension.** For a cyclic extension `L/K` of
nonarchimedean local fields, the Herbrand quotient of `Lˣ` is `[L : K]`. -/
theorem herbrandQuotient_units_eq_finrank [IsCyclic (L ≃ₐ[K] L)] :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) = finrank K L := by
  rw [herbrandQuotient_units_eq_finrank_mul, TateCohomology.herbrandQuotient_unitFiltration_zero,
    mul_one]

end TauCeti
