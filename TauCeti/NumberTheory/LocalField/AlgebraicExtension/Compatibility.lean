/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.RingTheory.Valuation.ValuativeRel.Henselian

/-!
# Algebraic extensions of local fields are compatible with the valuations

Let `K` and `F` be nonarchimedean local fields, each with its own valuative relation, and let
`F` be an algebraic `K`-algebra. Nothing in this data asks the valuation of `F` to restrict to the
valuation of `K`; this file specializes the general Henselian rigidity theorems of
`TauCeti.RingTheory.Valuation.ValuativeRel.Henselian` to record that it always does
(`ValuativeExtension.of_isAlgebraic`). For instance every finite `ℚ_p`-algebra structure on a
nonarchimedean local field is compatible with the `p`-adic valuation.

## Main results

* `TauCeti.valuation_algebraMap_eq_one_of_mem_unitFiltration_zero`: a `K`-algebra structure on a
  nonarchimedean local field `F` sends the units of `𝒪[K]` to elements of valuation one.
* `ValuativeExtension.of_isAlgebraic`: an algebraic extension of nonarchimedean local fields is a
  valuative extension.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, for the extension of the valuation to an algebraic
  extension.
* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. 108 (1933), 1–25.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F]

variable (F) in
/-- **The units of `𝒪[K]` keep valuation one in every local field over `K`.** For any
`K`-algebra structure on a nonarchimedean local field `F`, compatible with the valuations or not,
a unit `x` of the valuation ring of `K` has `v_F(x) = 1`. -/
theorem valuation_algebraMap_eq_one_of_mem_unitFiltration_zero {x : Kˣ}
    (hx : x ∈ unitFiltration K 0) : valuation F (algebraMap K F x) = 1 :=
  (algebraMap K F).valuation_map_eq_one_of_valuation_eq_one ((mem_unitFiltration_zero x).1 hx)

end TauCeti

/-- **Algebraic extensions of local fields are valuative extensions.** If `F` is an algebraic
`K`-algebra, `K` and `F` nonarchimedean local fields, then the valuation of `F` restricts to the
valuation of `K`; no compatibility between the two valuative relations needs to be assumed. -/
theorem ValuativeExtension.of_isAlgebraic (K F : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra K F] [Algebra.IsAlgebraic K F] :
    ValuativeExtension K F :=
  ValuativeExtension.of_isIntegral K F
