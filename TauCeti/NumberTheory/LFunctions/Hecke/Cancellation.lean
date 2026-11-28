/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Comparison of presented and cancellation-continued Hecke L-functions

For a nontrivial ray class character `χ ≠ 1` over a number field `K`, any agreement of
`TauCeti.LFunctions.heckeLFunctionC χ` with the defining `L`-series on `Re z > 1` extends by the
identity principle for meromorphic normal forms (`MeromorphicNFOn.eqOn_of_isPreconnected`) to
equality with `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` throughout the open half-plane
`Re z > 1 - 1 / [K : ℚ]`.

Separating this comparison from Landau nonvanishing lets continuation modules such as
`TauCeti.NumberTheory.LFunctions.Hecke.ModulusOne` import it without pulling in the nonvanishing
machinery.

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_eqOn_continuedLFunctionOfWeight`: for `χ ≠ 1`, series
  agreement on `Re z > 1` extends `heckeLFunctionC χ` to agree with
  `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` on `Re z > 1 - 1 / [K : ℚ]`.
-/

public section

open Filter IsDedekindDomain NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Comparison with the cancellation continuation for any modulus.** For a nontrivial ray class
character `χ ≠ 1`, if `heckeLFunctionC χ` agrees with the defining `L`-series on `Re z > 1`, then
it agrees with `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` throughout the open half-plane
`Re z > 1 - 1 / [K : ℚ]`. -/
theorem heckeLFunctionC_eqOn_continuedLFunctionOfWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    EqOn (heckeLFunctionC χ) (continuedLFunctionOfWeight χ.toUnitaryIdealWeight)
      {z | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} := by
  set U : Set ℂ := {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) U :=
    differentiableOn_continuedLFunctionOfWeight
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)
  have hz₀U : (2 : ℂ) ∈ U :=
    setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by norm_num)
  refine MeromorphicNFOn.eqOn_of_isPreconnected
    (fun z _ ↦ meromorphicNFOn_heckeLFunctionC χ (Set.mem_univ z))
    (hdiff.analyticOnNhd hUopen).meromorphicNFOn (convex_halfSpace_re_gt _).isPreconnected
    hz₀U ?_
  refine nhdsWithin_le_nhds ?_
  have hre_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hre_open.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z (hz : 1 < z.re)
  rw [hLL hz, continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hz]

end TauCeti.LFunctions
