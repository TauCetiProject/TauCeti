/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import TauCeti.Analysis.SpecialFunctions.Airy.Equation
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.CubeArgument

/-!
# Maclaurin series of the Airy functions

The Maclaurin series of `Ai`, `Bi` and their derivatives in the Pochhammer form of
DLMF 9.4.1–9.4.4:

`Ai(z) = Ai(0) ∑ₖ 3^k (⅓)_k z^{3k}/(3k)! + Ai′(0) ∑ₖ 3^k (⅔)_k z^{3k+1}/(3k + 1)!`,

`Ai′(z) = Ai′(0) ∑ₖ 3^k (⅔)_k z^{3k}/(3k)! + Ai(0) ∑ₖ 3^k (4/3)_k z^{3k+2}/(3k + 2)!`,

and the same for `Bi` and `Bi′` with `Bi(0)`, `Bi′(0)` in place of `Ai(0)`, `Ai′(0)`. They follow
from the hypergeometric definitions of `TauCeti.Analysis.SpecialFunctions.Airy.Basic`, the
derivative formulas of `TauCeti.Analysis.SpecialFunctions.Airy.Equation`, and the Pochhammer-form
series of `₀F₁(; b; z³/9)` for `b = ⅓, ⅔, 4/3, 5/3` of
`TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.CubeArgument`.

## Main results

* `TauCeti.hasSum_airyAi`, `TauCeti.hasSum_airyBi`: DLMF 9.4.1 and 9.4.3.
* `TauCeti.hasSum_deriv_airyAi`, `TauCeti.hasSum_deriv_airyBi`: DLMF 9.4.2 and 9.4.4.

## References

* NIST Digital Library of Mathematical Functions, §9.4, <https://dlmf.nist.gov/9.4>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Basic/Maclaurin.lean` (`hasSum_airyAi_maclaurin`, `hasSum_airyAiDeriv_maclaurin`,
`hasSum_airyBi_maclaurin`, `hasSum_airyBiDeriv_maclaurin`).
-/

public section

noncomputable section

open Complex
open scoped Nat

namespace TauCeti

/-- **The Maclaurin series of `Ai`** (DLMF 9.4.1). -/
theorem hasSum_airyAi (z : ℂ) :
    HasSum (fun k : ℕ =>
      airyAi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        deriv airyAi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (airyAi z) := by
  convert ((hasSum_regularizedHGFun_two_thirds_cube_div_nine z).mul_left
    ((3 : ℂ) ^ (-2 / 3 : ℂ))).sub
    ((hasSum_div_three_mul_regularizedHGFun_four_thirds_cube_div_nine z).mul_left
      ((3 : ℂ) ^ (-1 / 3 : ℂ))) using 1
  · ext k
    rw [airyAi_zero, deriv_airyAi_zero]
    ring
  · -- Write the exponent `−1/3` of `Ai′(0)` as `−4/3 + 1`, so that `cpow_add` relates it to the
    -- exponent `−4/3` of the definition.
    have h : (-1 / 3 : ℂ) = -4 / 3 + 1 := by norm_num
    rw [airyAi_def, h, cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]
    ring

/-- **The Maclaurin series of `Bi`** (DLMF 9.4.3). -/
theorem hasSum_airyBi (z : ℂ) :
    HasSum (fun k : ℕ =>
      airyBi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        deriv airyBi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (airyBi z) := by
  convert ((hasSum_regularizedHGFun_two_thirds_cube_div_nine z).mul_left
    ((3 : ℂ) ^ (-1 / 6 : ℂ))).add
    ((hasSum_div_three_mul_regularizedHGFun_four_thirds_cube_div_nine z).mul_left
      ((3 : ℂ) ^ (1 / 6 : ℂ))) using 1
  · ext k
    rw [airyBi_zero, deriv_airyBi_zero]
    ring
  · -- Write the exponent `1/6` of `Bi′(0)` as `−5/6 + 1`, so that `cpow_add` relates it to the
    -- exponent `−5/6` of the definition.
    have h : (1 / 6 : ℂ) = -5 / 6 + 1 := by norm_num
    rw [airyBi_def, h, cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]
    ring

/-- **The Maclaurin series of `Ai′`** (DLMF 9.4.2). -/
theorem hasSum_deriv_airyAi (z : ℂ) :
    HasSum (fun k : ℕ =>
      deriv airyAi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k) / (3 * k)!) +
        airyAi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (4 / 3) * z ^ (3 * k + 2) / (3 * k + 2)!))
      (deriv airyAi z) := by
  rw [deriv_airyAi_zero, airyAi_zero, deriv_airyAi z, mul_assoc _ (z ^ 2 / 3)]
  refine (((hasSum_regularizedHGFun_one_third_cube_div_nine z).mul_left _).add
    ((hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine z).mul_left
      _)).congr_fun fun k => ?_
  ring

/-- **The Maclaurin series of `Bi′`** (DLMF 9.4.4). -/
theorem hasSum_deriv_airyBi (z : ℂ) :
    HasSum (fun k : ℕ =>
      deriv airyBi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k) / (3 * k)!) +
        airyBi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (4 / 3) * z ^ (3 * k + 2) / (3 * k + 2)!))
      (deriv airyBi z) := by
  rw [deriv_airyBi_zero, airyBi_zero, deriv_airyBi z, mul_assoc _ (z ^ 2 / 3)]
  refine (((hasSum_regularizedHGFun_one_third_cube_div_nine z).mul_left _).add
    ((hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine z).mul_left
      _)).congr_fun fun k => ?_
  ring

end TauCeti
