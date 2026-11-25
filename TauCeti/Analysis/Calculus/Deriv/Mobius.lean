/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivatives of fractional-linear maps

The fractional-linear map `w ↦ (k w + l) / (m w + n)` has first and second derivatives
`(k n - l m) / (m w + n) ^ 2` and `-2 m (k n - l m) / (m w + n) ^ 3` where `m w + n ≠ 0`.

## Main results

* `TauCeti.hasDerivAt_mul_add_div_mul_add`, `TauCeti.hasDerivAt_deriv_mul_add_div_mul_add`: the
  first and second derivatives of the fractional-linear map `w ↦ (k w + l) / (m w + n)`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k l m n z : 𝕜}

/-- The derivative of the fractional-linear map `w ↦ (k w + l) / (m w + n)` at a point `z` with
`m z + n ≠ 0` is `(k n - l m) / (m z + n) ^ 2`. -/
theorem hasDerivAt_mul_add_div_mul_add (hz : m * z + n ≠ 0) :
    HasDerivAt (fun w ↦ (k * w + l) / (m * w + n)) ((k * n - l * m) / (m * z + n) ^ 2) z := by
  refine ((((hasDerivAt_id z).const_mul k).add_const l).div
    (((hasDerivAt_id z).const_mul m).add_const n) hz).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- The derivative of the fractional-linear map `w ↦ (k w + l) / (m w + n)`, as a function, has
derivative `-2 m (k n - l m) / (m z + n) ^ 3` at a point `z` with `m z + n ≠ 0`. -/
theorem hasDerivAt_deriv_mul_add_div_mul_add (hz : m * z + n ≠ 0) :
    HasDerivAt (deriv fun w ↦ (k * w + l) / (m * w + n))
      (-2 * m * (k * n - l * m) / (m * z + n) ^ 3) z := by
  -- Near `z` the denominator stays nonzero, so the derivative is `(k n - l m) / (m w + n) ^ 2`.
  have hopen : IsOpen {w : 𝕜 | m * w + n ≠ 0} :=
    isOpen_ne_fun (continuous_const.mul continuous_id |>.add continuous_const) continuous_const
  have hev : (fun w ↦ (k * n - l * m) / (m * w + n) ^ 2) =ᶠ[𝓝 z]
      deriv fun w ↦ (k * w + l) / (m * w + n) :=
    Filter.mem_of_superset (hopen.mem_nhds hz) fun w hw ↦
      (hasDerivAt_mul_add_div_mul_add hw).deriv.symm
  refine (((hasDerivAt_const z (k * n - l * m)).div
    ((((hasDerivAt_id z).const_mul m).add_const n).pow 2)
    (pow_ne_zero 2 hz)).congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [id, Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

end TauCeti
