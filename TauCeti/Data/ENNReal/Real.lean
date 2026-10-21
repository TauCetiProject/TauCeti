/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Real

/-!
# Scaling a density by a Jacobian in `ℝ≥0∞`

A change of variables with Jacobian `J ≥ 0` turns an integrand `ofReal (g (r / J))`, evaluated on
the transported density `r / J`, into `J * ofReal (g (r / J))`. This file reads that product in `ℝ`
as `ofReal (J * g (r.toReal / J))`, the form in which the internal energy `∫ J U(r / J)` of a
transported measure is written.

## Main declarations

* `ENNReal.ofReal_mul_ofReal_apply_toReal_div`:
  `ofReal J * ofReal (g (r / ofReal J).toReal) = ofReal (J * g (r.toReal / J))` for `J ≥ 0`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- For `J ≥ 0` and any `g : ℝ → ℝ`, the product `J * (g ((r / J).toReal))⁺` in `ℝ≥0∞` is the
positive part `(J g(r.toReal / J))⁺` of the corresponding real product. -/
theorem ofReal_mul_ofReal_apply_toReal_div {J : ℝ} (hJ : 0 ≤ J) (g : ℝ → ℝ) (r : ℝ≥0∞) :
    ENNReal.ofReal J * ENNReal.ofReal (g (r / ENNReal.ofReal J).toReal) =
      ENNReal.ofReal (J * g (r.toReal / J)) := by
  rw [toReal_div, toReal_ofReal hJ, ← ofReal_mul hJ]

end ENNReal
