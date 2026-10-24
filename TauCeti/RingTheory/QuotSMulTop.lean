/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# The `R ⧸ (x)`-action on `M ⧸ x M`

Mathlib makes `QuotSMulTop x M = M ⧸ x M` a module over `R ⧸ (x)`. This file records that this
action is induced by the `R`-action on `M`, the analogue for `x • ⊤` of Mathlib's
`Module.Quotient.mk_smul_mk` for `I • ⊤`.

## Main results

* `QuotSMulTop.mk_smul_mk`: `[r] • [m] = [r • m]` in `M ⧸ x M`.
-/

public section

namespace QuotSMulTop

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {x : R}

/-- The `R ⧸ (x)`-action on `M ⧸ x M` is induced by the `R`-action on `M`. -/
@[simp]
theorem mk_smul_mk (r : R) (m : M) :
    Ideal.Quotient.mk (Ideal.span {x}) r • (Submodule.Quotient.mk m : QuotSMulTop x M) =
      Submodule.Quotient.mk (r • m) :=
  rfl

end QuotSMulTop
