/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
-- Proof-only: the coefficients of `f(Y, X)`.
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Coefficients of commutative formal group laws

Mathlib states commutativity of a formal group law `F(X, Y)` as the identity `F(X, Y) = F(Y, X)`
of power series. This file records its coefficientwise form: the coefficient of `XⁱYʲ` in `F`
equals that of `XʲYⁱ`.

## Main results

* `FormalGroup.coeff_comm`: the coefficients of a commutative formal group law are symmetric.
-/

public section

open MvPowerSeries Finsupp

variable {A : Type*} [CommRing A]

namespace FormalGroup

/-- The coefficients of a commutative formal group law are symmetric: the coefficient of `XⁱYʲ`
equals that of `XʲYⁱ`. -/
theorem coeff_comm (F : FormalGroup A) [F.IsComm] (i j : ℕ) :
    coeff (single 0 i + single 1 j) F.toPowerSeries =
      coeff (single 0 j + single 1 i) F.toPowerSeries := by
  conv_lhs => rw [IsComm.comm (F := F)]
  simp [coeff_subst_X_one_X_zero]

end FormalGroup
