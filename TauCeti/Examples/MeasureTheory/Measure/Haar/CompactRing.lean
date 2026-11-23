/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.Finite.Basic
import TauCeti.MeasureTheory.Measure.Haar.CompactRing

/-!
# Checks for null zero loci on compact rings

The hypotheses of `TauCeti.measure_pi_setOf_eval_eq_zero_of_compactRing` are needed. Over the
finite field `ℤ/p`, every point is isolated and the nonzero polynomial `X ^ p - X` vanishes on all
of `ℤ/p`, a set of Haar probability one. On the Boolean ring `(ℤ/2)^ℕ`, which is compact without
isolated points but not a domain, `X ^ 2 - X` vanishes everywhere.
-/

namespace TauCeti.Examples

open Polynomial

-- `X ^ p - X` vanishes on all of `ℤ/p`.
example (p : ℕ) [Fact p.Prime] (x : ZMod p) : (X ^ p - X : (ZMod p)[X]).eval x = 0 := by
  simp [ZMod.pow_card]

-- `X ^ p - X` is a nonzero polynomial over `ℤ/p`.
example (p : ℕ) [hp : Fact p.Prime] : (X ^ p - X : (ZMod p)[X]) ≠ 0 :=
  X_pow_sub_X_ne_zero hp.out.one_lt

-- Every element of the Boolean ring `(ℤ/2)^ℕ` is a root of `X ^ 2 - X`.
example (x : ℕ → ZMod 2) : x ^ 2 - x = 0 := by
  ext n
  simp [ZMod.pow_card]

end TauCeti.Examples
