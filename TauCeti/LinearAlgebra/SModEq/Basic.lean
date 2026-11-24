/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Congruence modulo an ideal acting on the ring

In a commutative ring `A`, adic completeness for an ideal `I` is phrased through congruences
modulo the submodules `I ^ n • ⊤` of `A`. Since `I • ⊤ = I` as a submodule of `A`, such a
congruence is membership of the difference in the ideal.

## Main results

* `SModEq.ideal_smul_top_iff_sub_mem`: `x ≡ y [SMOD I • ⊤] ↔ x - y ∈ I`.
-/

public section

namespace SModEq

variable {A : Type*} [CommRing A]

/-- Congruence modulo `I • ⊤` in a commutative ring is congruence modulo the ideal `I`. -/
theorem ideal_smul_top_iff_sub_mem {I : Ideal A} {x y : A} :
    x ≡ y [SMOD I • (⊤ : Submodule A A)] ↔ x - y ∈ I := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

end SModEq
