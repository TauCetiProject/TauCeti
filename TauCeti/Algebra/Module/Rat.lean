/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat

/-!
# Rational modules: restriction to `ℚ≥0` and division by natural numbers

Every module over `ℚ` is a module over `ℚ≥0` by restriction of scalars along
`algebraMap ℚ≥0 ℚ`. This is deliberately not a global instance: Mathlib already builds
`Module ℚ≥0 R` from `DivisionSemiring R`, so a second global path would put two structures on
types such as `ℚ` itself; they agree by `subsingleton_nnrat_module`, but not definitionally.

Consumers activate it where they need it with
`attribute [local instance] TauCeti.moduleNNRat`. The typical use is to obtain Mathlib's
`BinomialRing` instance — which is stated for a `Module ℚ≥0` — on a possibly noncommutative
`ℚ`-algebra such as a universal enveloping algebra, so that `Ring.choose` elaborates there.

Over a semiring that is a `ℚ`-module, scaling by `(n : ℚ)⁻¹` undoes multiplication by a nonzero
natural number `n`.

## Main definitions

* `TauCeti.moduleNNRat`: the `ℚ≥0`-module structure on a `ℚ`-module.

## Main statements

* `TauCeti.inv_natCast_smul_natCast_mul`: `(n : ℚ)⁻¹ • (n * x) = x` for `n ≠ 0`.
-/

public section

namespace TauCeti

/-- The nonnegative-rational module structure induced on a rational module. -/
@[instance_reducible]
def moduleNNRat {A : Type*} [AddCommMonoid A] [Module ℚ A] : Module ℚ≥0 A :=
  Module.compHom _ (algebraMap ℚ≥0 ℚ)

/-- Over a semiring that is a `ℚ`-module, `(n : ℚ)⁻¹ •` undoes multiplication by a nonzero natural
number `n`. -/
theorem inv_natCast_smul_natCast_mul {A : Type*} [Semiring A] [Module ℚ A] {n : ℕ} (hn : n ≠ 0)
    (x : A) : (n : ℚ)⁻¹ • ((n : A) * x) = x := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn)]

end TauCeti
