/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.RingTheory.Complex
public import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# The Killing form under restriction of scalars

Let `F` be a commutative `K`-algebra that is free as a `K`-module, and let `L` be a Lie algebra
over `F` that is free as an `F`-module, viewed also as a Lie algebra over `K`. The Killing form of
`L` over `K` is the algebra trace from `F` to `K` of its Killing form over `F`:
`B_K(x, y) = Tr_{F/K}(B_F(x, y))`. For a complex Lie algebra viewed as a real one this reads
`B_ℝ(x, y) = 2 Re B_ℂ(x, y)`.

## Main results

* `TauCeti.killingForm_restrictScalars`: `B_K(x, y) = Tr_{F/K}(B_F(x, y))`.
* `TauCeti.killingForm_real_eq_two_mul_re`: `B_ℝ(x, y) = 2 Re B_ℂ(x, y)` for a complex Lie
  algebra.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §1, Proposition 6.3 and
  the discussion of complex Lie algebras viewed as real ones.
-/

public section

open LieAlgebra

namespace TauCeti

/-- **The Killing form under restriction of scalars.** For a Lie algebra `L` over a free
`K`-algebra `F`, free as an `F`-module, the Killing form over `K` is the algebra trace of the
Killing form over `F`. -/
theorem killingForm_restrictScalars {K F L : Type*} [CommRing K] [CommRing F] [Algebra K F]
    [Module.Free K F] [LieRing L] [LieAlgebra K L] [LieAlgebra F L] [IsScalarTower K F L]
    [Module.Free F L] (x y : L) :
    killingForm K L x y = Algebra.trace K F (killingForm F L x y) := by
  rw [killingForm, killingForm, LieModule.traceForm_apply_apply,
    LieModule.traceForm_apply_apply, ← LinearMap.trace_restrictScalars]
  rfl

/-- **The real Killing form of a complex Lie algebra** is twice the real part of its complex
Killing form: `B_ℝ(x, y) = 2 Re B_ℂ(x, y)`. -/
theorem killingForm_real_eq_two_mul_re {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L]
    [IsScalarTower ℝ ℂ L] (x y : L) :
    killingForm ℝ L x y = 2 * (killingForm ℂ L x y).re := by
  rw [killingForm_restrictScalars (F := ℂ), Algebra.trace_complex_apply]

end TauCeti
