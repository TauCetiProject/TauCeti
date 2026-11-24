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

Let `F` be a commutative `K`-algebra that is free as a `K`-module, let `L` be a Lie algebra over
both `F` and `K`, and let `M` be a Lie module over `L`, free as an `F`-module, viewed also as a
Lie module over `K`. The trace form of `M` over `K` is the algebra trace from `F` to `K` of its
trace form over `F`: `B_K(x, y) = Tr_{F/K}(B_F(x, y))`. Taking `M = L` gives the same identity for
the Killing form. For a complex Lie algebra viewed as a real one this reads
`B_ℝ(x, y) = 2 Re B_ℂ(x, y)`.

## Main results

* `TauCeti.traceForm_restrictScalars`: `B_K(x, y) = Tr_{F/K}(B_F(x, y))` for the trace form of a
  Lie module.
* `TauCeti.traceForm_real_eq_two_mul_re`: `B_ℝ(x, y) = 2 Re B_ℂ(x, y)` for the trace form of a
  complex Lie module.
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

/-- **The trace form under restriction of scalars.** For a Lie module `M` over a Lie algebra `L`
over a free `K`-algebra `F`, with `M` free as an `F`-module, the trace form over `K` is the algebra
trace of the trace form over `F`. -/
theorem traceForm_restrictScalars {K F L M : Type*} [CommRing K] [CommRing F] [Algebra K F]
    [Module.Free K F] [LieRing L] [LieAlgebra K L] [LieAlgebra F L] [AddCommGroup M]
    [Module K M] [Module F M] [IsScalarTower K F M] [LieRingModule L M] [LieModule K L M]
    [LieModule F L M] [Module.Free F M] (x y : L) :
    LieModule.traceForm K L M x y = Algebra.trace K F (LieModule.traceForm F L M x y) := by
  rw [LieModule.traceForm_apply_apply, LieModule.traceForm_apply_apply,
    ← LinearMap.trace_restrictScalars]
  -- Both endomorphisms send `m` to `⁅x, ⁅y, m⁆⁆`.
  exact congrArg _ (LinearMap.ext fun m ↦ by simp)

/-- **The real trace form of a complex Lie module** is twice the real part of its complex trace
form: `B_ℝ(x, y) = 2 Re B_ℂ(x, y)`. -/
theorem traceForm_real_eq_two_mul_re {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] [LieRingModule L M]
    [LieModule ℂ L M] [LieModule ℝ L M] (x y : L) :
    LieModule.traceForm ℝ L M x y = 2 * (LieModule.traceForm ℂ L M x y).re := by
  rw [traceForm_restrictScalars (F := ℂ), Algebra.trace_complex_apply]

/-- **The Killing form under restriction of scalars.** For a Lie algebra `L` over a free
`K`-algebra `F`, free as an `F`-module, the Killing form over `K` is the algebra trace of the
Killing form over `F`. -/
theorem killingForm_restrictScalars {K F L : Type*} [CommRing K] [CommRing F] [Algebra K F]
    [Module.Free K F] [LieRing L] [LieAlgebra K L] [LieAlgebra F L] [IsScalarTower K F L]
    [Module.Free F L] (x y : L) :
    killingForm K L x y = Algebra.trace K F (killingForm F L x y) :=
  traceForm_restrictScalars x y

/-- **The real Killing form of a complex Lie algebra** is twice the real part of its complex
Killing form: `B_ℝ(x, y) = 2 Re B_ℂ(x, y)`. -/
theorem killingForm_real_eq_two_mul_re {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L]
    [IsScalarTower ℝ ℂ L] (x y : L) :
    killingForm ℝ L x y = 2 * (killingForm ℂ L x y).re :=
  traceForm_real_eq_two_mul_re x y

end TauCeti
