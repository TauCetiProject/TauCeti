/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness for modules killed by a scalar

If an `S`-module is killed by `f`, its scalar action factors through `S ⧸ (f)`. Thus a finite
`S`-module killed by `f` is finite over a coefficient semiring `A` whenever `S ⧸ (f)` is finite
over `A`. This transfers quotient-finiteness results to modules annihilated by distinguished
power series.
-/

public section

namespace Module.IsTorsionBy

/-- A finite `S`-module killed by `f` is finite over `A` if `S ⧸ (f)` is finite over `A`. -/
theorem finite_of_finite_quotient {A S M : Type*} [CommSemiring A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M] [Module.Finite S M]
    {f : S} (h : Module.IsTorsionBy S M f) [Module.Finite A (S ⧸ Ideal.span {f})] :
    Module.Finite A M := by
  have hM : Module.IsTorsionBySet S M (Ideal.span {f}) :=
    (Module.isTorsionBySet_span_singleton_iff f).mpr h
  let := hM.module
  have : IsScalarTower A (S ⧸ Ideal.span {f}) M := hM.isScalarTower
  have : Module.Finite (S ⧸ Ideal.span {f}) M := Module.Finite.of_restrictScalars_finite S _ M
  exact Module.Finite.trans (S ⧸ Ideal.span {f}) M

end Module.IsTorsionBy
