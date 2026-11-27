/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.VonNeumannRegular.Basic
import TauCeti.RingTheory.VonNeumannRegular.Jacobson
import TauCeti.RingTheory.Idempotents.Ideal

/-!
# Semisimple rings are von Neumann regular

An element `a` of a ring is *von Neumann regular* when `a * b * a = a` for some `b`. Every element
of a semisimple ring is regular because every principal left ideal has an idempotent generator.
Conversely, the Jacobson radical of any von Neumann regular ring vanishes, so an Artinian ring
is semisimple exactly when every element is regular.

This is the ring-theoretic input of the criterion recognising a semisimple abelian category from
its endomorphism rings: a morphism `f` with `f ≫ g ≫ f = f` has a kernel and a cokernel as soon
as idempotents split.

## Main results

* Every semisimple ring has an `IsVonNeumannRegularSemigroup` instance.
* `IsArtinianRing.isSemisimpleRing_iff_isVonNeumannRegularSemigroup`: an Artinian ring is
  semisimple if and only if it is von Neumann regular.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Graduate Texts in Mathematics
  **131**, Springer (2001), §4, Corollary 4.24.
-/

public section

variable {R : Type*} [Ring R]

/-- A semisimple ring is von Neumann regular. -/
instance [IsSemisimpleRing R] : TauCeti.IsVonNeumannRegularSemigroup R where
  exists_mul_mul_eq_self a :=
    (TauCeti.exists_isIdempotentElem_span_singleton_eq_iff a).mp
      (IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {a}))

/-- An Artinian ring is semisimple exactly when it is von Neumann regular. -/
theorem IsArtinianRing.isSemisimpleRing_iff_isVonNeumannRegularSemigroup [IsArtinianRing R] :
    IsSemisimpleRing R ↔ TauCeti.IsVonNeumannRegularSemigroup R :=
  ⟨fun _ ↦ inferInstance, fun _ ↦
    isSemisimpleRing_iff_jacobson.mpr TauCeti.IsVonNeumannRegularSemigroup.jacobson_eq_bot⟩
