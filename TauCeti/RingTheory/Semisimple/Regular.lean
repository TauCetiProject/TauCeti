/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.VonNeumannRegular
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

* `IsSemisimpleRing.exists_mul_mul_eq_self`: every element of a semisimple ring is regular.
* `IsArtinianRing.isSemisimpleRing_iff_forall_exists_mul_mul_eq_self`: an Artinian ring is
  semisimple if and only if every element is regular.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Graduate Texts in Mathematics
  **131**, Springer (2001), §4, Corollary 4.24.
-/

public section

variable {R : Type*} [Ring R]

/-- **Every element of a semisimple ring is von Neumann regular**: `a * b * a = a` for some `b`. -/
theorem IsSemisimpleRing.exists_mul_mul_eq_self [IsSemisimpleRing R] (a : R) :
    ∃ b, a * b * a = a :=
  (TauCeti.exists_isIdempotentElem_span_singleton_eq_iff a).mp
    (IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {a}))

/-- A semisimple ring is von Neumann regular. -/
instance [IsSemisimpleRing R] : TauCeti.IsVonNeumannRegularRing R :=
  ⟨IsSemisimpleRing.exists_mul_mul_eq_self⟩

namespace IsArtinianRing

variable [IsArtinianRing R]

/-- **An Artinian ring whose elements are all von Neumann regular is semisimple.** -/
theorem isSemisimpleRing_of_forall_exists_mul_mul_eq_self (h : ∀ a : R, ∃ b, a * b * a = a) :
    IsSemisimpleRing R := by
  let : TauCeti.IsVonNeumannRegularRing R := ⟨h⟩
  exact isSemisimpleRing_iff_jacobson.mpr TauCeti.IsVonNeumannRegularRing.jacobson_eq_bot

/-- **An Artinian ring is semisimple exactly when it is von Neumann regular.** -/
theorem isSemisimpleRing_iff_forall_exists_mul_mul_eq_self :
    IsSemisimpleRing R ↔ ∀ a : R, ∃ b, a * b * a = a :=
  ⟨fun _ ↦ IsSemisimpleRing.exists_mul_mul_eq_self,
    isSemisimpleRing_of_forall_exists_mul_mul_eq_self⟩

end IsArtinianRing
