/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# Transcendence degree in towers

This file records consequences of algebraic independence and Mathlib's transcendence-degree
tower inequality `lift_trdeg_add_le` for towers of commutative rings.

## Main results

* `TauCeti.trdeg_eq_of_isAlgebraic_base`: an injective algebraic extension of the base ring
  preserves transcendence degree in any commutative algebra over the larger base.
* `TauCeti.isAlgebraic_of_trdeg_le`: if the top ring has finite transcendence degree over the
  middle ring, at least its transcendence degree over the bottom ring, then the middle ring is
  algebraic over the bottom ring; `TauCeti.isAlgebraic_of_trdeg_eq_one` is the case of
  transcendence degree one.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- An injective algebraic extension of the base ring preserves transcendence degree, provided
the larger base has no zero divisors. The top algebra may have zero divisors, and its structure
map need not be injective. -/
theorem trdeg_eq_of_isAlgebraic_base
    [NoZeroDivisors S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S] :
    Algebra.trdeg S A = Algebra.trdeg R A := by
  -- Mathlib's algebraic-independence transfer identifies the sets in the defining supremum.
  rw [Algebra.trdeg, Algebra.trdeg,
    funext fun _ ↦ propext (Algebra.IsAlgebraic.algebraicIndependent_iff R S (A := A)).symm]

variable [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A]

/-- In an injective tower `R → S → A`, if `A` has finite transcendence degree over `S` that is
at least its transcendence degree over `R`, then `S` is algebraic over `R`. Finiteness allows
cancellation in the transcendence-degree tower inequality `lift_trdeg_add_le`. -/
theorem isAlgebraic_of_trdeg_le (h : Algebra.trdeg R A ≤ Algebra.trdeg S A)
    (hfin : Algebra.trdeg S A < Cardinal.aleph0) : Algebra.IsAlgebraic R S := by
  rw [← trdeg_eq_zero_iff, ← Cardinal.lift_eq_zero.{w}, ← nonpos_iff_eq_zero,
    ← Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.lift_lt_aleph0.mpr hfin), zero_add]
  exact lift_trdeg_add_le.trans (Cardinal.lift_le.mpr h)

/-- In an injective tower `R → S → A`, if `A` has transcendence degree one over both
`R` and `S`, then `S` is algebraic over `R`. -/
theorem isAlgebraic_of_trdeg_eq_one (h : Algebra.trdeg R A = 1) (h' : Algebra.trdeg S A = 1) :
    Algebra.IsAlgebraic R S :=
  isAlgebraic_of_trdeg_le (h.trans h'.symm).le (h' ▸ Cardinal.one_lt_aleph0)

end TauCeti
