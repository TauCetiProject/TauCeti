/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Algebraicity from transcendence degree in towers

This file records consequences of Mathlib's transcendence-degree tower inequality
`lift_trdeg_add_le` for injective towers of commutative rings.

## Main results

* `TauCeti.isAlgebraic_of_trdeg_eq`: if the top ring has the same finite transcendence degree
  over the bottom and middle rings, then the middle ring is algebraic over the bottom ring;
  `TauCeti.isAlgebraic_of_trdeg_eq_one` is the case of transcendence degree one.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [Nontrivial R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
variable [FaithfulSMul R S] [FaithfulSMul S A]

/-- In an injective tower `R → S → A`, if `A` has the same finite transcendence degree over
`R` and `S`, then `S` is algebraic over `R`. Finiteness allows cancellation in the
transcendence-degree tower inequality. -/
theorem isAlgebraic_of_trdeg_eq (h : Algebra.trdeg S A = Algebra.trdeg R A)
    (hfin : Algebra.trdeg R A < Cardinal.aleph0) : Algebra.IsAlgebraic R S := by
  rw [← trdeg_eq_zero_iff]
  have hz : Cardinal.lift.{w} (Algebra.trdeg R S) ≤ 0 :=
    (Cardinal.add_le_add_iff_of_lt_aleph0
      (γ := Cardinal.lift.{v} (Algebra.trdeg R A))
      (Cardinal.lift_lt_aleph0.mpr hfin)).mp
      (by simpa only [h, zero_add] using (lift_trdeg_add_le (R := R) (S := S) (A := A)))
  simpa using hz

/-- In an injective tower `R → S → A`, if `A` has transcendence degree one over both
`R` and `S`, then `S` is algebraic over `R`. -/
theorem isAlgebraic_of_trdeg_eq_one (h : Algebra.trdeg R A = 1) (h' : Algebra.trdeg S A = 1) :
    Algebra.IsAlgebraic R S :=
  isAlgebraic_of_trdeg_eq (h'.trans h.symm) (by rw [h]; exact Cardinal.one_lt_aleph0)

end TauCeti
