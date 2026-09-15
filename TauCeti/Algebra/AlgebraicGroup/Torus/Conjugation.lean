/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Conjugation of maximal tori

Conjugation by a rational point is an automorphism of the ambient affine group, so it preserves
maximal tori. This file records that invariance for the Hopf-ideal definition of a maximal torus.

This invariance is the half of a conjugacy statement for maximal tori that does not depend on
the existence of a conjugating rational point.

## Main declarations

* `TauCeti.HopfIdeal.IsMaximalTorus.conjugate`: the conjugate of a maximal torus is maximal.
* `TauCeti.HopfIdeal.isMaximalTorus_conjugate_iff`: maximal-torus status is invariant under
  conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Section 11.1.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The conjugate of a maximal torus by a rational point is a maximal torus. -/
theorem IsMaximalTorus.conjugate {I : HopfIdeal k H}
    (hI : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [conjugate_eq_comapOfSurjective]
  exact h

/-- Maximal-torus status is invariant under conjugation by a rational point.

This is not a `simp` lemma: `isMaximalTorus_iff` unfolds `IsMaximalTorus` on the left-hand
side, so the statement is never in `simp`-normal form. -/
theorem isMaximalTorus_conjugate_iff
    (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) ↔
      IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I := by
  constructor
  · intro hI
    have h := hI.conjugate g⁻¹
    simpa using h
  · exact fun hI ↦ hI.conjugate g

end TauCeti.HopfIdeal
