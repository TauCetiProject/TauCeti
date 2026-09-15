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

The result supplies the invariance half of the conjugacy statement in Layer 7, "Borel subgroups,
maximal tori, and their conjugacy", of the ReductiveGroups roadmap. Existence of a rational point
conjugating two maximal tori remains to be proved.

## Main declarations

* `TauCeti.HopfIdeal.IsMaximalTorus.conjugate`: the conjugate of a maximal torus is maximal.
* `TauCeti.HopfIdeal.isMaximalTorus_conjugate_iff`: maximal-torus status is invariant under
  conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Section 11.1.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

private noncomputable def pointConjugationFiniteTypeIso
    (g : WithConv (H →ₐ[k] k)) :
    FiniteTypeCommHopfAlgCat.of k H ≅ FiniteTypeCommHopfAlgCat.of k H :=
  ObjectProperty.isoMk _ <|
    _root_.CommHopfAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv g)

/-- The conjugate of a maximal torus by a rational point is a maximal torus. -/
theorem IsMaximalTorus.conjugate {I : HopfIdeal k H}
    (hI : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) := by
  let e := pointConjugationFiniteTypeIso g
  have h := hI.comapOfIso e
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
