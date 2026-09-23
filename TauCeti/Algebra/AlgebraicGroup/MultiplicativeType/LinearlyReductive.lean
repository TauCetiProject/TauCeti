/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# Groups of multiplicative type are linearly reductive

An affine group of multiplicative type over a field `k` becomes diagonalizable over the algebraic
closure `AlgebraicClosure k`, where its coordinate Hopf algebra is a group algebra. Comodules over
a group algebra are completely reducible, being direct sums of their weight spaces, and complete
reducibility descends from any extension field back to `k`. Hence every group of multiplicative
type, and in particular every torus, split or not, is linearly reductive over its base field.

This is the easy implication of the characterization of linearly reductive groups in positive
characteristic: over an algebraically closed field of characteristic `p`, a smooth connected
affine group is linearly reductive exactly when it is a torus.

## Main declarations

* `TauCeti.multiplicativeTypeCommHopfAlgProperty.linearlyReductive`: a finite-type commutative
  Hopf algebra of multiplicative type is linearly reductive.
* `TauCeti.torusCommHopfAlgProperty.linearlyReductive`: the coordinate Hopf algebra of a torus is
  linearly reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Groups of multiplicative type are linearly reductive.** A finite-type commutative Hopf
algebra over a field that becomes diagonalizable over an algebraic closure is linearly
reductive. -/
theorem multiplicativeTypeCommHopfAlgProperty.linearlyReductive
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  obtain ⟨G, ⟨e⟩⟩ := (multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing k H).1 hH
  refine linearlyReductiveCommHopfAlgProperty.of_baseChange (AlgebraicClosure k) ?_
  exact (linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    ((ObjectProperty.ι _).mapIso e)
    (linearlyReductiveCommHopfAlgProperty_monoidAlgebra (AlgebraicClosure k) G)

/-- **Tori are linearly reductive.** The coordinate Hopf algebra of a torus over a field, split
or not, is linearly reductive. -/
theorem torusCommHopfAlgProperty.linearlyReductive (hH : torusCommHopfAlgProperty k H) :
    linearlyReductiveCommHopfAlgProperty k H.obj :=
  hH.multiplicativeType.linearlyReductive

end TauCeti
