/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.Lie.Presentation.Serre.TripleBond

/-!
# The triple-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a triple bond satisfy the length-six braid
relation in the actual points of every Chevalley datum over every commutative ring.
In particular the equality holds in characteristics two and three and over nonreduced
rings, without division by the root-string factorials in those rings.

The rational Serre-operator identity is restricted to the admissible lattice and then
base changed using the shared word-identity transport in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned Weyl representatives at a triple bond satisfy the length-six braid relation
in the actual point group over every commutative value ring. The Cartan convention has
roots as rows, so `i` is the long node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -3) (hji : t.cartanMatrix j i = -1)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  have h' := D.weylElement_word_eq_of_serre_word_eq
    [i, j, i, j, i, j] [j, i, j, i, j, i] (by
      intro H E F hs hE hF
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, mul_assoc] using (hs.weylUnit_braid_of_cartan_eq_neg_three
          (i := j) (j := i) (by simp) (by simp) hij hji (hE j) (hF j) (hE i) (hF i)).symm) A
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using h'

end TauCeti.DynkinType.ChevalleyDatum
