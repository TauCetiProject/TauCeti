/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.Lie.Presentation.Serre.TripleBond
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic

/-!
# The triple-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a triple bond satisfy the length-six braid
relation over every commutative ring. This is an equality in the actual point group,
not just in a Weyl quotient. With the orthogonal, single-bond and double-bond relations
it completes the braid relations between simple Weyl representatives in every type.

The rational operator identity is
`IsSerreSystem.weylUnit_braid_of_cartan_eq_neg_three`. Restrict it to the datum's
Kostant-stable lattice and extend it to the value ring by
`TauCeti.DynkinType.ChevalleyDatum.weylElement_prod_eq_of_weylUnit_prod_eq`. In
particular the divisions by two and six in the rational calculation never take place in
the value ring, so the relation also holds in characteristics two and three and over
nonreduced rings.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned simple Weyl representatives at a triple bond satisfy the length-six braid
relation over every commutative value ring. The Cartan matrix is indexed by root, then coroot,
so `j` is the long node and `i` the short node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -3)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  -- The Lie basis uses the transpose of the displayed Cartan matrix. Reverse the
  -- two nodes in the operator theorem and then reverse its equality.
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    using D.weylElement_prod_eq_of_weylUnit_prod_eq [i, j, i, j, i, j] [j, i, j, i, j, i]
    (fun hE hF => by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
        using (D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_three
          (i := j) (j := i) (by simp) (by simp)
          (t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two i j (by omega)) hji
          (hE j) (hF j) (hE i) (hF i)).symm) A

end TauCeti.DynkinType.ChevalleyDatum
