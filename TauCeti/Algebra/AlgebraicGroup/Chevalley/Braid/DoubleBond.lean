/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.Lie.Presentation.Serre.DoubleBond

/-!
# The double-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a double bond satisfy the length-four braid
relation over every commutative ring. This is an equality in the actual point group,
not just in a Weyl quotient. It supplies the double-bond relation needed to identify
the quotient of the Weyl subgroup by the torus.

The rational operator identity is
`IsSerreSystem.weylUnit_braid_of_cartan_eq_neg_two`. Restrict it to the datum's
Kostant-stable lattice, then use multiplicativity of scalar extension and the matrix
realization. In particular, no division takes place in the value ring, and no
restriction on weight multiplicities, characteristic or reducedness is needed.
The lattice-to-matrix transport uses the shared word-identity theorem in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned simple Weyl representatives at a double bond satisfy the length-four braid
relation over every commutative value ring. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_two (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -2)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  have h' := D.weylElement_word_eq_of_serre_word_eq [i, j, i, j] [j, i, j, i] (by
    intro H E F hs hE hF
    -- Serre's convention transposes the root-row Cartan matrix, so exchange the nodes.
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using (hs.weylUnit_braid_of_cartan_eq_neg_two
        (i := j) (j := i) (by simp) (by simp) hij hji (hE j) (hF j) (hE i) (hF i)).symm) A
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using h'

end TauCeti.DynkinType.ChevalleyDatum
