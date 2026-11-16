/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.IteratedNeighborhood
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.CompactPair

/-!
# Borel–Moore homology of complements in finite polyhedra

Let `K` be an abstract simplicial complex with finitely many faces and `P` any precomplex of vertex
sets. In the compact Hausdorff polyhedron `|K| = Realization K`, the subpolyhedron
`|P| = {y : Realization K | y.1.support ∈ P}` is closed (`subcomplexNDRPair.isClosed`) and its
iterated open simplicial neighbourhoods `K.iteratedOpenSimplicialNeighborhood P n` are open,
strong deformation retract onto `|P|` (`exists_deformation_iteratedOpenSimplicialNeighborhood`),
and are cofinal among all open neighbourhoods of `|P|`
(`exists_iteratedOpenSimplicialNeighborhood_subset`).

Applying the compact-pair comparison theorem from
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.CompactPair` together with the
locally-compact and `σ`-compact instances on `|K| \ |P|` from
`TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.IteratedNeighborhood` yields, for every
local coefficient system `L` on `|K|` and every degree `j`, the canonical isomorphism
`realizationTwistedHomologyIsoBorelMooreHomologyCompl` between `H_j(|K|, |P|; L)` and
`H_j^{BM}(|K| \ |P|; L|_{|K| \ |P|})`.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem TauCeti.SetLike

namespace AbstractSimplicialComplex

universe u v w

variable {R : Type u} [Ring R] {ι : Type v}
  (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

private lemma exists_retraction_iteratedOpenSimplicialNeighborhood (n : ℕ) :
    ∃ r : C(K.iteratedOpenSimplicialNeighborhood P n, {y : Realization K | y.1.support ∈ P}),
      (∀ a, r (ContinuousMap.inclusion
        (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P n) a) = a) ∧
      ((ContinuousMap.inclusion
        (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P n)).comp r).Homotopic
          (ContinuousMap.id _) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := K.exists_deformation_iteratedOpenSimplicialNeighborhood P n
  exact ⟨r, hr, ⟨H.toHomotopy⟩⟩

/-- **Borel–Moore homology of the complement of a subpolyhedron** in a finite polyhedron `|K|`,
with respect to an explicit compact exhaustion `E` of `|K| \ |P|`. -/
def realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion (hfin : K.faces.Finite)
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Realization K)))
    (E : CompactExhaustion ({y : Realization K | y.1.support ∈ P}ᶜ : Set (Realization K)))
    (j : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (Realization K))
        {y : Realization K | y.1.support ∈ P}).twistedHomology L j ≅
      borelMooreHomology
        ((pullback
          (X := TopCat.of ({y : Realization K | y.1.support ∈ P}ᶜ : Set (Realization K)))
          (ContinuousMap.subtypeVal _)).obj L) j :=
  have := K.compactSpace_realization_of_finite_faces hfin
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    (X := TopCat.of (Realization K))
    (K.subcomplexNDRPair P).isClosed
    (K.isOpen_iteratedOpenSimplicialNeighborhood P)
    (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P)
    (K.exists_iteratedOpenSimplicialNeighborhood_subset P hfin)
    (K.exists_retraction_iteratedOpenSimplicialNeighborhood P) L E j

@[simp]
theorem realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion_hom
    (hfin : K.faces.Finite)
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Realization K)))
    (E : CompactExhaustion ({y : Realization K | y.1.support ∈ P}ᶜ : Set (Realization K)))
    (j : ℕ) :
    (K.realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion P hfin L E j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion (X := TopCat.of (Realization K))
        (K.subcomplexNDRPair P).isClosed L E j :=
  have := K.compactSpace_realization_of_finite_faces hfin
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction_hom
    (X := TopCat.of (Realization K)) (K.subcomplexNDRPair P).isClosed
    (K.isOpen_iteratedOpenSimplicialNeighborhood P)
    (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P)
    (K.exists_iteratedOpenSimplicialNeighborhood_subset P hfin)
    (K.exists_retraction_iteratedOpenSimplicialNeighborhood P) L E j

/-- **Borel–Moore homology of the complement of a subpolyhedron** in a finite polyhedron `|K|`:
`H_j(|K|, |P|; L) ≅ H_j^{BM}(|K| \ |P|; L|_{|K| \ |P|})` for every local coefficient system `L` on
`|K|` and every degree `j`. -/
def realizationTwistedHomologyIsoBorelMooreHomologyCompl [Finite (Face K)]
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Realization K))) (j : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (Realization K))
        {y : Realization K | y.1.support ∈ P}).twistedHomology L j ≅
      borelMooreHomology
        ((pullback
          (X := TopCat.of ({y : Realization K | y.1.support ∈ P}ᶜ : Set (Realization K)))
          (ContinuousMap.subtypeVal _)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
    (X := TopCat.of (Realization K)) (K.subcomplexNDRPair P).isClosed
    (K.isOpen_iteratedOpenSimplicialNeighborhood P)
    (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P)
    (K.exists_iteratedOpenSimplicialNeighborhood_subset P (Set.toFinite K.faces))
    (K.exists_retraction_iteratedOpenSimplicialNeighborhood P) L j

@[simp]
theorem realizationTwistedHomologyIsoBorelMooreHomologyCompl_hom [Finite (Face K)]
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Realization K))) (j : ℕ) :
    (K.realizationTwistedHomologyIsoBorelMooreHomologyCompl P L j).hom =
      twistedHomologyToBorelMooreHomologyCompl (X := TopCat.of (Realization K))
        (K.subcomplexNDRPair P).isClosed L j :=
  twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction_hom
    (X := TopCat.of (Realization K)) (K.subcomplexNDRPair P).isClosed
    (K.isOpen_iteratedOpenSimplicialNeighborhood P)
    (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P)
    (K.exists_iteratedOpenSimplicialNeighborhood_subset P (Set.toFinite K.faces))
    (K.exists_retraction_iteratedOpenSimplicialNeighborhood P) L j

/-- The canonical comparison map `H_j(|K|, |P|; L) ⟶ H_j^{BM}(|K| \ |P|; L|_{|K| \ |P|})` is an
isomorphism for every finite abstract simplicial complex `K` and precomplex `P`. -/
theorem isIso_twistedHomologyToBorelMooreHomologyCompl [Finite (Face K)]
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Realization K))) (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyCompl (X := TopCat.of (Realization K))
      (K.subcomplexNDRPair P).isClosed L j) :=
  K.realizationTwistedHomologyIsoBorelMooreHomologyCompl_hom P L j ▸
    (inferInstance : IsIso (K.realizationTwistedHomologyIsoBorelMooreHomologyCompl P L j).hom)

end AbstractSimplicialComplex
