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

For a finite abstract simplicial complex `K` and precomplex `P`, the iterated open simplicial
neighbourhoods of `|P|` in `|K|` are open, cofinal, and deformation retract onto `|P|`, yielding
`H_j(|K|, |P|; L) ≅ H_j^{BM}(|K| \ |P|; L|_{|K| \ |P|})`.
-/

public section
noncomputable section
open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem TauCeti.SetLike
namespace AbstractSimplicialComplex
universe u v w
variable {R : Type u} [Ring R] {ι : Type v}
  (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

private lemma exists_retraction_iteratedOpenSimplicialNeighborhood (n : ℕ) :
    ∃ r : C(K.iteratedOpenSimplicialNeighborhood P n, {y : Realization K | y.val.support ∈ P}),
      (∀ a, r (ContinuousMap.inclusion
        (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P n) a) = a) ∧
      ((ContinuousMap.inclusion
        (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P n)).comp r).Homotopic
          (ContinuousMap.id _) :=
  let ⟨r, hr, ⟨H⟩⟩ := K.exists_deformation_iteratedOpenSimplicialNeighborhood P n
  ⟨r, hr, ⟨H.toHomotopy⟩⟩

variable (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Realization K)))
/-- Borel–Moore comparison isomorphism for `|K| \ |P|` with respect to an exhaustion `E`. -/
def realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion (hfin : K.faces.Finite)
    (E : CompactExhaustion ({y : Realization K | y.val.support ∈ P}ᶜ : Set (Realization K)))
    (j : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (Realization K))
        {y : Realization K | y.val.support ∈ P}).twistedHomology L j ≅
      borelMooreHomology ((pullback
        (X := TopCat.of ({y : Realization K | y.val.support ∈ P}ᶜ : Set (Realization K)))
        (ContinuousMap.subtypeVal _)).obj L) j :=
  have := K.compactSpace_realization_of_finite_faces hfin
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    (X := TopCat.of (Realization K)) (K.subcomplexNDRPair P).isClosed
    (K.isOpen_iteratedOpenSimplicialNeighborhood P)
    (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P)
    (K.exists_iteratedOpenSimplicialNeighborhood_subset P hfin)
    (K.exists_retraction_iteratedOpenSimplicialNeighborhood P) L E j
@[simp] theorem realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion_hom
    (hfin : K.faces.Finite)
    (E : CompactExhaustion ({y : Realization K | y.val.support ∈ P}ᶜ : Set (Realization K)))
    (j : ℕ) :
    (K.realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion P L hfin E j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion (X := TopCat.of (Realization K))
        (K.subcomplexNDRPair P).isClosed L E j := by
  simp [realizationTwistedHomologyIsoBorelMooreHomologyComplOfExhaustion]
/-- Borel–Moore comparison isomorphism `H_j(|K|, |P|; L) ≅ H_j^{BM}(|K| \ |P|; L|_{|K| \ |P|})`. -/
def realizationTwistedHomologyIsoBorelMooreHomologyCompl [Finite (Face K)] (j : ℕ) :
    (TopPair.ofSubset (X := TopCat.of (Realization K))
        {y : Realization K | y.val.support ∈ P}).twistedHomology L j ≅
      borelMooreHomology ((pullback
        (X := TopCat.of ({y : Realization K | y.val.support ∈ P}ᶜ : Set (Realization K)))
        (ContinuousMap.subtypeVal _)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
    (X := TopCat.of (Realization K)) (K.subcomplexNDRPair P).isClosed
    (K.isOpen_iteratedOpenSimplicialNeighborhood P)
    (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P)
    (K.exists_iteratedOpenSimplicialNeighborhood_subset P (Set.toFinite K.faces))
    (K.exists_retraction_iteratedOpenSimplicialNeighborhood P) L j
@[simp] theorem realizationTwistedHomologyIsoBorelMooreHomologyCompl_hom [Finite (Face K)] (j : ℕ) :
    (K.realizationTwistedHomologyIsoBorelMooreHomologyCompl P L j).hom =
      twistedHomologyToBorelMooreHomologyCompl (X := TopCat.of (Realization K))
        (K.subcomplexNDRPair P).isClosed L j :=
  twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction_hom
    (hU_cofinal := K.exists_iteratedOpenSimplicialNeighborhood_subset P (Set.toFinite K.faces)) ..
/-- The comparison map `H_j(|K|, |P|; L) ⟶ H_j^{BM}(|K| \ |P|; L|_{|K| \ |P|})` is an iso. -/
theorem isIso_twistedHomologyToBorelMooreHomologyCompl [Finite (Face K)] (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyCompl (X := TopCat.of (Realization K))
      (K.subcomplexNDRPair P).isClosed L j) :=
  K.realizationTwistedHomologyIsoBorelMooreHomologyCompl_hom P L j ▸
    (inferInstance : IsIso (K.realizationTwistedHomologyIsoBorelMooreHomologyCompl P L j).hom)
end AbstractSimplicialComplex
