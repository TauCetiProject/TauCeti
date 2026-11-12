/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Comparison

/-!
# Torus compatibility from simple-root compatibility

A homomorphism between the point groups of two Chevalley data that matches their positive
and negative simple root maps also matches their simple coroots: each coroot value is the
root word `n_i(s) n_i(1)⁻¹`. Taking products gives compatibility with restriction from the
full weight lattice over every commutative ring.

This determines the map on the actual torus whenever the source datum has full weight
lattice, or whenever the units of the value ring are divisible. In particular it supplies
the torus equation for root-preserving comparisons over algebraically closed fields. The
target torus map is restriction between the actual character lattices, in their chosen
bases, not an identification of their coordinate tuples.

No generation theorem for all points is needed, and no existence of a root-preserving
homomorphism is asserted. For a proper weight lattice over a general field the conclusion
only concerns the image of the full-weight parametrization: root compatibility alone need
not determine the map on the entire actual torus.

The argument uses `ChevalleyDatum.simpleCorootPoints_eq_weylElement_mul_inv` and
`ChevalleyDatum.torusPoints_fullWeightTorusRestriction_eq_prod_simpleCorootPoints`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 28(c), and
  Corollary 5 to Theorem 4′.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D E : ChevalleyDatum t ht)
  {A : Type*} [CommRing A] (f : D.points A →* E.points A)

/-- Matching both signs of a simple root map forces compatibility with its simple coroot,
over every commutative ring. -/
theorem map_simpleCorootPoints_of_rootSubgroupPoints (i : Fin t.rank)
    (hpos : ∀ u, f (D.rootSubgroupPoints (t.simpleIndex ht i) A u) =
      E.rootSubgroupPoints (t.simpleIndex ht i) A u)
    (hneg : ∀ u, f (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
      (t.simpleIndex ht i) (t.simpleIndex ht i)) A u) =
        E.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A u)
    (s : Aˣ) : f (D.simpleCorootPoints i A s) = E.simpleCorootPoints i A s := by
  rw [D.simpleCorootPoints_eq_weylElement_mul_inv,
    E.simpleCorootPoints_eq_weylElement_mul_inv]
  simp only [weylElement_def, map_mul, map_inv, hpos, hneg]

variable
  (hpos : ∀ i u, f (D.rootSubgroupPoints (t.simpleIndex ht i) A u) =
    E.rootSubgroupPoints (t.simpleIndex ht i) A u)
  (hneg : ∀ i u, f (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
    (t.simpleIndex ht i) (t.simpleIndex ht i)) A u) =
    E.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
      (t.simpleIndex ht i) (t.simpleIndex ht i)) A u)

include hpos hneg

/-- Root compatibility determines the map on the full-weight torus image, without assuming
that this image is the entire actual torus. -/
theorem map_torusPoints_fullWeightTorusRestriction_of_rootSubgroupPoints
    (s : Fin t.rank → Aˣ) :
    f (D.torusPoints A (D.fullWeightTorusRestriction A s)) =
      E.torusPoints A (E.fullWeightTorusRestriction A s) := by
  rw [D.torusPoints_fullWeightTorusRestriction_eq_prod_simpleCorootPoints,
    E.torusPoints_fullWeightTorusRestriction_eq_prod_simpleCorootPoints, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def]
  congr 2
  funext i
  exact D.map_simpleCorootPoints_of_rootSubgroupPoints E f i (hpos i) (hneg i) (s i)

/-- If full-weight restriction reaches every source torus parameter, root compatibility
forces the actual torus equation by restriction of characters. -/
theorem map_torusPoints_of_rootSubgroupPoints_of_surjective
    (hs : Function.Surjective (D.fullWeightTorusRestriction A))
    (h : E.weightLattice ≤ D.weightLattice) (s : Fin t.rank → Aˣ) :
    f (D.torusPoints A s) = E.torusPoints A (D.torusRestriction E h s) := by
  obtain ⟨u, rfl⟩ := hs s
  rw [D.map_torusPoints_fullWeightTorusRestriction_of_rootSubgroupPoints E f hpos hneg,
    torusRestriction_fullWeightTorusRestriction]

/-- With divisible units, a root-preserving homomorphism matches the actual tori by restriction
of characters. In particular this applies over every algebraically closed field. -/
theorem map_torusPoints_of_rootSubgroupPoints [RootableBy Aˣ ℕ]
    (h : E.weightLattice ≤ D.weightLattice) (s : Fin t.rank → Aˣ) :
    f (D.torusPoints A s) = E.torusPoints A (D.torusRestriction E h s) :=
  D.map_torusPoints_of_rootSubgroupPoints_of_surjective E f hpos hneg
    (D.fullWeightTorusRestriction_surjective A) h s

/-- For a source datum with full weight lattice, matching the simple root maps forces the
actual torus equation over every commutative ring, not only over algebraically closed fields. -/
theorem map_torusPoints_of_rootSubgroupPoints_of_weightLattice_eq_top
    (hD : D.weightLattice = ⊤) (s : Fin t.rank → Aˣ) :
    f (D.torusPoints A s) =
      E.torusPoints A (D.torusRestriction E (le_top.trans hD.ge) s) :=
  D.map_torusPoints_of_rootSubgroupPoints_of_surjective E f hpos hneg
    (D.fullWeightTorusRestriction_surjective_of_weightLattice_eq_top A hD)
    (le_top.trans hD.ge) s

end TauCeti.DynkinType.ChevalleyDatum
