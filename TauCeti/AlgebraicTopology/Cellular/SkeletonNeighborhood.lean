/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Chains
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Neighborhood

/-!
# The skeletal pair and the skeleton with the cell cores removed

For a relative CW complex, the skeletal pair `(Xⁿ, Xⁿ⁻¹)` — in Tau Ceti's indexing
`TauCeti.skeletonPair C n`, with ambient space `skeletonLT C (n + 1)` — includes into the pair
`TauCeti.skeletonNeighborhoodPair C n`, whose subspace `TauCeti.skeletonNeighborhood C n` is
`Xⁿ` with the inner half of every open `n`-cell removed.  The endpoint
`TauCeti.skeletonNeighborhoodEndpoint` of the radial deformation
`TauCeti.skeletonNeighborhoodHomotopy` is a homotopy inverse of this inclusion of pairs, the
deformation itself supplying both homotopies, so the inclusion induces isomorphisms on
relative singular homology in every degree.  In particular the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` is the relative homology of `(Xⁿ, TauCeti.skeletonNeighborhood C n)`.

The point of the replacement is excision: unlike `Xⁿ⁻¹`, the subspace
`TauCeti.skeletonNeighborhood C n` contains `Xⁿ⁻¹` in its interior
(`TauCeti.skeletonLT_subset_interior_skeletonNeighborhood`), so `Xⁿ⁻¹` can be excised from the
new pair, leaving the open `n`-cells relative to their outer halves.

## Main results

* `TauCeti.isIso_singularHomologyMap_skeletonPairToNeighborhood`: the inclusion
  `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, TauCeti.skeletonNeighborhood C n)` induces isomorphisms on relative singular
  homology.
* `TauCeti.skeletonNeighborhoodToPair`, `TauCeti.skeletonPairToNeighborhoodHomotopy`, and
  `TauCeti.skeletonNeighborhoodToPairHomotopy`: the inverse map and the two pair homotopies.
* `TauCeti.cellularChainGroupIsoNeighborhood`: the resulting isomorphism from the cellular chain
  group.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, proof of Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The pair `(Xⁿ, TauCeti.skeletonNeighborhood C n)`: the `n`-skeleton
`skeletonLT C (n + 1)` relative to its subset obtained by removing the inner half of every open
`n`-cell. -/
abbrev skeletonNeighborhoodPair (n : ℕ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of X) (skeletonNeighborhood_subset_skeletonLT_succ C n)

/-- The inclusion of the skeletal pair `(Xⁿ, Xⁿ⁻¹)` into
`(Xⁿ, TauCeti.skeletonNeighborhood C n)`. -/
def skeletonPairToNeighborhood (n : ℕ) : skeletonPair C n ⟶ skeletonNeighborhoodPair C n :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.id _) fun _ hx ↦
    skeletonLT_subset_skeletonNeighborhood n hx

@[simp]
lemma skeletonPairToNeighborhood_fst_apply (n : ℕ) (x : (skeletonPair C n).fst) :
    ConcreteCategory.hom (X := TopCat.of (skeletonLT C (n + 1)))
      (TopPair.Hom.fst (skeletonPairToNeighborhood C n)) x = x :=
  TopPair.ofInclusionMap_fst_apply _ _ x

@[simp]
lemma skeletonPairToNeighborhood_snd_apply (n : ℕ) (x : (skeletonPair C n).snd) :
    (ConcreteCategory.hom (X := TopCat.of (skeletonLT C n))
      (TopPair.Hom.snd (skeletonPairToNeighborhood C n)) x).1 = x.1 :=
  TopPair.ofInclusionMap_snd_apply _ _ x

/-- The radial deformation retraction, as a map of pairs
`(Xⁿ, TauCeti.skeletonNeighborhood C n) ⟶ (Xⁿ, Xⁿ⁻¹)`; it is a homotopy inverse of
`TauCeti.skeletonPairToNeighborhood`. -/
def skeletonNeighborhoodToPair (n : ℕ) : skeletonNeighborhoodPair C n ⟶ skeletonPair C n :=
  TopPair.ofInclusionMap _ _ (skeletonNeighborhoodEndpoint C n) fun x hx ↦
    skeletonNeighborhoodEndpoint_mem x hx

/-- The inclusion followed by the inverse is homotopic to the identity on the skeletal pair. -/
def skeletonPairToNeighborhoodHomotopy (n : ℕ) :
    TopPair.Homotopy (skeletonPairToNeighborhood C n ≫ skeletonNeighborhoodToPair C n)
      (𝟙 (skeletonPair C n)) := by
  rw [skeletonPairToNeighborhood, skeletonNeighborhoodToPair, ← TopPair.ofInclusionMap_comp,
    ← TopPair.ofInclusionMap_id]
  have hF (t : unitInterval) (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
      (hx : (x : X) ∈ (skeletonLT C n : Set X)) :
      ((skeletonNeighborhoodHomotopy C n).symm (t, x) : X) ∈ (skeletonLT C n : Set X) := by
    rw [ContinuousMap.Homotopy.symm_apply, skeletonNeighborhoodHomotopy_apply_of_mem _ x hx]
    exact hx
  exact TopPair.ofInclusionHomotopy (skeletonNeighborhoodHomotopy C n).symm hF

/-- The inverse followed by the inclusion is homotopic to the identity on the neighborhood
pair. -/
def skeletonNeighborhoodToPairHomotopy (n : ℕ) :
    TopPair.Homotopy (skeletonNeighborhoodToPair C n ≫ skeletonPairToNeighborhood C n)
      (𝟙 (skeletonNeighborhoodPair C n)) := by
  rw [skeletonPairToNeighborhood, skeletonNeighborhoodToPair, ← TopPair.ofInclusionMap_comp,
    ← TopPair.ofInclusionMap_id]
  exact TopPair.ofInclusionHomotopy (skeletonNeighborhoodHomotopy C n).symm
    fun t x hx ↦ skeletonNeighborhoodHomotopy_mem _ x hx

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Preadditive A]
  [CategoryWithHomology A] (R : A)

/-- **The inclusion `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, TauCeti.skeletonNeighborhood C n)` induces isomorphisms
on relative singular homology** in every degree. -/
theorem isIso_singularHomologyMap_skeletonPairToNeighborhood (n k : ℕ) :
    IsIso ((skeletonPair C n).singularHomologyMap (skeletonPairToNeighborhood C n) R k) := by
  refine TopPair.isIso_singularHomologyMap _ (skeletonNeighborhoodToPair C n) ?_ ?_ R k
  · exact skeletonPairToNeighborhoodHomotopy C n
  · exact skeletonNeighborhoodToPairHomotopy C n

end

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The cellular chain group `Hₙ(Xⁿ, Xⁿ⁻¹)` is the relative singular homology of the pair
`(Xⁿ, TauCeti.skeletonNeighborhood C n)`, through `TauCeti.skeletonPairToNeighborhood`. -/
def cellularChainGroupIsoNeighborhood (n : ℕ) :
    cellularChainGroup C R n ≅ (skeletonNeighborhoodPair C n).singularHomology R n :=
  have := isIso_singularHomologyMap_skeletonPairToNeighborhood C R n n
  asIso ((skeletonPair C n).singularHomologyMap (skeletonPairToNeighborhood C n) R n)

@[simp]
lemma cellularChainGroupIsoNeighborhood_hom (n : ℕ) :
    (cellularChainGroupIsoNeighborhood C R n).hom =
      (skeletonPair C n).singularHomologyMap (skeletonPairToNeighborhood C n) R n :=
  (rfl)

end

end TauCeti
