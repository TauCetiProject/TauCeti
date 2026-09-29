/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Chains
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.CWComplex.Classical.SkeletonNbhd

/-!
# The skeletal pair and the skeleton with the cell cores removed

For a relative CW complex, the skeletal pair `(Xⁿ, Xⁿ⁻¹)` — in Tau Ceti's indexing
`TauCeti.skeletonPair C n`, with ambient space `skeletonLT C (n + 1)` — includes into the pair
`TauCeti.skeletonNbhdPair C n`, whose subspace `TauCeti.skeletonNbhd C n` is `Xⁿ` with the inner
half of every open `n`-cell removed.  The endpoint `TauCeti.skeletonNbhdRetraction` of the
radial deformation `TauCeti.skeletonNbhdHomotopy` is a homotopy inverse of this inclusion of
pairs, the deformation itself supplying both homotopies, so the inclusion induces isomorphisms on
relative singular homology in every degree.  In particular the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` is the relative homology of `(Xⁿ, TauCeti.skeletonNbhd C n)`.

The point of the replacement is excision: unlike `Xⁿ⁻¹`, the subspace `TauCeti.skeletonNbhd C n`
contains `Xⁿ⁻¹` in its interior (`TauCeti.skeletonLT_subset_interior_skeletonNbhd`), so `Xⁿ⁻¹` can
be excised from the new pair, leaving the open `n`-cells relative to their outer halves.

## Main results

* `TauCeti.isIso_singularHomologyMap_skeletonPairToNbhd`: the inclusion
  `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, TauCeti.skeletonNbhd C n)` induces isomorphisms on relative singular
  homology.
* `TauCeti.cellularChainGroupIsoNbhd`: the resulting isomorphism from the cellular chain group.

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

/-- The pair `(Xⁿ, TauCeti.skeletonNbhd C n)`: the `n`-skeleton `skeletonLT C (n + 1)` relative to
its subset obtained by removing the inner half of every open `n`-cell. -/
abbrev skeletonNbhdPair (n : ℕ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of X) (skeletonNbhd_subset_skeletonLT_succ C n)

/-- The inclusion of the skeletal pair `(Xⁿ, Xⁿ⁻¹)` into `(Xⁿ, TauCeti.skeletonNbhd C n)`. -/
def skeletonPairToNbhd (n : ℕ) : skeletonPair C n ⟶ skeletonNbhdPair C n :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.id _) fun _ hx ↦ skeletonLT_subset_skeletonNbhd n hx

/-- The radial deformation retraction, as a map of pairs
`(Xⁿ, TauCeti.skeletonNbhd C n) ⟶ (Xⁿ, Xⁿ⁻¹)`; it is a homotopy inverse of
`TauCeti.skeletonPairToNbhd`. -/
private def skeletonNbhdToPair (n : ℕ) : skeletonNbhdPair C n ⟶ skeletonPair C n :=
  TopPair.ofInclusionMap _ _ (skeletonNbhdRetraction C n) fun x hx ↦
    skeletonNbhdRetraction_mem x hx

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Preadditive A]
  [CategoryWithHomology A] (R : A)

/-- **The inclusion `(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, TauCeti.skeletonNbhd C n)` induces isomorphisms on relative
singular homology** in every degree. -/
theorem isIso_singularHomologyMap_skeletonPairToNbhd (n k : ℕ) :
    IsIso ((skeletonPair C n).singularHomologyMap (skeletonPairToNbhd C n) R k) := by
  refine TopPair.isIso_singularHomologyMap _ (skeletonNbhdToPair C n) ?_ ?_ R k
  · -- On `(Xⁿ, Xⁿ⁻¹)` the composite is the retraction, which the deformation joins to the
    -- identity while fixing `Xⁿ⁻¹`.
    rw [skeletonPairToNbhd, skeletonNbhdToPair, ← TopPair.ofInclusionMap_comp
      (h := fun x hx ↦ skeletonNbhdRetraction_mem x (skeletonLT_subset_skeletonNbhd n hx)),
      ← TopPair.ofInclusionMap_id (h := fun _ hx ↦ hx)]
    have hF (t : unitInterval) (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
        (hx : (x : X) ∈ (skeletonLT C n : Set X)) :
        ((skeletonNbhdHomotopy C n).symm (t, x) : X) ∈ (skeletonLT C n : Set X) := by
      rw [ContinuousMap.Homotopy.symm_apply, skeletonNbhdHomotopy_apply_of_mem _ x hx]
      exact hx
    exact TopPair.ofInclusionHomotopy (skeletonNbhdHomotopy C n).symm hF
  · -- On `(Xⁿ, TauCeti.skeletonNbhd C n)` the composite is again the retraction, and the
    -- deformation keeps `TauCeti.skeletonNbhd C n` inside itself.
    rw [skeletonPairToNbhd, skeletonNbhdToPair, ← TopPair.ofInclusionMap_comp
      (h := fun x hx ↦ skeletonLT_subset_skeletonNbhd n (skeletonNbhdRetraction_mem x hx)),
      ← TopPair.ofInclusionMap_id (h := fun _ hx ↦ hx)]
    exact TopPair.ofInclusionHomotopy (skeletonNbhdHomotopy C n).symm
      fun t x hx ↦ skeletonNbhdHomotopy_mem _ x hx

end

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The cellular chain group `Hₙ(Xⁿ, Xⁿ⁻¹)` is the relative singular homology of the pair
`(Xⁿ, TauCeti.skeletonNbhd C n)`, through `TauCeti.skeletonPairToNbhd`. -/
def cellularChainGroupIsoNbhd (n : ℕ) :
    cellularChainGroup C R n ≅ (skeletonNbhdPair C n).singularHomology R n :=
  have := isIso_singularHomologyMap_skeletonPairToNbhd C R n n
  asIso ((skeletonPair C n).singularHomologyMap (skeletonPairToNbhd C n) R n)

@[simp]
lemma cellularChainGroupIsoNbhd_hom (n : ℕ) :
    (cellularChainGroupIsoNbhd C R n).hom =
      (skeletonPair C n).singularHomologyMap (skeletonPairToNbhd C n) R n :=
  (rfl)

end

end TauCeti
