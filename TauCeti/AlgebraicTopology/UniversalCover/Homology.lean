/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.HomologyLift
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup

/-!
# First homology of connected abelian covers

For a homomorphism `φ : π₁(X, x) → H` to an abelian group, the actual cover constructed as
`SubgroupQuotient x φ.ker` gives an exact pair
`H₁(SubgroupQuotient x φ.ker; ℤ) → H₁(X; ℤ) → H`.
The first arrow is the map induced by the covering projection; the second is
`HurewiczOne.homologyLift x φ`. If `φ` is surjective, the second arrow is surjective as well,
giving the right-exact sequence ending in `H → 0`. The first arrow need not be injective.
No torsion-freeness or finite-generation assumption on `H` is needed.

Exactness follows from the subgroup recovered by the projection and the natural degree-one
Hurewicz isomorphism, rather than an assumed homological exactness property of the cover.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Choice 1.2, p. 211.
-/

public section
noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
variable [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
variable {H : Type*} [AddCommGroup H]

/-- The map on first integral homology induced by the covering associated to `ker φ` has
image exactly the kernel of the homology lift of `φ`. -/
theorem exact_subgroupQuotientProj_homologyLift (x : X)
    (φ : FundamentalGroup X x →* Multiplicative H) :
    Function.Exact
      (ContinuousMap.singularHomologyMap ℤ 1
        ⟨subgroupQuotientProj x φ.ker, continuous_subgroupQuotientProj x φ.ker⟩)
      (HurewiczOne.homologyLift x φ) :=
  HurewiczOne.exact_homologyMap_homologyLift
    (TopCat.ofHom
      ⟨subgroupQuotientProj x φ.ker, continuous_subgroupQuotientProj x φ.ker⟩)
    (subgroupQuotientProj_basepoint x φ.ker) φ
    (range_mapOfEq_subgroupQuotientProj x φ.ker)

end TauCeti.UniversalCover
