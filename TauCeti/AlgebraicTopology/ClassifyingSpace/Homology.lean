/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.GroupHomology

/-!
# The singular homology of a classifying space is group homology

For every group `G` and every commutative ring `k`, the singular homology of Milnor's classifying
space `classifyingSpace G` with coefficients in `k` is Mathlib's group homology of `G` with
coefficients in the trivial representation `k`, in every degree
(`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`):

`Hₙ(BG; k) ≅ Hₙ(G, k)`.

The countable join `universalGSpace G` is weakly contractible and carries a CW structure, so it is
contractible by Whitehead's theorem (`TauCeti.instContractibleSpaceUniversalGSpace`). The orbit
map `classifyingSpaceProj G` is the quotient covering map of the free action of `G` on it, so its
singular chains are a free resolution of `k` over `k[G]` whose coinvariants are the singular
chains of `classifyingSpace G` (`IsQuotientCoveringMap.singularHomologyIsoGroupHomology`). No
hypothesis on `G` is needed.

## Main definitions

* `TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(BG; k) ≅ Hₙ(G, k)`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- **The singular homology of the classifying space is group homology**: for every group `G`,
the singular homology `Hₙ(BG; k)` of Milnor's classifying space with coefficients in a
commutative ring `k` is Mathlib's group homology `Hₙ(G, k)` of the trivial representation. It
comes from the free resolution of `k` by the singular chains of `universalGSpace G`. -/
def classifyingSpaceSingularHomologyIsoGroupHomology (n : ℕ) :
    ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology n ≅
      groupHomology (Rep.trivial k G k) n :=
  IsQuotientCoveringMap.singularHomologyIsoGroupHomology (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k n

end TauCeti
