/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.Cohomology.GroupCohomology

/-!
# The singular cohomology of a classifying space is group cohomology

For every group `G`, every commutative ring `k` and every `k`-module `M`, the singular cohomology
of Milnor's classifying space `classifyingSpace G` with coefficients in `M` is Mathlib's group
cohomology of `G` with coefficients in the trivial representation `M`, in every degree
(`TauCeti.classifyingSpaceSingularCohomologyIsoGroupCohomology`):

`Hⁿ(BG; M) ≅ Hⁿ(G, M)`.

The countable join `universalGSpace G` is contractible
(`TauCeti.instContractibleSpaceUniversalGSpace`) and the orbit map `classifyingSpaceProj G` is the
quotient covering map of the free action of `G` on it, so its singular chains are a free
resolution of `k` over `k[G]` whose `G`-invariant `M`-valued cochains are the singular cochains of
`classifyingSpace G` (`IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology`). No hypothesis
on `G` is needed. This is the cohomological counterpart of
`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`.

## Main definitions

* `TauCeti.classifyingSpaceSingularCohomologyIsoGroupCohomology`: the isomorphism
  `Hⁿ(BG; M) ≅ Hⁿ(G, M)`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G] (M : Type u) [AddCommGroup M]
  [Module k M]

/-- **The singular cohomology of the classifying space is group cohomology**: for every group
`G`, the singular cohomology `Hⁿ(BG; M)` of Milnor's classifying space with coefficients in a
module `M` over a commutative ring `k` is Mathlib's group cohomology `Hⁿ(G, M)` of the trivial
representation `M`. It comes from the free resolution of `k` by the singular chains of
`universalGSpace G`. -/
def classifyingSpaceSingularCohomologyIsoGroupCohomology (n : ℕ) :
    (TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k M) n ≅
      groupCohomology (Rep.trivial k G M) n :=
  IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k M n

end TauCeti
