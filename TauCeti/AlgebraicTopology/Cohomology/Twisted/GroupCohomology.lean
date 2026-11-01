/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.GroupHomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.CoinvariantsTensor

/-!
# Twisted cohomology of the base of a contractible free cover is group cohomology

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, let `k` be a commutative ring, `A` a `k`-linear representation
of `G` and `N` a `k`-module. The twisted singular cohomology
`TauCeti.LocalCoefficientSystem.twistedCohomology` of `B` with coefficients in the local system
`L_A` associated to `A` (`IsQuotientCoveringMap.associatedLocalSystem`) and values in `N` is the
cohomology of `Hom(C(B; L_A), N)`. The twisted chains are the coinvariants `(A ⊗ C(E; k))_G`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`), and a map
`(A ⊗ C(E; k))_G ⟶ N` is a morphism of representations `C(E; k) ⟶ Homₖ(A, N)`
(`HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`). So the twisted cochains of `B` are
the complex `Hom_G(C(E; k), Homₖ(A, N))`.

If `E` is contractible, its singular chains are a projective resolution of the trivial
representation (`TauCeti.singularChainsResolution`), so the twisted cohomology of `B` is the group
cohomology of `G` with coefficients in the internal hom `Homₖ(A, N)`
(`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`):

`Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

The internal hom appears because Tau Ceti's twisted cochains with values in `N` are maps out of
the twisted chains, that is, cochains with coefficients in the dual system `Homₖ(L_A, N)`. For the
trivial representation `A = k` the fibres `(k ⊗ k[p⁻¹ x])_G` of `L_A` are copies of `k` and
`Homₖ(k, N)` is the trivial representation `N`, so this is the twisted form of the comparison
`IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology` of untwisted singular cohomology.
This is the cohomological counterpart of `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology`.

## Main definitions

* `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`: for contractible `E`, the twisted
  cohomology `Hⁿ(B; L_A, N)` is the group cohomology `Hⁿ(G, Homₖ(A, N))`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace IsQuotientCoveringMap

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (A : Rep.{u} k G) (N : Type u)
  [AddCommGroup N] [Module k N]

/-- **The twisted cohomology of the base of a contractible free cover is group cohomology**: for
the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total space, a
representation `A` of `G` and a `k`-module `N`, the cohomology of `B` with coefficients in the
local system associated to `A` and values in `N` is Mathlib's group cohomology
`Hⁿ(G, Homₖ(A, N))` of the internal hom into the trivial representation `N`. The singular chains
of `E` form a free resolution of `k` over `k[G]`, the twisted chains of `B` are the coinvariants
`(A ⊗ C(E; k))_G`, and maps from these to `N` are morphisms `C(E; k) ⟶ Homₖ(A, N)`. -/
def twistedCohomologyIsoGroupCohomology [ContractibleSpace E] (n : ℕ) :
    (hG.associatedLocalSystem k A).twistedCohomology k (ModuleCat.of k N) n ≅
      groupCohomology ((Rep.ihom A).obj (Rep.trivial k G N)) n :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  letI := Classical.decEq G
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).mapIso
        (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).op) ≪≫
    (Rep.groupCohomologyIhomIso A N n (singularChainsResolution k E G)).symm

end IsQuotientCoveringMap
