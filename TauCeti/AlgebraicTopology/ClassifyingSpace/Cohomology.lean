/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
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

The isomorphism is natural in the coefficients: a linear map `f : M →ₗ[k] N` acts on
`Hⁿ(BG; -)` by postcomposing cochains and on `Hⁿ(G, -)` by Mathlib's `groupCohomology.map`, and
the two isomorphisms intertwine these maps
(`TauCeti.classifyingSpaceSingularCohomologyIsoGroupCohomology_hom_naturality`).

It is also natural in the group: for every `φ : G →* H`, the map `Hⁿ(BH; M) ⟶ Hⁿ(BG; M)` induced
by the strictly functorial map `MonoidHom.classifyingSpaceMap φ` is Mathlib's change-of-group map
`groupCohomology.map φ`, with the identity on the trivial coefficients `M`
(`MonoidHom.classifyingSpaceSingularCohomologyIsoGroupCohomology_hom_naturality`). No hypothesis on
`φ` is needed.

## Main definitions

* `TauCeti.classifyingSpaceSingularCohomologyIsoGroupCohomology`: the isomorphism
  `Hⁿ(BG; M) ≅ Hⁿ(G, M)`.

## Main results

* `TauCeti.classifyingSpaceSingularCohomologyIsoGroupCohomology_hom_naturality`: the isomorphism is
  natural in the coefficients.
* `MonoidHom.classifyingSpaceSingularCohomologyIsoGroupCohomology_hom_naturality`: the isomorphism
  is natural in the group.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4 and Section III.8.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory

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

variable {M} {N : Type u} [AddCommGroup N] [Module k N]

/-- **The comparison `Hⁿ(BG; M) ≅ Hⁿ(G, M)` is natural in the coefficients**: for a `k`-linear
map `f : M →ₗ[k] N`, it carries the map on the singular cohomology of the classifying space
induced by postcomposing cochains with `f` to Mathlib's map
`groupCohomology.map (MonoidHom.id G)` induced by `f` on trivial representations. -/
@[reassoc]
theorem classifyingSpaceSingularCohomologyIsoGroupCohomology_hom_naturality (f : M →ₗ[k] N)
    (n : ℕ) :
    HomologicalComplex.homologyMap (((singularChains k).obj
        (TopCat.of (classifyingSpace G))).linearYonedaObjMap k (ModuleCat.ofHom f)) n ≫
        (classifyingSpaceSingularCohomologyIsoGroupCohomology k G N n).hom =
      (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M n).hom ≫
        groupCohomology.map (MonoidHom.id G) ((Rep.trivialFunctor k G).map (ModuleCat.ofHom f))
          n :=
  IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology_hom_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k M f n

end TauCeti

namespace MonoidHom

open TauCeti

universe u

variable {G H : Type u} [Group G] [Group H]

/-- **The singular cohomology of the classifying space is naturally group cohomology.** For every
group homomorphism `φ : G →* H`, the identifications `Hⁿ(BH; M) ≅ Hⁿ(H, M)` and
`Hⁿ(BG; M) ≅ Hⁿ(G, M)` carry the map on singular cohomology induced by
`MonoidHom.classifyingSpaceMap φ` to Mathlib's change-of-group map `groupCohomology.map φ`, with
the identity on the trivial coefficients `M`. -/
@[reassoc]
theorem classifyingSpaceSingularCohomologyIsoGroupCohomology_hom_naturality (φ : G →* H)
    (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M] [Module k M] (n : ℕ) :
    TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k M)
        (TopCat.ofHom φ.classifyingSpaceMap) n ≫
        (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M n).hom =
      (classifyingSpaceSingularCohomologyIsoGroupCohomology k H M n).hom ≫
        groupCohomology.map φ (A := Rep.trivial k H M) (B := Rep.trivial k G M)
          (𝟙 (Rep.trivial k G M)) n :=
  IsQuotientCoveringMap.singularCohomologyMap_comp_singularCohomologyIsoGroupCohomology_hom
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k M
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) _
    (ConcreteCategory.hom_ext _ _ fun x ↦ (φ.classifyingSpaceMap_proj x)) n

end MonoidHom
