/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.EquivariantMap
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.GroupCohomology

/-!
# The (co)homology of a classifying space with local coefficients is group (co)homology

For every group `G`, every commutative ring `k` and every `k`-linear representation `A` of `G`,
the homology of Milnor's classifying space `classifyingSpace G` with local coefficients in `A` is
Mathlib's group homology of `G` with coefficients in `A`, in every degree
(`TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`):

`Hₙ(BG; A) ≅ Hₙ(G, A)`.

The local coefficient system `TauCeti.classifyingSpaceLocalSystem k A` is the one associated to
`A` by the orbit map of the countable join `universalGSpace G`, which is the quotient covering
map of a free action of `G`: its fibre over a point `x` is `(A ⊗ k[π⁻¹ x])_G`, and transport
along a path is induced by lifting the path to `universalGSpace G`. The countable join is
contractible, so `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology` applies. No hypothesis on
`G` is needed.

The identification is natural in both the coefficients and the group. For a fixed group `G`, a
morphism of representations `f : A ⟶ A'` induces a morphism of local systems
`TauCeti.classifyingSpaceLocalSystemMap f`, and the induced map `Hₙ(BG; A) ⟶ Hₙ(BG; A')`
corresponds to Mathlib's map `groupHomology.map (MonoidHom.id G) f`
(`TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`). For a group
homomorphism `φ : G →* H`, pulling `classifyingSpaceLocalSystem k D` back along
`MonoidHom.classifyingSpaceMap φ` identifies it canonically with the local system on `BG`
associated to the restricted representation `Rep.res φ D`
(`MonoidHom.classifyingSpaceLocalSystemPullbackIso`). More generally, a compatible coefficient map
`ξ : A ⟶ Rep.res φ D` induces a map of local systems `MonoidHom.classifyingSpaceLocalSystemMapOver`
and a geometric map `MonoidHom.classifyingSpaceTwistedHomologyMap` on twisted homology, by
coefficient change followed by pushforward along `φ.classifyingSpaceMap`. The comparison carries
this map to `groupHomology.map φ ξ`
(`MonoidHom.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`), and these geometric
maps respect identities and composition.

It also respects the coefficient long exact sequences. The associated local systems form an exact
functor `TauCeti.classifyingSpaceLocalSystemFunctor k G` of the representation, so a short exact
sequence `0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` of representations gives a short exact sequence of local
systems on `BG` (`TauCeti.shortExact_map_classifyingSpaceLocalSystemFunctor`) and a long exact
sequence in homology with local coefficients. Its connecting map `Hₙ(BG; A₃) ⟶ Hₘ(BG; A₁)`,
`m + 1 = n`, corresponds to Mathlib's connecting map `groupHomology.δ`
(`TauCeti.twistedHomologyδ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_hom`). Together
with the naturality in the coefficients, this identifies the long exact sequence of homology of
`BG` with local coefficients with that of group homology.

Likewise, the direct local-coefficient cohomology of `classifyingSpace G` with coefficients in
`TauCeti.classifyingSpaceLocalSystem k A` (cochains assigning to each base simplex an element of the
fibre over its initial vertex) is Mathlib's group cohomology of `G` with coefficients in `A` itself
(`TauCeti.classifyingSpaceCohomologyIsoGroupCohomology`):

`Hⁿ(BG; A) ≅ Hⁿ(G, A)`.

This direct comparison comes from `IsQuotientCoveringMap.cohomologyIsoGroupCohomology`, requires no
projectivity or flatness assumption on `A`, is covariantly natural in `f : A ⟶ A'`
(`TauCeti.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality`), contravariantly natural
along any `φ : G →* H` and `ξ : Rep.res φ D ⟶ A` via `MonoidHom.classifyingSpaceCohomologyMap`
(`MonoidHom.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality`), and carries the
coefficient connecting map `ShortComplex.ShortExact.cohomologyδ` of any short exact sequence of
representations to `groupCohomology.δ`
(`TauCeti.cohomologyδ_comp_classifyingSpaceCohomologyIsoGroupCohomology_hom`).

Dually, for a `k`-module `N`, the cohomology of `classifyingSpace G` with coefficients in the same
local system and values in `N` is the group cohomology of `G` with coefficients in the internal
hom `Homₖ(A, N)`, where `N` carries the trivial action
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`):

`Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

Twisted cochains with values in `N` are maps out of the twisted chains, so this is cohomology with
coefficients in the dual local system `Homₖ(A, N)`; it comes from
`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`.

This dual identification is natural in both coefficient variables and in the group. A morphism of
representations `f : A ⟶ A'` induces `Hⁿ(BG; A', N) ⟶ Hⁿ(BG; A, N)` through
`TauCeti.classifyingSpaceLocalSystemMap f`, corresponding to precomposition with `f` on
`Hⁿ(G, Homₖ(-, N))`
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left`), while a linear
map `g : N →ₗ[k] N'` acts on cochains by postcomposition and on group cohomology through the
induced map `Homₖ(A, N) ⟶ Homₖ(A, N')`
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_right`). Along a group
homomorphism `φ : G →* H` and a compatible morphism `ξ : A ⟶ Rep.res φ D`, pulling twisted
cohomology back along `φ.classifyingSpaceMap` and changing local coefficients along
`φ.classifyingSpaceLocalSystemMapOver k ξ` defines `MonoidHom.classifyingSpaceTwistedCohomologyMap`,
which corresponds to `groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ)`
(`MonoidHom.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality`) and respects
identities and composition.

When the underlying module of `A` is projective over `k`, a short exact sequence
`0 ⟶ N₁ ⟶ N₂ ⟶ N₃ ⟶ 0` of `k`-modules gives a long exact sequence of twisted cohomology groups
`Hⁿ(BG; A, Nᵢ)` and one of group cohomology groups `Hⁿ(G, Homₖ(A, Nᵢ))`, and the identification
carries the connecting map of the first, the Bockstein homomorphism
`TauCeti.LocalCoefficientSystem.twistedCohomologyBockstein`, to Mathlib's `groupCohomology.δ`
(`TauCeti.twistedCohomologyBockstein_comp_classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom`).
Together with the naturality in the module of values, the identification is an isomorphism of
long exact sequences.

## Main definitions

* `TauCeti.classifyingSpaceLocalSystem`: the local coefficient system on `classifyingSpace G`
  associated to a representation of `G`.
* `TauCeti.classifyingSpaceLocalSystemMap`: the morphism of local systems induced by a morphism
  of representations.
* `MonoidHom.classifyingSpaceLocalSystemMapOver`: the map of local systems over the map of
  classifying spaces induced by a group homomorphism and a compatible coefficient map.
* `MonoidHom.classifyingSpaceLocalSystemPullbackIso`: the isomorphism identifying the pullback of
  `classifyingSpaceLocalSystem k D` along `φ.classifyingSpaceMap` with
  `classifyingSpaceLocalSystem k (Rep.res φ D)`.
* `MonoidHom.classifyingSpaceTwistedHomologyMap`: the resulting geometric change-of-group map
  on twisted homology.
* `MonoidHom.classifyingSpaceCohomologyMap`: the resulting geometric change-of-group map on direct
  local-coefficient cohomology.
* `MonoidHom.classifyingSpaceTwistedCohomologyMap`: the resulting geometric change-of-group map
  on twisted cohomology with values in a fixed module `N`.
* `TauCeti.classifyingSpaceLocalSystemFunctor`: the associated local systems as a functor of the
  representation.
* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(BG; A) ≅ Hₙ(G, A)`.
* `TauCeti.classifyingSpaceCohomologyIsoGroupCohomology`: the direct cohomology isomorphism
  `Hⁿ(BG; A) ≅ Hⁿ(G, A)`.
* `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`: the dual-coefficient isomorphism
  `Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

## Main results

* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`,
  `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality`: the isomorphism is
  natural in the coefficients.
* `MonoidHom.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`,
  `MonoidHom.classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality`,
  `MonoidHom.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_pullback`: naturality in the
  group and compatible coefficient maps.
* `MonoidHom.classifyingSpaceTwistedHomologyMap_id`,
  `MonoidHom.classifyingSpaceTwistedHomologyMap_comp`: the geometric homology maps respect
  identities and composition.
* `MonoidHom.classifyingSpaceTwistedHomologyMap_id_hom`: for the identity group homomorphism,
  the geometric homology map is the existing coefficient-change map.
* `TauCeti.shortExact_map_classifyingSpaceLocalSystemFunctor`,
  `TauCeti.twistedHomologyδ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_hom`,
  `TauCeti.groupHomology_δ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_inv`: the
  isomorphism carries the coefficient connecting map of homology with local coefficients to the
  connecting map of group homology.
* `TauCeti.classifyingSpaceCohomologyIsoGroupCohomology_def`,
  `TauCeti.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality`,
  `TauCeti.classifyingSpaceCohomologyIsoGroupCohomology_inv_naturality`: the direct cohomology
  isomorphism specializes `IsQuotientCoveringMap.cohomologyIsoGroupCohomology` and is covariantly
  natural in the representation.
* `TauCeti.cohomologyδ_comp_classifyingSpaceCohomologyIsoGroupCohomology_hom`,
  `TauCeti.groupCohomology_δ_comp_classifyingSpaceCohomologyIsoGroupCohomology_inv`: for any short
  exact sequence of representations, the direct cohomology isomorphism carries `cohomologyδ` to
  `groupCohomology.δ`.
* `MonoidHom.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality`,
  `MonoidHom.classifyingSpaceCohomologyIsoGroupCohomology_inv_naturality`,
  `MonoidHom.classifyingSpaceCohomologyIsoGroupCohomology_hom_pullback`,
  `MonoidHom.classifyingSpaceCohomologyIsoGroupCohomology_inv_pullback`: naturality of the direct
  cohomology isomorphism in the group and compatible coefficients.
* `MonoidHom.classifyingSpaceLocalSystemPullbackIso_def`,
  `MonoidHom.classifyingSpaceCohomologyMap_eq_associatedCohomologyMap`: specialization of
  `IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso` and
  `IsQuotientCoveringMap.associatedCohomologyMap` to `isQuotientCoveringMap_classifyingSpaceProj`.
* `MonoidHom.classifyingSpaceCohomologyMap_naturality`,
  `MonoidHom.cohomologyδ_comp_classifyingSpaceCohomologyMap`,
  `MonoidHom.classifyingSpaceCohomologyMap_id`,
  `MonoidHom.classifyingSpaceCohomologyMap_comp`,
  `MonoidHom.classifyingSpaceCohomologyMap_id_hom`: coefficient naturality, connecting-map
  compatibility, and functoriality of `MonoidHom.classifyingSpaceCohomologyMap`.
* `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left`,
  `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_right`: the
  dual-coefficient cohomological isomorphism is natural in the representation and in the module of
  values.
* `MonoidHom.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality`,
  `MonoidHom.classifyingSpaceTwistedCohomologyIsoGroupCohomology_inv_naturality`,
  `MonoidHom.classifyingSpaceTwistedCohomologyIsoGroupCohomology_inv_pullback`: the dual-coefficient
  cohomological isomorphism is natural in the group and compatible coefficients.
* `MonoidHom.classifyingSpaceTwistedCohomologyMap_id`,
  `MonoidHom.classifyingSpaceTwistedCohomologyMap_comp`,
  `MonoidHom.classifyingSpaceTwistedCohomologyMap_id_hom`: functoriality of the geometric
  twisted-cohomology maps.
* `TauCeti.twistedCohomologyBockstein_comp_classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom`:
  for `k`-projective `A`, it carries the Bockstein homomorphism of twisted cohomology to the
  connecting map of group cohomology.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4, III.1, and III.8.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory TauCeti.LocalCoefficientSystem

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] {G : Type u} [Group G] (A : Rep.{u} k G)

/-- The local coefficient system on Milnor's classifying space associated to a representation `A`
of `G`: its fibre over `x` is `(A ⊗ k[π⁻¹ x])_G`, where `π` is the orbit map of the countable join,
and transport along a path is induced by lifting it to the countable join. -/
abbrev classifyingSpaceLocalSystem : LocalCoefficientSystem k (TopCat.of (classifyingSpace G)) :=
  IsQuotientCoveringMap.associatedLocalSystem (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k A

/-- **The homology of the classifying space with local coefficients is group homology**: for
every group `G` and every representation `A` of `G` over a commutative ring `k`, the homology
`Hₙ(BG; A)` of Milnor's classifying space with coefficients in the local system associated to `A`
is Mathlib's group homology `Hₙ(G, A)`. It comes from the free resolution of `k` by the singular
chains of `universalGSpace G`. -/
def classifyingSpaceTwistedHomologyIsoGroupHomology (n : ℕ) :
    twistedHomology.{u, u, u} (classifyingSpaceLocalSystem k A) n ≅ groupHomology A n :=
  IsQuotientCoveringMap.twistedHomologyIsoGroupHomology (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k A n

/-- **The cohomology of the classifying space with local coefficients in a representation is group
cohomology**: for every group `G` and every representation `A` of `G` over a commutative ring `k`,
the direct cohomology `Hⁿ(BG; A)` of Milnor's classifying space with coefficients in the local
system associated to `A` is Mathlib's group cohomology `Hⁿ(G, A)` of `A` itself. It comes from the
free resolution of `k` by the singular chains of `universalGSpace G`. -/
def classifyingSpaceCohomologyIsoGroupCohomology (n : ℕ) :
    (classifyingSpaceLocalSystem k A).cohomology n ≅ groupCohomology A n :=
  IsQuotientCoveringMap.cohomologyIsoGroupCohomology (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k A n

/-- `classifyingSpaceCohomologyIsoGroupCohomology` specializes
`IsQuotientCoveringMap.cohomologyIsoGroupCohomology` to
`isQuotientCoveringMap_classifyingSpaceProj`. -/
theorem classifyingSpaceCohomologyIsoGroupCohomology_def (n : ℕ) :
    classifyingSpaceCohomologyIsoGroupCohomology k A n =
      IsQuotientCoveringMap.cohomologyIsoGroupCohomology (E := TopCat.of (universalGSpace G))
        (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
        (isQuotientCoveringMap_classifyingSpaceProj G) k A n :=
  (rfl)

variable (N : Type u) [AddCommGroup N] [Module k N]

/-- **The cohomology of the classifying space with local coefficients is group cohomology**: for
every group `G`, every representation `A` of `G` over a commutative ring `k` and every `k`-module
`N`, the cohomology `Hⁿ(BG; A, N)` of Milnor's classifying space with coefficients in the local
system associated to `A` and values in `N` is Mathlib's group cohomology `Hⁿ(G, Homₖ(A, N))` of
the internal hom into the trivial representation `N`. It comes from the free resolution of `k` by
the singular chains of `universalGSpace G`. -/
def classifyingSpaceTwistedCohomologyIsoGroupCohomology (n : ℕ) :
    (classifyingSpaceLocalSystem k A).twistedCohomology k (ModuleCat.of k N) n ≅
      groupCohomology ((Rep.ihom A).obj (Rep.trivial k G N)) n :=
  IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k A N n

variable {k A} {A' : Rep.{u} k G}

/-- The morphism of local coefficient systems on Milnor's classifying space induced by a morphism
of representations `f : A ⟶ A'`: on the fibre over `x` it is the map
`(A ⊗ k[π⁻¹ x])_G ⟶ (A' ⊗ k[π⁻¹ x])_G` induced by `f`. -/
abbrev classifyingSpaceLocalSystemMap (f : A ⟶ A') :
    classifyingSpaceLocalSystem k A ⟶ classifyingSpaceLocalSystem k A' :=
  IsQuotientCoveringMap.associatedLocalSystemMap (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k f

/-- **The homology of the classifying space with local coefficients is naturally group
homology**: for a morphism of representations `f : A ⟶ A'`, the identifications
`Hₙ(BG; A) ≅ Hₙ(G, A)` and `Hₙ(BG; A') ≅ Hₙ(G, A')` carry the map on twisted homology induced by
`TauCeti.classifyingSpaceLocalSystemMap k f` to Mathlib's map
`groupHomology.map (MonoidHom.id G) f`. -/
@[reassoc]
theorem classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality (f : A ⟶ A') (n : ℕ) :
    twistedHomologyCoefficientMap.{u, u, u} (classifyingSpaceLocalSystemMap f) n ≫
        (classifyingSpaceTwistedHomologyIsoGroupHomology k A' n).hom =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k A n).hom ≫
        groupHomology.map (MonoidHom.id G) f n :=
  IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k f n

/-- The inverse identification of group homology with the homology of the classifying space with
local coefficients is natural in the coefficients. -/
@[reassoc]
theorem classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality (f : A ⟶ A') (n : ℕ) :
    groupHomology.map (MonoidHom.id G) f n ≫
        (classifyingSpaceTwistedHomologyIsoGroupHomology k A' n).inv =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k A n).inv ≫
        twistedHomologyCoefficientMap.{u, u, u} (classifyingSpaceLocalSystemMap f) n :=
  IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_inv_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k f n

/-- **The direct cohomology of the classifying space with local coefficients is naturally group
cohomology**: for a morphism of representations `f : A ⟶ A'`, the identifications
`Hⁿ(BG; A) ≅ Hⁿ(G, A)` and `Hⁿ(BG; A') ≅ Hⁿ(G, A')` carry the map on cohomology induced by
`TauCeti.classifyingSpaceLocalSystemMap f` to Mathlib's map
`groupCohomology.map (MonoidHom.id G) f`. -/
@[reassoc]
theorem classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality (f : A ⟶ A') (n : ℕ) :
    cohomologyCoefficientMap (classifyingSpaceLocalSystemMap f) n ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k A' n).hom =
      (classifyingSpaceCohomologyIsoGroupCohomology k A n).hom ≫
        groupCohomology.map (MonoidHom.id G) f n :=
  IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k f n

/-- The inverse identification of group cohomology with the direct local-coefficient cohomology of
the classifying space is covariantly natural in the representation. -/
@[reassoc]
theorem classifyingSpaceCohomologyIsoGroupCohomology_inv_naturality (f : A ⟶ A') (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k A' n).inv =
      (classifyingSpaceCohomologyIsoGroupCohomology k A n).inv ≫
        cohomologyCoefficientMap (classifyingSpaceLocalSystemMap f) n :=
  IsQuotientCoveringMap.cohomologyIsoGroupCohomology_inv_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k f n

variable (k G) in
/-- The local coefficient systems on Milnor's classifying space associated to representations of
`G`, as a functor of the representation: it sends `A` to `TauCeti.classifyingSpaceLocalSystem k A`
and a morphism `f` to `TauCeti.classifyingSpaceLocalSystemMap f`. -/
abbrev classifyingSpaceLocalSystemFunctor :
    Rep.{u} k G ⥤ LocalCoefficientSystem k (TopCat.of (classifyingSpace G)) :=
  IsQuotientCoveringMap.associatedLocalSystemFunctor (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k

-- Instance search does not find the general instance at this quotient covering map, whose
-- spaces are bundled with `TopCat.of`, so it is supplied directly.
instance : (classifyingSpaceLocalSystemFunctor k G).Additive :=
  IsQuotientCoveringMap.additive_associatedLocalSystemFunctor _ k

-- With the concrete Milnor source and target, instance search does not recover the bundled
-- covering from its underlying map. Delegate to the generic construction with that data fixed.
open _root_.IsQuotientCoveringMap in
instance : Limits.PreservesFiniteLimits (classifyingSpaceLocalSystemFunctor k G) := by
  have := instPreservesLimitsOfSizeRepLocalCoefficientSystemAssociatedLocalSystemFunctor
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
  infer_instance

open _root_.IsQuotientCoveringMap in
instance : Limits.PreservesFiniteColimits (classifyingSpaceLocalSystemFunctor k G) := by
  have := instPreservesColimitsOfSizeRepLocalCoefficientSystemAssociatedLocalSystemFunctor
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
  infer_instance

variable {X : ShortComplex (Rep.{u} k G)}

/-- A short exact sequence of representations of `G` gives a short exact sequence of the
associated local coefficient systems on Milnor's classifying space. -/
theorem shortExact_map_classifyingSpaceLocalSystemFunctor (hX : X.ShortExact) :
    (X.map (classifyingSpaceLocalSystemFunctor k G)).ShortExact :=
  IsQuotientCoveringMap.shortExact_associatedLocalSystem
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k hX

/-- **The homology of the classifying space with local coefficients respects the long exact
sequences**: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations of `G`, the
identifications `Hₙ(BG; Xᵢ) ≅ Hₙ(G, Xᵢ)` carry the coefficient connecting map
`Hₙ(BG; X₃) ⟶ Hₘ(BG; X₁)`, `m + 1 = n`, of the short exact sequence of associated local systems to
Mathlib's connecting map `groupHomology.δ`. -/
@[reassoc]
theorem twistedHomologyδ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_hom
    (hX : X.ShortExact) (n m : ℕ) (h : m + 1 = n) :
    (shortExact_map_classifyingSpaceLocalSystemFunctor hX).twistedHomologyδ n m h ≫
        (classifyingSpaceTwistedHomologyIsoGroupHomology k X.X₁ m).hom =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k X.X₃ n).hom ≫
        groupHomology.δ hX n m h :=
  IsQuotientCoveringMap.twistedHomologyδ_comp_twistedHomologyIsoGroupHomology_hom
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k hX n m h

/-- **The homology of the classifying space with local coefficients respects the long exact
sequences**, inverse form: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations
of `G`, the inverses of the identifications `Hₙ(BG; Xᵢ) ≅ Hₙ(G, Xᵢ)` carry Mathlib's connecting
map `groupHomology.δ` to the coefficient connecting map of the short exact sequence of associated
local systems. -/
@[reassoc]
theorem groupHomology_δ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_inv
    (hX : X.ShortExact) (n m : ℕ) (h : m + 1 = n) :
    groupHomology.δ hX n m h ≫ (classifyingSpaceTwistedHomologyIsoGroupHomology k X.X₁ m).inv =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k X.X₃ n).inv ≫
        (shortExact_map_classifyingSpaceLocalSystemFunctor hX).twistedHomologyδ n m h :=
  IsQuotientCoveringMap.groupHomology_δ_comp_twistedHomologyIsoGroupHomology_inv
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k hX n m h

/-- **The direct cohomology of the classifying space with local coefficients respects the
coefficient long exact sequences**: for any short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
representations of `G` (with no projectivity or flatness assumption), the identifications
`Hⁿ(BG; Xᵢ) ≅ Hⁿ(G, Xᵢ)` carry the geometric connecting map `cohomologyδ` of the associated short
exact sequence of local systems to Mathlib's `groupCohomology.δ`. -/
@[reassoc]
theorem cohomologyδ_comp_classifyingSpaceCohomologyIsoGroupCohomology_hom
    (hX : X.ShortExact) (n m : ℕ) (h : n + 1 = m := by lia) :
    (shortExact_map_classifyingSpaceLocalSystemFunctor hX).cohomologyδ n m h ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k X.X₁ m).hom =
      (classifyingSpaceCohomologyIsoGroupCohomology k X.X₃ n).hom ≫
        groupCohomology.δ hX n m h :=
  IsQuotientCoveringMap.cohomologyδ_comp_cohomologyIsoGroupCohomology_hom
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k hX n m h

/-- **The direct cohomology of the classifying space with local coefficients respects the
coefficient long exact sequences**, inverse form: for any short exact sequence of representations of
`G`, the inverses of `Hⁿ(BG; Xᵢ) ≅ Hⁿ(G, Xᵢ)` carry `groupCohomology.δ` to `cohomologyδ`. -/
@[reassoc]
theorem groupCohomology_δ_comp_classifyingSpaceCohomologyIsoGroupCohomology_inv
    (hX : X.ShortExact) (n m : ℕ) (h : n + 1 = m := by lia) :
    groupCohomology.δ hX n m h ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k X.X₁ m).inv =
      (classifyingSpaceCohomologyIsoGroupCohomology k X.X₃ n).inv ≫
        (shortExact_map_classifyingSpaceLocalSystemFunctor hX).cohomologyδ n m h :=
  IsQuotientCoveringMap.groupCohomology_δ_comp_cohomologyIsoGroupCohomology_inv
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k hX n m h

/-- **The cohomology of the classifying space with local coefficients is naturally group
cohomology, in the representation**: for a morphism of representations `f : A ⟶ A'`, the
identifications `Hⁿ(BG; A', N) ≅ Hⁿ(G, Homₖ(A', N))` and `Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))` carry
the map on twisted cohomology induced by `TauCeti.classifyingSpaceLocalSystemMap f` to Mathlib's
map `groupCohomology.map (MonoidHom.id G)` induced by precomposition with `f`,
`Homₖ(A', N) ⟶ Homₖ(A, N)`. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left (f : A ⟶ A')
    (n : ℕ) :
    twistedCohomologyCoefficientMap k (ModuleCat.of k N) (classifyingSpaceLocalSystemMap f) n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A' N n).hom ≫
        groupCohomology.map (MonoidHom.id G) ((MonoidalClosed.pre f).app (Rep.trivial k G N)) n :=
  IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_left
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k N f n

variable (A) {N} {N' : Type u} [AddCommGroup N'] [Module k N']

/-- **The cohomology of the classifying space with local coefficients is naturally group
cohomology, in the module of values**: for a `k`-linear map `g : N →ₗ[k] N'`, the identifications
`Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))` and `Hⁿ(BG; A, N') ≅ Hⁿ(G, Homₖ(A, N'))` carry the map on
twisted cohomology given by postcomposing cochains with `g` to Mathlib's map
`groupCohomology.map (MonoidHom.id G)` induced by the map `Homₖ(A, N) ⟶ Homₖ(A, N')` of internal
homs. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_right
    (g : N →ₗ[k] N') (n : ℕ) :
    HomologicalComplex.homologyMap ((classifyingSpaceLocalSystem k A).twistedChainComplex
        |>.linearYonedaObjMap k (ModuleCat.ofHom g)) n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N' n).hom =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom ≫
        groupCohomology.map (MonoidHom.id G)
          ((Rep.ihom A).map ((Rep.trivialFunctor k G).map (ModuleCat.ofHom g))) n :=
  IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_right
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k A N g n

/-- The fibres of the local system on the classifying space associated to a representation whose
underlying module is projective over `k` are projective. -/
-- Instance search does not find `IsQuotientCoveringMap.projective_associatedLocalSystem_obj`
-- through the abbreviation `classifyingSpaceLocalSystem`, whose quotient covering is bundled with
-- `TopCat.of`, so the instance is registered for the abbreviation as well.
instance [Module.Projective k A] (x : FundamentalGroupoid (TopCat.of (classifyingSpace G))) :
    Projective ((classifyingSpaceLocalSystem k A).obj x) :=
  IsQuotientCoveringMap.projective_associatedLocalSystem_obj _ k A x

/-- **The cohomology of the classifying space with local coefficients is group cohomology,
compatibly with the long exact sequences in the module of values**: for a representation `A` of
`G` whose underlying module is projective over `k` and a short exact sequence
`0 ⟶ N₁ ⟶ N₂ ⟶ N₃ ⟶ 0` of `k`-modules, the identifications `Hⁿ(BG; A, Nᵢ) ≅ Hⁿ(G, Homₖ(A, Nᵢ))`
carry the Bockstein homomorphism `Hⁿ(BG; A, N₃) ⟶ Hᵐ(BG; A, N₁)`, `n + 1 = m`, of twisted
cohomology to Mathlib's connecting map `groupCohomology.δ` of the short exact sequence of
representations `0 ⟶ Homₖ(A, N₁) ⟶ Homₖ(A, N₂) ⟶ Homₖ(A, N₃) ⟶ 0`. -/
@[reassoc]
theorem twistedCohomologyBockstein_comp_classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom
    [Module.Projective k A] {S : ShortComplex (ModuleCat.{u} k)} (hS : S.ShortExact) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    twistedCohomologyBockstein.{u, u, u, u} k (classifyingSpaceLocalSystem k A) hS n m h ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A S.X₁ m).hom =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A S.X₃ n).hom ≫
        groupCohomology.δ (Rep.shortExact_map_ihom A (Rep.shortExact_map_trivialFunctor hS))
          n m h :=
  IsQuotientCoveringMap.twistedCohomologyBockstein_comp_twistedCohomologyIsoGroupCohomology_hom
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k A hS n m h

end TauCeti

namespace MonoidHom

open TauCeti

universe u

variable {G H K : Type u} [Group G] [Group H] [Group K]
  (φ : G →* H) (k : Type u) [CommRing k]
  {A : Rep.{u} k G} {D : Rep.{u} k H}

/-- A group homomorphism and a compatible coefficient map induce a map from the associated
local system on `BG` to the pullback of the associated local system on `BH`. -/
abbrev classifyingSpaceLocalSystemMapOver (ξ : A ⟶ Rep.res φ D) :
    classifyingSpaceLocalSystem k A ⟶
      (LocalCoefficientSystem.pullback φ.classifyingSpaceMap).obj
        (classifyingSpaceLocalSystem k D) :=
  (isQuotientCoveringMap_classifyingSpaceProj G).associatedLocalSystemMapOver k
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ

/-- **Pullback of associated local systems on classifying spaces**: pulling the local coefficient
system on `BH` associated to an `H`-representation `D` back along `MonoidHom.classifyingSpaceMap φ`
identifies it canonically with the local coefficient system on `BG` associated to the restricted
representation `Rep.res φ D`. -/
def classifyingSpaceLocalSystemPullbackIso (D : Rep.{u} k H) :
    classifyingSpaceLocalSystem k (Rep.res φ D) ≅
      (LocalCoefficientSystem.pullback φ.classifyingSpaceMap).obj
        (classifyingSpaceLocalSystem k D) :=
  IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D

/-- `classifyingSpaceLocalSystemPullbackIso` specializes
`IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso` to
`isQuotientCoveringMap_classifyingSpaceProj`. -/
theorem classifyingSpaceLocalSystemPullbackIso_def (D : Rep.{u} k H) :
    φ.classifyingSpaceLocalSystemPullbackIso k D =
      IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso
        (E := TopCat.of (universalGSpace G))
        (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
        (isQuotientCoveringMap_classifyingSpaceProj G) k
        (F := TopCat.of (universalGSpace H))
        (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
        (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
        (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
        (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D :=
  (rfl)

/-- The forward morphism of `classifyingSpaceLocalSystemPullbackIso` is
`classifyingSpaceLocalSystemMapOver` for the identity of `Rep.res φ D`. -/
@[simp]
theorem classifyingSpaceLocalSystemPullbackIso_hom (D : Rep.{u} k H) :
    (φ.classifyingSpaceLocalSystemPullbackIso k D).hom =
      φ.classifyingSpaceLocalSystemMapOver k (𝟙 (Rep.res φ D)) :=
  IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso_hom
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D

/-- Every change-of-groups morphism of classifying-space local systems factors as the fixed-group
coefficient morphism `classifyingSpaceLocalSystemMap ξ` followed by
`classifyingSpaceLocalSystemPullbackIso`. -/
theorem classifyingSpaceLocalSystemMapOver_eq (ξ : A ⟶ Rep.res φ D) :
    φ.classifyingSpaceLocalSystemMapOver k ξ =
      classifyingSpaceLocalSystemMap ξ ≫ (φ.classifyingSpaceLocalSystemPullbackIso k D).hom :=
  IsQuotientCoveringMap.associatedLocalSystemMapOver_eq
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ

/-- The geometric change-of-group map `Hₙ(BG; A) ⟶ Hₙ(BH; D)`: change coefficients by `ξ`
and then push forward along the strictly functorial map of classifying spaces. -/
def classifyingSpaceTwistedHomologyMap (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    twistedHomology.{u, u, u} (classifyingSpaceLocalSystem k A) n ⟶
      twistedHomology.{u, u, u} (classifyingSpaceLocalSystem k D) n :=
  twistedHomologyCoefficientMap (φ.classifyingSpaceLocalSystemMapOver k ξ) n ≫
    twistedHomologyMap (TopCat.ofHom φ.classifyingSpaceMap) (classifyingSpaceLocalSystem k D) n

/-- The geometric change-of-group map is coefficient change followed by pushforward. -/
theorem classifyingSpaceTwistedHomologyMap_def (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    φ.classifyingSpaceTwistedHomologyMap k ξ n =
      twistedHomologyCoefficientMap (φ.classifyingSpaceLocalSystemMapOver k ξ) n ≫
        twistedHomologyMap (TopCat.ofHom φ.classifyingSpaceMap)
          (classifyingSpaceLocalSystem k D) n :=
  (rfl)

/-- **The local-coefficient homology comparison is natural in the group.** The geometric map
induced by `φ` and `ξ` corresponds to Mathlib's change-of-group map `groupHomology.map φ ξ`.
In particular this applies to restriction of any `H`-module along any homomorphism `G →* H`. -/
@[reassoc]
theorem classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    φ.classifyingSpaceTwistedHomologyMap k ξ n ≫
        (classifyingSpaceTwistedHomologyIsoGroupHomology k D n).hom =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k A n).hom ≫ groupHomology.map φ ξ n := by
  have h := IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_naturality_over
      (E := TopCat.of (universalGSpace G))
      (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
      (F := TopCat.of (universalGSpace H))
      (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
      (isQuotientCoveringMap_classifyingSpaceProj G)
      (isQuotientCoveringMap_classifyingSpaceProj H) k (TopCat.ofHom φ.universalGSpaceMap)
      (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
      (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ n
  rw [IsQuotientCoveringMap.associatedTwistedChainMap_def,
    HomologicalComplex.homologyMap_comp] at h
  rw [classifyingSpaceTwistedHomologyMap_def]
  -- The coefficient-change and pushforward homology maps are abbreviations for `homologyMap`;
  -- the local system and comparison specialize those of the quotient cover of Milnor's model.
  exact h

/-- The inverse local-coefficient homology comparison is also natural in the group. -/
@[reassoc]
theorem classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    groupHomology.map φ ξ n ≫ (classifyingSpaceTwistedHomologyIsoGroupHomology k D n).inv =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k A n).inv ≫
        φ.classifyingSpaceTwistedHomologyMap k ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality, Iso.inv_hom_id_assoc]

/-- Pushing twisted homology forward along `MonoidHom.classifyingSpaceMap φ` from the pulled-back
local system `(φ.classifyingSpaceMap)^* L_D` corresponds, via
`MonoidHom.classifyingSpaceLocalSystemPullbackIso`, to `groupHomology.map φ (𝟙 (Rep.res φ D))`. -/
@[reassoc]
theorem classifyingSpaceTwistedHomologyIsoGroupHomology_hom_pullback (D : Rep.{u} k H) (n : ℕ) :
    twistedHomologyMap.{u, u, u} (TopCat.ofHom φ.classifyingSpaceMap)
        (classifyingSpaceLocalSystem k D) n ≫
      (classifyingSpaceTwistedHomologyIsoGroupHomology k D n).hom =
      twistedHomologyCoefficientMap.{u, u, u}
          (φ.classifyingSpaceLocalSystemPullbackIso k D).inv n ≫
        (classifyingSpaceTwistedHomologyIsoGroupHomology k (Rep.res φ D) n).hom ≫
        groupHomology.map φ (𝟙 (Rep.res φ D)) n :=
  IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_pullback
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G)
    (isQuotientCoveringMap_classifyingSpaceProj H) k (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D n

/-- The geometric change-of-group map `Hⁿ(BH; D, N) ⟶ Hⁿ(BG; A, N)` on twisted cohomology: pull
back along the strictly functorial map of classifying spaces and then change coefficients by `ξ`. -/
def classifyingSpaceTwistedCohomologyMap (N : Type u) [AddCommGroup N] [Module k N]
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    (classifyingSpaceLocalSystem k D).twistedCohomology k (ModuleCat.of k N) n ⟶
      (classifyingSpaceLocalSystem k A).twistedCohomology k (ModuleCat.of k N) n :=
  twistedCohomologyMap k (ModuleCat.of k N) (TopCat.ofHom φ.classifyingSpaceMap)
      (classifyingSpaceLocalSystem k D) n ≫
    twistedCohomologyCoefficientMap k (ModuleCat.of k N)
      (φ.classifyingSpaceLocalSystemMapOver k ξ) n

/-- The geometric change-of-group map on twisted cohomology is pullback followed by coefficient
change. -/
theorem classifyingSpaceTwistedCohomologyMap_def (N : Type u) [AddCommGroup N] [Module k N]
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    φ.classifyingSpaceTwistedCohomologyMap k N ξ n =
      twistedCohomologyMap k (ModuleCat.of k N) (TopCat.ofHom φ.classifyingSpaceMap)
          (classifyingSpaceLocalSystem k D) n ≫
        twistedCohomologyCoefficientMap k (ModuleCat.of k N)
          (φ.classifyingSpaceLocalSystemMapOver k ξ) n :=
  (rfl)

/-- **The local-coefficient cohomology comparison is natural in the group.** The geometric map
induced by `φ` and `ξ` corresponds to Mathlib's change-of-group map
`groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ)`. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality
    (N : Type u) [AddCommGroup N] [Module k N] (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    φ.classifyingSpaceTwistedCohomologyMap k N ξ n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k D N n).hom ≫
        groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n := by
  rw [classifyingSpaceTwistedCohomologyMap_def, Category.assoc]
  exact IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_over
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k N
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ n

/-- The inverse local-coefficient cohomology comparison is also natural in the group. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_inv_naturality
    (N : Type u) [AddCommGroup N] [Module k N] (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).inv =
      (classifyingSpaceTwistedCohomologyIsoGroupCohomology k D N n).inv ≫
        φ.classifyingSpaceTwistedCohomologyMap k N ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality, Iso.inv_hom_id_assoc]

/-- Pulling twisted cohomology back along `MonoidHom.classifyingSpaceMap φ` corresponds, via
`MonoidHom.classifyingSpaceLocalSystemPullbackIso`, to
`groupCohomology.map φ (φ.ihomTrivialPrecomp N (𝟙 (Rep.res φ D)))`. -/
@[reassoc]
theorem classifyingSpaceTwistedCohomologyIsoGroupCohomology_inv_pullback
    (D : Rep.{u} k H) (N : Type u) [AddCommGroup N] [Module k N] (n : ℕ) :
    (classifyingSpaceTwistedCohomologyIsoGroupCohomology k D N n).inv ≫
        twistedCohomologyMap k (ModuleCat.of k N) (TopCat.ofHom φ.classifyingSpaceMap)
          (classifyingSpaceLocalSystem k D) n =
      groupCohomology.map φ (φ.ihomTrivialPrecomp N (𝟙 (Rep.res φ D))) n ≫
        (classifyingSpaceTwistedCohomologyIsoGroupCohomology k (Rep.res φ D) N n).inv ≫
        twistedCohomologyCoefficientMap k (ModuleCat.of k N)
          (φ.classifyingSpaceLocalSystemPullbackIso k D).inv n :=
  IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_inv_pullback
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k N
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D n

/-- The geometric change-of-group map `Hⁿ(BH; D) ⟶ Hⁿ(BG; A)` on direct local-coefficient
cohomology: pull cohomology back along `MonoidHom.classifyingSpaceMap φ`, identify the pulled-back
local system with `classifyingSpaceLocalSystem k (Rep.res φ D)`, and apply `ξ`. -/
def classifyingSpaceCohomologyMap (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    (classifyingSpaceLocalSystem k D).cohomology n ⟶
      (classifyingSpaceLocalSystem k A).cohomology n :=
  cohomologyPullback (TopCat.ofHom φ.classifyingSpaceMap) (classifyingSpaceLocalSystem k D) n ≫
    cohomologyCoefficientMap
      ((φ.classifyingSpaceLocalSystemPullbackIso k D).inv ≫ classifyingSpaceLocalSystemMap ξ) n

/-- The geometric change-of-group map on direct cohomology is pullback along
`φ.classifyingSpaceMap` followed by the base-change and coefficient maps of local systems. -/
theorem classifyingSpaceCohomologyMap_def (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    φ.classifyingSpaceCohomologyMap k ξ n =
      cohomologyPullback (TopCat.ofHom φ.classifyingSpaceMap)
          (classifyingSpaceLocalSystem k D) n ≫
        cohomologyCoefficientMap
          ((φ.classifyingSpaceLocalSystemPullbackIso k D).inv ≫
            classifyingSpaceLocalSystemMap ξ) n :=
  (rfl)

/-- `classifyingSpaceCohomologyMap` specializes `IsQuotientCoveringMap.associatedCohomologyMap` to
`isQuotientCoveringMap_classifyingSpaceProj`. -/
theorem classifyingSpaceCohomologyMap_eq_associatedCohomologyMap
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    φ.classifyingSpaceCohomologyMap k ξ n =
      IsQuotientCoveringMap.associatedCohomologyMap
        (E := TopCat.of (universalGSpace G))
        (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
        (isQuotientCoveringMap_classifyingSpaceProj G) k
        (F := TopCat.of (universalGSpace H))
        (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
        (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
        (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
        (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ n := by
  rw [classifyingSpaceCohomologyMap_def, IsQuotientCoveringMap.associatedCohomologyMap_def,
    classifyingSpaceLocalSystemPullbackIso_def]

/-- **The direct local-coefficient cohomology comparison is natural in the group.** The geometric
map induced by `φ : G →* H` and `ξ : Rep.res φ D ⟶ A` corresponds to Mathlib's change-of-group map
`groupCohomology.map φ ξ`. -/
@[reassoc]
theorem classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    φ.classifyingSpaceCohomologyMap k ξ n ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k A n).hom =
      (classifyingSpaceCohomologyIsoGroupCohomology k D n).hom ≫
        groupCohomology.map φ ξ n := by
  rw [classifyingSpaceCohomologyMap_eq_associatedCohomologyMap]
  exact IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality_over
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) ξ n

/-- The inverse direct local-coefficient cohomology comparison is also natural in the group. -/
@[reassoc]
theorem classifyingSpaceCohomologyIsoGroupCohomology_inv_naturality
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    groupCohomology.map φ ξ n ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k A n).inv =
      (classifyingSpaceCohomologyIsoGroupCohomology k D n).inv ≫
        φ.classifyingSpaceCohomologyMap k ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality, Iso.inv_hom_id_assoc]

/-- Pulling direct cohomology back along `MonoidHom.classifyingSpaceMap φ` corresponds, via
`MonoidHom.classifyingSpaceLocalSystemPullbackIso`, to `groupCohomology.map φ (𝟙 (Rep.res φ D))`. -/
@[reassoc]
theorem classifyingSpaceCohomologyIsoGroupCohomology_hom_pullback (D : Rep.{u} k H) (n : ℕ) :
    cohomologyPullback (TopCat.ofHom φ.classifyingSpaceMap) (classifyingSpaceLocalSystem k D) n ≫
        cohomologyCoefficientMap (φ.classifyingSpaceLocalSystemPullbackIso k D).inv n ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k (Rep.res φ D) n).hom =
      (classifyingSpaceCohomologyIsoGroupCohomology k D n).hom ≫
        groupCohomology.map φ (𝟙 (Rep.res φ D)) n :=
  IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_pullback
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D n

/-- Inverse pullback compatibility for direct local-coefficient cohomology of classifying spaces. -/
@[reassoc]
theorem classifyingSpaceCohomologyIsoGroupCohomology_inv_pullback (D : Rep.{u} k H) (n : ℕ) :
    (classifyingSpaceCohomologyIsoGroupCohomology k D n).inv ≫
        cohomologyPullback (TopCat.ofHom φ.classifyingSpaceMap)
          (classifyingSpaceLocalSystem k D) n =
      groupCohomology.map φ (𝟙 (Rep.res φ D)) n ≫
        (classifyingSpaceCohomologyIsoGroupCohomology k (Rep.res φ D) n).inv ≫
        cohomologyCoefficientMap (φ.classifyingSpaceLocalSystemPullbackIso k D).hom n :=
  IsQuotientCoveringMap.cohomologyIsoGroupCohomology_inv_pullback
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) D n

/-- `classifyingSpaceCohomologyMap` is natural with respect to compatible morphisms of
coefficient representations: if `ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂`, then the induced maps on
direct local-coefficient cohomology commute with `cohomologyCoefficientMap`. -/
@[reassoc]
theorem classifyingSpaceCohomologyMap_naturality
    {D₁ D₂ : Rep.{u} k H} {A₁ A₂ : Rep.{u} k G}
    (β : D₁ ⟶ D₂) (α : A₁ ⟶ A₂)
    (ξ₁ : Rep.res φ D₁ ⟶ A₁) (ξ₂ : Rep.res φ D₂ ⟶ A₂)
    (hcomm : ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂) (n : ℕ) :
    cohomologyCoefficientMap (classifyingSpaceLocalSystemMap β) n ≫
        φ.classifyingSpaceCohomologyMap k ξ₂ n =
      φ.classifyingSpaceCohomologyMap k ξ₁ n ≫
        cohomologyCoefficientMap (classifyingSpaceLocalSystemMap α) n := by
  rw [classifyingSpaceCohomologyMap_eq_associatedCohomologyMap,
    classifyingSpaceCohomologyMap_eq_associatedCohomologyMap]
  exact IsQuotientCoveringMap.associatedCohomologyMap_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) β α ξ₁ ξ₂ hcomm n

/-- **The geometric connecting map of direct local-coefficient cohomology on classifying spaces
commutes with change of groups.** -/
@[reassoc]
theorem cohomologyδ_comp_classifyingSpaceCohomologyMap
    {Y : ShortComplex (Rep.{u} k H)} {X : ShortComplex (Rep.{u} k G)}
    (hY : Y.ShortExact) (hX : X.ShortExact)
    (Φ : Y.map (Rep.resFunctor φ) ⟶ X) (n m : ℕ) (h : n + 1 = m := by lia) :
    (shortExact_map_classifyingSpaceLocalSystemFunctor hY).cohomologyδ n m h ≫
        φ.classifyingSpaceCohomologyMap k Φ.τ₁ m =
      φ.classifyingSpaceCohomologyMap k Φ.τ₃ n ≫
        (shortExact_map_classifyingSpaceLocalSystemFunctor hX).cohomologyδ n m h := by
  rw [classifyingSpaceCohomologyMap_eq_associatedCohomologyMap,
    classifyingSpaceCohomologyMap_eq_associatedCohomologyMap]
  exact IsQuotientCoveringMap.cohomologyδ_comp_associatedCohomologyMap
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) (TopCat.ofHom φ.classifyingSpaceMap)
    (ConcreteCategory.hom_ext _ _ fun x ↦ φ.classifyingSpaceMap_proj x) hY hX Φ n m h

variable {k}

/-- Change of groups along the identity homomorphism is the existing coefficient-change map on
direct local-coefficient cohomology of the classifying space. -/
@[simp]
theorem classifyingSpaceCohomologyMap_id_hom {A' : Rep.{u} k G}
    (f : A ⟶ A') (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceCohomologyMap k f n =
      cohomologyCoefficientMap (classifyingSpaceLocalSystemMap f) n := by
  apply (cancel_mono (classifyingSpaceCohomologyIsoGroupCohomology k A' n).hom).1
  rw [classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality,
    TauCeti.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality]

/-- The identity homomorphism with identity coefficients induces the identity on direct
local-coefficient cohomology of the classifying space. -/
-- Match before the general identity-homomorphism rule reduces to coefficient change.
@[simp↓]
theorem classifyingSpaceCohomologyMap_id (A : Rep.{u} k G) (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceCohomologyMap k (𝟙 A) n = 𝟙 _ := by
  apply (cancel_mono (classifyingSpaceCohomologyIsoGroupCohomology k A n).hom).1
  rw [classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality,
    groupCohomology.map_id, Category.comp_id, Category.id_comp]

/-- Geometric change of groups on direct local-coefficient cohomology contravariantly respects
composition, including the induced restriction of the outer coefficient map. -/
-- Match before simplification rewrites restriction of the coefficient morphism.
@[simp↓, reassoc]
theorem classifyingSpaceCohomologyMap_comp (ψ : H →* K) {V : Rep.{u} k K}
    (ξ : Rep.res φ D ⟶ A) (ζ : Rep.res ψ V ⟶ D) (n : ℕ) :
    (ψ.comp φ).classifyingSpaceCohomologyMap k ((Rep.resFunctor φ).map ζ ≫ ξ) n =
      ψ.classifyingSpaceCohomologyMap k ζ n ≫
        φ.classifyingSpaceCohomologyMap k ξ n := by
  apply (cancel_mono (classifyingSpaceCohomologyIsoGroupCohomology k A n).hom).1
  have hs := (CommSq.mk
    (ψ.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality k ζ n)).horiz_comp
      (CommSq.mk (φ.classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality k ξ n))
  rw [classifyingSpaceCohomologyIsoGroupCohomology_hom_naturality, groupCohomology.map_comp]
  exact hs.w.symm

/-- Change of groups along the identity homomorphism is the existing coefficient-change map
on twisted homology of the classifying space. -/
@[simp]
theorem classifyingSpaceTwistedHomologyMap_id_hom {A' : Rep.{u} k G}
    (f : A ⟶ A') (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceTwistedHomologyMap k f n =
      twistedHomologyCoefficientMap (classifyingSpaceLocalSystemMap f) n := by
  apply (cancel_mono (classifyingSpaceTwistedHomologyIsoGroupHomology k A' n).hom).1
  rw [classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality,
    TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality]

/-- The identity homomorphism with identity coefficients induces the identity in twisted
homology of the classifying space. -/
-- Match before the general identity-homomorphism rule reduces to coefficient change.
@[simp↓]
theorem classifyingSpaceTwistedHomologyMap_id (A : Rep.{u} k G) (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceTwistedHomologyMap k (𝟙 A) n = 𝟙 _ := by
  apply (cancel_mono (classifyingSpaceTwistedHomologyIsoGroupHomology k A n).hom).1
  rw [classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality,
    groupHomology.map_id, Category.comp_id, Category.id_comp]

/-- Geometric change of groups on twisted homology respects composition, including the induced
restriction of the second coefficient map. -/
-- Match before simplification rewrites restriction of the coefficient morphism.
@[simp↓, reassoc]
theorem classifyingSpaceTwistedHomologyMap_comp (ψ : H →* K) {V : Rep.{u} k K}
    (ξ : A ⟶ Rep.res φ D) (ζ : D ⟶ Rep.res ψ V) (n : ℕ) :
    (ψ.comp φ).classifyingSpaceTwistedHomologyMap k (ξ ≫ (Rep.resFunctor φ).map ζ) n =
      φ.classifyingSpaceTwistedHomologyMap k ξ n ≫ ψ.classifyingSpaceTwistedHomologyMap k ζ n := by
  apply (cancel_mono (classifyingSpaceTwistedHomologyIsoGroupHomology k V n).hom).1
  have hs := (CommSq.mk
    (φ.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality k ξ n)).horiz_comp
      (CommSq.mk (ψ.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality k ζ n))
  rw [classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality, groupHomology.map_comp]
  exact hs.w.symm

/-- Change of groups along the identity homomorphism is the existing coefficient-change map
on twisted cohomology of the classifying space. -/
@[simp]
theorem classifyingSpaceTwistedCohomologyMap_id_hom {A' : Rep.{u} k G}
    (N : Type u) [AddCommGroup N] [Module k N] (f : A ⟶ A') (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceTwistedCohomologyMap k N f n =
      twistedCohomologyCoefficientMap k (ModuleCat.of k N)
        (classifyingSpaceLocalSystemMap f) n := by
  apply (cancel_mono (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom).1
  have hpre : (MonoidHom.id G).ihomTrivialPrecomp N f =
      (MonoidalClosed.pre f).app (Rep.trivial k G N) :=
    Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      LinearMap.ext fun ℓ ↦ LinearMap.ext fun a ↦
        (MonoidHom.id G).ihomTrivialPrecomp_hom_apply N f ℓ a
  rw [classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality, hpre,
    TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left]
  rfl

/-- The identity homomorphism with identity coefficients induces the identity in twisted
cohomology of the classifying space. -/
-- Match before the general identity-homomorphism rule reduces to coefficient change.
@[simp↓]
theorem classifyingSpaceTwistedCohomologyMap_id (A : Rep.{u} k G)
    (N : Type u) [AddCommGroup N] [Module k N] (n : ℕ) :
    (MonoidHom.id G).classifyingSpaceTwistedCohomologyMap k N (𝟙 A) n = 𝟙 _ := by
  apply (cancel_mono (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom).1
  rw [classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality,
    ihomTrivialPrecomp_id, groupCohomology.map_id, Category.comp_id, Category.id_comp]

/-- Geometric change of groups on twisted cohomology contravariantly respects composition,
including the induced restriction of the second coefficient map. -/
-- Match before simplification rewrites restriction of the coefficient morphism.
@[simp↓, reassoc]
theorem classifyingSpaceTwistedCohomologyMap_comp (ψ : H →* K) {V : Rep.{u} k K}
    (N : Type u) [AddCommGroup N] [Module k N]
    (ξ : A ⟶ Rep.res φ D) (ζ : D ⟶ Rep.res ψ V) (n : ℕ) :
    (ψ.comp φ).classifyingSpaceTwistedCohomologyMap k N (ξ ≫ (Rep.resFunctor φ).map ζ) n =
      ψ.classifyingSpaceTwistedCohomologyMap k N ζ n ≫
        φ.classifyingSpaceTwistedCohomologyMap k N ξ n := by
  apply (cancel_mono (classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n).hom).1
  have hs := (CommSq.mk
    (ψ.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality k N ζ n)).horiz_comp
      (CommSq.mk (φ.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality k N ξ n))
  rw [classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality,
    ihomTrivialPrecomp_comp, groupCohomology.map_comp]
  exact hs.w.symm

end MonoidHom
