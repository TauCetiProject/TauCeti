/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.GroupCohomology
public import TauCeti.AlgebraicTopology.Singular.Twisted.GroupHomology

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

The identification is natural in the coefficients: a morphism of representations `f : A ⟶ A'`
induces a morphism of local systems `TauCeti.classifyingSpaceLocalSystemMap k f`, and the induced
map `Hₙ(BG; A) ⟶ Hₙ(BG; A')` corresponds to Mathlib's map `groupHomology.map (MonoidHom.id G) f`
(`TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`).

It also respects the coefficient long exact sequences. The associated local systems form an exact
functor `TauCeti.classifyingSpaceLocalSystemFunctor k G` of the representation, so a short exact
sequence `0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` of representations gives a short exact sequence of local
systems on `BG` (`TauCeti.shortExact_map_classifyingSpaceLocalSystemFunctor`) and a long exact
sequence in homology with local coefficients. Its connecting map `Hₙ(BG; A₃) ⟶ Hₘ(BG; A₁)`,
`m + 1 = n`, corresponds to Mathlib's connecting map `groupHomology.δ`
(`TauCeti.twistedHomologyδ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_hom`). Together
with the naturality in the coefficients, this identifies the long exact sequence of homology of
`BG` with local coefficients with that of group homology.

Dually, for a `k`-module `N`, the cohomology of `classifyingSpace G` with coefficients in the same
local system and values in `N` is the group cohomology of `G` with coefficients in the internal
hom `Homₖ(A, N)`, where `N` carries the trivial action
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`):

`Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

Twisted cochains with values in `N` are maps out of the twisted chains, so this is cohomology with
coefficients in the dual local system `Homₖ(A, N)`; it comes from
`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`.

This identification is natural in both coefficient variables. A morphism of representations
`f : A ⟶ A'` induces `Hⁿ(BG; A', N) ⟶ Hⁿ(BG; A, N)` through
`TauCeti.classifyingSpaceLocalSystemMap k f`, and this corresponds to the map
`Hⁿ(G, Homₖ(A', N)) ⟶ Hⁿ(G, Homₖ(A, N))` given by precomposition with `f`
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left`). A linear map
`g : N →ₗ[k] N'` acts on cochains by postcomposition and on group cohomology through the induced
map `Homₖ(A, N) ⟶ Homₖ(A, N')`
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_right`).

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
* `TauCeti.classifyingSpaceLocalSystemFunctor`: the associated local systems as a functor of the
  representation.
* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(BG; A) ≅ Hₙ(G, A)`.
* `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`: the isomorphism
  `Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

## Main results

* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`,
  `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality`: the isomorphism is
  natural in the coefficients.
* `TauCeti.shortExact_map_classifyingSpaceLocalSystemFunctor`,
  `TauCeti.twistedHomologyδ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_hom`,
  `TauCeti.groupHomology_δ_comp_classifyingSpaceTwistedHomologyIsoGroupHomology_inv`: the
  isomorphism carries the coefficient connecting map of homology with local coefficients to the
  connecting map of group homology.
* `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_left`,
  `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom_naturality_right`: the
  cohomological isomorphism is natural in the representation and in the module of values.
* `TauCeti.twistedCohomologyBockstein_comp_classifyingSpaceTwistedCohomologyIsoGroupCohomology_hom`:
  for `k`-projective `A`, it carries the Bockstein homomorphism of twisted cohomology to the
  connecting map of group cohomology.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
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
