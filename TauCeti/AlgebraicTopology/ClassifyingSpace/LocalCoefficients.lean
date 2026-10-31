/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.GroupCohomology
public import TauCeti.AlgebraicTopology.Singular.Twisted.EquivariantMap

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

It is also natural in the group: a homomorphism `φ : G →* H` and a compatible coefficient map
`ξ : A ⟶ Rep.res φ D` give a geometric map on twisted homology, by coefficient change followed
by pushforward along `φ.classifyingSpaceMap`. The comparison carries this map to
`groupHomology.map φ ξ`
(`MonoidHom.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`). These geometric
maps respect identities and composition.

Dually, for a `k`-module `N`, the cohomology of `classifyingSpace G` with coefficients in the same
local system and values in `N` is the group cohomology of `G` with coefficients in the internal
hom `Homₖ(A, N)`, where `N` carries the trivial action
(`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`):

`Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

Twisted cochains with values in `N` are maps out of the twisted chains, so this is cohomology with
coefficients in the dual local system `Homₖ(A, N)`; it comes from
`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`.

## Main definitions

* `TauCeti.classifyingSpaceLocalSystem`: the local coefficient system on `classifyingSpace G`
  associated to a representation of `G`.
* `TauCeti.classifyingSpaceLocalSystemMap`: the morphism of local systems induced by a morphism
  of representations.
* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(BG; A) ≅ Hₙ(G, A)`.
* `TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`: the isomorphism
  `Hⁿ(BG; A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

## Main results

* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality`,
  `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality`: the isomorphism is
  natural in the coefficients.

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

/-- The geometric change-of-group map `Hₙ(BG; A) ⟶ Hₙ(BH; D)`: change coefficients by `ξ`
and then push forward along the strictly functorial map of classifying spaces. -/
abbrev classifyingSpaceTwistedHomologyMap (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    twistedHomology.{u, u, u} (classifyingSpaceLocalSystem k A) n ⟶
      twistedHomology.{u, u, u} (classifyingSpaceLocalSystem k D) n :=
  twistedHomologyCoefficientMap (φ.classifyingSpaceLocalSystemMapOver k ξ) n ≫
    twistedHomologyMap (TopCat.ofHom φ.classifyingSpaceMap) (classifyingSpaceLocalSystem k D) n

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
  exact h

/-- The inverse local-coefficient homology comparison is also natural in the group. -/
@[reassoc]
theorem classifyingSpaceTwistedHomologyIsoGroupHomology_inv_naturality
    (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    groupHomology.map φ ξ n ≫ (classifyingSpaceTwistedHomologyIsoGroupHomology k D n).inv =
      (classifyingSpaceTwistedHomologyIsoGroupHomology k A n).inv ≫
        φ.classifyingSpaceTwistedHomologyMap k ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    φ.classifyingSpaceTwistedHomologyIsoGroupHomology_hom_naturality k ξ n,
    Iso.inv_hom_id_assoc]

variable {k}

/-- The identity homomorphism with identity coefficients induces the identity in twisted
homology of the classifying space. -/
@[simp]
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

end MonoidHom
