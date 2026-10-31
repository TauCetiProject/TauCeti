/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.Singular.Twisted.GroupHomology

/-!
# The homology of a classifying space with local coefficients is group homology

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

## Main definitions

* `TauCeti.classifyingSpaceLocalSystem`: the local coefficient system on `classifyingSpace G`
  associated to a representation of `G`.
* `TauCeti.classifyingSpaceLocalSystemMap`: the morphism of local systems induced by a morphism
  of representations.
* `TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(BG; A) ≅ Hₙ(G, A)`.

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
