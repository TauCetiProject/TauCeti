/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
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

The identification is natural in the group. The geometric chain identification commutes with
every group homomorphism (`MonoidHom.classifyingSpaceSingularChainsCoinvariants_naturality`), and
on homology, for every `φ : G →* H`, the map `Hₙ(BG; k) ⟶ Hₙ(BH; k)` induced by the strictly
functorial map `MonoidHom.classifyingSpaceMap φ` is Mathlib's change-of-group map
`groupHomology.map φ` (`MonoidHom.classifyingSpaceSingularHomologyIsoGroupHomology_hom_naturality`).
No hypothesis on `φ` is needed.

## Main definitions

* `TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(BG; k) ≅ Hₙ(G, k)`.

## Main results

* `MonoidHom.classifyingSpaceSingularHomologyIsoGroupHomology_hom_naturality`,
  `MonoidHom.classifyingSpaceSingularHomologyIsoGroupHomology_inv_naturality`: the isomorphism
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

namespace MonoidHom

open TauCeti

universe u

variable {G H : Type u} [Group G] [Group H]

/-- **The geometric chain comparison for Milnor classifying spaces is natural in the group.**
Applying a group homomorphism to the labels in the universal space before passing to
coinvariant chains agrees with pushing chains forward along its map of classifying spaces. -/
@[reassoc]
theorem classifyingSpaceSingularChainsCoinvariants_naturality (φ : G →* H)
    (k : Type u) [CommRing k] :
    singularChainsCoinvariantsMap k (TopCat.ofHom φ.universalGSpaceMap)
        (fun g x ↦ φ.universalGSpaceMap_smul g x) ≫
        (IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso
          (p := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
          (isQuotientCoveringMap_classifyingSpaceProj H) k).hom =
      (IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso
          (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
          (isQuotientCoveringMap_classifyingSpaceProj G) k).hom ≫
        (singularChains k).map (TopCat.ofHom φ.classifyingSpaceMap) := by
  exact IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso_naturality
    (isQuotientCoveringMap_classifyingSpaceProj G) k
      (isQuotientCoveringMap_classifyingSpaceProj H) _
      (fun g x ↦ φ.universalGSpaceMap_smul g x) _
      (ConcreteCategory.hom_ext _ _ fun x ↦ (φ.classifyingSpaceMap_proj x))

/-- **The singular homology of the classifying space is naturally group homology.** For every
group homomorphism `φ : G →* H`, the identifications `Hₙ(BG; k) ≅ Hₙ(G, k)` and
`Hₙ(BH; k) ≅ Hₙ(H, k)` carry the map induced by `MonoidHom.classifyingSpaceMap φ` to Mathlib's
change-of-group map `groupHomology.map φ`, with the identity on the trivial coefficients `k`. -/
@[reassoc]
theorem classifyingSpaceSingularHomologyIsoGroupHomology_hom_naturality (φ : G →* H)
    (k : Type u) [CommRing k] (n : ℕ) :
    HomologicalComplex.homologyMap
        ((singularChains k).map (TopCat.ofHom φ.classifyingSpaceMap)) n ≫
        (classifyingSpaceSingularHomologyIsoGroupHomology k H n).hom =
      (classifyingSpaceSingularHomologyIsoGroupHomology k G n).hom ≫
        groupHomology.map φ (A := Rep.trivial k G k) (B := Rep.trivial k H k)
          (𝟙 (Rep.trivial k G k)) n :=
  IsQuotientCoveringMap.singularHomologyIsoGroupHomology_hom_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k
    (F := TopCat.of (universalGSpace H))
    (q := TopCat.ofHom ⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩)
    (isQuotientCoveringMap_classifyingSpaceProj H) (TopCat.ofHom φ.universalGSpaceMap)
    (fun g x ↦ φ.universalGSpaceMap_smul g x) _
    (ConcreteCategory.hom_ext _ _ fun x ↦ (φ.classifyingSpaceMap_proj x)) n

/-- The inverse identification of group homology with the singular homology of the classifying
space is natural in the group. -/
@[reassoc]
theorem classifyingSpaceSingularHomologyIsoGroupHomology_inv_naturality (φ : G →* H)
    (k : Type u) [CommRing k] (n : ℕ) :
    groupHomology.map φ (A := Rep.trivial k G k) (B := Rep.trivial k H k)
        (𝟙 (Rep.trivial k G k)) n ≫ (classifyingSpaceSingularHomologyIsoGroupHomology k H n).inv =
      (classifyingSpaceSingularHomologyIsoGroupHomology k G n).inv ≫
        HomologicalComplex.homologyMap
          ((singularChains k).map (TopCat.ofHom φ.classifyingSpaceMap)) n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    φ.classifyingSpaceSingularHomologyIsoGroupHomology_hom_naturality k n, Iso.inv_hom_id_assoc]

end MonoidHom
