/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# The first homology of a classifying space

For every group `G`, the first singular homology group with integer coefficients of Milnor's
classifying space `classifyingSpace G` is the abelianization of `G`
(`TauCeti.classifyingSpaceFirstHomologyAddEquiv`). The isomorphism is the composite of the
Hurewicz isomorphism `H₁(BG; ℤ) ≅ π₁(BG)ᵃᵇ` (`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`) with
the abelianization of the identification `π₁(BG) ≅ G` of
`TauCeti.classifyingSpaceFundamentalGroupMulEquiv`, so the class of a loop at the base point goes
to the class of the group element the loop represents there. It is natural in `G`: the map of
classifying spaces induced by `φ : G →* H` acts on first homology as the map `Gᵃᵇ → Hᵃᵇ` induced
by `φ`.

Mathlib computes the first group homology with trivial coefficients `A` as `Gᵃᵇ ⊗ A`
(`groupHomology.H1AddEquivOfIsTrivial`). For `A = ℤ` this identifies the topological and the
algebraic first homology of `G` (`TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology`):
the class of a loop representing `g` goes to the class of the `1`-chain `g`.

Singular chains with integer coefficients are defined on spaces in the lowest universe, so `G` is
a group in `Type`.

## Main definitions

* `TauCeti.classifyingSpaceFirstHomologyAddEquiv`: the isomorphism `H₁(BG; ℤ) ≃+ Gᵃᵇ`.
* `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology`: the isomorphism
  `H₁(BG; ℤ) ≃+ H₁(G, ℤ)` with Mathlib's group homology of the trivial module.

## Main results

* `TauCeti.classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv`,
  `TauCeti.classifyingSpaceFirstHomologyAddEquiv_loopClass`,
  `TauCeti.classifyingSpaceFirstHomologyAddEquiv_symm_ofMul_of`: the class of a loop representing
  `g` corresponds to the class of `g`.
* `TauCeti.classifyingSpaceFirstHomologyAddEquiv_homologyMap`: naturality in the group.
* `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_hurewiczHomologyAddEquiv`,
  `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_loopClass`: the class of a loop
  representing `g` corresponds to the class of the `1`-chain `g`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2A.1 for the
  Hurewicz isomorphism in degree one, and Section 1.B for `K(G, 1)` spaces.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.3 and II.4.
-/

public section

noncomputable section

open CategoryTheory TauCeti.HurewiczOne

namespace TauCeti

variable (G : Type) [Group G]

/-- **The first homology of the classifying space is the abelianization.** The first singular
homology group with integer coefficients of `classifyingSpace G` is `Gᵃᵇ`: the Hurewicz
isomorphism followed by the abelianization of `classifyingSpaceFundamentalGroupMulEquiv G`. -/
def classifyingSpaceFirstHomologyAddEquiv :
    ((singularChains ℤ).obj (TopCat.of (classifyingSpace G))).homology 1 ≃+
      Additive (Abelianization G) :=
  (hurewiczHomologyAddEquiv (X := TopCat.of (classifyingSpace G))
      (classifyingSpaceBasepoint G)).symm.trans
    (MulEquiv.toAdditive (classifyingSpaceFundamentalGroupMulEquiv G).abelianizationCongr)

variable {G}

/-- The Hurewicz class of a loop at the base point corresponds to the class of the group element
the loop represents under `classifyingSpaceFundamentalGroupMulEquiv`. -/
@[simp]
theorem classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv
    (γ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)) :
    classifyingSpaceFirstHomologyAddEquiv G
        (hurewiczHomologyAddEquiv (X := TopCat.of (classifyingSpace G))
          (classifyingSpaceBasepoint G) (Additive.ofMul (Abelianization.of γ))) =
      Additive.ofMul (Abelianization.of (classifyingSpaceFundamentalGroupMulEquiv G γ)) := by
  rw [classifyingSpaceFirstHomologyAddEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact congrArg Additive.ofMul (abelianizationCongr_of _ γ)

/-- The singular homology class of a loop `p` at the base point corresponds to the class of the
group element `p` represents under `classifyingSpaceFundamentalGroupMulEquiv`. -/
@[simp]
theorem classifyingSpaceFirstHomologyAddEquiv_loopClass
    (p : Path (classifyingSpaceBasepoint G) (classifyingSpaceBasepoint G)) :
    classifyingSpaceFirstHomologyAddEquiv G
        (H₁AddEquivHomology _ (loopClass (X := TopCat.of (classifyingSpace G)) p)) =
      Additive.ofMul (Abelianization.of (classifyingSpaceFundamentalGroupMulEquiv G
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)))) := by
  rw [← hurewiczHomologyAddEquiv_ofMul_of_mk,
    classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv]

/-- The class of `g` in `Gᵃᵇ` corresponds to the Hurewicz class of a loop representing `g`. -/
theorem classifyingSpaceFirstHomologyAddEquiv_symm_ofMul_of (g : G) :
    (classifyingSpaceFirstHomologyAddEquiv G).symm (Additive.ofMul (Abelianization.of g)) =
      hurewiczHomologyAddEquiv (X := TopCat.of (classifyingSpace G))
        (classifyingSpaceBasepoint G)
        (Additive.ofMul
          (Abelianization.of ((classifyingSpaceFundamentalGroupMulEquiv G).symm g))) := by
  rw [AddEquiv.symm_apply_eq, classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv,
    MulEquiv.apply_symm_apply]

/-- **The first homology of the classifying space is natural in the group.** Under the
identifications `classifyingSpaceFirstHomologyAddEquiv` of `H₁(BG; ℤ)` with `Gᵃᵇ` and of
`H₁(BH; ℤ)` with `Hᵃᵇ`, the map induced on first homology by `φ.classifyingSpaceMap` is the map of
abelianizations induced by `φ`. -/
theorem classifyingSpaceFirstHomologyAddEquiv_homologyMap {H : Type} [Group H] (φ : G →* H)
    (x : ((singularChains ℤ).obj (TopCat.of (classifyingSpace G))).homology 1) :
    classifyingSpaceFirstHomologyAddEquiv H
        ((HomologicalComplex.homologyMap
          ((singularChains ℤ).map (TopCat.ofHom φ.classifyingSpaceMap)) 1).hom x) =
      (Abelianization.map φ).toAdditive (classifyingSpaceFirstHomologyAddEquiv G x) := by
  obtain ⟨a, rfl⟩ := (hurewiczHomologyAddEquiv (X := TopCat.of (classifyingSpace G))
    (classifyingSpaceBasepoint G)).surjective x
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  -- `Abelianization G` is the quotient of `G` by its commutator subgroup and `Abelianization.of`
  -- is `QuotientGroup.mk'`; Mathlib states no surjectivity lemma for `Abelianization.of` itself.
  obtain ⟨γ, rfl⟩ : ∃ γ, Abelianization.of γ = a := QuotientGroup.mk'_surjective _ a
  rw [homologyMap_hurewiczHomologyAddEquiv_mapOfEq _ φ.classifyingSpaceMap_basepoint,
    toMul_ofMul, Abelianization.map_of,
    classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv,
    classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv]
  -- `TopCat.ofHom φ.classifyingSpaceMap` has underlying continuous map `φ.classifyingSpaceMap`
  -- by `TopCat.hom_ofHom`, which `rw` cannot reach under the dependent base point proof.
  simp only [TopCat.hom_ofHom, MonoidHom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, Abelianization.map_of]

open groupHomology

variable (G)

/-- **The first homology of the classifying space is the first group homology.** The first
singular homology group with integer coefficients of `classifyingSpace G` is Mathlib's first
group homology of `G` with trivial coefficients in `ℤ`: the composite of
`classifyingSpaceFirstHomologyAddEquiv G` with the identification of `H₁(G, ℤ)` with `Gᵃᵇ ⊗ ℤ`
of `groupHomology.H1AddEquivOfIsTrivial`. -/
def classifyingSpaceFirstHomologyAddEquivGroupHomology :
    ((singularChains ℤ).obj (TopCat.of (classifyingSpace G))).homology 1 ≃+
      groupHomology (Rep.trivial ℤ G ℤ) 1 :=
  (classifyingSpaceFirstHomologyAddEquiv G).trans
    ((TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv.symm.trans
      (H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).symm)

variable {G}

/-- The comparison with first group homology is the abelianization computation followed by
Mathlib's trivial-coefficient group-homology isomorphism. -/
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_apply
    (x : ((singularChains ℤ).obj (TopCat.of (classifyingSpace G))).homology 1) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology G x =
      (H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).symm
        ((TensorProduct.rid ℤ (Additive (Abelianization G))).symm
          (classifyingSpaceFirstHomologyAddEquiv G x)) :=
  (rfl)

/-- The Hurewicz class of a loop at the base point representing `g` corresponds to the class in
`H₁(G, ℤ)` of the `1`-cycle `g` with coefficient `1`. -/
@[simp]
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_hurewiczHomologyAddEquiv
    (γ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology G
        (hurewiczHomologyAddEquiv (X := TopCat.of (classifyingSpace G))
          (classifyingSpaceBasepoint G) (Additive.ofMul (Abelianization.of γ))) =
      H1π (Rep.trivial ℤ G ℤ) ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
        (Finsupp.single (classifyingSpaceFundamentalGroupMulEquiv G γ) 1)) := by
  rw [classifyingSpaceFirstHomologyAddEquivGroupHomology, AddEquiv.trans_apply,
    classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv, AddEquiv.trans_apply]
  exact H1AddEquivOfIsTrivial_symm_tmul (A := Rep.trivial ℤ G ℤ) _ 1

/-- The singular homology class of a loop `p` at the base point corresponds to the class in
`H₁(G, ℤ)` of the `1`-cycle, with coefficient `1`, at the group element that `p` represents under
`classifyingSpaceFundamentalGroupMulEquiv`. -/
@[simp]
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_loopClass
    (p : Path (classifyingSpaceBasepoint G) (classifyingSpaceBasepoint G)) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology G
        (H₁AddEquivHomology _ (loopClass (X := TopCat.of (classifyingSpace G)) p)) =
      H1π (Rep.trivial ℤ G ℤ) ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
        (Finsupp.single (classifyingSpaceFundamentalGroupMulEquiv G
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) 1)) := by
  rw [← hurewiczHomologyAddEquiv_ofMul_of_mk,
    classifyingSpaceFirstHomologyAddEquivGroupHomology_hurewiczHomologyAddEquiv]

end TauCeti
