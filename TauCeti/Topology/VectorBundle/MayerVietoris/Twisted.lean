/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
public import TauCeti.AlgebraicTopology.Singular.Twisted.MayerVietoris.Pair
public import TauCeti.AlgebraicTopology.Singular.Twisted.ProdThomPair
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic

/-!
# The Mayer–Vietoris sequence of Thom pairs with local coefficients

Let `E → B` be a real vector bundle with model fibre `F`, `E₀` the complement of its zero section,
and `L` a local coefficient system on the total space `E`, with arbitrary module fibres over an
arbitrary ring. For a subset `W` of the base, write `Hₙ(E|_W, E₀|_W; L)` for the relative homology
of the Thom pair over `W` (`TauCeti.thomPairOver`) with `L` restricted to `E|_W`
(`TauCeti.thomPairOverTwistedHomology`). For `W ⊆ W'` the inclusion of pairs induces a map
`Hₙ(E|_W, E₀|_W; L) ⟶ Hₙ(E|_{W'}, E₀|_{W'}; L)` (`TauCeti.thomPairOverTwistedHomologyMap`).

For open sets `U` and `V` of the base this file constructs the Mayer–Vietoris long exact sequence

```
⋯ ⟶ Hₙ(E|_{U ∩ V}, E₀|_{U ∩ V}; L) ⟶ Hₙ(E|_U, E₀|_U; L) ⊞ Hₙ(E|_V, E₀|_V; L)
  ⟶ Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L) ⟶ Hₙ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V}; L) ⟶ ⋯
```

(`TauCeti.thomPairOverTwistedMayerVietoris_exact₁`, `thomPairOverTwistedMayerVietoris_exact₂` and
`thomPairOverTwistedMayerVietoris_exact₃`), whose maps are the restrictions, with a sign on the
second component of the first map. It is the Mayer–Vietoris sequence of the pairs `(E|_U, E₀|_U)`
and `(E|_V, E₀|_V)` of subspaces of `E`
(`TauCeti.LocalCoefficientSystem.pairTwistedMayerVietorisδ`), read on the pairs over `U ∩ V` and
`U ∪ V`, which are the intersection and the union of these pairs.

Over a subset `W` of the base set of a linear trivialization the Thom pair is that of the product
bundle `W × F` (`Bundle.Trivialization.thomPairOverIso`), whose homology with any local
coefficients vanishes below the rank `r = dim F` (`TauCeti.isZero_twistedHomology_prodThomPair`);
so does `Hₙ(E|_W, E₀|_W; L)` (`Bundle.Trivialization.isZero_thomPairOverTwistedHomology`). The
Mayer–Vietoris sequence propagates this vanishing to finite unions of trivializing open sets
(`TauCeti.isZero_thomPairOverTwistedHomology_biUnion`). Its map onto the homology over `U ∪ V` is
an epimorphism when the homology over `U ∩ V` vanishes one degree lower
(`TauCeti.epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero`), so that morphisms out of
`Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L)` are then determined over `U` and over `V`
(`TauCeti.thomPairOverTwistedHomology_union_hom_ext`). Up to the rank degree, morphisms out of the
homology over a finite union of trivializing open sets are therefore determined over the sets
(`TauCeti.thomPairOverTwistedHomology_biUnion_hom_ext`).

These are the inputs of the inductive proof of the Thom isomorphism with local coefficients,
`Hₙ₊ᵣ(E, E₀; L) ≅ Hₙ(B; o(E) ⊗ s^*L)` with `o(E)` the orientation local system and `s` the zero
section, over finite unions of trivializing open sets (Milnor–Stasheff, Lemma 10.3 and the proof of
Theorem 10.4, for constant coefficients; Spanier, Chapter 5, Section 7, for local coefficients).
For constant coefficients the corresponding statements are in
`TauCeti.Topology.VectorBundle.MayerVietoris.Basic`.

## Main definitions

* `TauCeti.thomPairOverTwistedHomology`: `Hₙ(E|_W, E₀|_W; L)`.
* `TauCeti.thomPairOverTwistedHomologyMap`: the map induced by an inclusion `W ⊆ W'`.
* `TauCeti.thomPairOverTwistedMayerVietorisToBiprod`,
  `TauCeti.thomPairOverTwistedMayerVietorisFromBiprod`,
  `TauCeti.thomPairOverTwistedMayerVietorisδ`: the maps of the Mayer–Vietoris sequence.
* `TauCeti.thomPairOverTwistedHomologyInterIso`, `TauCeti.thomPairOverTwistedHomologyUnionIso`:
  the homology over `U ∩ V` and over `U ∪ V` is that of the intersection and of the union of the
  pairs over `U` and over `V`.

## Main results

* `TauCeti.thomPairOverTwistedMayerVietoris_exact₁`, `thomPairOverTwistedMayerVietoris_exact₂`,
  `thomPairOverTwistedMayerVietoris_exact₃`: exactness of the Mayer–Vietoris sequence.
* `TauCeti.isZero_thomPairOverTwistedHomology_union`: vanishing over `U ∪ V` from vanishing over
  `U`, `V` and, one degree lower, `U ∩ V`.
* `Bundle.Trivialization.isZero_thomPairOverTwistedHomology`,
  `TauCeti.isZero_thomPairOverTwistedHomology_biUnion`: vanishing below the rank over a
  trivializing set and over a finite union of trivializing open sets.
* `TauCeti.epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero`,
  `TauCeti.thomPairOverTwistedHomology_union_hom_ext`: the sequence is onto the homology over
  `U ∪ V` when the homology over `U ∩ V` vanishes one degree lower.
* `TauCeti.thomPairOverTwistedHomology_biUnion_hom_ext`: up to the rank degree, morphisms out of
  the homology over a finite union of trivializing open sets are determined over the sets.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4.
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill (1966), Chapter 5, Section 7.
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients) and Section 4.D, the proof of
  Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module TauCeti.LocalCoefficientSystem

universe u w w'

namespace TauCeti

section MayerVietoris

variable {R : Type u} [Ring R] {B : Type w} {F : Type*} {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  (L : LocalCoefficientSystem.{u, w, max w w'} R (TopCat.of (TotalSpace F E)))

/-- The relative homology `Hₙ(E|_W, E₀|_W; L)` of the Thom pair over a subset `W` of the base, with
coefficients in the restriction of a local coefficient system `L` on the total space. -/
abbrev thomPairOverTwistedHomology (W : Set B) (n : ℕ) : ModuleCat.{max w w'} R :=
  (thomPairOver F E W).twistedHomology ((LocalCoefficientSystem.pullback
    (X := TopCat.of ↥(π F E ⁻¹' W)) (ContinuousMap.subtypeVal (π F E ⁻¹' W))).obj L) n

/-- The map `Hₙ(E|_W, E₀|_W; L) ⟶ Hₙ(E|_{W'}, E₀|_{W'}; L)` induced by an inclusion `W ⊆ W'` of
subsets of the base. -/
def thomPairOverTwistedHomologyMap {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverTwistedHomology L W n ⟶ thomPairOverTwistedHomology L W' n :=
  HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L inter_subset_left
    inter_subset_left (preimage_mono h) (inter_subset_inter_left _ (preimage_mono h))) n

/-- The map induced by an inclusion `W ⊆ W'` is induced by the map of relative twisted chains of
the inclusion of the pairs of subsets of the total space. -/
theorem thomPairOverTwistedHomologyMap_def {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverTwistedHomologyMap L h n =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L inter_subset_left
        inter_subset_left (preimage_mono h) (inter_subset_inter_left _ (preimage_mono h))) n :=
  (rfl)

/-- The restriction map on twisted homology of Thom pairs over `W ⊆ W'` is the change of
coefficients identifying the two restrictions of `L` to `E|_W`, followed by the map induced by
`TauCeti.thomPairOverMap`. -/
theorem thomPairOverTwistedHomologyMap_eq {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverTwistedHomologyMap L h n =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullbackCompIso
              (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h))).hom
              (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).hom.app L ≫
            eqToHom (congrArg (fun g : (thomPairOver F E W).fst ⟶ (thomPairOver F E W').fst ↦
              (LocalCoefficientSystem.pullback g.hom).obj
                ((LocalCoefficientSystem.pullback
                  (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).obj L))
              (thomPairOverMap_fst F E h).symm)) n ≫
        TopPair.twistedHomologyMap (thomPairOverMap F E h)
          ((LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' W'))
            (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).obj L) n := by
  have hmap : TopPair.ofHom (X := thomPairOver F E W) (Y := thomPairOver F E W')
      (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h)))
      (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_inter_left _ (preimage_mono h)))) rfl =
      thomPairOverMap F E h :=
    TopPair.hom_ext_of_fst _ (thomPairOverMap_fst F E h).symm
  rw [thomPairOverTwistedHomologyMap_def, subsetPairTwistedChainComplexMap_def]
  -- `erw`: `(TopPair.ofInclusion _).fst` matches `TopCat.of ↥(π F E ⁻¹' W)` after unfolding.
  erw [TopPair.twistedChainComplexMap_congr _ (congrArg TopPair.Hom.fst hmap),
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc, HomologicalComplex.homologyMap_comp]
  -- Both `eqToHom` proofs witness the same equality of local systems, equal by proof irrelevance.
  rfl

/-- The map induced by the identity inclusion is the identity. -/
@[simp]
theorem thomPairOverTwistedHomologyMap_self (W : Set B) (n : ℕ) :
    thomPairOverTwistedHomologyMap L (subset_refl W) n = 𝟙 _ :=
  (congrArg (HomologicalComplex.homologyMap · n)
    (subsetPairTwistedChainComplexMap_self L _)).trans (HomologicalComplex.homologyMap_id _ n)

/-- The maps induced by inclusions compose. -/
@[reassoc (attr := simp)]
theorem thomPairOverTwistedHomologyMap_comp {W₁ W₂ W₃ : Set B} (h : W₁ ⊆ W₂) (h' : W₂ ⊆ W₃)
    (n : ℕ) :
    thomPairOverTwistedHomologyMap L h n ≫ thomPairOverTwistedHomologyMap L h' n =
      thomPairOverTwistedHomologyMap L (h.trans h') n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap L _ _ _ _ _ _ _))

/-- The relative homology of the Thom pair over the empty set vanishes. -/
theorem isZero_thomPairOverTwistedHomology_empty (n : ℕ) :
    IsZero (thomPairOverTwistedHomology L ∅ n) := by
  have hfst : IsEmpty ↥(π F E ⁻¹' (∅ : Set B)) := ⟨fun v ↦ v.property.elim⟩
  have hsnd : IsEmpty ↥(π F E ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E) :=
    ⟨fun v ↦ v.property.1.elim⟩
  -- Both spaces of the pair are empty, so the inclusion is an isomorphism on twisted homology.
  refine TopPair.isZero_twistedHomology_of_isIso _ _ (fun k ↦ ?_) n
  exact isIso_of_source_target_iso_zero _
    (isZero_twistedHomology_of_isEmpty (X := TopCat.of ↥(π F E ⁻¹' (∅ : Set B) ∩
      zeroSectionCompl F E)) _ k).isoZero
    (isZero_twistedHomology_of_isEmpty (X := TopCat.of ↥(π F E ⁻¹' (∅ : Set B))) _ k).isoZero

/-! ### The Mayer–Vietoris sequence -/

variable (U V : Set B)

/-- The pair over `U ∩ V` is the intersection of the pairs over `U` and over `V`: the twisted
homology of the Thom pair over `U ∩ V` is that of the intersection of the pairs `(E|_U, E₀|_U)` and
`(E|_V, E₀|_V)` of subspaces of `E`. -/
def thomPairOverTwistedHomologyInterIso (n : ℕ) :
    thomPairOverTwistedHomology L (U ∩ V) n ≅
      (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
        (inter_subset_inter (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))).twistedHomology
        ((LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' U ∩ π F E ⁻¹' V))
          (ContinuousMap.subtypeVal (π F E ⁻¹' U ∩ π F E ⁻¹' V))).obj L) n :=
  HomologicalComplex.homologyMapIso (subsetPairTwistedChainComplexIsoOfEq L inter_subset_left
    (inter_subset_inter inter_subset_left inter_subset_left) preimage_inter
    (by rw [preimage_inter, inter_inter_distrib_right])) n

/-- The pair over `U ∪ V` is the union of the pairs over `U` and over `V`: the twisted homology of
the Thom pair over `U ∪ V` is that of the union of the pairs `(E|_U, E₀|_U)` and `(E|_V, E₀|_V)` of
subspaces of `E`. -/
def thomPairOverTwistedHomologyUnionIso (n : ℕ) :
    thomPairOverTwistedHomology L (U ∪ V) n ≅
      (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
        (union_subset_union (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))).twistedHomology
        ((LocalCoefficientSystem.pullback (X := TopCat.of ↥(π F E ⁻¹' U ∪ π F E ⁻¹' V))
          (ContinuousMap.subtypeVal (π F E ⁻¹' U ∪ π F E ⁻¹' V))).obj L) n :=
  HomologicalComplex.homologyMapIso (subsetPairTwistedChainComplexIsoOfEq L inter_subset_left
    (union_subset_union inter_subset_left inter_subset_left) preimage_union
    (by rw [preimage_union, union_inter_distrib_right])) n

/-- The identification of the homology over `U ∩ V` is induced by the inclusion of pairs. -/
@[simp]
theorem thomPairOverTwistedHomologyInterIso_hom (n : ℕ) :
    (thomPairOverTwistedHomologyInterIso L U V n).hom =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L inter_subset_left
        (inter_subset_inter inter_subset_left inter_subset_left) preimage_inter.le
        (by rw [preimage_inter, inter_inter_distrib_right])) n := by
  rw [thomPairOverTwistedHomologyInterIso, HomologicalComplex.homologyMapIso_hom,
    subsetPairTwistedChainComplexIsoOfEq_hom]

/-- The inverse of the identification of the homology over `U ∩ V` is induced by an inclusion. -/
@[simp]
theorem thomPairOverTwistedHomologyInterIso_inv (n : ℕ) :
    (thomPairOverTwistedHomologyInterIso L U V n).inv =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L
        (inter_subset_inter inter_subset_left inter_subset_left) inter_subset_left
        preimage_inter.ge (by rw [preimage_inter, ← inter_inter_distrib_right])) n := by
  rw [thomPairOverTwistedHomologyInterIso, HomologicalComplex.homologyMapIso_inv,
    subsetPairTwistedChainComplexIsoOfEq_inv]

/-- The identification of the homology over `U ∪ V` is induced by the inclusion of pairs. -/
@[simp]
theorem thomPairOverTwistedHomologyUnionIso_hom (n : ℕ) :
    (thomPairOverTwistedHomologyUnionIso L U V n).hom =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L inter_subset_left
        (union_subset_union inter_subset_left inter_subset_left) preimage_union.le
        (by rw [preimage_union, union_inter_distrib_right])) n := by
  rw [thomPairOverTwistedHomologyUnionIso, HomologicalComplex.homologyMapIso_hom,
    subsetPairTwistedChainComplexIsoOfEq_hom]

/-- The inverse of the identification of the homology over `U ∪ V` is induced by an inclusion. -/
@[simp]
theorem thomPairOverTwistedHomologyUnionIso_inv (n : ℕ) :
    (thomPairOverTwistedHomologyUnionIso L U V n).inv =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L
        (union_subset_union inter_subset_left inter_subset_left) inter_subset_left
        preimage_union.ge (by rw [preimage_union, union_inter_distrib_right])) n := by
  rw [thomPairOverTwistedHomologyUnionIso, HomologicalComplex.homologyMapIso_inv,
    subsetPairTwistedChainComplexIsoOfEq_inv]

/-- The first map `Hₙ(E|_{U ∩ V}, E₀|_{U ∩ V}; L) ⟶ Hₙ(E|_U, E₀|_U; L) ⊞ Hₙ(E|_V, E₀|_V; L)` of the
Mayer–Vietoris sequence of the Thom pairs over `U` and over `V`: the restriction to `U` and minus
the restriction to `V`. -/
def thomPairOverTwistedMayerVietorisToBiprod (n : ℕ) :
    thomPairOverTwistedHomology L (U ∩ V) n ⟶
      thomPairOverTwistedHomology L U n ⊞ thomPairOverTwistedHomology L V n :=
  biprod.lift (thomPairOverTwistedHomologyMap L inter_subset_left n)
    (-thomPairOverTwistedHomologyMap L inter_subset_right n)

/-- The first map of the Mayer–Vietoris sequence of Thom pairs is the biproduct lift of the
restriction to `U` and minus the restriction to `V`. -/
theorem thomPairOverTwistedMayerVietorisToBiprod_def (n : ℕ) :
    thomPairOverTwistedMayerVietorisToBiprod L U V n =
      biprod.lift (thomPairOverTwistedHomologyMap L inter_subset_left n)
        (-thomPairOverTwistedHomologyMap L inter_subset_right n) :=
  (rfl)

@[reassoc (attr := simp)]
theorem thomPairOverTwistedMayerVietorisToBiprod_fst (n : ℕ) :
    thomPairOverTwistedMayerVietorisToBiprod L U V n ≫ biprod.fst =
      thomPairOverTwistedHomologyMap L inter_subset_left n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem thomPairOverTwistedMayerVietorisToBiprod_snd (n : ℕ) :
    thomPairOverTwistedMayerVietorisToBiprod L U V n ≫ biprod.snd =
      -thomPairOverTwistedHomologyMap L inter_subset_right n :=
  biprod.lift_snd _ _

/-- The second map `Hₙ(E|_U, E₀|_U; L) ⊞ Hₙ(E|_V, E₀|_V; L) ⟶ Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L)` of the
Mayer–Vietoris sequence of the Thom pairs over `U` and over `V`: the sum of the restrictions. -/
def thomPairOverTwistedMayerVietorisFromBiprod (n : ℕ) :
    thomPairOverTwistedHomology L U n ⊞ thomPairOverTwistedHomology L V n ⟶
      thomPairOverTwistedHomology L (U ∪ V) n :=
  biprod.desc (thomPairOverTwistedHomologyMap L subset_union_left n)
    (thomPairOverTwistedHomologyMap L subset_union_right n)

/-- The second map of the Mayer–Vietoris sequence of Thom pairs is the biproduct desc of the
restrictions from `U` and from `V`. -/
theorem thomPairOverTwistedMayerVietorisFromBiprod_def (n : ℕ) :
    thomPairOverTwistedMayerVietorisFromBiprod L U V n =
      biprod.desc (thomPairOverTwistedHomologyMap L subset_union_left n)
        (thomPairOverTwistedHomologyMap L subset_union_right n) :=
  (rfl)

@[reassoc (attr := simp)]
theorem inl_thomPairOverTwistedMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ thomPairOverTwistedMayerVietorisFromBiprod L U V n =
      thomPairOverTwistedHomologyMap L subset_union_left n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_thomPairOverTwistedMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ thomPairOverTwistedMayerVietorisFromBiprod L U V n =
      thomPairOverTwistedHomologyMap L subset_union_right n :=
  biprod.inr_desc _ _

/-- The first two maps of the Mayer–Vietoris sequence compose to zero: both composites are the
restriction from `U ∩ V` to `U ∪ V`. -/
@[reassoc (attr := simp)]
theorem thomPairOverTwistedMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    thomPairOverTwistedMayerVietorisToBiprod L U V n ≫
      thomPairOverTwistedMayerVietorisFromBiprod L U V n = 0 := by
  simp [thomPairOverTwistedMayerVietorisToBiprod, thomPairOverTwistedMayerVietorisFromBiprod]

/-- The first map of the Mayer–Vietoris sequence of the Thom pairs is that of the pairs over `U`
and over `V`, read on the pair over `U ∩ V`. -/
@[reassoc]
theorem thomPairOverTwistedHomologyInterIso_hom_pairTwistedMayerVietorisToBiprod (n : ℕ) :
    (thomPairOverTwistedHomologyInterIso L U V n).hom ≫ pairTwistedMayerVietorisToBiprod L
      inter_subset_left inter_subset_left n = thomPairOverTwistedMayerVietorisToBiprod L U V n := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    [rw [Category.assoc, pairTwistedMayerVietorisToBiprod_fst,
      thomPairOverTwistedMayerVietorisToBiprod_fst];
    rw [Category.assoc, pairTwistedMayerVietorisToBiprod_snd,
      thomPairOverTwistedMayerVietorisToBiprod_snd, Preadditive.comp_neg, neg_inj]] <;>
    rw [thomPairOverTwistedHomologyInterIso_hom, thomPairOverTwistedHomologyMap_def,
      ← HomologicalComplex.homologyMap_comp,
      subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap]

/-- The second map of the Mayer–Vietoris sequence of the Thom pairs is that of the pairs over `U`
and over `V`, read on the pair over `U ∪ V`. -/
@[reassoc]
theorem thomPairOverTwistedMayerVietorisFromBiprod_thomPairOverTwistedHomologyUnionIso_hom
    (n : ℕ) :
    thomPairOverTwistedMayerVietorisFromBiprod L U V n ≫
        (thomPairOverTwistedHomologyUnionIso L U V n).hom =
      pairTwistedMayerVietorisFromBiprod L inter_subset_left inter_subset_left n := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    [rw [inl_thomPairOverTwistedMayerVietorisFromBiprod_assoc,
      inl_pairTwistedMayerVietorisFromBiprod];
    rw [inr_thomPairOverTwistedMayerVietorisFromBiprod_assoc,
      inr_pairTwistedMayerVietorisFromBiprod]] <;>
    rw [thomPairOverTwistedHomologyUnionIso_hom, thomPairOverTwistedHomologyMap_def,
      ← HomologicalComplex.homologyMap_comp,
      subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap]

variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] {U V}

/-- The connecting morphism `Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L) ⟶ Hₘ(E|_{U ∩ V}, E₀|_{U ∩ V}; L)`,
`m + 1 = n`, of the Mayer–Vietoris sequence of the Thom pairs over open sets `U` and `V` of the
base: the connecting morphism of the Mayer–Vietoris sequence of the pairs `(E|_U, E₀|_U)` and
`(E|_V, E₀|_V)` of subspaces of `E` (`TauCeti.LocalCoefficientSystem.pairTwistedMayerVietorisδ`),
read on the pairs over `U ∪ V` and over `U ∩ V`. -/
def thomPairOverTwistedMayerVietorisδ (hU : IsOpen U) (hV : IsOpen V) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    thomPairOverTwistedHomology L (U ∪ V) n ⟶ thomPairOverTwistedHomology L (U ∩ V) m :=
  (thomPairOverTwistedHomologyUnionIso L U V n).hom ≫
    pairTwistedMayerVietorisδ L inter_subset_left inter_subset_left
      (isOpen_thomPairOver_mayerVietoris hU hV).1 (isOpen_thomPairOver_mayerVietoris hU hV).2.1
      (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
      (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 n m h ≫
    (thomPairOverTwistedHomologyInterIso L U V m).inv

/-- The connecting morphism of the Mayer–Vietoris sequence of the Thom pairs is that of the pairs
`(E|_U, E₀|_U)` and `(E|_V, E₀|_V)`, read on the pairs over `U ∪ V` and over `U ∩ V`. -/
theorem thomPairOverTwistedMayerVietorisδ_def (hU : IsOpen U) (hV : IsOpen V) (n m : ℕ)
    (h : m + 1 = n) :
    thomPairOverTwistedMayerVietorisδ L hU hV n m h =
      (thomPairOverTwistedHomologyUnionIso L U V n).hom ≫
        pairTwistedMayerVietorisδ L inter_subset_left inter_subset_left
          (isOpen_thomPairOver_mayerVietoris hU hV).1 (isOpen_thomPairOver_mayerVietoris hU hV).2.1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 n m h ≫
        (thomPairOverTwistedHomologyInterIso L U V m).inv :=
  (rfl)

/-- The connecting morphism followed by the first map vanishes. -/
@[reassoc (attr := simp)]
theorem thomPairOverTwistedMayerVietorisδ_toBiprod (hU : IsOpen U) (hV : IsOpen V) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    thomPairOverTwistedMayerVietorisδ L hU hV n m h ≫
      thomPairOverTwistedMayerVietorisToBiprod L U V m = 0 := by
  rw [thomPairOverTwistedMayerVietorisδ_def,
    ← thomPairOverTwistedHomologyInterIso_hom_pairTwistedMayerVietorisToBiprod,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    pairTwistedMayerVietorisδ_toBiprod L _ _ _ _ _ _ n m h, comp_zero]

/-- The second map followed by the connecting morphism vanishes. -/
@[reassoc (attr := simp)]
theorem thomPairOverTwistedMayerVietorisFromBiprod_δ (hU : IsOpen U) (hV : IsOpen V) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    thomPairOverTwistedMayerVietorisFromBiprod L U V n ≫
      thomPairOverTwistedMayerVietorisδ L hU hV n m h = 0 := by
  rw [thomPairOverTwistedMayerVietorisδ_def,
    thomPairOverTwistedMayerVietorisFromBiprod_thomPairOverTwistedHomologyUnionIso_hom_assoc,
    pairTwistedMayerVietorisFromBiprod_δ_assoc L _ _ _ _ _ _ n m h, zero_comp]

/-- **Exactness of the Mayer–Vietoris sequence of Thom pairs with local coefficients at
`Hₘ(E|_{U ∩ V}, E₀|_{U ∩ V}; L)`**, for open sets `U` and `V` of the base. -/
theorem thomPairOverTwistedMayerVietoris_exact₁ (hU : IsOpen U) (hV : IsOpen V) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (thomPairOverTwistedMayerVietorisδ_toBiprod L hU hV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (pairTwistedMayerVietoris_exact₁ L
    inter_subset_left inter_subset_left (isOpen_thomPairOver_mayerVietoris hU hV).1
    (isOpen_thomPairOver_mayerVietoris hU hV).2.1 (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
    (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 n m h)
  -- The commutativity goals are stated on the projections of `ShortComplex.mk`, which
  -- `dsimp only` reduces so that the defining equations can be rewritten.
  exact ShortComplex.isoMk (thomPairOverTwistedHomologyUnionIso L U V n)
    (thomPairOverTwistedHomologyInterIso L U V m) (Iso.refl _)
    (by
      dsimp only
      rw [thomPairOverTwistedMayerVietorisδ_def, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id])
    (by
      dsimp only
      rw [Iso.refl_hom, Category.comp_id,
        thomPairOverTwistedHomologyInterIso_hom_pairTwistedMayerVietorisToBiprod])

/-- **Exactness of the Mayer–Vietoris sequence of Thom pairs with local coefficients at
`Hₙ(E|_U, E₀|_U; L) ⊞ Hₙ(E|_V, E₀|_V; L)`**, for open sets `U` and `V` of the base. -/
theorem thomPairOverTwistedMayerVietoris_exact₂ (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (ShortComplex.mk _ _ (thomPairOverTwistedMayerVietorisToBiprod_fromBiprod L U V n)).Exact := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  refine (ShortComplex.exact_iff_of_iso ?_).2 (pairTwistedMayerVietoris_exact₂ L
    inter_subset_left inter_subset_left hA hB hC hD n)
  exact ShortComplex.isoMk (thomPairOverTwistedHomologyInterIso L U V n) (Iso.refl _)
    (thomPairOverTwistedHomologyUnionIso L U V n)
    (by
      dsimp only
      rw [Iso.refl_hom, Category.comp_id,
        thomPairOverTwistedHomologyInterIso_hom_pairTwistedMayerVietorisToBiprod])
    (by
      dsimp only
      rw [Iso.refl_hom, Category.id_comp,
        thomPairOverTwistedMayerVietorisFromBiprod_thomPairOverTwistedHomologyUnionIso_hom])

/-- **Exactness of the Mayer–Vietoris sequence of Thom pairs with local coefficients at
`Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L)`**, for open sets `U` and `V` of the base. -/
theorem thomPairOverTwistedMayerVietoris_exact₃ (hU : IsOpen U) (hV : IsOpen V) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (thomPairOverTwistedMayerVietorisFromBiprod_δ L hU hV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (pairTwistedMayerVietoris_exact₃ L
    inter_subset_left inter_subset_left (isOpen_thomPairOver_mayerVietoris hU hV).1
    (isOpen_thomPairOver_mayerVietoris hU hV).2.1 (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
    (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 n m h)
  exact ShortComplex.isoMk (Iso.refl _) (thomPairOverTwistedHomologyUnionIso L U V n)
    (thomPairOverTwistedHomologyInterIso L U V m)
    (by
      dsimp only
      rw [Iso.refl_hom, Category.id_comp,
        thomPairOverTwistedMayerVietorisFromBiprod_thomPairOverTwistedHomologyUnionIso_hom])
    (by
      dsimp only
      rw [thomPairOverTwistedMayerVietorisδ_def, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id])

/-- **The end of the Mayer–Vietoris sequence of Thom pairs with local coefficients**: for open sets
`U` and `V` of the base, if `Hₙ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V}; L)` vanishes (or `n = 0`), every class
over `U ∪ V` is a sum of restrictions of classes over `U` and over `V`. -/
theorem epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero (hU : IsOpen U) (hV : IsOpen V)
    {n : ℕ} (hUV : ∀ m, m + 1 = n → IsZero (thomPairOverTwistedHomology L (U ∩ V) m)) :
    Epi (thomPairOverTwistedMayerVietorisFromBiprod L U V n) := by
  cases n with
  | zero =>
    obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
    have := epi_pairTwistedMayerVietorisFromBiprod_zero L inter_subset_left inter_subset_left
      hA hB hC hD
    rw [(Iso.eq_comp_inv _).2
      (thomPairOverTwistedMayerVietorisFromBiprod_thomPairOverTwistedHomologyUnionIso_hom L U V 0)]
    infer_instance
  | succ m =>
    exact (thomPairOverTwistedMayerVietoris_exact₃ L hU hV (m + 1) m).epi_f
      ((hUV m rfl).eq_of_tgt _ _)

/-- **Vanishing propagates along the Mayer–Vietoris sequence of Thom pairs**: for open sets `U` and
`V` of the base, if `Hₙ(E|_U, E₀|_U; L)` and `Hₙ(E|_V, E₀|_V; L)` vanish, and so does
`Hₙ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V}; L)` when `n` is positive, then `Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L)`
vanishes. -/
theorem isZero_thomPairOverTwistedHomology_union (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUn : IsZero (thomPairOverTwistedHomology L U n))
    (hVn : IsZero (thomPairOverTwistedHomology L V n))
    (hUV : ∀ m, m + 1 = n → IsZero (thomPairOverTwistedHomology L (U ∩ V) m)) :
    IsZero (thomPairOverTwistedHomology L (U ∪ V) n) :=
  have := epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero L hU hV hUV
  IsZero.of_epi_eq_zero (thomPairOverTwistedMayerVietorisFromBiprod L U V n)
    (((biprod_isZero_iff _ _).2 ⟨hUn, hVn⟩).eq_of_src _ _)

variable {L} in
/-- **Morphisms out of the homology over `U ∪ V` are determined over `U` and over `V`** when
`Hₙ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V}; L)` vanishes (or `n = 0`): the Mayer–Vietoris sequence of the Thom
pairs over the open sets `U` and `V` is then onto `Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V}; L)`. -/
theorem thomPairOverTwistedHomology_union_hom_ext (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUV : ∀ m, m + 1 = n → IsZero (thomPairOverTwistedHomology L (U ∩ V) m))
    {T : ModuleCat.{max w w'} R} {g g' : thomPairOverTwistedHomology L (U ∪ V) n ⟶ T}
    (hgU : thomPairOverTwistedHomologyMap L subset_union_left n ≫ g =
      thomPairOverTwistedHomologyMap L subset_union_left n ≫ g')
    (hgV : thomPairOverTwistedHomologyMap L subset_union_right n ≫ g =
      thomPairOverTwistedHomologyMap L subset_union_right n ≫ g') :
    g = g' := by
  have := epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero L hU hV hUV
  refine (cancel_epi (thomPairOverTwistedMayerVietorisFromBiprod L U V n)).1
    (biprod.hom_ext' _ _ ?_ ?_)
  · rwa [inl_thomPairOverTwistedMayerVietorisFromBiprod_assoc,
      inl_thomPairOverTwistedMayerVietorisFromBiprod_assoc]
  · rwa [inr_thomPairOverTwistedMayerVietorisFromBiprod_assoc,
      inr_thomPairOverTwistedMayerVietorisFromBiprod_assoc]

end MayerVietoris

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {R : Type u} [Ring R] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  (L : LocalCoefficientSystem.{u, w, max w w'} R (TopCat.of (TotalSpace F E)))

/-- **The relative homology of the Thom pair over a trivializing set vanishes below the rank, with
any local coefficients**: for `W` contained in the base set of a linear trivialization,
`Hₙ(E|_W, E₀|_W; L) = 0` for `n < dim F`. -/
theorem isZero_thomPairOverTwistedHomology (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {W : Set B} (hW : W ⊆ e.baseSet) {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero (thomPairOverTwistedHomology L W n) :=
  -- The trivialization identifies the pair with the Thom pair of the product bundle `W × F`.
  (isZero_twistedHomology_prodThomPair _ hn).of_iso
    (asIso (TopPair.twistedHomologyMap (e.thomPairOverIso ℝ hW).inv _ n)).symm

end Bundle.Trivialization

namespace TauCeti

variable {R : Type u} [Ring R] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (L : LocalCoefficientSystem.{u, w, max w w'} R (TopCat.of (TotalSpace F E)))

omit [FiniteDimensional ℝ F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- Intersecting a family of trivializing open sets with an open set `W₀` of the base gives a family
of trivializing open sets: the sets `W₀ ∩ W i`, `i ∈ s`, are open and lie in base sets of linear
trivializations. -/
private theorem isOpen_inter_and_subset_baseSet {ι : Type*} {s : Finset ι} {W₀ : Set B}
    {W : ι → Set B} (hW₀ : IsOpen W₀) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet) :
    (∀ i ∈ s, IsOpen (W₀ ∩ W i)) ∧
      ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W₀ ∩ W i ⊆ e.baseSet :=
  ⟨fun i hi ↦ hW₀.inter (hWo i hi), fun i hi ↦
    (hWe i hi).imp fun _ ⟨he, hi'⟩ ↦ ⟨he, inter_subset_right.trans hi'⟩⟩

/-- **The relative homology of the Thom pair over a finite union of trivializing open sets vanishes
below the rank, with any local coefficients**: if each of the finitely many open sets `W i`,
`i ∈ s`, lies in the base set of a linear trivialization, then `Hₙ(E|_W, E₀|_W; L) = 0` for
`n < dim F`, where `W` is their union. -/
theorem isZero_thomPairOverTwistedHomology_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero (thomPairOverTwistedHomology L (⋃ i ∈ s, W i) n) := by
  classical
  induction s using Finset.induction_on generalizing W n with
  | empty => simpa using isZero_thomPairOverTwistedHomology_empty L n
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine isZero_thomPairOverTwistedHomology_union L (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      (e.isZero_thomPairOverTwistedHomology L he hn)
      (ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) hn) fun m hm ↦ ?_
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have hinter := isOpen_inter_and_subset_baseSet (hWo a (Finset.mem_insert_self a s))
      (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    rw [inter_iUnion₂]
    exact ih hinter.1 hinter.2 (by omega)

variable {L} in
/-- **Morphisms out of the homology over a finite union of trivializing open sets are determined
over the sets**, up to the rank degree: if each of the finitely many open sets `W i`, `i ∈ s`, lies
in the base set of a linear trivialization, `W` is their union and `n ≤ dim F`, then two morphisms
out of `Hₙ(E|_W, E₀|_W; L)` which agree after the restriction from every `W i` are equal. -/
theorem thomPairOverTwistedHomology_biUnion_hom_ext {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {n : ℕ} (hn : n ≤ finrank ℝ F) {T : ModuleCat.{max w w'} R}
    {g g' : thomPairOverTwistedHomology L (⋃ i ∈ s, W i) n ⟶ T}
    (h : ∀ i (hi : i ∈ s), thomPairOverTwistedHomologyMap L (subset_biUnion_of_mem hi) n ≫ g =
      thomPairOverTwistedHomologyMap L (subset_biUnion_of_mem hi) n ≫ g') :
    g = g' := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    -- Over the empty set the Thom pair has no homology.
    exact IsZero.eq_of_src (by simpa using isZero_thomPairOverTwistedHomology_empty L n) g g'
  | insert a s _ ih =>
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    -- Split off `W a`, through the restrictions between the two expressions of the union.
    have hW := (Finset.set_biUnion_insert a s W).symm
    have hid := thomPairOverTwistedHomologyMap_comp L hW.ge hW.le n
    rw [thomPairOverTwistedHomologyMap_self] at hid
    rw [← Category.id_comp g, ← Category.id_comp g', ← hid, Category.assoc, Category.assoc]
    congr 1
    refine thomPairOverTwistedHomology_union_hom_ext (hWo a ha)
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)) (fun m hm ↦ ?_) ?_ ?_
    · -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
      have hinter := isOpen_inter_and_subset_baseSet (hWo a ha) (fun i hi ↦ hWo i (hs i hi))
        (fun i hi ↦ hWe i (hs i hi))
      rw [inter_iUnion₂]
      exact isZero_thomPairOverTwistedHomology_biUnion L s hinter.1 hinter.2 (by omega)
    · rw [thomPairOverTwistedHomologyMap_comp_assoc, thomPairOverTwistedHomologyMap_comp_assoc]
      exact h a ha
    · refine ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) fun i hi ↦ ?_
      rw [thomPairOverTwistedHomologyMap_comp_assoc, thomPairOverTwistedHomologyMap_comp_assoc,
        thomPairOverTwistedHomologyMap_comp_assoc, thomPairOverTwistedHomologyMap_comp_assoc]
      exact h i (hs i hi)

end TauCeti
