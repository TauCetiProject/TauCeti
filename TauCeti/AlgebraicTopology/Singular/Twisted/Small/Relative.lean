/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains

/-!
# Support of relative twisted chains

Two facts about the relative twisted chains of an arbitrary topological pair `P` with coefficients
in a local coefficient system `L` on its ambient space. An ambient chain vanishes in relative
chains exactly when it is supported in the subspace
(`TopPair.twistedChainComplexπ_f_apply_eq_zero_iff`), and on a relative cycle, iterated
barycentric subdivision changes the relative class of a representative by the boundary of the
class of its subdivision prism (`TopPair.twistedChainComplexπ_f_sub_iterate_twistedSubdivision`).
They are the inputs from small chains to excision with local coefficients.

For subsets `C ⊆ A` of `X`, with `L` restricted to `A`, the relative twisted chains of the pair
`(A, C)` are the quotient of the twisted chains of `X` supported in `A` by those supported in `C`
(`TauCeti.LocalCoefficientSystem.isColimitSubsetPairTwistedChainComplexπ`). An inclusion of pairs
of subsets induces a map of relative twisted chains
(`TauCeti.LocalCoefficientSystem.subsetPairTwistedChainComplexMap`), characterized by
`TauCeti.LocalCoefficientSystem.twistedChainComplexπ_comp_subsetPairTwistedChainComplexMap` and
functorial in the inclusion, and so is the induced map of relative twisted homology
(`TauCeti.LocalCoefficientSystem.subsetPairTwistedHomologyMap`). Pairs of subsets with the same sets
therefore have isomorphic relative twisted homology
(`TauCeti.LocalCoefficientSystem.subsetPairTwistedHomologyIso`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Topology Simplicial

universe u v w

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Support

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- An ambient twisted chain vanishes in relative chains exactly when it is supported in the
subspace. -/
lemma twistedChainComplexπ_f_apply_eq_zero_iff {k : ℕ} (z : L.twistedChainComplex.X k) :
    ((P.twistedChainComplexπ L).f k).hom z = 0 ↔
      z ∈ smallTwistedChains L (fun _ : Unit ↦ Set.range P.map) k := by
  have hsmall (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌) :
      σ ∈ (P.fst.smallSingularSubcomplex fun _ : Unit ↦ Set.range P.map).obj _ ↔
        Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map := by
    rw [TopCat.mem_smallSingularSubcomplex_iff, exists_const,
      ← P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff,
      P.mem_range_toSSet_map_app_iff_range_simplexMap_subset]
  rw [mem_smallTwistedChains_iff]
  constructor
  · intro hz σ hσ
    rw [← P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ (mt (hsmall σ).2 hσ), hz,
      map_zero]
  · intro hz
    refine P.twistedChainComplex_ext_coeff L fun σ hσ ↦ ?_
    rw [P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply, map_zero]
    exact hz σ (mt (hsmall σ).1 hσ)

/-- On a relative cycle, iterated barycentric subdivision of a representing ambient chain changes
its relative class by the boundary of the relative class of the subdivision prism. -/
lemma twistedChainComplexπ_f_sub_iterate_twistedSubdivision {n : ℕ}
    (c : L.twistedChainComplex.X n)
    (hc : (P.twistedChainComplex L).d n (n - 1) ((P.twistedChainComplexπ L).f n c) = 0)
    (N : ℕ) :
    (P.twistedChainComplexπ L).f n c -
        (P.twistedChainComplexπ L).f n ((End.of (twistedSubdivisionChainMap L) ^ N).asHom.f n c) =
      (P.twistedChainComplex L).d (n + 1) n ((P.twistedChainComplexπ L).f (n + 1)
        (((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1) c)) := by
  rw [HomologicalComplex.Hom.comm_apply, ← map_sub]
  cases n with
  | zero =>
    have h := ((twistedSubdivisionHomotopy L).idPow N).comm_zero_apply c
    rw [HomologicalComplex.id_f, ModuleCat.id_apply] at h
    rw [sub_eq_of_eq_add h]
  | succ k =>
    have h := ((twistedSubdivisionHomotopy L).idPow N).comm_succ_apply k c
    rw [HomologicalComplex.id_f, ModuleCat.id_apply] at h
    -- The boundary of `c` lies in the subspace, hence so does its prism.
    have hd : (P.twistedChainComplexπ L).f k (L.twistedChainComplex.d (k + 1) k c) = 0 := by
      rw [← HomologicalComplex.Hom.comm_apply]
      exact hc
    rw [twistedChainComplexπ_f_apply_eq_zero_iff] at hd
    have hD := (P.twistedChainComplexπ_f_apply_eq_zero_iff L _).2
      (idPow_twistedSubdivisionHomotopy_hom_mem_smallTwistedChains L _ hd N)
    rw [sub_eq_of_eq_add h, map_add, hD, zero_add]

end Support

end TopPair

namespace TauCeti.LocalCoefficientSystem

open Limits

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-! ### Relative chains of pairs of subsets as quotients of supported chains -/

section Quotient

variable {A C : Set X}

/- The ambient space of `TopPair.ofInclusion h` is `TopCat.of A` only after unfolding the Mathlib
definition `CategoryTheory.Arrow.mk`, so composites with the relative chains of this pair are not
type-correct at the transparency used by `rw` and `simp`, and even `Category.assoc` fails to
rewrite them. The proofs below that mention the pair directly are therefore assembled from
equations by `Eq.trans`, which unifies up to unfolding. -/

/-- The chains of `C` vanish in the relative chains of `(A, C)`. -/
@[simp, reassoc]
lemma subsetTwistedChainComplexMap_comp_twistedChainComplexπ (h : C ⊆ A) :
    subsetTwistedChainComplexMap L h ≫ (TopPair.ofInclusion h).twistedChainComplexπ
      ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) = 0 :=
  (congrArg (· ≫ _) (subsetTwistedChainComplexMap_def L h)).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((TopPair.ofInclusion h).twistedChainComplexMap_comp_twistedChainComplexπ
      ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L))).trans comp_zero

/-- The quotient map from the twisted chains of `X` supported in `A` onto the relative twisted
chains of the pair `(A, C)`, with `L` restricted to `A`. -/
def subsetPairTwistedChainComplexπ (h : C ⊆ A) :
    smallTwistedChainComplex L (fun _ : Unit ↦ A) ⟶
      (TopPair.ofInclusion h).twistedChainComplex
        ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) :=
  (subspaceTwistedChainComplexIso L A).inv ≫ (TopPair.ofInclusion h).twistedChainComplexπ _

/-- Read on the twisted chains of the subspace `A`, the quotient map onto the relative chains of
`(A, C)` is the quotient map of the pair. -/
@[reassoc (attr := simp)]
lemma subspaceTwistedChainComplexIso_hom_comp_subsetPairTwistedChainComplexπ (h : C ⊆ A) :
    (subspaceTwistedChainComplexIso L A).hom ≫ subsetPairTwistedChainComplexπ L h =
      (TopPair.ofInclusion h).twistedChainComplexπ _ :=
  Iso.hom_inv_id_assoc _ _

instance epi_subsetPairTwistedChainComplexπ (h : C ⊆ A) :
    Epi (subsetPairTwistedChainComplexπ L h) :=
  epi_comp' inferInstance (TopPair.epi_twistedChainComplexπ _ _)

/-- The chains of `X` supported in `C` vanish in the relative chains of `(A, C)`. -/
@[simp, reassoc]
lemma smallTwistedChainComplexSubsetInclusion_comp_subsetPairTwistedChainComplexπ (h : C ⊆ A) :
    smallTwistedChainComplexSubsetInclusion L h ≫ subsetPairTwistedChainComplexπ L h = 0 :=
  (smallTwistedChainComplexSubsetInclusion_comp_subspaceTwistedChainComplexIso_inv_assoc
      L h _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (subsetTwistedChainComplexMap_comp_twistedChainComplexπ L h)).trans
      comp_zero

/-- The chains of the subspace of the pair `(A, C)`, read in the chains of `X` supported in `A`,
are supported in `C`. -/
private lemma exists_twistedChainComplexMap_ofInclusion_map_comp (h : C ⊆ A) :
    ∃ ℓ, twistedChainComplexMap (TopPair.ofInclusion h).map
        ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) ≫
      (subspaceTwistedChainComplexIso L A).hom =
        ℓ ≫ smallTwistedChainComplexSubsetInclusion L h := by
  let g := twistedChainComplexMap (TopPair.ofInclusion h).map
    ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L)
  have hind : Topology.IsInducing (TopPair.ofInclusion h).map :=
    (TopPair.ofInclusion h).prop.isInducing
  refine ⟨smallTwistedChainComplexLift
    (g ≫ twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L) fun n ↦ ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    refine twistedChainComplexMap_mem_smallTwistedChains
      (fun _ : Unit ↦ Set.range (TopPair.ofInclusion h).map) (fun _ : Unit ↦ C)
      (TopCat.ofHom (ContinuousMap.subtypeVal A)) L id (fun _ ↦ ?_) ?_
    · rintro _ ⟨y, rfl⟩
      exact y.property
    · rw [← range_twistedChainComplexMap_f _ _ hind]
      exact LinearMap.mem_range_self _ x
  · refine (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ A))).1
      ((Category.assoc _ _ _).trans <| (congrArg (g ≫ ·)
        (subspaceTwistedChainComplexIso_hom_ι L A)).trans ?_)
    rw [Category.assoc, smallTwistedChainComplexInclusion_ι, smallTwistedChainComplexLift_ι]

/-- **The relative twisted chains of `(A, C)` are the quotient of the chains of `X` supported in
`A` by those supported in `C`.** -/
def isColimitSubsetPairTwistedChainComplexπ (h : C ⊆ A) :
    IsColimit (CokernelCofork.ofπ (subsetPairTwistedChainComplexπ L h)
      (smallTwistedChainComplexSubsetInclusion_comp_subsetPairTwistedChainComplexπ L h)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun k hk ↦
    ⟨(TopPair.ofInclusion h).twistedChainComplexDesc _
        ((subspaceTwistedChainComplexIso L A).hom ≫ k) (by
          obtain ⟨ℓ, hℓ⟩ := exists_twistedChainComplexMap_ofInclusion_map_comp L h
          exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ k) hℓ).trans <|
            (Category.assoc _ _ _).trans <| (congrArg (ℓ ≫ ·) hk).trans comp_zero),
      (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
        ((TopPair.ofInclusion h).twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _)).trans
          (Iso.inv_hom_id_assoc _ _)⟩

end Quotient

/-! ### Maps of relative twisted chains of pairs of subsets -/

section SubsetPair

variable {A₁ C₁ A₂ C₂ A₃ C₃ : Set X} (hC₁ : C₁ ⊆ A₁) (hC₂ : C₂ ⊆ A₂) (hC₃ : C₃ ⊆ A₃)

/-- The map of relative twisted chains `C(A₁, C₁; L) ⟶ C(A₂, C₂; L)` induced by an inclusion of
pairs of subsets of `X`, `A₁ ⊆ A₂` and `C₁ ⊆ C₂`, with `L` restricted to `A₁` and to `A₂`: the
change of coefficients identifying the two restrictions of `L` to `A₁`, followed by the map
`TopPair.twistedChainComplexMap` of the inclusion of pairs. It is characterized by
`TauCeti.LocalCoefficientSystem.twistedChainComplexπ_comp_subsetPairTwistedChainComplexMap`. -/
def subsetPairTwistedChainComplexMap (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) :
    (TopPair.ofInclusion hC₁).twistedChainComplex
        ((pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj L) ⟶
      (TopPair.ofInclusion hC₂).twistedChainComplex
        ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj L) :=
  (TopPair.ofInclusion hC₁).twistedChainComplexCoefficientMap
      ((pullbackCompIso (TopCat.ofHom (ContinuousMap.inclusion hA)).hom
        (TopCat.ofHom (ContinuousMap.subtypeVal A₂)).hom).hom.app L) ≫
    TopPair.twistedChainComplexMap
      (TopPair.ofHom (X := TopPair.ofInclusion hC₁) (Y := TopPair.ofInclusion hC₂)
        (TopCat.ofHom (ContinuousMap.inclusion hA)) (TopCat.ofHom (ContinuousMap.inclusion hC)) rfl)
      ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj L)

/-- The map of relative twisted chains induced by an inclusion of pairs of subsets is the change of
coefficients identifying the two restrictions of `L` to `A₁`, followed by the map of the inclusion
of pairs. -/
lemma subsetPairTwistedChainComplexMap_def (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) :
    subsetPairTwistedChainComplexMap L hC₁ hC₂ hA hC =
      (TopPair.ofInclusion hC₁).twistedChainComplexCoefficientMap
          ((pullbackCompIso (TopCat.ofHom (ContinuousMap.inclusion hA)).hom
            (TopCat.ofHom (ContinuousMap.subtypeVal A₂)).hom).hom.app L) ≫
        TopPair.twistedChainComplexMap
          (TopPair.ofHom (X := TopPair.ofInclusion hC₁) (Y := TopPair.ofInclusion hC₂)
            (TopCat.ofHom (ContinuousMap.inclusion hA)) (TopCat.ofHom (ContinuousMap.inclusion hC))
            rfl)
          ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj L) :=
  (rfl)

/-- The map of relative twisted chains induced by an inclusion of pairs of subsets is induced by
the map `TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexMap` of absolute twisted
chains. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_subsetPairTwistedChainComplexMap (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) :
    (TopPair.ofInclusion hC₁).twistedChainComplexπ _ ≫
        subsetPairTwistedChainComplexMap L hC₁ hC₂ hA hC =
      subsetTwistedChainComplexMap L hA ≫ (TopPair.ofInclusion hC₂).twistedChainComplexπ _ :=
  (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
    ((TopPair.ofInclusion hC₁).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
      _)).trans <| (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap _ _)).trans <|
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (subsetTwistedChainComplexMap_def L hA).symm)

/-- The map of relative twisted chains induced by an inclusion of pairs of subsets is induced by
the inclusion of the chains of `X` supported in `A₁` into those supported in `A₂`. -/
@[reassoc (attr := simp)]
lemma subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap (hA : A₁ ⊆ A₂)
    (hC : C₁ ⊆ C₂) :
    subsetPairTwistedChainComplexπ L hC₁ ≫ subsetPairTwistedChainComplexMap L hC₁ hC₂ hA hC =
      smallTwistedChainComplexSubsetInclusion L hA ≫ subsetPairTwistedChainComplexπ L hC₂ :=
  (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
    (twistedChainComplexπ_comp_subsetPairTwistedChainComplexMap L hC₁ hC₂ hA hC)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
        (smallTwistedChainComplexSubsetInclusion_comp_subspaceTwistedChainComplexIso_inv
          L hA).symm).trans (Category.assoc _ _ _)

/-- The map of relative twisted chains induced by the identity inclusion of a pair of subsets is
the identity. -/
@[simp]
lemma subsetPairTwistedChainComplexMap_self :
    subsetPairTwistedChainComplexMap L hC₁ hC₁ subset_rfl subset_rfl = 𝟙 _ := by
  refine (cancel_epi (subsetPairTwistedChainComplexπ L hC₁)).1 <|
    (subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap L hC₁ hC₁ _ _).trans <|
      .trans ?_ (Category.comp_id _).symm
  exact (congrArg (· ≫ subsetPairTwistedChainComplexπ L hC₁)
    smallTwistedChainComplexInclusion_refl).trans (Category.id_comp _)

/-- The maps of relative twisted chains induced by inclusions of pairs of subsets compose. -/
@[reassoc (attr := simp)]
lemma subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap (hA : A₁ ⊆ A₂)
    (hC : C₁ ⊆ C₂) (hA' : A₂ ⊆ A₃) (hC' : C₂ ⊆ C₃) :
    subsetPairTwistedChainComplexMap L hC₁ hC₂ hA hC ≫
        subsetPairTwistedChainComplexMap L hC₂ hC₃ hA' hC' =
      subsetPairTwistedChainComplexMap L hC₁ hC₃ (hA.trans hA') (hC.trans hC') := by
  rw [← cancel_epi (subsetPairTwistedChainComplexπ L hC₁),
    subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap_assoc,
    subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap,
    subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap, ← Category.assoc,
    smallTwistedChainComplexInclusion_comp]

/-- Equal pairs of subsets have isomorphic relative twisted chains: the maps induced by the two
inclusions are inverse to each other. This compares pairs of subsets which are equal but are
written differently, such as `f ⁻¹' (U ∩ V)` and `f ⁻¹' U ∩ f ⁻¹' V`. -/
def subsetPairTwistedChainComplexIsoOfEq (hA : A₁ = A₂) (hC : C₁ = C₂) :
    (TopPair.ofInclusion hC₁).twistedChainComplex
        ((pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj L) ≅
      (TopPair.ofInclusion hC₂).twistedChainComplex
        ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj L) where
  hom := subsetPairTwistedChainComplexMap L hC₁ hC₂ hA.le hC.le
  inv := subsetPairTwistedChainComplexMap L hC₂ hC₁ hA.ge hC.ge
  hom_inv_id := (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap L hC₁ hC₂
    hC₁ _ _ _ _).trans (subsetPairTwistedChainComplexMap_self L hC₁)
  inv_hom_id := (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap L hC₂ hC₁
    hC₂ _ _ _ _).trans (subsetPairTwistedChainComplexMap_self L hC₂)

@[simp]
lemma subsetPairTwistedChainComplexIsoOfEq_hom (hA : A₁ = A₂) (hC : C₁ = C₂) :
    (subsetPairTwistedChainComplexIsoOfEq L hC₁ hC₂ hA hC).hom =
      subsetPairTwistedChainComplexMap L hC₁ hC₂ hA.le hC.le :=
  (rfl)

@[simp]
lemma subsetPairTwistedChainComplexIsoOfEq_inv (hA : A₁ = A₂) (hC : C₁ = C₂) :
    (subsetPairTwistedChainComplexIsoOfEq L hC₁ hC₂ hA hC).inv =
      subsetPairTwistedChainComplexMap L hC₂ hC₁ hA.ge hC.ge :=
  (rfl)

/-- The map of relative twisted homology `Hₙ(A₁, C₁; L) ⟶ Hₙ(A₂, C₂; L)` induced by an inclusion of
pairs of subsets of `X`. -/
abbrev subsetPairTwistedHomologyMap (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) (n : ℕ) :
    (TopPair.ofInclusion hC₁).twistedHomology
        ((pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj L) n ⟶
      (TopPair.ofInclusion hC₂).twistedHomology
        ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj L) n :=
  HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L hC₁ hC₂ hA hC) n

/-- The map of relative twisted homology induced by the identity inclusion of a pair of subsets is
the identity. -/
@[simp]
lemma subsetPairTwistedHomologyMap_self (n : ℕ) :
    subsetPairTwistedHomologyMap L hC₁ hC₁ subset_rfl subset_rfl n = 𝟙 _ := by
  rw [subsetPairTwistedHomologyMap, subsetPairTwistedChainComplexMap_self,
    HomologicalComplex.homologyMap_id]

/-- The maps of relative twisted homology induced by inclusions of pairs of subsets compose. -/
@[reassoc (attr := simp)]
lemma subsetPairTwistedHomologyMap_comp_subsetPairTwistedHomologyMap (hA : A₁ ⊆ A₂)
    (hC : C₁ ⊆ C₂) (hA' : A₂ ⊆ A₃) (hC' : C₂ ⊆ C₃) (n : ℕ) :
    subsetPairTwistedHomologyMap L hC₁ hC₂ hA hC n ≫
        subsetPairTwistedHomologyMap L hC₂ hC₃ hA' hC' n =
      subsetPairTwistedHomologyMap L hC₁ hC₃ (hA.trans hA') (hC.trans hC') n := by
  rw [← HomologicalComplex.homologyMap_comp,
    subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap]

/-- Two pairs of subsets of `X` with the same sets have isomorphic relative twisted homology,
through the maps induced by the inclusions both ways. -/
@[expose, simps]
def subsetPairTwistedHomologyIso (hA : A₁ ⊆ A₂) (hA' : A₂ ⊆ A₁) (hC : C₁ ⊆ C₂) (hC' : C₂ ⊆ C₁)
    (n : ℕ) :
    (TopPair.ofInclusion hC₁).twistedHomology
        ((pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj L) n ≅
      (TopPair.ofInclusion hC₂).twistedHomology
        ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj L) n where
  hom := subsetPairTwistedHomologyMap L hC₁ hC₂ hA hC n
  inv := subsetPairTwistedHomologyMap L hC₂ hC₁ hA' hC' n
  hom_inv_id := by simp
  inv_hom_id := by simp

end SubsetPair

end TauCeti.LocalCoefficientSystem
