/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Compacts
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic

/-!
# Compact supports of singular homology

Every singular simplex has compact image, so the singular simplicial set and the singular homology
of a topological space `X` are the filtered colimits of those of its compact subsets
`K : Compacts X` (`TauCeti.isColimitMapCoconeToSSetCompacts` and
`TauCeti.isColimitMapCoconeSingularHomologyCompacts`). More generally, the same holds for any
monotone family of subsets indexed by a nonempty directed preorder whose members absorb every
compact subset (`TauCeti.isColimitMapCoconeSingularHomologySubset`).

With coefficients in a module `N`, the colimit statement gives two concrete consequences:

* every singular homology class of `X` is the image of a class of some compact subset `K ⊆ X`
  (`TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq`), and in a weakly locally compact
  space it comes from an open subset `U` contained in a compact subset `K`
  (`TauCeti.exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq`);
* a singular homology class of a compact subset `K ⊆ X` whose image in `X` vanishes already
  vanishes in some compact superset `L ⊇ K`
  (`TauCeti.exists_isCompact_singularHomologyMap_inclusion_eq_zero`).

This file also records the disjoint-open vanishing principle
(`TauCeti.eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint`): if classes on two disjoint
open subsets `U` and `W` of `X` map to the same class in `Hₖ(U ∪ W; N)`, then both map to zero.
Together with compact supports, this drives the vanishing of top singular homology on noncompact
manifolds (`TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact`).

## Main definitions and results

* `TauCeti.subsetDiagram` and `TauCeti.subsetCocone`: the diagram of subspaces of a monotone family
  and its cocone of inclusions into `X`.
* `TauCeti.isColimitMapCoconeToSSetSubset` and
  `TauCeti.isColimitMapCoconeSingularHomologySubset`: the singular simplicial set and singular
  homology of `X` as filtered colimits over a monotone family absorbing compact sets.
* `TauCeti.exists_singularHomologyMap_subtypeVal_eq` and
  `TauCeti.exists_singularHomologyMap_inclusion_eq_zero_of_subset`: compact support of classes and
  of homological relations for a monotone family absorbing compact sets.
* `TauCeti.compactsDiagram` and `TauCeti.compactsCocone`: the diagram of compact subsets
  `Compacts X` of `X` and its cocone of inclusions into `X`.
* `TauCeti.isColimitMapCoconeToSSetCompacts` and
  `TauCeti.isColimitMapCoconeSingularHomologyCompacts`: Hatcher's Proposition 3.33, expressing
  singular simplices and singular homology as filtered colimits over `Compacts X`.
* `TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq` and
  `TauCeti.exists_isCompact_singularHomologyMap_inclusion_eq_zero`: compact support of classes and
  of homological relations in `Hₖ(X; N)`.
* `TauCeti.exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq`: in a weakly locally compact
  space, every class of `Hₖ(X; N)` comes from an open set contained in a compact set.
* `TauCeti.isZero_singularHomology_of_isEmpty` and
  `TauCeti.eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint`: vanishing of singular homology
  of an empty space, and vanishing of classes on disjoint open sets that agree on their union.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.33, p. 244.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology TopologicalSpace TopCat Set

universe w v u

namespace TauCeti

section SubsetFamily

variable {X : TopCat.{w}} {J : Type w} [Preorder J] {U : J → Set X}

/-- The subspaces `U j` of a monotone family in `X`, as a functor on the index preorder. -/
@[expose, simps]
def subsetDiagram (hU : Monotone U) : J ⥤ TopCat.{w} where
  obj j := of ↥(U j)
  map f := ofHom (ContinuousMap.inclusion (hU f.le))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The cocone of inclusions `U j ⟶ X` over `TauCeti.subsetDiagram`. -/
@[expose, simps]
def subsetCocone (hU : Monotone U) : Cocone (subsetDiagram hU) where
  pt := X
  ι :=
    { app j := ofHom (ContinuousMap.subtypeVal (U j))
      naturality _ _ _ := (Category.comp_id _).symm }

variable [IsDirected J (· ≤ ·)] [Nonempty J]

/-- **Singular simplices of a family absorbing compact sets.** If `U` is a monotone family of
subsets of `X` indexed by a nonempty directed preorder such that every compact subset of `X` lies
in some `U j`, then the singular simplicial set of `X` is the colimit of those of the `U j`. -/
def isColimitMapCoconeToSSetSubset (hU : Monotone U)
    (hK : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ U j) :
    IsColimit (toSSet.mapCocone (subsetCocone hU)) :=
  isColimitMapCoconeToSSet (subsetCocone hU)
    (fun _ ↦ IsEmbedding.subtypeVal)
    fun K hKc ↦ (hK K hKc).imp fun _ hj x hx ↦ ⟨⟨x, hj hx⟩, rfl⟩

/-- **Singular homology of a family absorbing compact sets.** If `U` is a monotone family of
subsets of `X` indexed by a nonempty directed preorder such that every compact subset of `X` lies
in some `U j`, then the singular homology of `X` is the colimit of the singular homology of the
`U j`, whenever filtered colimits of shape `J` are exact in `C`. -/
def isColimitMapCoconeSingularHomologySubset {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] (R : C) (k : ℕ) [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (hU : Monotone U) (hK : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ U j) :
    IsColimit (((singularHomologyFunctor C k).obj R).mapCocone (subsetCocone hU)) :=
  isColimitMapCoconeSingularHomology R k (subsetCocone hU)
    (fun _ ↦ IsEmbedding.subtypeVal)
    fun K hKc ↦ (hK K hKc).imp fun _ hj x hx ↦ ⟨⟨x, hj hx⟩, rfl⟩

/-- **Every singular homology class comes from a member of a family absorbing compact sets.** With
coefficients in a module `N`, if `U` is a monotone family indexed by a nonempty directed preorder
absorbing compact subsets of `X`, every class of `Hₖ(X; N)` lies in the image of `Hₖ(U j; N)` for
some `j`. -/
theorem exists_singularHomologyMap_subtypeVal_eq {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)
    (k : ℕ) (hU : Monotone U) (hK : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ U j)
    (x : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj X) :
    ∃ (j : J) (y : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥(U j))),
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.subtypeVal (U j))) y = x :=
  Concrete.isColimit_exists_rep _ (isColimitMapCoconeSingularHomologySubset N k hU hK) x

/-- **Vanishing in the space is detected in a member of a family absorbing compact sets.** With
coefficients in a module `N`, if `U` is a monotone family indexed by a nonempty directed preorder
absorbing compact subsets of `X`, a class of `Hₖ(U i; N)` whose image in `Hₖ(X; N)` vanishes
already vanishes in `Hₖ(U j; N)` for some `j ≥ i`. -/
theorem exists_singularHomologyMap_inclusion_eq_zero_of_subset {Λ : Type w} [Ring Λ]
    (N : ModuleCat.{w} Λ) (k : ℕ) (hU : Monotone U)
    (hK : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ U j) {i : J}
    (y : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥(U i)))
    (hy : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (ofHom (ContinuousMap.subtypeVal (U i))) y = 0) :
    ∃ (j : J) (hij : i ≤ j),
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.inclusion (hU hij))) y = 0 := by
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq (i := i) (j := i) _
    (isColimitMapCoconeSingularHomologySubset N k hU hK) y 0 (by rw [map_zero]; exact hy)
  dsimp only [Functor.comp_map, subsetDiagram_map] at hfg
  rw [map_zero] at hfg
  exact ⟨j, f.le, hfg⟩

end SubsetFamily

section CompactSubsets

/-- The diagram of compact subsets `Compacts X` of `X`, ordered by inclusion. -/
@[expose]
def compactsDiagram (X : TopCat.{w}) : Compacts X ⥤ TopCat.{w} :=
  subsetDiagram (U := SetLike.coe) fun _ _ h ↦ h

@[simp]
theorem compactsDiagram_obj (X : TopCat.{w}) (K : Compacts X) :
    (compactsDiagram X).obj K = of K :=
  (rfl)

@[simp]
theorem compactsDiagram_map (X : TopCat.{w}) {K L : Compacts X} (f : K ⟶ L) :
    (compactsDiagram X).map f = ofHom (ContinuousMap.inclusion (s := (K : Set X)) f.le) :=
  (rfl)

/-- The cocone of inclusions `K ⟶ X` over the diagram `TauCeti.compactsDiagram` of compact subsets
of `X`. -/
@[expose]
def compactsCocone (X : TopCat.{w}) : Cocone (compactsDiagram X) :=
  subsetCocone (U := SetLike.coe) fun _ _ h ↦ h

@[simp]
theorem compactsCocone_pt (X : TopCat.{w}) : (compactsCocone X).pt = X :=
  (rfl)

@[simp]
theorem compactsCocone_ι_app (X : TopCat.{w}) (K : Compacts X) :
    (compactsCocone X).ι.app K = ofHom (ContinuousMap.subtypeVal (K : Set X)) :=
  (rfl)

/-- **Singular simplices are the colimit over compact subsets.** The singular simplicial set of `X`
is the filtered colimit of the singular simplicial sets of the compact subsets of `X`. -/
def isColimitMapCoconeToSSetCompacts (X : TopCat.{w}) :
    IsColimit (toSSet.mapCocone (compactsCocone X)) :=
  isColimitMapCoconeToSSetSubset (X := X) (U := fun K : Compacts X ↦ (K : Set X))
    (fun _ _ h ↦ h) fun K hK ↦ ⟨⟨K, hK⟩, subset_rfl⟩

/-- **Singular homology is the colimit over compact subsets** (Hatcher, Proposition 3.33). In every
degree, the singular homology of `X` is the filtered colimit of the singular homology of the
compact subsets `Compacts X` of `X`, provided filtered colimits over `Compacts X` are exact in
`C`. -/
def isColimitMapCoconeSingularHomologyCompacts {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] (R : C) (k : ℕ) (X : TopCat.{w})
    [HasColimitsOfShape (Compacts X) C] [HasExactColimitsOfShape (Compacts X) C] :
    IsColimit (((singularHomologyFunctor C k).obj R).mapCocone (compactsCocone X)) :=
  isColimitMapCoconeSingularHomologySubset (X := X) (U := fun K : Compacts X ↦ (K : Set X))
    R k (fun _ _ h ↦ h) fun K hK ↦ ⟨⟨K, hK⟩, subset_rfl⟩

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) (k : ℕ) {Y : Type w} [TopologicalSpace Y]

/-- **Every singular homology class is supported on a compact set** (Hatcher, Proposition 3.33).
With coefficients in a module `N`, every class of `Hₖ(Y; N)` is the image of a class of `Hₖ(K; N)`
for some compact subset `K ⊆ Y`. -/
theorem exists_isCompact_singularHomologyMap_subtypeVal_eq
    (x : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of Y)) :
    ∃ (K : Set Y) (_ : IsCompact K)
      (y : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥K)),
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.subtypeVal K)) y = x := by
  obtain ⟨K, y, hy⟩ :=
    Concrete.isColimit_exists_rep _ (isColimitMapCoconeSingularHomologyCompacts N k (of Y)) x
  exact ⟨K.1, K.2, y, hy⟩

/-- **A class on a compact subset that vanishes in the space vanishes in a compact superset**
(Hatcher, Proposition 3.33). If `K ⊆ Y` is compact and `y ∈ Hₖ(K; N)` maps to zero in `Hₖ(Y; N)`,
then `y` already maps to zero in `Hₖ(L; N)` for some compact `L` with `K ⊆ L`. -/
theorem exists_isCompact_singularHomologyMap_inclusion_eq_zero {K : Set Y} (hK : IsCompact K)
    (y : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥K))
    (hy : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (ofHom (ContinuousMap.subtypeVal K)) y = 0) :
    ∃ (L : Set Y) (_ : IsCompact L) (hKL : K ⊆ L),
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.inclusion hKL)) y = 0 := by
  obtain ⟨L, hKL, hyL⟩ := exists_singularHomologyMap_inclusion_eq_zero_of_subset N k
    (X := of Y) (U := fun S : Compacts (of Y) ↦ (S : Set (of Y))) (fun _ _ h ↦ h)
    (fun S hS ↦ ⟨⟨S, hS⟩, subset_rfl⟩) (i := ⟨K, hK⟩) y hy
  exact ⟨L.1, L.2, hKL, hyL⟩

/-- **In a weakly locally compact space, every homology class comes from a relatively compact open
set.** Every class of `Hₖ(Y; N)` is the image of a class of `Hₖ(U; N)` for an open subset `U`
contained in a compact subset `K` of `Y`. -/
theorem exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq [WeaklyLocallyCompactSpace Y]
    (x : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of Y)) :
    ∃ (U K : Set Y), IsOpen U ∧ IsCompact K ∧ U ⊆ K ∧
      ∃ u : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥U),
        ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
          (ofHom (ContinuousMap.subtypeVal U)) u = x := by
  obtain ⟨A, hA, a, rfl⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq N k x
  obtain ⟨K, hK, hAK⟩ := exists_compact_superset hA
  refine ⟨interior K, K, isOpen_interior, hK, interior_subset,
    ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map (ofHom (ContinuousMap.inclusion hAK))
      a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end CompactSubsets

section DisjointOpens

/-- The homology of the singular simplicial set of an empty space vanishes in every degree. -/
theorem isZero_toSSet_homology_of_isEmpty {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] (R : C) (X : TopCat.{w}) [IsEmpty X] (k : ℕ) :
    IsZero ((toSSet.obj X).homology R k) := by
  have : (toSSet.obj X).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      isEmptyElim (TopCat.toSSetObj₀Equiv σ)
  exact (HomologicalComplex.homologyFunctor C _ k).map_isZero ((toSSet.obj X).isZero_chainComplex R)

/-- **The singular homology of an empty space vanishes** in every degree, for arbitrary
coefficients. -/
theorem isZero_singularHomology_of_isEmpty {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] (R : C) (X : TopCat.{w}) [IsEmpty X] (k : ℕ) :
    IsZero (((singularHomologyFunctor C k).obj R).obj X) :=
  isZero_toSSet_homology_of_isEmpty R X k

/-- **Classes on disjoint open sets that agree in the homology of their union vanish.** Let `U` and
`W` be disjoint open subsets of `Y`, and let `u ∈ Hₖ(U; N)` and `v ∈ Hₖ(W; N)` map to the same
element of `Hₖ(U ∪ W; N)`. Then that common image is zero: by exactness of the Mayer–Vietoris
sequence of `{U, W}` on `U ∪ W` and the vanishing of `Hₖ(∅; N)`, the map
`Hₖ(U; N) ⊞ Hₖ(W; N) ⟶ Hₖ(U ∪ W; N)` is a monomorphism sending `(u, -v)` to zero. -/
theorem eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint {Λ : Type w} [Ring Λ]
    (N : ModuleCat.{w} Λ) {k : ℕ} {Y : Type w} [TopologicalSpace Y] {U W : Set Y}
    (hU : IsOpen U) (hW : IsOpen W) (hUW : Disjoint U W)
    (u : ((toSSet.obj (of ↥U)).homology N k : ModuleCat.{w} Λ))
    (v : ((toSSet.obj (of ↥W)).homology N k : ModuleCat.{w} Λ))
    (huv : SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
        (subset_union_left (s := U) (t := W))))) N k u =
      SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
        (subset_union_right (s := U) (t := W))))) N k v) :
    SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
      (subset_union_left (s := U) (t := W))))) N k u = 0 := by
  let Z : TopCat.{w} := of ↥(U ∪ W)
  let U' : Set Z := Subtype.val ⁻¹' U
  let W' : Set Z := Subtype.val ⁻¹' W
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have hW' : IsOpen W' := hW.preimage continuous_subtype_val
  have hcov : U' ∪ W' = univ := eq_univ_of_forall fun x ↦ x.2
  have : IsEmpty (of ↥(U' ∩ W')) := ⟨fun x ↦ hUW.le_bot ⟨x.2.1, x.2.2⟩⟩
  have hzero := isZero_toSSet_homology_of_isEmpty N (of ↥(U' ∩ W')) k
  have hmono : Mono (SSet.mayerVietorisFromBiprod N
      (toSSet.map (ofHom (ContinuousMap.subtypeVal U')))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal W'))) k) :=
    (TopCat.mayerVietoris_exact₂ N hU' hW' hcov k).mono_g (hzero.eq_of_src _ _)
  let fU : of ↥U ⟶ of ↥U' := ofHom ⟨fun x ↦ ⟨⟨x.1, Or.inl x.2⟩, x.2⟩, by fun_prop⟩
  let fW : of ↥W ⟶ of ↥W' := ofHom ⟨fun x ↦ ⟨⟨x.1, Or.inr x.2⟩, x.2⟩, by fun_prop⟩
  let HU' : ModuleCat.{w} Λ := (toSSet.obj (of ↥U')).homology N k
  let HW' : ModuleCat.{w} Λ := (toSSet.obj (of ↥W')).homology N k
  set u' : HU' := SSet.homologyMap (toSSet.map fU) N k u with hu'_def
  set v' : HW' := SSet.homologyMap (toSSet.map fW) N k v with hv'_def
  have hfacU : ofHom (ContinuousMap.inclusion (subset_union_left (s := U) (t := W))) =
      fU ≫ ofHom (ContinuousMap.subtypeVal U') := rfl
  have hfacW : ofHom (ContinuousMap.inclusion (subset_union_right (s := U) (t := W))) =
      fW ≫ ofHom (ContinuousMap.subtypeVal W') := rfl
  have hinl : (SSet.mayerVietorisFromBiprod N
      (toSSet.map (ofHom (ContinuousMap.subtypeVal U')))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal W'))) k)
      ((biprod.inl : HU' ⟶ HU' ⊞ HW') u') =
      (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U'))) N k) u' :=
    ConcreteCategory.congr_hom (SSet.inl_mayerVietorisFromBiprod N _ _ k) u'
  have hinr : (SSet.mayerVietorisFromBiprod N
      (toSSet.map (ofHom (ContinuousMap.subtypeVal U')))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal W'))) k)
      ((biprod.inr : HW' ⟶ HU' ⊞ HW') v') =
      (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W'))) N k) v' :=
    ConcreteCategory.congr_hom (SSet.inr_mayerVietorisFromBiprod N _ _ k) v'
  have hu_eq : (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U'))) N k) u' =
      SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
        (subset_union_left (s := U) (t := W))))) N k u := by
    rw [hfacU, toSSet.map_comp, SSet.homologyMap_comp, ConcreteCategory.comp_apply, ← hu'_def]
  have hv_eq : (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W'))) N k) v' =
      SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
        (subset_union_right (s := U) (t := W))))) N k v := by
    rw [hfacW, toSSet.map_comp, SSet.homologyMap_comp, ConcreteCategory.comp_apply, ← hv'_def]
  have hpair_eq :
      (SSet.mayerVietorisFromBiprod N
        (toSSet.map (ofHom (ContinuousMap.subtypeVal U')))
        (toSSet.map (ofHom (ContinuousMap.subtypeVal W'))) k)
        ((biprod.inl : HU' ⟶ HU' ⊞ HW') u' - (biprod.inr : HW' ⟶ HU' ⊞ HW') v') = 0 := by
    rw [map_sub, hinl, hinr, hu_eq, hv_eq, huv, sub_self]
  have hbw : (biprod.inl : HU' ⟶ HU' ⊞ HW') u' - (biprod.inr : HW' ⟶ HU' ⊞ HW') v' = 0 :=
    ((ModuleCat.mono_iff_injective _).1 hmono) (by simpa only [map_zero] using hpair_eq)
  have hu'_zero : u' = 0 := by
    simpa [HU', HW', ← ConcreteCategory.comp_apply] using
      congrArg (biprod.fst : HU' ⊞ HW' ⟶ HU') hbw
  rw [← hu_eq, hu'_zero, map_zero]

end DisjointOpens

end TauCeti
