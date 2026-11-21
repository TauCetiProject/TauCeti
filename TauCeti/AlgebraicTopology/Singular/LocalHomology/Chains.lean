/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative

/-!
# Relative singular chains supported along closed sets

For a subset `S` of a space `M`, the relative singular chain complex `C(M, M ∖ S)`
(`TauCeti.localChainComplex`) is the chain-level form of the local homology `Hₖ(M, M ∖ S)`
(`TauCeti.localHomology`). For `S ⊆ T` the identity of `M` induces the restriction chain map
`C(M, M ∖ T) ⟶ C(M, M ∖ S)` (`TauCeti.localChainRestriction`), so `S ↦ C(M, M ∖ S)` is
contravariant in `S`. In Pardon's construction of virtual fundamental classes, these complexes on
the closed, or compact, subsets of a space are the basic example of a homotopy K-sheaf: the
partial virtual complexes of an implicit atlas are relative chains of this form on its deformation
spaces, and the duality between the relative homology `H_(n-•)(M, M ∖ Z)` of a manifold and the
compactly supported Čech cohomology of the orientation sheaf on a closed set `Z` is proved from
these properties. This file proves the three properties (Pardon, Lemma A.6.3), all at the level
of chain complexes and for an arbitrary space `M`:

* **The empty set.** `C(M, M ∖ ∅) = C(M, M)` is zero, in particular acyclic
  (`TauCeti.isZero_localChainComplex_empty`).
* **Mayer–Vietoris.** For closed sets `S` and `T`, the sequence
  `C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T) ⟶ C(M, M ∖ (S ∩ T))`, with first map
  `(res, -res)` and second map `res + res`, has monomorphic first map
  (`TauCeti.mono_localChainMayerVietorisToBiprod`, for any `S` and `T`), and the second map
  induces a quasi-isomorphism from the cokernel of the first
  (`TauCeti.quasiIso_cokernelDesc_localChainMayerVietorisFromBiprod`). So the total complex of this
  three-term complex is acyclic. This is the relative Mayer–Vietoris sequence of the open sets
  `M ∖ S` and `M ∖ T` on chains
  (`TopCat.quasiIso_cokernelDesc_relativeMayerVietorisChainFromBiprod`).
* **Continuity.** For a directed decreasing family of closed sets `K i`, the complex
  `C(M, M ∖ ⋂ i, K i)` is the colimit of the complexes `C(M, M ∖ K i)` along the restriction maps
  (`TauCeti.isColimitMapCoconeSingularChainComplexComplPairCoconeIInter`): a singular simplex of
  `M ∖ ⋂ i, K i` has compact image, which misses some `K i`. This is an isomorphism of chain
  complexes, stronger than the quasi-isomorphism Pardon's axiom asks for. More generally the same
  holds for any directed decreasing family of sets `K i ⊇ S` such that every compact set disjoint
  from `S` misses some `K i` (`TauCeti.isColimitMapCoconeSingularChainComplexComplPairCocone`);
  in a Hausdorff space the neighbourhoods of `S` form such a family.

## Main definitions

* `TauCeti.localChainComplex R S`: the relative singular chains `C(M, M ∖ S)`.
* `TauCeti.localChainRestriction R h`: the restriction `C(M, M ∖ T) ⟶ C(M, M ∖ S)` for `S ⊆ T`.
* `TauCeti.localChainMayerVietorisToBiprod R S T`,
  `TauCeti.localChainMayerVietorisFromBiprod R S T`: the maps
  `C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T) ⟶ C(M, M ∖ (S ∩ T))`.
* `TauCeti.complPairDiagram hK`, `TauCeti.complPairCocone hK hSK`: the pairs `(M, M ∖ K i)` of a
  decreasing family of sets, and their cocone over the pair `(M, M ∖ S)` for `S ⊆ K i`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Definition A.2.5 (homotopy K-sheaves) and
  Lemma A.6.3 (relative singular chains).
* A. Hatcher, *Algebraic Topology*, Section 2.2, the relative Mayer–Vietoris sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {M : Type w} [TopologicalSpace M]

/-! ### The chain complexes and their restriction maps -/

/-- The relative singular chain complex `C(M, M ∖ S)` of `M` modulo the complement of `S`, whose
homology is the local homology `Hₖ(M, M ∖ S)` (`TauCeti.localHomology`). -/
abbrev localChainComplex (S : Set M) : ChainComplex A ℕ :=
  (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularChainComplex R

/-- For `S ⊆ T`, the chain map `C(M, M ∖ T) ⟶ C(M, M ∖ S)` on relative singular chains induced by
the identity of `M`. -/
def localChainRestriction {S T : Set M} (h : S ⊆ T) :
    localChainComplex R T ⟶ localChainComplex R S :=
  TopPair.singularChainComplexMap
    (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (compl_subset_compl.2 h)) R

lemma localChainRestriction_def {S T : Set M} (h : S ⊆ T) :
    localChainRestriction R h = TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (compl_subset_compl.2 h)) R :=
  (rfl)

@[simp]
lemma localChainRestriction_refl (S : Set M) :
    localChainRestriction R (subset_refl S) = 𝟙 _ :=
  (congrArg (TopPair.singularChainComplexMap · R) (TopPair.ofSubsetMap_id _)).trans
    (TopPair.singularChainComplexMap_id _ R)

@[reassoc (attr := simp)]
lemma localChainRestriction_comp {S T W : Set M} (h₁ : S ⊆ T) (h₂ : T ⊆ W) :
    localChainRestriction R h₂ ≫ localChainRestriction R h₁ =
      localChainRestriction R (h₁.trans h₂) := by
  rw [localChainRestriction, localChainRestriction, localChainRestriction,
    ← TopPair.singularChainComplexMap_comp]
  exact congrArg (TopPair.singularChainComplexMap · R)
    (TopPair.ofSubsetMap_comp (𝟙 (TopCat.of M)) (𝟙 (TopCat.of M)) _ _ _).symm

/-- On homology, the restriction of relative singular chains is the restriction of local
homology. -/
@[simp]
lemma homologyMap_localChainRestriction {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    HomologicalComplex.homologyMap (localChainRestriction R h) k =
      localHomologyRestriction R h k := by
  rw [localHomologyRestriction_def, localChainRestriction_def]

/-! ### The empty set -/

/-- **The relative chains along the empty set vanish**: `C(M, M ∖ ∅) = C(M, M) = 0`. -/
theorem isZero_localChainComplex_empty : IsZero (localChainComplex R (∅ : Set M)) :=
  TopPair.isZero_singularChainComplex_of_surjective_map _ R <|
    Set.range_eq_univ.1 (TopPair.range_ofSubset_map.trans compl_empty)

/-! ### Mayer–Vietoris -/

section MayerVietoris

variable (S T : Set M)

/-- The first map `C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T)` of the Mayer–Vietoris sequence of
relative singular chains, with components the restriction and minus the restriction. -/
abbrev localChainMayerVietorisToBiprod :
    localChainComplex R (S ∪ T) ⟶ localChainComplex R S ⊞ localChainComplex R T :=
  biprod.lift (localChainRestriction R subset_union_left)
    (-localChainRestriction R subset_union_right)

/-- The second map `C(M, M ∖ S) ⊞ C(M, M ∖ T) ⟶ C(M, M ∖ (S ∩ T))` of the Mayer–Vietoris sequence
of relative singular chains, the sum of the restrictions. -/
abbrev localChainMayerVietorisFromBiprod :
    localChainComplex R S ⊞ localChainComplex R T ⟶ localChainComplex R (S ∩ T) :=
  biprod.desc (localChainRestriction R inter_subset_left)
    (localChainRestriction R inter_subset_right)

/-- The two maps `C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T) ⟶ C(M, M ∖ (S ∩ T))` of the
Mayer–Vietoris sequence of relative singular chains compose to zero. -/
@[reassoc]
lemma localChainMayerVietorisToBiprod_fromBiprod :
    localChainMayerVietorisToBiprod R S T ≫ localChainMayerVietorisFromBiprod R S T = 0 :=
  TopCat.relativeMayerVietorisChainToBiprod_fromBiprod R (X := TopCat.of M)
    (U := Sᶜ) (V := Tᶜ) (compl_subset_compl.2 subset_union_left)
    (compl_subset_compl.2 subset_union_right) (compl_subset_compl.2 inter_subset_left)
    (compl_subset_compl.2 inter_subset_right)

/-- The first map `C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T)` of the Mayer–Vietoris sequence of
relative singular chains, with components the restriction and minus the restriction, is a
monomorphism, for any sets `S` and `T`. -/
theorem mono_localChainMayerVietorisToBiprod : Mono (localChainMayerVietorisToBiprod R S T) :=
  TopCat.mono_relativeMayerVietorisChainToBiprod R (X := TopCat.of M) (U := Sᶜ) (V := Tᶜ)
    (compl_subset_compl.2 subset_union_left) (compl_subset_compl.2 subset_union_right)
    (compl_union S T).ge

variable {S T} in
/-- **Mayer–Vietoris for relative singular chains along closed sets.** For closed sets `S` and
`T`, the second map `C(M, M ∖ S) ⊞ C(M, M ∖ T) ⟶ C(M, M ∖ (S ∩ T))`, the sum of the restrictions,
induces a quasi-isomorphism from the cokernel of the first map
`C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T)`, which is a monomorphism
(`TauCeti.mono_localChainMayerVietorisToBiprod`). So the total complex of the three-term complex
`C(M, M ∖ (S ∪ T)) ⟶ C(M, M ∖ S) ⊞ C(M, M ∖ T) ⟶ C(M, M ∖ (S ∩ T))` is acyclic. -/
theorem quasiIso_cokernelDesc_localChainMayerVietorisFromBiprod (hS : IsClosed S)
    (hT : IsClosed T) :
    QuasiIso (cokernel.desc _ _ (localChainMayerVietorisToBiprod_fromBiprod R S T)) :=
  TopCat.quasiIso_cokernelDesc_relativeMayerVietorisChainFromBiprod R (X := TopCat.of M)
    hS.isOpen_compl hT.isOpen_compl (compl_subset_compl.2 subset_union_left)
    (compl_subset_compl.2 subset_union_right) (compl_subset_compl.2 inter_subset_left)
    (compl_subset_compl.2 inter_subset_right) (compl_union S T).ge (compl_inter S T).le

end MayerVietoris

/-! ### Continuity along decreasing families -/

section Family

variable {S : Set M} {ι : Type w} [Preorder ι] {K : ι → Set M} (hK : Antitone K)
  (hSK : ∀ i, S ⊆ K i)

/-- The pairs `(M, M ∖ K i)` of a decreasing family of sets `K i`, with the maps induced by the
identity of `M`. -/
@[expose, simps]
def complPairDiagram : ι ⥤ TopPair.{w} where
  obj i := TopPair.ofSubset ((K i)ᶜ : Set (TopCat.of M))
  map h := TopPair.ofSubsetMap (𝟙 _) (compl_subset_compl.2 (hK h.le))
  map_id _ := TopPair.ofSubsetMap_id _
  map_comp _ _ := TopPair.ofSubsetMap_comp (𝟙 _) (𝟙 _) _ _ _

/-- The cocone of the pairs `(M, M ∖ K i)` over the pair `(M, M ∖ S)`, for `S ⊆ K i`, with the
maps induced by the identity of `M`. -/
@[expose, simps]
def complPairCocone : Cocone (complPairDiagram hK) where
  pt := TopPair.ofSubset (Sᶜ : Set (TopCat.of M))
  ι := { app i := TopPair.ofSubsetMap (𝟙 _) (compl_subset_compl.2 (hSK i))
         naturality _ _ _ :=
           (TopPair.ofSubsetMap_comp (𝟙 _) (𝟙 _) _ _ _).symm.trans (Category.comp_id _).symm }

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (hcpt : ∀ T : Set M, IsCompact T → Disjoint T S → ∃ i, Disjoint T (K i))
include hcpt

/-- **Relative singular chains along a set are the colimit along larger sets.** Let `K i ⊇ S` be a
directed decreasing family of sets such that every compact set disjoint from `S` misses some
`K i`. Then the relative singular chain complex `C(M, M ∖ S)` is the colimit of the complexes
`C(M, M ∖ K i)`: on the ambient spaces the maps are identities, and a compact subset of `M ∖ S`
lies in some `M ∖ K i`. -/
def isColimitMapCoconeSingularChainComplexComplPairCocone :
    IsColimit (((TopPair.singularChainComplexFunctor A).obj R).mapCocone
      (complPairCocone hK hSK)) := by
  have hfst (i : ι) : TopPair.Hom.fst ((complPairCocone hK hSK).ι.app i) = 𝟙 (TopCat.of M) :=
    TopPair.ofSubsetMap_fst _ _
  refine TopPair.isColimitMapCoconeSingularChainComplex R _ (fun i ↦ ?_) (fun T _ ↦ ?_)
    fun T hT ↦ ?_
  · rw [hfst]
    exact Topology.IsEmbedding.id
  · refine ⟨Classical.arbitrary ι, fun x _ ↦ ⟨x, ?_⟩⟩
    rw [hfst]
    rfl
  · obtain ⟨i, hi⟩ := hcpt _ (hT.image continuous_subtypeVal)
      (disjoint_left.2 fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property)
    exact ⟨i, fun x hx ↦ ⟨⟨x.val, disjoint_left.1 hi ⟨x, hx, rfl⟩⟩,
      Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)⟩⟩

end Family

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {K : ι → Set M}
  (hK : Antitone K) (hKc : ∀ i, IsClosed (K i))

/-- **Relative singular chains along an intersection of closed sets.** For a directed decreasing
family of closed sets `K i`, the relative singular chain complex `C(M, M ∖ ⋂ i, K i)` is the
colimit of the complexes `C(M, M ∖ K i)`: a compact set disjoint from `⋂ i, K i` is disjoint from
some `K i`. -/
def isColimitMapCoconeSingularChainComplexComplPairCoconeIInter :
    IsColimit (((TopPair.singularChainComplexFunctor A).obj R).mapCocone
      (complPairCocone hK (iInter_subset K))) :=
  isColimitMapCoconeSingularChainComplexComplPairCocone R hK (iInter_subset K)
    fun _ hT hTK ↦ hT.elim_directed_family_closed K hKc hTK
      (directed_of_isDirected_le fun _ _ h ↦ hK h)

end TauCeti
