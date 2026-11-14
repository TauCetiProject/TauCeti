/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import TauCeti.Topology.Category.TopCat.Subspace
public import TauCeti.Topology.Category.TopPair
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.CategoryTheory.Limits.Shapes.Kernels

/-!
# Singular homology of a directed union

A singular simplex has compact image, so it lies in one member of any directed family of subspaces
whose members absorb every compact subset. Consequently the singular simplicial set of a space is
the filtered colimit of the singular simplicial sets of such a family, and, since the singular
chain complex preserves colimits and homology commutes with exact filtered colimits, singular
homology of the space is the colimit of the singular homology of the members. This is the
"compact supports" property of singular homology.

The typical family is an increasing family of open subsets covering a space: a compact set is
covered by finitely many of them, hence by one. For coefficients in modules, the colimit statement
says that a class in the homology of a member which vanishes in the whole space already vanishes in
some larger member. This is the compactness step in the computation of the homology of the
complement of an embedded cube or sphere (`TauCeti/AlgebraicTopology/Singular/CubeComplement`).

The same holds for relative singular homology of a filtered diagram of topological pairs, provided
compact subsets of both the ambient space and the subspace of the apex are absorbed.  The relative
chains are the cokernel of the chains of the subspace in the chains of the ambient space, and
cokernels commute with colimits (`TauCeti.isColimitOfIsColimitCokernelCofork`).

## Main definitions and results

* `TauCeti.isColimitMapCoconeToSSet`: for a cocone over a filtered diagram of spaces whose legs
  are embeddings, such that every compact subset of the apex lies in the range of a leg, the
  singular simplicial sets form a colimit cocone.
* `TauCeti.isColimitMapCoconeSingularHomology`: the same cocone is a colimit cocone after applying
  singular homology, for coefficients in an abelian category whose filtered colimits are exact.
* `TauCeti.exists_singularHomologyMap_inclusion_eq_zero`: with coefficients in a module, a class of
  one member of an increasing cover of a subspace by relatively open sets that vanishes in the
  subspace already vanishes in some larger member.
* `TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq` and
  `TauCeti.exists_isCompact_singularHomologyMap_inclusion_eq_zero`: with coefficients in a module,
  every singular homology class comes from a compact subset, and a class of a compact subset that
  vanishes in the ambient space already vanishes in some larger compact subset.
* `TopPair.isColimitMapCoconeSingularChainComplex` and `TopPair.isColimitMapCoconeSingularHomology`:
  for a cocone over a filtered diagram of topological pairs whose legs are embeddings of the
  ambient spaces, such that every compact subset of the ambient space and of the subspace of the
  apex lies in the range of a leg, the relative singular chain complexes, and relative singular
  homology for coefficients whose filtered colimits are exact, form colimit cocones.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.6 and the compactness argument in
  the proof of Proposition 2B.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology TopCat

universe w v u

namespace TauCeti

section SSet

variable {J : Type*} [Category J] {F : J ⥤ TopCat.{w}} (c : Cocone F)

/-- **Singular simplices have compact support.** Let `c` be a cocone over a filtered diagram of
spaces whose legs are embeddings, such that every compact subset of the apex lies in the range of
some leg. Then the singular simplicial sets of the diagram form a colimit cocone with apex the
singular simplicial set of `c.pt`. -/
def isColimitMapCoconeToSSet [IsFiltered J] (hc : ∀ j, IsEmbedding (c.ι.app j))
    (hK : ∀ K : Set c.pt, IsCompact K → ∃ j, K ⊆ Set.range (c.ι.app j)) :
    IsColimit (toSSet.mapCocone c) :=
  evaluationJointlyReflectsColimits _ fun n ↦ by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun σ ↦ ?_) (fun j x y hxy ↦ ?_)
    · obtain ⟨j, hj⟩ := hK _ (isCompact_range (c.pt.toSSetObjEquiv n σ).continuous)
      obtain ⟨τ, hτ⟩ :=
        ((hc j).isInducing.mem_range_toSSet_map_app_iff n σ).2 hj
      exact ⟨j, τ, hτ.symm⟩
    · refine ⟨j, 𝟙 j, ?_⟩
      have : Mono (c.ι.app j) := (TopCat.mono_iff_injective _).2 (hc j).injective
      have : Mono ((((evaluation _ _).obj n).mapCocone (toSSet.mapCocone c)).ι.app j) :=
        inferInstanceAs (Mono ((toSSet.map (c.ι.app j)).app n))
      rw [(CategoryTheory.mono_iff_injective _).1 this hxy]

end SSet

section Homology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] {F : J ⥤ TopCat.{w}} (c : Cocone F)

/-- **Singular homology has compact supports.** For a cocone over a filtered diagram of spaces
whose legs are embeddings, such that every compact subset of the apex lies in the range of some
leg, singular homology of the apex is the colimit of singular homology of the diagram, provided
filtered colimits of the coefficient category are exact. -/
def isColimitMapCoconeSingularHomology (hc : ∀ j, IsEmbedding (c.ι.app j))
    (hK : ∀ K : Set c.pt, IsCompact K → ∃ j, K ⊆ Set.range (c.ι.app j)) :
    IsColimit (((singularHomologyFunctor C n).obj R).mapCocone c) :=
  isColimitOfPreserves
    ((SSet.chainComplexFunctor C).obj R ⋙ HomologicalComplex.homologyFunctor C _ n)
    (isColimitMapCoconeToSSet c hc hK)

end Homology

section Module

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A) (n : ℕ) {Y : TopCat.{w}} {J : Type}
  [Preorder J] [IsDirected J (· ≤ ·)] {U : J → Set Y} (hU : Monotone U)
  {V : Set Y} (hUV : ∀ j, U j ⊆ V) (hopen : ∀ j, IsOpen (Subtype.val ⁻¹' U j : Set V))
  (hcover : V ⊆ ⋃ j, U j)

include hopen hcover in
/-- **Vanishing of a homology class is detected in a member of an increasing open cover.** With
coefficients in a module, a singular homology class of one member `U i` of an increasing cover of
`V` by subsets open in `V` that vanishes in `V` already vanishes in some larger member `U j`. -/
theorem exists_singularHomologyMap_inclusion_eq_zero {i : J}
    (x : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj (of (U i)))
    (hx : ((singularHomologyFunctor _ n).obj M).map (ofHom (ContinuousMap.inclusion (hUV i))) x =
      0) :
    ∃ j, ∃ hij : i ≤ j,
      ((singularHomologyFunctor _ n).obj M).map (ofHom (ContinuousMap.inclusion (hU hij))) x =
        0 := by
  have : Nonempty J := ⟨i⟩
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{w} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  -- The subspaces `U j` and their inclusions into `V` form a cocone of embeddings.
  let c : Cocone ({ obj j := of (U j)
                    map f := ofHom (ContinuousMap.inclusion (hU f.le)) } : J ⥤ TopCat.{w}) :=
    { pt := of V, ι := { app j := ofHom (ContinuousMap.inclusion (hUV j)) } }
  -- A compact subset of `V` is covered by finitely many of the `U j`, hence by one.
  have hK (K : Set c.pt) (hK : IsCompact K) : ∃ j, K ⊆ Set.range (c.ι.app j) := by
    obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ (Subtype.val ⁻¹' U j : Set V)) hopen
      (fun x _ ↦ Set.mem_iUnion.2 (Set.mem_iUnion.1 (hcover x.2) : ∃ j, x.1 ∈ U j))
      (Monotone.directed_le fun _ _ h ↦ Set.preimage_mono (hU h))
    exact ⟨j, fun x hx ↦ ⟨⟨x.1, hj hx⟩, rfl⟩⟩
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq (j := i) _
    (isColimitMapCoconeSingularHomology M n c (fun j ↦ IsEmbedding.inclusion (hUV j)) hK) x 0
    (by rw [map_zero]; exact hx)
  rw [map_zero] at hfg
  exact ⟨j, f.le, hfg⟩

end Module

section CompactSubsets

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A) (n : ℕ) {X : Type w} [TopologicalSpace X]

private instance : IsDirected {K : Set X // IsCompact K} (· ≤ ·) :=
  ⟨fun K₁ K₂ ↦ ⟨⟨K₁.1 ∪ K₂.1, K₁.2.union K₂.2⟩, Set.subset_union_left, Set.subset_union_right⟩⟩

private instance : Nonempty {K : Set X // IsCompact K} :=
  ⟨⟨∅, isCompact_empty⟩⟩

/-- The filtered diagram of compact subsets of `X` and their inclusions. -/
private abbrev compactSubsetDiagram (X : Type w) [TopologicalSpace X] :
    {K : Set X // IsCompact K} ⥤ TopCat.{w} where
  obj K := of K.1
  map f := ofHom (ContinuousMap.inclusion f.le)

/-- The cocone of inclusions of compact subsets into `X`. -/
private abbrev compactSubsetCocone (X : Type w) [TopologicalSpace X] :
    Cocone (compactSubsetDiagram X) where
  pt := of X
  ι := { app K := ofHom (ContinuousMap.subtypeVal K.1) }

private def isColimitCompactSubsetSingularHomology :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).mapCocone
      (compactSubsetCocone X)) :=
  isColimitMapCoconeSingularHomology M n (compactSubsetCocone X)
    (fun _ ↦ IsEmbedding.subtypeVal) fun K hK ↦ ⟨⟨K, hK⟩, Subtype.range_coe.ge⟩

/-- **Every singular homology class comes from a compact subset.** With coefficients in a module,
every class in `Hₙ(X; M)` is pushed forward from `Hₙ(K; M)` for some compact `K ⊆ X`. -/
theorem exists_isCompact_singularHomologyMap_subtypeVal_eq
    (x : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj (of X)) :
    ∃ K : Set X, IsCompact K ∧
      ∃ y : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj (of K),
        ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).map
          (ofHom (ContinuousMap.subtypeVal K)) y = x := by
  obtain ⟨K, y, hy⟩ := Concrete.isColimit_exists_rep _
    (isColimitCompactSubsetSingularHomology M n (X := X)) x
  exact ⟨K.1, K.2, y, hy⟩

/-- **Vanishing of a class from a compact subset is witnessed on a larger compact subset.** With
coefficients in a module, if a class in `Hₙ(K; M)` for compact `K ⊆ X` vanishes in `Hₙ(X; M)`, it
already vanishes in `Hₙ(L; M)` for some compact `L ⊇ K`. -/
theorem exists_isCompact_singularHomologyMap_inclusion_eq_zero {K : Set X} (hK : IsCompact K)
    (y : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj (of K))
    (hy : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).map
      (ofHom (ContinuousMap.subtypeVal K)) y = 0) :
    ∃ L : Set X, IsCompact L ∧ ∃ hKL : K ⊆ L,
      ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).map
        (ofHom (ContinuousMap.inclusion hKL)) y = 0 := by
  let hc := isColimitOfPreserves (forget (ModuleCat.{w} A))
    (isColimitCompactSubsetSingularHomology M n (X := X))
  obtain ⟨L, f, hfg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hc (i := ⟨K, hK⟩) y 0).1
      (by dsimp; rw [map_zero]; exact hy)
  dsimp at hfg
  rw [map_zero] at hfg
  exact ⟨L.1, L.2, f.le, hfg⟩

end CompactSubsets

end TauCeti

namespace TopPair

section Relative

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)
  {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  {F : J ⥤ TopPair.{w}} (c : Cocone F)

/-- **Relative singular chains have compact supports.** Let `c` be a cocone over a filtered
diagram of topological pairs whose legs are embeddings of the ambient spaces, such that every
compact subset of the ambient space of the apex, and every compact subset of its subspace, lies in
the range of some leg. Then the relative singular chain complexes form a colimit cocone with apex
the relative singular chain complex of `c.pt`. -/
def isColimitMapCoconeSingularChainComplex (hfst : ∀ j, IsEmbedding (Hom.fst (c.ι.app j)))
    (hfstK : ∀ K : Set c.pt.fst, IsCompact K → ∃ j, K ⊆ Set.range (Hom.fst (c.ι.app j)))
    (hsndK : ∀ K : Set c.pt.snd, IsCompact K → ∃ j, K ⊆ Set.range (Hom.snd (c.ι.app j))) :
    IsColimit (((singularChainComplexFunctor C).obj R).mapCocone c) := by
  rw [singularChainComplexFunctor_obj_eq_toSSetPair_comp]
  -- The relative chains of each pair, and of the apex, are the cokernel of the chains of the
  -- subspace in the chains of the ambient space, and both of these have compact supports; the
  -- legs are embeddings on the subspaces too, since the subspaces are embedded.
  refine TauCeti.isColimitOfIsColimitCokernelCofork
    (α := Functor.whiskerLeft (F ⋙ toSSetPair)
      ((SSetPair.chainComplexFunctorLeftToRight C).app R))
    (π := Functor.whiskerLeft (F ⋙ toSSetPair) ((SSetPair.chainComplexFunctorπ C).app R))
    (w := fun j ↦ (toSSetPair.obj (F.obj j)).chainComplex_condition R)
    (wp := (toSSetPair.obj c.pt).chainComplex_condition R)
    (fun j ↦ (toSSetPair.obj (F.obj j)).isColimitCokernelCoforkChainComplex R)
    (isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R)
      (TauCeti.isColimitMapCoconeToSSet (proj₂.mapCocone c)
        (fun j ↦ isEmbedding_snd_of_isEmbedding_fst _ (hfst j)) hsndK))
    (isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R)
      (TauCeti.isColimitMapCoconeToSSet (proj₁.mapCocone c) hfst hfstK))
    (fun j ↦ ?_) (fun j ↦ singularChainComplexπ_pair_naturality (c.ι.app j) R)
    (c.pt.isColimitCokernelCoforkSingularChainComplex R)
  -- The remaining goal is, by definition of the components involved, the square of chain maps
  -- induced by the commuting square of the leg at `j`.
  have h : SSet.chainComplexMap (TopCat.toSSet.map (Hom.snd (c.ι.app j))) R ≫
      SSet.chainComplexMap (TopCat.toSSet.map c.pt.map) R =
        SSet.chainComplexMap (TopCat.toSSet.map (F.obj j).map) R ≫
          SSet.chainComplexMap (TopCat.toSSet.map (Hom.fst (c.ι.app j))) R := by
    simp only [← Functor.map_comp]
    exact congrArg _ (congrArg _ (Hom.w (c.ι.app j)))
  exact h

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] {F : J ⥤ TopPair.{w}} (c : Cocone F)

/-- **Relative singular homology has compact supports.** For a cocone over a filtered diagram of
topological pairs whose legs are embeddings of the ambient spaces, such that every compact subset
of the ambient space of the apex, and every compact subset of its subspace, lies in the range of
some leg, relative singular homology of the apex is the colimit of relative singular homology of
the diagram, provided filtered colimits of the coefficient category are exact. -/
def isColimitMapCoconeSingularHomology (hfst : ∀ j, IsEmbedding (Hom.fst (c.ι.app j)))
    (hfstK : ∀ K : Set c.pt.fst, IsCompact K → ∃ j, K ⊆ Set.range (Hom.fst (c.ι.app j)))
    (hsndK : ∀ K : Set c.pt.snd, IsCompact K → ∃ j, K ⊆ Set.range (Hom.snd (c.ι.app j))) :
    IsColimit ((singularHomologyFunctor R n).mapCocone c) := by
  rw [singularHomologyFunctor_eq_chainComplexFunctor]
  exact isColimitOfPreserves (HomologicalComplex.homologyFunctor C _ n)
    (isColimitMapCoconeSingularChainComplex R c hfst hfstK hsndK)

end Relative

end TopPair
