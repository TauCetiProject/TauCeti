/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.Topology.Category.TopPair

/-!
# Relative singular homology and compact supports

For a filtered diagram of pairs `(Xᵢ, Aᵢ)`, suppose the ambient maps into `X` are embeddings,
and every compact subset of either component lies in one stage.
Then relative singular chains, and relative singular homology with exact filtered colimits
of coefficients, form colimit cocones. The legs are the maps induced by the given maps of pairs.

This applies to filtrations of CW pairs once compact subsets are known to lie in bounded
skeleta. No openness, finite dimensionality, or finiteness of the cell sets is required here.
The chain statement only requires preadditive coefficients with `w`-indexed coproducts;
exactness is needed only to pass from chains to homology.

The proof uses `TauCeti.isColimitMapCoconeToSSet` for the two components and Mathlib's
`SSetPair.isColimitCokernelCoforkChainComplex` to present relative chains as cokernels.
The compact-support argument is that of Hatcher, *Algebraic Topology*, Section 2.2,
proof of Theorem 2.35.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology

universe w v u

namespace TauCeti

section Chains

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

variable {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  {F : J ⥤ TopPair.{w}} (c : Cocone F)
  (hX : ∀ j, IsEmbedding (TopPair.Hom.fst (c.ι.app j)))
  (hKX : ∀ K : Set c.pt.fst, IsCompact K → ∃ j, K ⊆ Set.range (TopPair.Hom.fst (c.ι.app j)))
  (hKA : ∀ K : Set c.pt.snd, IsCompact K → ∃ j, K ⊆ Set.range (TopPair.Hom.snd (c.ι.app j)))

/-- Relative singular chains commute with filtered unions that absorb compact subsets in
both the ambient space and the subspace. The cocone legs are the induced relative chain maps. -/
def isColimitMapCoconeRelativeSingularChainComplex :
    IsColimit (((TopPair.singularChainComplexFunctor C).obj R).mapCocone c) := by
  have hA (j : J) : IsEmbedding (TopPair.Hom.snd (c.ι.app j)) :=
    TopPair.Hom.isEmbedding_snd_of_isEmbedding_fst (c.ι.app j) (hX j)
  -- `Functor.mapCocone` commutes definitionally with functor composition, which also
  -- reassociates definitionally. Unfolding the abbreviations `TopPair.proj₁` and
  -- `TopPair.proj₂` identifies their legs with `Hom.fst` and `Hom.snd`, and their
  -- points with `c.pt.fst` and `c.pt.snd`; there are no `TopPair`-specific projection lemmas.
  let d := (TopPair.singularChainComplexShortComplexFunctor R).mapCocone c
  have h₁ : IsColimit
      ((TopPair.singularChainComplexShortComplexFunctor R ⋙ ShortComplex.π₁).mapCocone c) := by
    rw [TopPair.singularChainComplexShortComplexFunctor_comp_π₁]
    exact isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R)
      (isColimitMapCoconeToSSet (TopPair.proj₂.mapCocone c) hA hKA)
  have h₂ : IsColimit
      ((TopPair.singularChainComplexShortComplexFunctor R ⋙ ShortComplex.π₂).mapCocone c) := by
    rw [TopPair.singularChainComplexShortComplexFunctor_comp_π₂]
    exact isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R)
      (isColimitMapCoconeToSSet (TopPair.proj₁.mapCocone c) hX hKX)
  rw [← TopPair.singularChainComplexShortComplexFunctor_comp_π₃]
  -- Transport the whole short complex before taking its second map or cokernel cofork:
  -- this keeps the hidden functor body and all dependent source/target objects abstract.
  exact isColimitπ₃MapCoconeOfIsCokernel d h₁ h₂
    (fun j ↦ by
      rw [Functor.comp_obj]
      exact (congrArg (fun S : ShortComplex (ChainComplex C ℕ) ↦ Epi S.g)
        (TopPair.singularChainComplexShortComplexFunctor_obj R (F.obj j))).mpr
          (Cofork.IsColimit.epi ((F.obj j).isColimitCokernelCoforkSingularChainComplex R)))
    ((congrArg (fun S : ShortComplex (ChainComplex C ℕ) ↦
      IsColimit (CokernelCofork.ofπ S.g S.zero))
        (TopPair.singularChainComplexShortComplexFunctor_obj R c.pt)).mpr
          (c.pt.isColimitCokernelCoforkSingularChainComplex R))

end Chains

section Homology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
  {F : J ⥤ TopPair.{w}} (c : Cocone F)
  (hX : ∀ j, IsEmbedding (TopPair.Hom.fst (c.ι.app j)))
  (hKX : ∀ K : Set c.pt.fst, IsCompact K → ∃ j, K ⊆ Set.range (TopPair.Hom.fst (c.ι.app j)))
  (hKA : ∀ K : Set c.pt.snd, IsCompact K → ∃ j, K ⊆ Set.range (TopPair.Hom.snd (c.ι.app j)))

/-- Relative singular homology has compact supports: for a filtered cocone of embeddings of
pairs absorbing compact subsets on both components, the induced homology cocone is a colimit.
The coefficient category must have exact colimits of the indexing shape. -/
def isColimitMapCoconeRelativeSingularHomology (n : ℕ) :
    IsColimit ((TopPair.singularHomologyFunctor R n).mapCocone c) := by
  rw [TopPair.singularHomologyFunctor_eq_chainComplexFunctor]
  exact isColimitOfPreserves (HomologicalComplex.homologyFunctor C _ n)
    (isColimitMapCoconeRelativeSingularChainComplex R c hX hKX hKA)

end Homology

end TauCeti
