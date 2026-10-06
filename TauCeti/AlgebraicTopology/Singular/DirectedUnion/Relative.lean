/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Relative singular homology and compact supports

For a filtered diagram of pairs `(Xᵢ, Aᵢ)`, suppose the ambient maps into `X` are embeddings,
and every compact subset of either component lies in one stage.
Then relative singular chains, and relative singular homology with exact filtered colimits
of coefficients, form colimit cocones. The legs are the maps induced by the given maps of pairs.

This applies to filtrations of CW pairs once compact subsets are known to lie in bounded
skeleta. No openness, finite dimensionality, or finiteness of the cell sets is required here.
The chain statement only requires preadditive coefficients; exactness is needed only to
pass from chains to homology.

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

-- This diagram of chain sequences is used only to pass the two absolute colimits to the quotient.
private def relativeChainSequenceFunctor : TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) where
  obj P := P.singularChainComplexShortComplex R
  map f := SSetPair.chainComplexShortComplexMap (TopPair.toSSetPair.map f) R
  map_id P := by
    ext <;> simp [SSet.chainComplexMap, SSetPair.chainComplexMap]
  map_comp f g := by
    ext <;> simp [SSet.chainComplexMap, SSetPair.chainComplexMap]

private lemma relativeChainSequenceFunctor_comp_π₁ :
    relativeChainSequenceFunctor R ⋙ ShortComplex.π₁ =
      TopPair.proj₂ ⋙ TopCat.toSSet ⋙ (SSet.chainComplexFunctor C).obj R := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro P Q f
  simp only [Functor.comp_map, relativeChainSequenceFunctor, ShortComplex.π₁_map,
    SSetPair.chainComplexShortComplexMap_τ₁, TopPair.toSSetPair_map_left]
  rfl

private lemma relativeChainSequenceFunctor_comp_π₂ :
    relativeChainSequenceFunctor R ⋙ ShortComplex.π₂ =
      TopPair.proj₁ ⋙ TopCat.toSSet ⋙ (SSet.chainComplexFunctor C).obj R := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro P Q f
  simp only [Functor.comp_map, relativeChainSequenceFunctor, ShortComplex.π₂_map,
    SSetPair.chainComplexShortComplexMap_τ₂, TopPair.toSSetPair_map_right]
  rfl

private lemma relativeChainSequenceFunctor_comp_π₃ :
    relativeChainSequenceFunctor R ⋙ ShortComplex.π₃ =
      (TopPair.singularChainComplexFunctor C).obj R := by
  refine CategoryTheory.Functor.hext (fun P ↦ ?_) ?_
  · simp [relativeChainSequenceFunctor]
  · intro P Q f
    simp only [Functor.comp_map, relativeChainSequenceFunctor, ShortComplex.π₃_map,
      SSetPair.chainComplexShortComplexMap_τ₃]
    exact ((conj_eqToHom_iff_heq _ _
      (TopPair.singularChainComplexFunctor_obj_obj P R)
      (TopPair.singularChainComplexFunctor_obj_obj Q R)).1
        (TopPair.singularChainComplexFunctor_obj_map P Q f R)).symm

variable {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  {F : J ⥤ TopPair.{w}} (c : Cocone F)
  (hX : ∀ j, IsEmbedding (TopPair.Hom.fst (c.ι.app j)))
  (hKX : ∀ K : Set c.pt.fst, IsCompact K → ∃ j, K ⊆ Set.range (TopPair.Hom.fst (c.ι.app j)))
  (hKA : ∀ K : Set c.pt.snd, IsCompact K → ∃ j, K ⊆ Set.range (TopPair.Hom.snd (c.ι.app j)))

/-- Relative singular chains commute with filtered unions that absorb compact subsets in
both the ambient space and the subspace. The cocone legs are the induced relative chain maps. -/
def isColimitMapCoconeRelativeSingularChainComplex :
    IsColimit (((TopPair.singularChainComplexFunctor C).obj R).mapCocone c) := by
  have hA (j : J) : IsEmbedding (TopPair.Hom.snd (c.ι.app j)) := by
    apply (c.pt.isEmbedding_map.of_comp_iff
      (f := TopPair.Hom.snd (c.ι.app j))).mp
    have hw : (c.pt.map : c.pt.snd → c.pt.fst) ∘ TopPair.Hom.snd (c.ι.app j) =
        TopPair.Hom.fst (c.ι.app j) ∘ (F.obj j).map :=
      funext (TopPair.Hom.w_apply (c.ι.app j))
    rw [hw]
    exact (hX j).comp (F.obj j).isEmbedding_map
  let d := (relativeChainSequenceFunctor R).mapCocone c
  have h₁ : IsColimit ((relativeChainSequenceFunctor R ⋙ ShortComplex.π₁).mapCocone c) := by
    rw [relativeChainSequenceFunctor_comp_π₁]
    exact isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R)
      (isColimitMapCoconeToSSet (TopPair.proj₂.mapCocone c) hA hKA)
  have h₂ : IsColimit ((relativeChainSequenceFunctor R ⋙ ShortComplex.π₂).mapCocone c) := by
    rw [relativeChainSequenceFunctor_comp_π₂]
    exact isColimitOfPreserves ((SSet.chainComplexFunctor C).obj R)
      (isColimitMapCoconeToSSet (TopPair.proj₁.mapCocone c) hX hKX)
  rw [← relativeChainSequenceFunctor_comp_π₃]
  exact isColimitπ₃MapCoconeOfIsCokernel d h₁ h₂
    (fun j ↦ (F.obj j).isColimitCokernelCoforkSingularChainComplex R)
    (c.pt.isColimitCokernelCoforkSingularChainComplex R)

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
