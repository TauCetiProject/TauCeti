/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import TauCeti.Topology.Category.TopCat.Subspace

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

## Main definitions and results

* `TauCeti.isColimitMapCoconeToSSet`: for a cocone over a filtered diagram of spaces whose legs
  are embeddings, such that every compact subset of the apex lies in the range of a leg, the
  singular simplicial sets form a colimit cocone.
* `TauCeti.isColimitMapCoconeSingularHomology`: the same cocone is a colimit cocone after applying
  singular homology, for coefficients in an abelian category whose filtered colimits are exact.
* `TauCeti.exists_singularHomologyMap_inclusion_eq_zero`: with coefficients in a module, a class of
  one member of an increasing cover of a subspace by relatively open sets that vanishes in the
  subspace already vanishes in some larger member.

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
  [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J] {U : J → Set Y} (hU : Monotone U)
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

end TauCeti
