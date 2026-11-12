/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
public import TauCeti.Topology.Category.TopCat.Subspace
import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# Singular homology with local coefficients has compact supports

A twisted singular chain is a finite sum of coefficients placed on singular simplices, and each
simplex has compact image. So every twisted chain of a space `X`, with coefficients in a local
system `L`, is a chain of every subspace containing a certain compact set, with `L` restricted to
that subspace
(`TauCeti.LocalCoefficientSystem.exists_isCompact_forall_mem_range_twistedChainComplexMap_f`).

Consequently, if `U` is a monotone family of subsets of `X` indexed by a directed order such that
every compact subset of `X` lies in some `U i`, then the twisted homology of `X` is the filtered
colimit of the twisted homology of the members `U i`, with the restricted systems:

* every class of `Hₖ(X; L)` comes from some `Hₖ(U i; L)`
  (`TauCeti.LocalCoefficientSystem.exists_twistedHomologyMap_subtypeVal_eq`);
* a class of `Hₖ(U i; L)` that vanishes in `X` already vanishes in some `Hₖ(U j; L)` with `i ≤ j`
  (`TauCeti.LocalCoefficientSystem.exists_homologyMap_subsetTwistedChainComplexMap_eq_zero`);
* together, the cocone of the maps `Hₖ(U i; L) ⟶ Hₖ(X; L)` is a colimit cocone
  (`TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedHomologyCocone`).

No openness, covering or local-finiteness hypothesis is needed, and the coefficient fibres are
arbitrary modules. The main instance is the skeletal filtration of a CW complex, and more generally
the preimages `f⁻¹(C^(q))` of the skeleta of a relative CW complex `C` under a map `f`, which absorb
every compact set even when `C` has infinitely many cells in infinitely many dimensions
(`TauCeti.LocalCoefficientSystem.isColimitPreimageSkeletonTwistedHomologyCocone`). For a fibration
over a CW complex this computes the twisted homology of the total space, and for the identity the
twisted homology of an infinite-dimensional CW complex, from the finite-dimensional stages.

This is the local-coefficient counterpart of `TauCeti.isColimitMapCoconeSingularHomology`. That
statement passes through the singular simplicial set; twisted chains are not a functor of the
simplicial set alone, so here the argument is made on the chains directly, through the
identification of the chains of a subspace with the chains of `X` supported in it
(`TauCeti.LocalCoefficientSystem.range_twistedChainComplexMap_subtypeVal_f`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.6 and the compactness argument in
  the proof of Proposition 2B.1, and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI, Section 2.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-! ### Functoriality of the maps of subspaces -/

section Subset

variable {A B C : Set X}

/-- The map of twisted chains induced by the identity inclusion `A ⊆ A` is the identity. -/
@[simp]
lemma subsetTwistedChainComplexMap_self (A : Set X) :
    subsetTwistedChainComplexMap L (subset_refl A) = 𝟙 _ := by
  rw [← cancel_mono (twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L),
    subsetTwistedChainComplexMap_twistedChainComplexMap, Category.id_comp]

/-- The maps of twisted chains induced by `A ⊆ B` and `B ⊆ C` compose to the map induced by
`A ⊆ C`. -/
@[reassoc (attr := simp)]
lemma subsetTwistedChainComplexMap_comp_subsetTwistedChainComplexMap (hAB : A ⊆ B)
    (hBC : B ⊆ C) :
    subsetTwistedChainComplexMap L hAB ≫ subsetTwistedChainComplexMap L hBC =
      subsetTwistedChainComplexMap L (hAB.trans hBC) := by
  rw [← cancel_mono (twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal C)) L)]
  simp only [Category.assoc, subsetTwistedChainComplexMap_twistedChainComplexMap]

end Subset

/-! ### Compact supports of chains and of homology classes -/

/-- **Twisted chains have compact supports.** Every twisted chain `c` of `X` is the pushforward of
a twisted chain of every subspace `A` containing a certain compact set `K`, the union of the images
of the finitely many simplices on which `c` has a nonzero coefficient. -/
theorem exists_isCompact_forall_mem_range_twistedChainComplexMap_f {k : ℕ}
    (c : L.twistedChainComplex.X k) :
    ∃ K : Set X, IsCompact K ∧ ∀ A : Set X, K ⊆ A →
      c ∈ LinearMap.range
        ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f k).hom := by
  refine ⟨⋃ σ ∈ {σ : (TopCat.toSSet.obj X) _⦋k⦌ | (twistedChainComplexCoeff L σ).hom c ≠ 0},
      Set.range (X.toSSetObjEquiv _ σ),
    (finite_support_twistedChainComplexCoeff L c).isCompact_biUnion
      fun σ _ ↦ isCompact_range (X.toSSetObjEquiv _ σ).continuous,
    fun A hA ↦ ?_⟩
  rw [range_twistedChainComplexMap_subtypeVal_f, mem_smallTwistedChains_iff]
  -- a simplex carrying a nonzero coefficient lies in `K`, hence in `A`
  refine fun σ hσ ↦ by_contra fun h ↦ hσ ?_
  exact (TopCat.mem_smallSingularSubcomplex_iff X _ σ).2
    ⟨(), (Set.subset_biUnion_of_mem (u := fun σ ↦ Set.range (X.toSSetObjEquiv _ σ)) h).trans hA⟩

variable {ι : Type*} {U : ι → Set X}

/-- **Every twisted homology class comes from a member of a family absorbing compact sets.** If
every compact subset of `X` lies in some `U i`, every class of `Hₖ(X; L)` is the image of a class
of some `Hₖ(U i; L)`, with `L` restricted to `U i`. -/
theorem exists_twistedHomologyMap_subtypeVal_eq
    (hK : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ U i) {k : ℕ} (x : L.twistedHomology k) :
    ∃ (i : ι) (y : ((pullback (X := TopCat.of ↥(U i)) (ContinuousMap.subtypeVal (U i))).obj
        L).twistedHomology k),
      twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal (U i))) L k y = x :=
  HomologicalComplex.exists_homologyMap_eq_of_injective k _
    (fun _ ↦ (ModuleCat.mono_iff_injective _).1 inferInstance)
    (fun c ↦ by
      obtain ⟨K, hKc, hc⟩ := exists_isCompact_forall_mem_range_twistedChainComplexMap_f L c
      obtain ⟨i, hi⟩ := hK K hKc
      obtain ⟨y, hy⟩ := hc (U i) hi
      exact ⟨i, y, hy⟩) x

/-- **A twisted homology class that vanishes in `X` vanishes in a larger member.** Let `U` be a
monotone family indexed by a directed order such that every compact subset of `X` lies in some
`U i`. A class of `Hₖ(U i; L)` whose image in `Hₖ(X; L)` vanishes already vanishes in some
`Hₖ(U j; L)` with `i ≤ j`. -/
theorem exists_homologyMap_subsetTwistedChainComplexMap_eq_zero [Preorder ι] [IsDirectedOrder ι]
    (hU : Monotone U) (hK : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ U i) {k : ℕ} {i : ι}
    (y : ((pullback (X := TopCat.of ↥(U i)) (ContinuousMap.subtypeVal (U i))).obj
      L).twistedHomology k)
    (hy : twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal (U i))) L k y = 0) :
    ∃ (j : ι) (hij : i ≤ j),
      HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L (hU hij)) k y = 0 :=
  HomologicalComplex.exists_homologyMap_eq_zero_of_injective k
    (fun j ↦ twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal (U j))) L)
    (fun _ ↦ (ModuleCat.mono_iff_injective _).1 inferInstance) (ChainComplex.prev ℕ k)
    (P := (i ≤ ·)) (fun _ hij ↦ subsetTwistedChainComplexMap L (hU hij))
    (fun _ hij ↦ subsetTwistedChainComplexMap_twistedChainComplexMap L (hU hij))
    (fun c ↦ by
      -- the bounding chain lies in some member, and then in a member above `i`
      obtain ⟨K, hKc, hc⟩ := exists_isCompact_forall_mem_range_twistedChainComplexMap_f L c
      obtain ⟨j₀, hj₀⟩ := hK K hKc
      obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
      obtain ⟨y, hy⟩ := hc (U j) (hj₀.trans (hU hj₀j))
      exact ⟨j, hij, y, hy⟩) y hy

/-! ### The colimit over a directed family -/

variable [Preorder ι] (hU : Monotone U) (k : ℕ)

/-- Twisted homology of the members of a monotone family `U` of subsets of `X`, with `L`
restricted to each member, as a functor on the index order. -/
-- Its object part must compute, so that the legs of `subsetTwistedHomologyCocone` are the maps
-- induced by the inclusions on the nose.
@[expose, simps]
def subsetTwistedHomologyFunctor : ι ⥤ ModuleCat.{max v w} R where
  obj i := ((pullback (X := TopCat.of ↥(U i)) (ContinuousMap.subtypeVal (U i))).obj
    L).twistedHomology k
  map {i j} f := HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L (hU f.le)) k
  map_id i := by
    rw [subsetTwistedChainComplexMap_self, HomologicalComplex.homologyMap_id]
  map_comp f g := by
    rw [← HomologicalComplex.homologyMap_comp,
      subsetTwistedChainComplexMap_comp_subsetTwistedChainComplexMap]

/-- The cocone of the maps `Hₖ(U i; L) ⟶ Hₖ(X; L)` induced by the inclusions of the members of a
monotone family `U`. -/
-- Its point must compute, so that it is the twisted homology of `X` on the nose.
@[expose, simps]
def subsetTwistedHomologyCocone : Cocone (subsetTwistedHomologyFunctor L hU k) where
  pt := L.twistedHomology k
  ι :=
    { app i := twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal (U i))) L k
      naturality _ _ f :=
        ((HomologicalComplex.homologyMap_comp _ _ k).symm.trans
          (congrArg (HomologicalComplex.homologyMap · k)
            (subsetTwistedChainComplexMap_twistedChainComplexMap L (hU f.le)))).trans
          (Category.comp_id _).symm }

/-- **Twisted singular homology has compact supports.** If `U` is a monotone family of subsets of
`X`, indexed by a directed order, such that every compact subset of `X` lies in some `U i`, then
`Hₖ(X; L)` is the colimit of the groups `Hₖ(U i; L)`, with `L` restricted to each member. -/
def isColimitSubsetTwistedHomologyCocone [IsDirectedOrder ι]
    (hK : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ U i) :
    IsColimit (subsetTwistedHomologyCocone L hU k) :=
  ModuleCat.isColimitOfJointlySurjective _
    (fun x ↦ exists_twistedHomologyMap_subtypeVal_eq L hK x)
    (fun i j xi xj hij ↦ by
      obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
      let F := subsetTwistedHomologyFunctor L hU k
      -- the difference of the two images at a common upper bound vanishes in `X`
      have hl : ((subsetTwistedHomologyCocone L hU k).ι.app l).hom
          ((F.map (homOfLE hil)).hom xi - (F.map (homOfLE hjl)).hom xj) = 0 := by
        rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, Cocone.w,
          ← ConcreteCategory.comp_apply, Cocone.w]
      rw [subsetTwistedHomologyCocone_ι_app] at hl
      obtain ⟨m, hlm, hm⟩ := exists_homologyMap_subsetTwistedChainComplexMap_eq_zero L hU hK _ hl
      refine ⟨m, homOfLE (hil.trans hlm), homOfLE (hjl.trans hlm), ?_⟩
      -- so it already vanishes in `U m`: `hm` is this statement by
      -- `subsetTwistedHomologyFunctor_map`; it is stated on the carriers of the homology modules,
      -- which agree with `F.obj` only by unfolding, so the exposed definition is used directly
      have hm' : (F.map (homOfLE hlm)).hom
          ((F.map (homOfLE hil)).hom xi - (F.map (homOfLE hjl)).hom xj) = 0 := hm
      rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← F.map_comp, ← F.map_comp] at hm')

/-! ### Preimages of the skeleta of a CW complex -/

section Skeleton

variable {B : Type*} [TopologicalSpace B] [T2Space B] {C D : Set B} [Topology.RelCWComplex C D]
  {f : X → B}

/-- **Twisted homology from the preimages of the skeleta of a CW complex.** For a continuous map
`f : X → B` with values in a relative CW complex `C`, the twisted homology of `X` is the colimit of
the twisted homology of the preimages `f⁻¹(C^(q))` of the skeleta, with `L` restricted to each.
The complex `C` may have infinitely many cells and be infinite-dimensional. -/
def isColimitPreimageSkeletonTwistedHomologyCocone (hf : Continuous f) (hfC : Set.range f ⊆ C) :
    IsColimit (subsetTwistedHomologyCocone L (monotone_preimageSkeleton (C := C) f) k) :=
  isColimitSubsetTwistedHomologyCocone L _ k
    fun _ hK ↦ exists_subset_preimageSkeleton_of_isCompact hf hfC hK

end Skeleton

end TauCeti.LocalCoefficientSystem
