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
import Mathlib.Topology.Sets.Compacts
import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# Singular homology with local coefficients has compact supports

A twisted singular chain is a finite sum of coefficients placed on singular simplices, and each
simplex has compact image. So every twisted chain of a space `X`, with coefficients in a local
system `L`, has a compact support `K`: it is a chain of a subspace, with `L` restricted to that
subspace, exactly when the subspace contains `K`
(`LocalCoefficientSystem.exists_isCompact_forall_subset_iff_mem_range_twistedChainComplexMap_f`).
The maps of twisted chains induced by inclusions of subspaces are monomorphisms
(`TauCeti.LocalCoefficientSystem.mono_subsetTwistedChainComplexMap`), and for a monotone family of
subsets they form a diagram of chain complexes
(`TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexDiagram`), whose homology is
`TauCeti.LocalCoefficientSystem.subsetTwistedHomologyFunctor`.

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

/-- The elementwise form of `subsetTwistedChainComplexMap_twistedChainComplexMap`. -/
lemma twistedChainComplexMap_f_subsetTwistedChainComplexMap_f_apply (h : A ⊆ B) {n : ℕ}
    (y : ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj
      L).twistedChainComplex.X n) :
    ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal B)) L).f n).hom
        (((subsetTwistedChainComplexMap L h).f n).hom y) =
      ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f n).hom y := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    subsetTwistedChainComplexMap_twistedChainComplexMap]

/-- The map of twisted chains induced by an inclusion of subsets is a monomorphism. -/
instance mono_subsetTwistedChainComplexMap (h : A ⊆ B) :
    Mono (subsetTwistedChainComplexMap L h) :=
  mono_of_mono_fac (subsetTwistedChainComplexMap_twistedChainComplexMap L h)

/-- In each degree, the map of twisted chains induced by an inclusion of subsets is a
monomorphism. -/
-- Mathlib's degreewise instance for a monomorphism of complexes gives this, but inside larger
-- terms its search for finite limits of modules can fail to unify their universes.
instance mono_subsetTwistedChainComplexMap_f (h : A ⊆ B) (n : ℕ) :
    Mono ((subsetTwistedChainComplexMap L h).f n) :=
  inferInstance

end Subset

/-! ### Compact supports of chains and of homology classes -/

/-- **Twisted chains have compact supports.** Every twisted chain `c` of `X` has a compact support
`K`, the union of the images of the finitely many simplices on which `c` has a nonzero coefficient:
`c` is the pushforward of a twisted chain of a subspace `A` exactly when `K ⊆ A`. -/
theorem exists_isCompact_forall_subset_iff_mem_range_twistedChainComplexMap_f {k : ℕ}
    (c : L.twistedChainComplex.X k) :
    ∃ K : Set X, IsCompact K ∧ ∀ A : Set X, K ⊆ A ↔
      c ∈ LinearMap.range
        ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f k).hom := by
  refine ⟨⋃ σ ∈ {σ : (TopCat.toSSet.obj X) _⦋k⦌ | (twistedChainComplexCoeff L σ).hom c ≠ 0},
      Set.range (X.toSSetObjEquiv _ σ),
    (finite_support_twistedChainComplexCoeff L c).isCompact_biUnion
      fun σ _ ↦ isCompact_range (X.toSSetObjEquiv _ σ).continuous,
    fun A ↦ ?_⟩
  rw [range_twistedChainComplexMap_subtypeVal_f, mem_smallTwistedChains_iff]
  refine ⟨fun hA σ hσ ↦ by_contra fun h ↦ hσ ?_, fun hA ↦ Set.iUnion₂_subset fun σ hσ ↦ ?_⟩
  · -- a simplex carrying a nonzero coefficient lies in `K`, hence in `A`
    exact (TopCat.mem_smallSingularSubcomplex_iff X _ σ).2
      ⟨(), (Set.subset_biUnion_of_mem (u := fun σ ↦ Set.range (X.toSSetObjEquiv _ σ)) h).trans hA⟩
  · -- conversely, a simplex carrying a nonzero coefficient of a chain of `A` lies in `A`
    by_contra h
    refine hσ (hA σ fun hσ' ↦ h ?_)
    obtain ⟨-, h'⟩ := (TopCat.mem_smallSingularSubcomplex_iff X _ σ).1 hσ'
    exact h'

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
      obtain ⟨K, hKc, hc⟩ :=
        exists_isCompact_forall_subset_iff_mem_range_twistedChainComplexMap_f L c
      obtain ⟨i, hi⟩ := hK K hKc
      obtain ⟨y, hy⟩ := (hc (U i)).1 hi
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
      obtain ⟨K, hKc, hc⟩ :=
        exists_isCompact_forall_subset_iff_mem_range_twistedChainComplexMap_f L c
      obtain ⟨j₀, hj₀⟩ := hK K hKc
      obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
      obtain ⟨y, hy⟩ := (hc (U j)).1 (hj₀.trans (hU hj₀j))
      exact ⟨j, hij, y, hy⟩) y hy

/-! ### Compact subsets -/

/-- **Every twisted homology class comes from a compact subset.** Every class of `Hₖ(X; L)` is the
image of a class of `Hₖ(K; L)` for some compact subset `K` of `X`, with `L` restricted to `K`. -/
theorem exists_isCompact_twistedHomologyMap_subtypeVal_eq {k : ℕ} (x : L.twistedHomology k) :
    ∃ (K : Set X) (_ : IsCompact K)
      (y : ((pullback (X := TopCat.of ↥K) (ContinuousMap.subtypeVal K)).obj L).twistedHomology k),
      twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal K)) L k y = x := by
  obtain ⟨K, y, hy⟩ := exists_twistedHomologyMap_subtypeVal_eq L
    (U := fun K : TopologicalSpace.Compacts X ↦ (K : Set X)) (fun K hK ↦ ⟨⟨K, hK⟩, le_rfl⟩) x
  exact ⟨K, K.isCompact, y, hy⟩

/-- **A twisted class on a compact subset that vanishes in `X` vanishes in a compact superset.**
If `K ⊆ X` is compact and a class of `Hₖ(K; L)` maps to zero in `Hₖ(X; L)`, then it already maps
to zero in `Hₖ(K'; L)` for some compact `K'` containing `K`. -/
theorem exists_isCompact_homologyMap_subsetTwistedChainComplexMap_eq_zero {K : Set X}
    (hK : IsCompact K) {k : ℕ}
    (y : ((pullback (X := TopCat.of ↥K) (ContinuousMap.subtypeVal K)).obj L).twistedHomology k)
    (hy : twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal K)) L k y = 0) :
    ∃ (K' : Set X) (_ : IsCompact K') (hKK' : K ⊆ K'),
      HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L hKK') k y = 0 := by
  obtain ⟨K', hK', hy'⟩ := exists_homologyMap_subsetTwistedChainComplexMap_eq_zero L
    (U := fun K : TopologicalSpace.Compacts X ↦ (K : Set X)) (fun _ _ h ↦ h)
    (fun K hK ↦ ⟨⟨K, hK⟩, le_rfl⟩) (i := ⟨K, hK⟩) y hy
  exact ⟨K', K'.isCompact, hK', hy'⟩

/-! ### The colimit over a directed family -/

variable [Preorder ι] (hU : Monotone U) (k : ℕ)

/-- The twisted chain complexes of the members of a monotone family `U` of subsets of `X`, with
`L` restricted to each member, and the maps induced by the inclusions. -/
-- Its object part must compute, so that the legs of `subsetTwistedHomologyCocone` are the maps
-- induced by the inclusions on the nose.
@[expose, simps]
def subsetTwistedChainComplexDiagram : ι ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ where
  obj i := ((pullback (X := TopCat.of ↥(U i)) (ContinuousMap.subtypeVal (U i))).obj
    L).twistedChainComplex
  map f := subsetTwistedChainComplexMap L (hU f.le)
  map_id i := subsetTwistedChainComplexMap_self L (U i)
  map_comp _ _ := (subsetTwistedChainComplexMap_comp_subsetTwistedChainComplexMap L _ _).symm

/-- Twisted homology of the members of a monotone family `U` of subsets of `X`, with `L`
restricted to each member, as a functor on the index order: the homology of
`subsetTwistedChainComplexDiagram`. -/
@[expose, simps!]
def subsetTwistedHomologyFunctor : ι ⥤ ModuleCat.{max v w} R :=
  subsetTwistedChainComplexDiagram L hU ⋙ HomologicalComplex.homologyFunctor _ _ k

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
  ModuleCat.isColimitOfJointlySurjectiveOfMapEqZero _
    (fun x ↦ exists_twistedHomologyMap_subtypeVal_eq L hK x)
    (fun _ y hy ↦ exists_homologyMap_subsetTwistedChainComplexMap_eq_zero L hU hK y hy)

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
