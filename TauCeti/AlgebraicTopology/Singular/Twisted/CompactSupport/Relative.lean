/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.Topology.Category.TopPair

/-!
# Relative singular homology with local coefficients has compact supports

Let `(X, A)` be a pair of a space and a subset, and `L` a local coefficient system on `X`. For a
map `π : X → Y` to a set and a subset `S ⊆ Y`, the pair over `S` is `(π⁻¹ S, π⁻¹ S ∩ A)`, included
into `(X, A)` by `TopCat.restrictPreimagePairMap`. For instance, for a vector bundle with
projection `π` and `A` the complement of the zero section, the pair over `S` is the Thom pair of
the restriction of the bundle to `S` (`TauCeti.thomPairOver`); for `π` the identity it is the pair
`(S, S ∩ A)`.

A relative twisted chain of `(X, A)` is the class of a chain of `X`, which is supported on the
union of the images of finitely many simplices, a compact set. So it is the image of a relative
chain of the pair over every `S` whose preimage contains that compact set
(`TopPair.exists_isCompact_forall_mem_range_twistedChainComplexMap_restrictPreimagePairMap_f`), and
the relative chains of the pairs over subsets inject into those of `(X, A)`. Consequently, if `S`
is a monotone family of subsets of `Y`, indexed by a directed order, such that every compact subset
of `X` lies in some `π⁻¹ (S i)`, then the relative twisted homology `Hₖ(X, A; L)` is the filtered
colimit of the groups `Hₖ(π⁻¹ (S i), π⁻¹ (S i) ∩ A; L)`, with `L` restricted to each member:

* every class of `Hₖ(X, A; L)` comes from some member
  (`TopPair.exists_twistedHomologyMap_restrictPreimagePairMap_eq`);
* a class of a member that vanishes in `Hₖ(X, A; L)` already vanishes in a larger member
  (`TopPair.exists_homologyMap_restrictPreimagePairTwistedChainComplexMap_eq_zero`);
* together, the cocone of the maps induced by the inclusions of pairs is a colimit cocone
  (`TopPair.isColimitRestrictPreimagePairTwistedHomologyCocone`).

The maps between members are `TopPair.restrictPreimagePairTwistedChainComplexMap`, the maps of
relative twisted chains induced by the inclusions `(π⁻¹ S, π⁻¹ S ∩ A) ⟶ (π⁻¹ T, π⁻¹ T ∩ A)` for
`S ⊆ T`.

This is the relative counterpart of
`TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedHomologyCocone`, and the twisted counterpart
of `TopPair.isColimitMapCoconeSingularHomology`. With `π` the
projection of a vector bundle and `S` the finite unions of trivializing open sets, it computes the
homology of a Thom pair with local coefficients from its homology over finite trivializing unions,
where the Mayer–Vietoris sequence of pairs applies.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.6 and the compactness argument in
  the proof of Proposition 2B.1, and Section 3.H.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the passage from finite trivializing unions to the whole base in the
  proof of the Thom isomorphism).
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] {X : TopCat.{v}} (A : Set X)
  (L : LocalCoefficientSystem.{u, v, max v w} R X) {Y : Type*} (π : X → Y)

/-! ### The maps of relative chains induced by the inclusions of the pairs over subsets -/

section Maps

variable {S T U : Set Y}

/-- The inclusion of pairs `(π⁻¹ S, π⁻¹ S ∩ A) ⟶ (π⁻¹ T, π⁻¹ T ∩ A)` for `S ⊆ T`. -/
private abbrev restrictPreimagePairInclusion (h : S ⊆ T) :
    ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ A ⊆ π ⁻¹' S) ⟶
      ofInclusion (Set.inter_subset_left : π ⁻¹' T ∩ A ⊆ π ⁻¹' T) :=
  ofInclusionMap Set.inter_subset_left Set.inter_subset_left
    (ContinuousMap.inclusion (Set.preimage_mono h)) fun _ hx ↦ ⟨h hx.1, hx.2⟩

/-- The map of relative twisted chains induced by the inclusion of pairs
`(π⁻¹ S, π⁻¹ S ∩ A) ⟶ (π⁻¹ T, π⁻¹ T ∩ A)` for `S ⊆ T`, with `L` restricted along the inclusions
of the two pairs into `(X, A)`. -/
def restrictPreimagePairTwistedChainComplexMap (h : S ⊆ T) :
    (ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ A ⊆ π ⁻¹' S)).twistedChainComplex
        ((LocalCoefficientSystem.pullback
          (Hom.fst (TopCat.restrictPreimagePairMap π A S)).hom).obj L) ⟶
      (ofInclusion (Set.inter_subset_left : π ⁻¹' T ∩ A ⊆ π ⁻¹' T)).twistedChainComplex
        ((LocalCoefficientSystem.pullback
          (Hom.fst (TopCat.restrictPreimagePairMap π A T)).hom).obj L) :=
  (ofInclusion _).twistedChainComplexCoefficientMap
      (eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (Hom.fst g).hom).obj L)
          (TopCat.ofInclusionMap_inclusion_comp_restrictPreimagePairMap π A h).symm) ≫
        (fstPullbackCompIso (restrictPreimagePairInclusion A π h)
          (TopCat.restrictPreimagePairMap π A T) L).hom) ≫
    twistedChainComplexMap (restrictPreimagePairInclusion A π h)
      ((LocalCoefficientSystem.pullback
        (Hom.fst (TopCat.restrictPreimagePairMap π A T)).hom).obj L)

/-- The map of relative twisted chains induced by `S ⊆ T`, followed by the map induced by the
inclusion of the pair over `T` into `(X, A)`, is the map induced by the inclusion of the pair over
`S`. -/
@[reassoc (attr := simp)]
lemma restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap (h : S ⊆ T) :
    restrictPreimagePairTwistedChainComplexMap A L π h ≫
        twistedChainComplexMap (TopCat.restrictPreimagePairMap π A T) L =
      twistedChainComplexMap (TopCat.restrictPreimagePairMap π A S) L := by
  rw [twistedChainComplexMap_congr L
      (congrArg Hom.fst (TopCat.ofInclusionMap_inclusion_comp_restrictPreimagePairMap π A h).symm),
    twistedChainComplexMap_comp (restrictPreimagePairInclusion A π h)
      (TopCat.restrictPreimagePairMap π A T) L,
    restrictPreimagePairTwistedChainComplexMap, twistedChainComplexCoefficientMap_comp]
  simp only [Category.assoc]

/-- The inclusion of the pair over `S` into `(X, A)` induces injective maps of relative twisted
chains. -/
theorem twistedChainComplexMap_restrictPreimagePairMap_f_injective (S : Set Y) (k : ℕ) :
    Function.Injective
      ((twistedChainComplexMap (TopCat.restrictPreimagePairMap π A S) L).f k).hom := by
  have : Mono (Hom.fst (TopCat.restrictPreimagePairMap π A S)) := by
    rw [TopCat.restrictPreimagePairMap_fst]
    exact (TopCat.mono_iff_injective _).2 Subtype.val_injective
  refine twistedChainComplexMap_f_injective (TopCat.restrictPreimagePairMap π A S) L
    (fun x hx ↦ ?_) k
  rw [Set.mem_preimage, range_ofSubset_map] at hx
  rw [range_ofInclusion_map]
  exact ⟨x.property, (congrArg (· ∈ A) (TopCat.restrictPreimagePairMap_fst_apply π A S x)).mp hx⟩

/-- The inclusion of the pair over `S` into `(X, A)` induces a monomorphism of relative twisted
chain complexes. -/
instance mono_twistedChainComplexMap_restrictPreimagePairMap (S : Set Y) :
    Mono (twistedChainComplexMap (TopCat.restrictPreimagePairMap π A S) L) :=
  HomologicalComplex.mono_of_mono_f _ fun k ↦ (ModuleCat.mono_iff_injective _).2
    (twistedChainComplexMap_restrictPreimagePairMap_f_injective A L π S k)

/-- The relative map induced by the identity inclusion `S ⊆ S` is the identity. -/
@[simp]
lemma restrictPreimagePairTwistedChainComplexMap_self (S : Set Y) :
    restrictPreimagePairTwistedChainComplexMap A L π (subset_refl S) = 𝟙 _ := by
  rw [← cancel_mono (twistedChainComplexMap (TopCat.restrictPreimagePairMap π A S) L),
    restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap, Category.id_comp]

/-- The relative maps induced by `S ⊆ T` and `T ⊆ U` compose to the map induced by `S ⊆ U`. -/
@[reassoc (attr := simp)]
lemma restrictPreimagePairTwistedChainComplexMap_comp_restrictPreimagePairTwistedChainComplexMap
    (hST : S ⊆ T) (hTU : T ⊆ U) :
    restrictPreimagePairTwistedChainComplexMap A L π hST ≫
        restrictPreimagePairTwistedChainComplexMap A L π hTU =
      restrictPreimagePairTwistedChainComplexMap A L π (hST.trans hTU) := by
  rw [← cancel_mono (twistedChainComplexMap (TopCat.restrictPreimagePairMap π A U) L)]
  simp only [Category.assoc, restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap]

end Maps

/-! ### Compact supports of relative chains and of relative homology classes -/

/-- **Relative twisted chains have compact supports.** Every relative twisted chain `c` of `(X, A)`
is the image of a relative twisted chain of the pair `(π⁻¹ S, π⁻¹ S ∩ A)` over every `S` whose
preimage contains a certain compact set `K`. -/
theorem exists_isCompact_forall_mem_range_twistedChainComplexMap_restrictPreimagePairMap_f
    {k : ℕ} (c : ((ofSubset A).twistedChainComplex L).X k) :
    ∃ K : Set X, IsCompact K ∧ ∀ S : Set Y, K ⊆ π ⁻¹' S →
      c ∈ LinearMap.range
        ((twistedChainComplexMap (TopCat.restrictPreimagePairMap π A S) L).f k).hom := by
  obtain ⟨c, rfl⟩ := (ofSubset A).twistedChainComplexπ_f_surjective L c
  obtain ⟨K, hK, hc⟩ :=
    LocalCoefficientSystem.exists_isCompact_forall_mem_range_twistedChainComplexMap_f L c
  refine ⟨K, hK, fun S hS ↦ ?_⟩
  -- the ambient chain is supported in `π⁻¹ S`, the range of the ambient inclusion
  have hrange : Set.range (Hom.fst (TopCat.restrictPreimagePairMap π A S)) = π ⁻¹' S := by
    rw [TopCat.restrictPreimagePairMap_fst]
    exact Subtype.range_coe
  have hind : Topology.IsInducing (Hom.fst (TopCat.restrictPreimagePairMap π A S)) := by
    rw [TopCat.restrictPreimagePairMap_fst]
    exact Topology.IsInducing.subtypeVal
  have hc' : c ∈ LinearMap.range ((LocalCoefficientSystem.twistedChainComplexMap
      (Hom.fst (TopCat.restrictPreimagePairMap π A S)) L).f k).hom := by
    refine (LocalCoefficientSystem.range_twistedChainComplexMap_f _ L hind k).ge ?_
    -- the two supports agree by `hrange`; `rw [hrange]` is not used because the ambient space of
    -- the pair `(X, A)` is `X` only up to unfolding, which the rewrite's motive check rejects
    convert (LocalCoefficientSystem.range_twistedChainComplexMap_subtypeVal_f L _ k).le
      (hc _ hS) using 3
    exact Iff.of_eq (congrArg (fun s ↦ c ∈ L.smallTwistedChains (fun _ : Unit ↦ s) k) hrange)
  obtain ⟨y, rfl⟩ := hc'
  exact ⟨((ofInclusion _).twistedChainComplexπ _).f k y,
    twistedChainComplexMap_f_twistedChainComplexπ_f_apply (TopCat.restrictPreimagePairMap π A S)
      L y⟩

variable {ι : Type*} {S : ι → Set Y}

/-- **Every relative twisted homology class comes from a member of a family absorbing compact
sets.** If every compact subset of `X` lies in the preimage of some `S i`, every class of
`Hₖ(X, A; L)` is the image of a class of `Hₖ(π⁻¹ (S i), π⁻¹ (S i) ∩ A; L)` for some `i`. -/
theorem exists_twistedHomologyMap_restrictPreimagePairMap_eq
    (hK : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ π ⁻¹' S i) {k : ℕ}
    (x : (ofSubset A).twistedHomology L k) :
    ∃ (i : ι) (y : (ofInclusion (Set.inter_subset_left : π ⁻¹' S i ∩ A ⊆ π ⁻¹' S i)).twistedHomology
        ((LocalCoefficientSystem.pullback
          (Hom.fst (TopCat.restrictPreimagePairMap π A (S i))).hom).obj L) k),
      twistedHomologyMap (TopCat.restrictPreimagePairMap π A (S i)) L k y = x :=
  HomologicalComplex.exists_homologyMap_eq_of_injective k _
    (fun i ↦ twistedChainComplexMap_restrictPreimagePairMap_f_injective A L π (S i) _)
    (fun c ↦ by
      obtain ⟨K, hKc, hc⟩ :=
        exists_isCompact_forall_mem_range_twistedChainComplexMap_restrictPreimagePairMap_f A L π c
      obtain ⟨i, hi⟩ := hK K hKc
      obtain ⟨y, hy⟩ := hc (S i) hi
      exact ⟨i, y, hy⟩) x

/-- **A relative twisted homology class that vanishes in `(X, A)` vanishes in a larger member.**
Let `S` be a monotone family indexed by a directed order such that every compact subset of `X`
lies in the preimage of some `S i`. A class of `Hₖ(π⁻¹ (S i), π⁻¹ (S i) ∩ A; L)` whose image in
`Hₖ(X, A; L)` vanishes already vanishes in the group of some `S j` with `i ≤ j`. -/
theorem exists_homologyMap_restrictPreimagePairTwistedChainComplexMap_eq_zero [Preorder ι]
    [IsDirectedOrder ι] (hS : Monotone S) (hK : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ π ⁻¹' S i)
    {k : ℕ} {i : ι}
    (y : (ofInclusion (Set.inter_subset_left : π ⁻¹' S i ∩ A ⊆ π ⁻¹' S i)).twistedHomology
      ((LocalCoefficientSystem.pullback
        (Hom.fst (TopCat.restrictPreimagePairMap π A (S i))).hom).obj L) k)
    (hy : twistedHomologyMap (TopCat.restrictPreimagePairMap π A (S i)) L k y = 0) :
    ∃ (j : ι) (hij : i ≤ j), HomologicalComplex.homologyMap
      (restrictPreimagePairTwistedChainComplexMap A L π (hS hij)) k y = 0 :=
  HomologicalComplex.exists_homologyMap_eq_zero_of_injective k
    (fun j ↦ twistedChainComplexMap (TopCat.restrictPreimagePairMap π A (S j)) L)
    (fun j ↦ twistedChainComplexMap_restrictPreimagePairMap_f_injective A L π (S j) _)
    (ChainComplex.prev ℕ k) (P := (i ≤ ·))
    (fun _ hij ↦ restrictPreimagePairTwistedChainComplexMap A L π (hS hij))
    (fun _ hij ↦ restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap A L π
      (hS hij))
    (fun c ↦ by
      -- the bounding chain lies in some member, and then in a member above `i`
      obtain ⟨K, hKc, hc⟩ :=
        exists_isCompact_forall_mem_range_twistedChainComplexMap_restrictPreimagePairMap_f A L π c
      obtain ⟨j₀, hj₀⟩ := hK K hKc
      obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
      obtain ⟨y, hy⟩ := hc (S j) (hj₀.trans (Set.preimage_mono (hS hj₀j)))
      exact ⟨j, hij, y, hy⟩) y hy

/-! ### The colimit over a directed family -/

variable [Preorder ι] (hS : Monotone S) (k : ℕ)

/-- Relative twisted homology of the pairs `(π⁻¹ (S i), π⁻¹ (S i) ∩ A)` over the members of a
monotone family `S`, with `L` restricted to each, as a functor on the index order. -/
-- Its object part must compute, so that the legs of
-- `restrictPreimagePairTwistedHomologyCocone` are the maps induced by the inclusions on the nose.
@[expose, simps]
def restrictPreimagePairTwistedHomologyFunctor : ι ⥤ ModuleCat.{max v w} R where
  obj i := (ofInclusion (Set.inter_subset_left : π ⁻¹' S i ∩ A ⊆ π ⁻¹' S i)).twistedHomology
    ((LocalCoefficientSystem.pullback
      (Hom.fst (TopCat.restrictPreimagePairMap π A (S i))).hom).obj L) k
  map {i j} f := HomologicalComplex.homologyMap
    (restrictPreimagePairTwistedChainComplexMap A L π (hS f.le)) k
  map_id i := by
    rw [restrictPreimagePairTwistedChainComplexMap_self, HomologicalComplex.homologyMap_id]
  map_comp f g := by
    rw [← HomologicalComplex.homologyMap_comp,
      restrictPreimagePairTwistedChainComplexMap_comp_restrictPreimagePairTwistedChainComplexMap]

/-- The cocone of the maps `Hₖ(π⁻¹ (S i), π⁻¹ (S i) ∩ A; L) ⟶ Hₖ(X, A; L)` induced by the
inclusions of the pairs over the members of a monotone family `S`. -/
-- Its point must compute, so that it is the relative twisted homology of `(X, A)` on the nose.
@[expose, simps]
def restrictPreimagePairTwistedHomologyCocone :
    Limits.Cocone (restrictPreimagePairTwistedHomologyFunctor A L π hS k) where
  pt := (ofSubset A).twistedHomology L k
  ι :=
    { app i := twistedHomologyMap (TopCat.restrictPreimagePairMap π A (S i)) L k
      naturality _ _ f :=
        ((HomologicalComplex.homologyMap_comp _ _ k).symm.trans
          (congrArg (HomologicalComplex.homologyMap · k)
            (restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap A L π
              (hS f.le)))).trans
          (Category.comp_id _).symm }

/-- **Relative twisted singular homology has compact supports.** If `S` is a monotone family of
subsets of `Y`, indexed by a directed order, such that every compact subset of `X` lies in the
preimage under `π` of some `S i`, then `Hₖ(X, A; L)` is the colimit of the groups
`Hₖ(π⁻¹ (S i), π⁻¹ (S i) ∩ A; L)`, with `L` restricted to each member. -/
def isColimitRestrictPreimagePairTwistedHomologyCocone [IsDirectedOrder ι]
    (hK : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ π ⁻¹' S i) :
    Limits.IsColimit (restrictPreimagePairTwistedHomologyCocone A L π hS k) :=
  ModuleCat.isColimitOfJointlySurjectiveOfMapEqZero _
    (fun x ↦ exists_twistedHomologyMap_restrictPreimagePairMap_eq A L π hK x)
    (fun _ y hy ↦
      exists_homologyMap_restrictPreimagePairTwistedChainComplexMap_eq_zero A L π hS hK y hy)

end TopPair
