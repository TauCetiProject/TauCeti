/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.ExhaustionComparison
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Functoriality
public import TauCeti.Topology.Compactness.SigmaCompact

/-!
# Open restriction of Borel–Moore homology with local coefficients

Borel–Moore homology restricts contravariantly along open embeddings `i : V ⟶ U` into Hausdorff
spaces. Given a compact exhaustion `K` of `V` and a local coefficient system `L` on `U`, each
image `i '' K n` is compact, hence closed in `U`, and the relative twisted chain complexes
`C(U, (i '' K n)ᶜ; L)` form a specialization `openRestrictionTower i L K` of
`complChainComplexTower` with surjective shifts. Locally finite chains of `U` map to
`(openRestrictionTower i L K).limComplex`, while excision with local coefficients
(`TopPair.quasiIso_twistedChainComplexMap_of_open_cover`) and `ComplexTower.quasiIso_limComplexMap`
make `locallyFiniteChainComplexOpenRestrictionExcision` from
`locallyFiniteChainComplex ((pullback i.hom).obj L)` to `(openRestrictionTower i L K).limComplex`
a quasi-isomorphism. Inverting the induced homology isomorphism defines
`borelMooreHomologyOpenRestrictionOfExhaustion` and, for weakly locally compact `σ`-compact `V`,
`borelMooreHomologyOpenRestriction`, together with exhaustion independence, coefficient naturality,
compatibility with finite chains, identity, contravariant functoriality, and Cartesian base change
with proper pushforward (`borelMooreHomologyMap`).

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
* B. Iversen, *Cohomology of Sheaves*, Universitext, Springer, 1986, Chapter IX.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite SimplexCategory Topology
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section AmbientTower

variable {V U : TopCat.{v}} (i : V ⟶ U)
  (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V)

/-- The tower of ambient relative twisted chain complexes `C(U, (i '' K n)ᶜ; L)` associated to a
map `i : V ⟶ U` and a compact exhaustion `K` of `V`. -/
-- Exposed so that the terms of the tower are definitionally the relative chain complexes, matching
-- `complChainComplexTower` and `relativeChainComplexTower`.
@[expose]
def openRestrictionTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  complChainComplexTower L (fun n ↦ i '' K n) (fun n ↦ Set.image_mono (K.subset_succ n))

/-- The stage-`n` term of `openRestrictionTower i L K` is `C(U, (i '' K n)ᶜ; L)`. -/
lemma openRestrictionTower_obj (n : ℕ) :
    (openRestrictionTower i L K).obj (op n) =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplex L :=
  (rfl)

/-- The successor transition of `openRestrictionTower i L K` is the triple quotient map. -/
@[simp]
lemma openRestrictionTower_map_succ (n : ℕ) :
    (openRestrictionTower i L K).map (homOfLE (Nat.le_succ n)).op =
      TopTriple.twistedChainComplexTotalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L :=
  complChainComplexTower_map_succ L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) n

/-- Every transition of `openRestrictionTower i L K` commutes with the projections from ambient
twisted chains. -/
@[reassoc, simp]
lemma twistedChainComplexπ_comp_openRestrictionTower_map {m n : ℕ} (f : op m ⟶ op n) :
    (TopPair.ofSubset (i '' K m)ᶜ).twistedChainComplexπ L ≫
        (openRestrictionTower i L K).map f =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexπ L :=
  twistedChainComplexπ_comp_complChainComplexTower_map L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) f

/-- The transitions of `openRestrictionTower i L K` are surjective in every degree. -/
lemma openRestrictionTower_transition_surjective (k n : ℕ) :
    Function.Surjective (((openRestrictionTower i L K).term k).transition n) :=
  complChainComplexTower_transition_surjective L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) k n

/-- The ambient relative tower of an open restriction has surjective shifts in every degree. -/
lemma openRestrictionTower_shift_surjective (k : ℕ) :
    Function.Surjective ((openRestrictionTower i L K).term k).shift :=
  complChainComplexTower_shift_surjective L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) k

/-- The canonical chain map from locally finite chains on `U` to the limit complex of
`openRestrictionTower i L K`. -/
def locallyFiniteChainComplexToOpenRestrictionLim :
    locallyFiniteChainComplex L ⟶ (openRestrictionTower i L K).limComplex :=
  locallyFiniteChainComplexToComplLim L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ (K.isCompact n).image i.hom.continuous)

/-- `locallyFiniteChainComplexToOpenRestrictionLim` is `locallyFiniteChainComplexToComplLim`
specialized to the compact images `n ↦ i '' K n`. -/
lemma locallyFiniteChainComplexToOpenRestrictionLim_eq_toComplLim :
    locallyFiniteChainComplexToOpenRestrictionLim i L K =
      locallyFiniteChainComplexToComplLim L (fun n ↦ i '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n))
        (fun n ↦ (K.isCompact n).image i.hom.continuous) :=
  (rfl)

/-- On stage `n`, `locallyFiniteChainComplexToOpenRestrictionLim` takes the relative class modulo
`(i '' K n)ᶜ`. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToOpenRestrictionLim_comp_π (n : ℕ) :
    locallyFiniteChainComplexToOpenRestrictionLim i L K ≫
        (openRestrictionTower i L K).limComplexπ n =
      (TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
        ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map :=
  locallyFiniteChainComplexToComplLim_comp_π L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ (K.isCompact n).image i.hom.continuous) n

variable {K} in
/-- Enlarging the exhaustion `K` on `V` induces a quotient morphism of ambient relative towers. -/
def openRestrictionTowerMap {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    openRestrictionTower i L K' ⟶ openRestrictionTower i L K :=
  complChainComplexTowerMap L (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun n ↦ Set.image_mono (K'.subset_succ n)) (fun n ↦ Set.image_mono (h n))

variable {K} in
/-- On level `n`, `openRestrictionTowerMap` is the triple quotient map from `(i '' K' n)ᶜ` to
`(i '' K n)ᶜ`. -/
@[simp]
lemma openRestrictionTowerMap_app {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (openRestrictionTowerMap i L h).app (op n) =
      (TopTriple.ofSubset
        (Set.compl_subset_compl.2 (Set.image_mono (h n)))).twistedChainComplexTotalToOuter L :=
  complChainComplexTowerMap_app L (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun n ↦ Set.image_mono (K'.subset_succ n)) (fun n ↦ Set.image_mono (h n)) n

variable {K} in
/-- `openRestrictionTowerMap` preserves the relative classes of finite ambient chains. -/
@[reassoc]
lemma twistedChainComplexπ_comp_openRestrictionTowerMap_app {K' : CompactExhaustion V}
    (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (TopPair.ofSubset (i '' K' n)ᶜ).twistedChainComplexπ L ≫
        (openRestrictionTowerMap i L h).app (op n) =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexπ L :=
  twistedChainComplexπ_comp_complChainComplexTowerMap_app L
    (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ Set.image_mono (K'.subset_succ n))
    (fun n ↦ Set.image_mono (h n)) n

variable {K} in
/-- `locallyFiniteChainComplexToOpenRestrictionLim` commutes with enlarging `K`. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToOpenRestrictionLim_comp_limComplexMap
    {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexToOpenRestrictionLim i L K' ≫
        ComplexTower.limComplexMap (openRestrictionTowerMap i L h) =
      locallyFiniteChainComplexToOpenRestrictionLim i L K :=
  locallyFiniteChainComplexToComplLim_comp_limComplexMap L
    (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ Set.image_mono (K'.subset_succ n))
    (fun n ↦ (K.isCompact n).image i.hom.continuous)
    (fun n ↦ (K'.isCompact n).image i.hom.continuous) (fun n ↦ Set.image_mono (h n))

variable {L} in
/-- Morphism of ambient relative towers induced by a morphism of local coefficient systems. -/
def openRestrictionTowerCoefficientMap {L' : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L ⟶ L') :
    openRestrictionTower i L K ⟶ openRestrictionTower i L' K :=
  complChainComplexTowerCoefficientMap (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) η

variable {L} in
/-- On level `n`, `openRestrictionTowerCoefficientMap` is the relative coefficient map on
`(U, (i '' K n)ᶜ)`. -/
@[simp]
lemma openRestrictionTowerCoefficientMap_app {L' : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L ⟶ L') (n : ℕ) :
    (openRestrictionTowerCoefficientMap i K η).app (op n) =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexCoefficientMap η :=
  complChainComplexTowerCoefficientMap_app (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) η n

variable {L} in
/-- `locallyFiniteChainComplexToOpenRestrictionLim` is natural in the local coefficient system. -/
@[reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp_toOpenRestrictionLim
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') :
    locallyFiniteChainComplexCoefficientMap η ≫
        locallyFiniteChainComplexToOpenRestrictionLim i L' K =
      locallyFiniteChainComplexToOpenRestrictionLim i L K ≫
        ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap i K η) :=
  locallyFiniteChainComplexCoefficientMap_comp_toComplLim (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) η (fun n ↦ (K.isCompact n).image i.hom.continuous)

end AmbientTower

section ExcisionTower

variable {V U : TopCat.{v}} (i : V ⟶ U)

/-- The tower morphism from the relative chain tower of `V` to `openRestrictionTower i L K`
induced by the pair maps `(V, (K n)ᶜ) ⟶ (U, (i '' K n)ᶜ)`. -/
def openRestrictionExcisionTowerMap (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) :
    relativeChainComplexTower ((pullback i.hom).obj L) K ⟶ openRestrictionTower i L K :=
  complChainComplexTowerPairMap i L K.subset_succ (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem))

/-- `openRestrictionExcisionTowerMap` is `complChainComplexTowerPairMap` specialized to `K` and
its images `n ↦ i '' K n`. -/
lemma openRestrictionExcisionTowerMap_eq_complChainComplexTowerPairMap
    (hinj : Function.Injective i) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K : CompactExhaustion V) :
    openRestrictionExcisionTowerMap i hinj L K =
      complChainComplexTowerPairMap i L K.subset_succ (fun n ↦ Set.image_mono (K.subset_succ n))
        (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem)) :=
  (rfl)

/-- On level `n`, `openRestrictionExcisionTowerMap` is the relative twisted chain map induced by
`i` on `(V, (K n)ᶜ) ⟶ (U, (i '' K n)ᶜ)`. -/
@[simp]
lemma openRestrictionExcisionTowerMap_app (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) (n : ℕ) :
    (openRestrictionExcisionTowerMap i hinj L K).app (op n) =
      TopPair.twistedChainComplexMap
        (TopPair.ofHom (X := TopPair.ofSubset (K n)ᶜ) (Y := TopPair.ofSubset (i '' K n)ᶜ) i
          (TopCat.ofHom ⟨Set.MapsTo.restrict i _ _ (fun _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem)),
            i.hom.continuous.restrict _⟩) rfl) L :=
  complChainComplexTowerPairMap_app i L K.subset_succ (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem)) n

/-- On finite ambient chains, `openRestrictionExcisionTowerMap` is induced by
`twistedChainComplexMap i L`. -/
@[reassoc]
lemma twistedChainComplexπ_comp_openRestrictionExcisionTowerMap_app (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) (n : ℕ) :
    (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ ((pullback i.hom).obj L) ≫
        (openRestrictionExcisionTowerMap i hinj L K).app (op n) =
      twistedChainComplexMap i L ≫ (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexπ L :=
  twistedChainComplexπ_comp_complChainComplexTowerPairMap_app i L K.subset_succ
    (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem)) n

/-- Enlarging `K` commutes with `openRestrictionExcisionTowerMap`. -/
@[reassoc]
lemma relativeChainComplexTowerMap_comp_openRestrictionExcisionTowerMap
    (hinj : Function.Injective i) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    relativeChainComplexTowerMap ((pullback i.hom).obj L) h ≫
        openRestrictionExcisionTowerMap i hinj L K =
      openRestrictionExcisionTowerMap i hinj L K' ≫ openRestrictionTowerMap i L h := by
  rw [relativeChainComplexTowerMap_eq_complChainComplexTowerMap]
  exact complChainComplexTowerMap_comp_complChainComplexTowerPairMap i L K.subset_succ
    K'.subset_succ (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun n ↦ Set.image_mono (K'.subset_succ n))
    (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem))
    (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem)) h (fun n ↦ Set.image_mono (h n))

/-- `openRestrictionExcisionTowerMap` is natural in the local coefficient system. -/
@[reassoc]
lemma openRestrictionExcisionTowerMap_naturality (hinj : Function.Injective i)
    {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R U} (η : L₁ ⟶ L₂)
    (K : CompactExhaustion V) :
    openRestrictionExcisionTowerMap i hinj L₁ K ≫ openRestrictionTowerCoefficientMap i K η =
      relativeChainComplexTowerCoefficientMap K ((pullback i.hom).map η) ≫
        openRestrictionExcisionTowerMap i hinj L₂ K := by
  have h : relativeChainComplexTowerCoefficientMap K ((pullback i.hom).map η) =
      complChainComplexTowerCoefficientMap K K.subset_succ ((pullback i.hom).map η) :=
    NatTrans.ext <| funext fun n ↦
      (relativeChainComplexTowerCoefficientMap_app K _ n.unop).trans
        (complChainComplexTowerCoefficientMap_app K K.subset_succ _ n.unop).symm
  rw [h]
  exact complChainComplexTowerPairMap_naturality i η K.subset_succ
    (fun n ↦ Set.image_mono (K.subset_succ n)) (fun _ _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem))

/-- **Excision at each stage of an open restriction.** -/
theorem quasiIso_openRestrictionExcisionTowerMap_app [T2Space U] (hi : IsOpenEmbedding i.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) (n : ℕ) :
    QuasiIso ((openRestrictionExcisionTowerMap i hi.injective L K).app (op n)) := by
  have hmaps : Set.MapsTo i (K n)ᶜ (i '' K n)ᶜ :=
    fun _ hx hmem ↦ hx (hi.injective.mem_set_image.1 hmem)
  rw [openRestrictionExcisionTowerMap_app]
  refine TopPair.quasiIso_twistedChainComplexMap_of_open_cover
    (TopPair.ofHom (X := TopPair.ofSubset (K n)ᶜ) (Y := TopPair.ofSubset (i '' K n)ᶜ) i
      (TopCat.ofHom ⟨hmaps.restrict, i.hom.continuous.restrict hmaps⟩) rfl) L hi.isEmbedding
    (fun x hx ↦ by rw [TopPair.range_ofSubset_map] at hx ⊢; exact fun hxK ↦ hx ⟨x, hxK, rfl⟩)
    (fun b : Bool ↦ bif b then Set.range i else (i '' K n)ᶜ)
    (Bool.rec ((K.isCompact n).image i.hom.continuous).isClosed.isOpen_compl hi.isOpen_range)
    (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 <|
      Classical.byCases (p := y ∈ i '' K n) (fun ⟨x, _, hxy⟩ ↦ ⟨true, x, hxy⟩) (⟨false, ·⟩))
    (Bool.rec (Or.inl (TopPair.range_ofSubset_map (B := (i '' K n)ᶜ)).ge) (Or.inr le_rfl))

/-- **Excision on the limit complex.** For an open embedding `i : V ⟶ U` into a Hausdorff space,
`openRestrictionExcisionTowerMap` induces a quasi-isomorphism on limit complexes. -/
theorem quasiIso_limComplexMap_openRestrictionExcisionTowerMap [T2Space U]
    (hi : IsOpenEmbedding i.hom) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K : CompactExhaustion V) :
    QuasiIso (ComplexTower.limComplexMap
      (openRestrictionExcisionTowerMap i hi.injective L K)) := by
  have (n : ℕ) := quasiIso_openRestrictionExcisionTowerMap_app i hi L K n
  exact ComplexTower.quasiIso_limComplexMap _
    (relativeChainComplexTower_shift_surjective ((pullback i.hom).obj L) K)
    (openRestrictionTower_shift_surjective i L K)

/-- The excision chain map from locally finite chains on `V` to the limit complex of
`openRestrictionTower i L K`. -/
def locallyFiniteChainComplexOpenRestrictionExcision (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) :
    locallyFiniteChainComplex ((pullback i.hom).obj L) ⟶ (openRestrictionTower i L K).limComplex :=
  (locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
    ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hinj L K)

/-- Unfolding lemma for `locallyFiniteChainComplexOpenRestrictionExcision`. -/
lemma locallyFiniteChainComplexOpenRestrictionExcision_def (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) :
    locallyFiniteChainComplexOpenRestrictionExcision i hinj L K =
      (locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
        ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hinj L K) :=
  (rfl)

/-- On stage `n`, `locallyFiniteChainComplexOpenRestrictionExcision` takes the relative class on
`(V, (K n)ᶜ)` followed by the excision map into `(U, (i '' K n)ᶜ)`. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexOpenRestrictionExcision_comp_π (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) (n : ℕ) :
    locallyFiniteChainComplexOpenRestrictionExcision i hinj L K ≫
        (openRestrictionTower i L K).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
          ((pullback i.hom).obj L) (K.isCompact n).compl_range_ofSubset_compl_map ≫
        (openRestrictionExcisionTowerMap i hinj L K).app (op n) :=
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans
      (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc _ K n _)

/-- Enlarging `K` commutes with `locallyFiniteChainComplexOpenRestrictionExcision`. -/
@[reassoc]
lemma locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap
    (hinj : Function.Injective i) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexOpenRestrictionExcision i hinj L K' ≫
        ComplexTower.limComplexMap (openRestrictionTowerMap i L h) =
      locallyFiniteChainComplexOpenRestrictionExcision i hinj L K := by
  rw [locallyFiniteChainComplexOpenRestrictionExcision_def,
    locallyFiniteChainComplexOpenRestrictionExcision_def, Category.assoc,
    ← ComplexTower.limComplexMap_comp,
    ← relativeChainComplexTowerMap_comp_openRestrictionExcisionTowerMap,
    ComplexTower.limComplexMap_comp,
    locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap_assoc]

/-- `locallyFiniteChainComplexOpenRestrictionExcision` is natural in the local coefficient
system. -/
@[reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision
    (hinj : Function.Injective i) {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L₁ ⟶ L₂) (K : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap ((pullback i.hom).map η) ≫
        locallyFiniteChainComplexOpenRestrictionExcision i hinj L₂ K =
      locallyFiniteChainComplexOpenRestrictionExcision i hinj L₁ K ≫
        ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap i K η) := by
  rw [locallyFiniteChainComplexOpenRestrictionExcision_def,
    locallyFiniteChainComplexOpenRestrictionExcision_def, ← Category.assoc,
    locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom, Category.assoc,
    ← ComplexTower.limComplexMap_comp, ← openRestrictionExcisionTowerMap_naturality,
    ComplexTower.limComplexMap_comp, Category.assoc]

/-- The excision chain map `locallyFiniteChainComplexOpenRestrictionExcision` is a
quasi-isomorphism. -/
theorem quasiIso_locallyFiniteChainComplexOpenRestrictionExcision [T2Space U]
    (hi : IsOpenEmbedding i.hom) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K : CompactExhaustion V) :
    QuasiIso (locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K) := by
  rw [locallyFiniteChainComplexOpenRestrictionExcision_def]
  have := quasiIso_limComplexMap_openRestrictionExcisionTowerMap i hi L K
  infer_instance

/-- In every degree `j`, the homology map induced by
`locallyFiniteChainComplexOpenRestrictionExcision` is an isomorphism. -/
theorem isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision [T2Space U]
    (hi : IsOpenEmbedding i.hom) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K : CompactExhaustion V) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K) j) := by
  have := quasiIso_locallyFiniteChainComplexOpenRestrictionExcision i hi L K
  infer_instance

end ExcisionTower

section OpenRestriction

variable {V U : TopCat.{v}} [T2Space U] (i : V ⟶ U) (hi : IsOpenEmbedding i.hom)
  (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V)

/-- **Contravariant open restriction of Borel–Moore homology**, defined with respect to an explicit
compact exhaustion `K` of `V` (and independent of `K` by
`borelMooreHomologyOpenRestrictionOfExhaustion_eq`). -/
def borelMooreHomologyOpenRestrictionOfExhaustion (j : ℕ) :
    borelMooreHomology L j ⟶ borelMooreHomology ((pullback i.hom).obj L) j :=
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision i hi L K j
  HomologicalComplex.homologyMap (locallyFiniteChainComplexToOpenRestrictionLim i L K) j ≫
    inv (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K) j)

/-- Characterizing equation of `borelMooreHomologyOpenRestrictionOfExhaustion`: followed by the
excision isomorphism into the homology of `(openRestrictionTower i L K).limComplex`, it is the map
induced by `locallyFiniteChainComplexToOpenRestrictionLim`. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K) j =
      HomologicalComplex.homologyMap (locallyFiniteChainComplexToOpenRestrictionLim i L K) j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision i hi L K j
  simp [borelMooreHomologyOpenRestrictionOfExhaustion]

/-- Uniqueness criterion for `borelMooreHomologyOpenRestrictionOfExhaustion`. -/
theorem eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion {M : ModuleCat.{max v w} R} {j : ℕ}
    {g : M ⟶ borelMooreHomology L j}
    {f : M ⟶ borelMooreHomology ((pullback i.hom).obj L) j}
    (hf : f ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K) j =
      g ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToOpenRestrictionLim i L K) j) :
    f = g ≫ borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision i hi L K j
  apply (cancel_mono (HomologicalComplex.homologyMap
    (locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K) j)).1
  rw [Category.assoc, borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap, hf]

/-- At each finite stage `n` of the exhaustion `K`, the relative class of the open-restricted
Borel–Moore homology class in `H_j(V, (K n)ᶜ; i^*L)` maps under excision to the relative class of
the ambient Borel–Moore homology class in `H_j(U, (i '' K n)ᶜ; L)`. -/
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp_toRelative (j n : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
            ((pullback i.hom).obj L) (K.isCompact n).compl_range_ofSubset_compl_map) j ≫
          HomologicalComplex.homologyMap
            ((openRestrictionExcisionTowerMap i hi.injective L K).app (op n)) j =
      HomologicalComplex.homologyMap
        ((TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map) j :=
  (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j).symm).trans <|
    (congrArg (fun φ ↦ _ ≫ HomologicalComplex.homologyMap φ j)
      (locallyFiniteChainComplexOpenRestrictionExcision_comp_π i hi.injective L K n).symm).trans <|
      (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j)).trans <|
        (borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_assoc i hi L K j _).trans <|
          (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
            (congrArg (HomologicalComplex.homologyMap · j)
              (locallyFiniteChainComplexToOpenRestrictionLim_comp_π i L K n))

private lemma borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset
    {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K' j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j := by
  refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K (g := 𝟙 _) ?_).trans
    (Category.id_comp _)
  rw [Category.id_comp, ← locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap
      i hi.injective L h, HomologicalComplex.homologyMap_comp,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp,
    locallyFiniteChainComplexToOpenRestrictionLim_comp_limComplexMap]

/-- **Exhaustion independence of open restriction.** Any two compact exhaustions of `V` define the
same open restriction map on Borel–Moore homology. -/
theorem borelMooreHomologyOpenRestrictionOfExhaustion_eq (K' : CompactExhaustion V) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K' j :=
  (borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset i hi L K
    (CompactExhaustion.subset_sup_left K K') j).symm.trans
    (borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset i hi L K'
      (CompactExhaustion.subset_sup_right K K') j)

/-- **Open restriction is natural in the local coefficient system.** -/
@[reassoc]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_naturality
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') (j : ℕ) :
    borelMooreHomologyCoefficientMap η j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i hi L' K j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        borelMooreHomologyCoefficientMap ((pullback i.hom).map η) j := by
  symm
  refine eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L' K ?_
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision,
    HomologicalComplex.homologyMap_comp,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp,
    ← locallyFiniteChainComplexCoefficientMap_comp_toOpenRestrictionLim,
    HomologicalComplex.homologyMap_comp]

/-- **Compatibility of open restriction with finite chains pushed forward from `V`.** -/
@[reassoc (attr := simp)]
theorem twistedHomologyMap_comp_borelMooreHomologyOpenRestrictionOfExhaustion (j : ℕ) :
    twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      twistedHomologyToBorelMooreHomology ((pullback i.hom).obj L) j := by
  symm
  refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K
    (g := twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j) ?_).trans
      (Category.assoc _ _ _).symm
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  refine (openRestrictionTower i L K).limComplex_hom_ext fun n ↦
    ((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·)
        (locallyFiniteChainComplexOpenRestrictionExcision_comp_π i hi.injective L K n)).trans <|
        (TopPair.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative_assoc
          (TopPair.ofSubset (K n)ᶜ) ((pullback i.hom).obj L) _ _).trans
          (twistedChainComplexπ_comp_openRestrictionExcisionTowerMap_app
            i hi.injective L K n)).trans
      ((Category.assoc _ _ _).trans <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
          (locallyFiniteChainComplexToOpenRestrictionLim_comp_π i L K n))).trans
          (congrArg (_ ≫ ·)
            (TopPair.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative
              (TopPair.ofSubset (i '' K n)ᶜ) L _))).symm

/-- **Contravariant open restriction of Borel–Moore homology** along an open embedding `i : V ⟶ U`
from a weakly locally compact `σ`-compact space `V` into a Hausdorff space `U`. -/
def borelMooreHomologyOpenRestriction [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (j : ℕ) :
    borelMooreHomology L j ⟶ borelMooreHomology ((pullback i.hom).obj L) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion i hi L (CompactExhaustion.choice V) j

/-- Any compact exhaustion computes `borelMooreHomologyOpenRestriction`. -/
@[simp]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V] (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      borelMooreHomologyOpenRestriction i hi L j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_eq i hi L K (CompactExhaustion.choice V) j

/-- `borelMooreHomologyOpenRestriction` is natural in the local coefficient system. -/
@[reassoc]
theorem borelMooreHomologyOpenRestriction_naturality
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') (j : ℕ) :
    borelMooreHomologyCoefficientMap η j ≫
        borelMooreHomologyOpenRestriction i hi L' j =
      borelMooreHomologyOpenRestriction i hi L j ≫
        borelMooreHomologyCoefficientMap ((pullback i.hom).map η) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_naturality i hi L (CompactExhaustion.choice V) η j

/-- Open restriction of a finite chain pushed forward from `V` recovers its locally finite class
on `V`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyMap_comp_borelMooreHomologyOpenRestriction
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V] (j : ℕ) :
    twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestriction i hi L j =
      twistedHomologyToBorelMooreHomology ((pullback i.hom).obj L) j :=
  twistedHomologyMap_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L
    (CompactExhaustion.choice V) j

end OpenRestriction

section Functoriality

/-- **Identity law for open restriction of Borel–Moore homology.** Restricting along `𝟙 U` agrees
with the canonical coefficient identification `L ⟶ (pullback (𝟙 U).hom).obj L`. -/
@[simp]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_id {U : TopCat.{v}} [T2Space U]
    (hi : IsOpenEmbedding (𝟙 U : U ⟶ U).hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion U) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion (𝟙 U) hi L K j =
      borelMooreHomologyCoefficientMap ((pullbackIdIso U).inv.app L) j := by
  symm
  refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion (𝟙 U) hi L K
    (g := 𝟙 _) ?_).trans (Category.id_comp _)
  rw [Category.id_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  apply (openRestrictionTower (𝟙 U) L K).limComplex_hom_ext
  intro n
  have hsub : (K n)ᶜ ⊆ ((𝟙 U : U ⟶ U) '' K n)ᶜ := by simp
  have hrel :
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap ((pullbackIdIso U).inv.app L) ≫
          (openRestrictionExcisionTowerMap (𝟙 U) hi.injective L K).app (op n) =
        (TopTriple.ofSubset hsub).twistedChainComplexTotalToOuter L := by
    apply (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_hom_ext L
    refine (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
      (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso U).inv.app L) _).trans <|
      (congrArg (_ ≫ ·) (twistedChainComplexπ_comp_openRestrictionExcisionTowerMap_app
        (𝟙 U) hi.injective L K n)).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) ?_).trans <|
          (Category.id_comp _).trans
            ((TopTriple.ofSubset hsub).twistedChainComplexπ_comp_totalToOuter L).symm
    exact (congrArg (_ ≫ ·) (twistedChainComplexMap_id L)).trans <|
      (twistedChainComplexCoefficientMap_comp _ _).symm.trans <|
        (congrArg twistedChainComplexCoefficientMap ((pullbackIdIso U).inv_hom_id_app L)).trans
          (twistedChainComplexCoefficientMap_id L)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (locallyFiniteChainComplexOpenRestrictionExcision_comp_π (𝟙 U) hi.injective L K n)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (TopPair.locallyFiniteChainComplexToRelative_naturality
          (TopPair.ofSubset (K n)ᶜ) _ ((pullbackIdIso U).inv.app L)).symm).trans <|
          (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hrel).trans <|
            (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
              (TopTriple.ofSubset hsub) L _ _).trans
              (locallyFiniteChainComplexToOpenRestrictionLim_comp_π (𝟙 U) L K n).symm

/-- Identity law for `borelMooreHomologyOpenRestriction`. -/
@[simp]
theorem borelMooreHomologyOpenRestriction_id {U : TopCat.{v}} [T2Space U]
    [WeaklyLocallyCompactSpace U] [SigmaCompactSpace U]
    (hi : IsOpenEmbedding (𝟙 U : U ⟶ U).hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (j : ℕ) :
    borelMooreHomologyOpenRestriction (𝟙 U) hi L j =
      borelMooreHomologyCoefficientMap ((pullbackIdIso U).inv.app L) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_id hi L (CompactExhaustion.choice U) j

/-- **Contravariant composition law for open restriction of Borel–Moore homology**, for explicit
compact exhaustions on `W` and `V`. -/
@[reassoc]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp
    {W V U : TopCat.{v}} [T2Space V] [T2Space U]
    (i₁ : W ⟶ V) (i₂ : V ⟶ U) (hi₁ : IsOpenEmbedding i₁.hom) (hi₂ : IsOpenEmbedding i₂.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K_W : CompactExhaustion W) (K_V : CompactExhaustion V) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W j ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j =
      borelMooreHomologyOpenRestrictionOfExhaustion i₂ hi₂ L K_V j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ ((pullback i₂.hom).obj L) K_W j := by
  let K_V' : CompactExhaustion V := K_V.supImage i₁.hom.continuous hi₁.isOpenMap K_W
  rw [borelMooreHomologyOpenRestrictionOfExhaustion_eq i₂ hi₂ L K_V K_V' j]
  have hWV (n : ℕ) : i₁ '' K_W n ⊆ K_V' n :=
    K_V.image_subset_supImage i₁.hom.continuous hi₁.isOpenMap K_W n
  have hUW (n : ℕ) : (i₁ ≫ i₂) '' K_W n ⊆ i₂ '' K_V' n := by
    rw [TopCat.coe_comp, Set.image_comp]; exact Set.image_mono (hWV n)
  have hMaps (n : ℕ) : Set.MapsTo i₂ (i₁ '' K_W n)ᶜ ((i₁ ≫ i₂) '' K_W n)ᶜ :=
    fun _ hy ⟨x, hx, hxy⟩ ↦ hy ⟨x, hx, hi₂.injective hxy⟩
  let qV : relativeChainComplexTower ((pullback i₂.hom).obj L) K_V' ⟶
      openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W :=
    complChainComplexTowerMap ((pullback i₂.hom).obj L)
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) K_V'.subset_succ hWV
  let qU : openRestrictionTower i₂ L K_V' ⟶ openRestrictionTower (i₁ ≫ i₂) L K_W :=
    complChainComplexTowerMap L
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) (fun n ↦ Set.image_mono (K_V'.subset_succ n)) hUW
  let eUW : openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W ⟶
      openRestrictionTower (i₁ ≫ i₂) L K_W :=
    complChainComplexTowerPairMap i₂ L
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) (fun n ↦ Set.image_mono (K_W.subset_succ n))
      hMaps
  have hSq1 : openRestrictionExcisionTowerMap i₂ hi₂.injective L K_V' ≫ qU = qV ≫ eUW :=
    (complChainComplexTowerMap_comp_complChainComplexTowerPairMap i₂ L
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) K_V'.subset_succ
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) (fun n ↦ Set.image_mono (K_V'.subset_succ n))
      hMaps _ hWV hUW).symm
  have hSq2 : openRestrictionExcisionTowerMap (i₁ ≫ i₂) (hi₂.comp hi₁).injective L K_W =
      relativeChainComplexTowerCoefficientMap K_W ((pullbackCompIso i₁.hom i₂.hom).hom.app L) ≫
        openRestrictionExcisionTowerMap i₁ hi₁.injective ((pullback i₂.hom).obj L) K_W ≫ eUW := by
    have hc : relativeChainComplexTowerCoefficientMap K_W
          ((pullbackCompIso i₁.hom i₂.hom).hom.app L) =
        complChainComplexTowerCoefficientMap K_W K_W.subset_succ
          ((pullbackCompIso i₁.hom i₂.hom).hom.app L) :=
      NatTrans.ext <| funext fun n ↦
        (relativeChainComplexTowerCoefficientMap_app K_W _ n.unop).trans
          (complChainComplexTowerCoefficientMap_app K_W K_W.subset_succ _ n.unop).symm
    rw [hc]
    exact complChainComplexTowerPairMap_comp i₁ i₂ L K_W.subset_succ
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) (fun n ↦ Set.image_mono (K_W.subset_succ n))
      _ hMaps _
  have hlim2 :
      locallyFiniteChainComplexOpenRestrictionExcision (i₁ ≫ i₂) (hi₂.comp hi₁).injective L K_W =
        locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) ≫
          locallyFiniteChainComplexOpenRestrictionExcision i₁ hi₁.injective
            ((pullback i₂.hom).obj L) K_W ≫ ComplexTower.limComplexMap eUW := by
    rw [locallyFiniteChainComplexOpenRestrictionExcision_def,
      locallyFiniteChainComplexOpenRestrictionExcision_def, hSq2,
      ComplexTower.limComplexMap_comp, ComplexTower.limComplexMap_comp,
      ← Category.assoc, ← locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom,
      Category.assoc, Category.assoc]
    rfl
  have hqV :
      (locallyFiniteChainComplexIsoLimComplex ((pullback i₂.hom).obj L) K_V').hom ≫
          ComplexTower.limComplexMap qV =
        locallyFiniteChainComplexToOpenRestrictionLim i₁ ((pullback i₂.hom).obj L) K_W :=
    locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap_compl
      ((pullback i₂.hom).obj L) K_V' (fun n ↦ Set.image_mono (K_W.subset_succ n))
      (fun n ↦ (K_W.isCompact n).image i₁.hom.continuous) hWV
  have hqU :
      locallyFiniteChainComplexToOpenRestrictionLim i₂ L K_V' ≫ ComplexTower.limComplexMap qU =
        locallyFiniteChainComplexToOpenRestrictionLim (i₁ ≫ i₂) L K_W :=
    locallyFiniteChainComplexToComplLim_comp_limComplexMap L
      (fun n ↦ Set.image_mono (K_W.subset_succ n))
      (fun n ↦ Set.image_mono (K_V'.subset_succ n))
      (fun n ↦ (K_W.isCompact n).image (i₁ ≫ i₂).hom.continuous)
      (fun n ↦ (K_V'.isCompact n).image i₂.hom.continuous) hUW
  suffices hmain :
      borelMooreHomologyOpenRestrictionOfExhaustion i₂ hi₂ L K_V' j ≫
          borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ ((pullback i₂.hom).obj L) K_W j ≫
            inv (borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j) =
        borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W j by
    rw [← hmain, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W
    (g := 𝟙 _) ?_).trans (Category.id_comp _)
  have hc : HomologicalComplex.homologyMap
      (locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L)) j =
      borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j := rfl
  rw [Category.id_comp, hlim2, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, hc, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc,
    ← Category.assoc (borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ _ K_W j),
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap,
    ← HomologicalComplex.homologyMap_comp, ← hqV,
    Category.assoc, ← ComplexTower.limComplexMap_comp, ← hSq1, ComplexTower.limComplexMap_comp,
    ← Category.assoc, HomologicalComplex.homologyMap_comp,
    ← locallyFiniteChainComplexOpenRestrictionExcision_def,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp, hqU]

/-- **Contravariant composition law for open restriction of Borel–Moore homology.** -/
@[reassoc]
theorem borelMooreHomologyOpenRestriction_comp
    {W V U : TopCat.{v}} [T2Space V] [T2Space U]
    [WeaklyLocallyCompactSpace W] [SigmaCompactSpace W]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (i₁ : W ⟶ V) (i₂ : V ⟶ U) (hi₁ : IsOpenEmbedding i₁.hom) (hi₂ : IsOpenEmbedding i₂.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (j : ℕ) :
    borelMooreHomologyOpenRestriction (i₁ ≫ i₂) (hi₂.comp hi₁) L j ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j =
      borelMooreHomologyOpenRestriction i₂ hi₂ L j ≫
        borelMooreHomologyOpenRestriction i₁ hi₁ ((pullback i₂.hom).obj L) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_comp i₁ i₂ hi₁ hi₂ L
    (CompactExhaustion.choice W) (CompactExhaustion.choice V) j

/-- **Base change between proper pushforward and open restriction**, for explicit compact
exhaustions. Given a Cartesian square with proper maps `f : U' ⟶ U`, `f' : V' ⟶ V` and open
embeddings `i : V ⟶ U`, `i' : V' ⟶ U'` satisfying `f' ≫ i = i' ≫ f` and
`f ⁻¹' Set.range i ⊆ Set.range i'`, pushing forward along `f` then restricting along `i` agrees with
restricting along `i'` then pushing forward along `f'`. -/
@[reassoc]
theorem borelMooreHomologyMap_comp_borelMooreHomologyOpenRestrictionOfExhaustion
    {V' V U' U : TopCat.{v}} [T2Space U'] [T2Space U]
    (i : V ⟶ U) (hi : IsOpenEmbedding i.hom) (i' : V' ⟶ U') (hi' : IsOpenEmbedding i'.hom)
    (f : U' ⟶ U) (hf : IsProperMap f.hom) (f' : V' ⟶ V) (hf' : IsProperMap f'.hom)
    (hw : f' ≫ i = i' ≫ f) (hcart : f ⁻¹' Set.range i ⊆ Set.range i')
    (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K_V : CompactExhaustion V) (K_V' : CompactExhaustion V') (j : ℕ) :
    borelMooreHomologyMap f hf L j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i hi L K_V j =
      borelMooreHomologyOpenRestrictionOfExhaustion i' hi' ((pullback f.hom).obj L) K_V' j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso f'.hom i.hom).app L).hom j ≫
        borelMooreHomologyMap f' hf' ((pullback i.hom).obj L) j := by
  let K_V'' : CompactExhaustion V' := K_V'.supPreimage hf' K_V
  rw [borelMooreHomologyOpenRestrictionOfExhaustion_eq i' hi' ((pullback f.hom).obj L) K_V' K_V'' j]
  have hf'_maps (n : ℕ) : Set.MapsTo f' (K_V'' n)ᶜ (K_V n)ᶜ :=
    fun x hx hfx ↦ hx (K_V'.preimage_subset_supPreimage hf' K_V n hfx)
  have hf_maps (n : ℕ) : Set.MapsTo f (i' '' K_V'' n)ᶜ (i '' K_V n)ᶜ := by
    rintro u' hu' ⟨v, hv, hfu'⟩
    obtain ⟨v', rfl⟩ : u' ∈ Set.range i' := hcart ⟨v, hfu'⟩
    have hfv' : f' v' = v := hi.injective <|
      (congrArg (fun g : V' ⟶ U ↦ g v') hw).trans hfu'.symm
    exact hu' ⟨v', K_V'.preimage_subset_supPreimage hf' K_V n (by simpa [hfv'] using hv), rfl⟩
  let α : (pullback i'.hom).obj ((pullback f.hom).obj L) ⟶
      (pullback f'.hom).obj ((pullback i.hom).obj L) :=
    (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
      eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
      (pullbackCompIso f'.hom i.hom).app L).hom
  let pV : relativeChainComplexTower ((pullback f'.hom).obj ((pullback i.hom).obj L)) K_V'' ⟶
      relativeChainComplexTower ((pullback i.hom).obj L) K_V :=
    complChainComplexTowerPairMap f' ((pullback i.hom).obj L)
      K_V''.subset_succ K_V.subset_succ hf'_maps
  let pU : openRestrictionTower i' ((pullback f.hom).obj L) K_V'' ⟶
      openRestrictionTower i L K_V :=
    complChainComplexTowerPairMap f L
      (fun n ↦ Set.image_mono (K_V''.subset_succ n))
      (fun n ↦ Set.image_mono (K_V.subset_succ n)) hf_maps
  have hpushV :
      locallyFiniteChainComplexMap f' hf' ((pullback i.hom).obj L) ≫
          (locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K_V).hom =
        (locallyFiniteChainComplexIsoLimComplex
            ((pullback f'.hom).obj ((pullback i.hom).obj L)) K_V'').hom ≫
          ComplexTower.limComplexMap pV :=
    locallyFiniteChainComplexMap_comp_isoLimComplex_hom f' hf' ((pullback i.hom).obj L)
      K_V'' K_V hf'_maps
  have hpushU :
      locallyFiniteChainComplexMap f hf L ≫
          locallyFiniteChainComplexToOpenRestrictionLim i L K_V =
        locallyFiniteChainComplexToOpenRestrictionLim i' ((pullback f.hom).obj L) K_V'' ≫
          ComplexTower.limComplexMap pU :=
    locallyFiniteChainComplexMap_comp_toComplLim f hf L
      (fun n ↦ Set.image_mono (K_V''.subset_succ n))
      (fun n ↦ (K_V''.isCompact n).image i'.hom.continuous)
      (fun n ↦ Set.image_mono (K_V.subset_succ n))
      (fun n ↦ (K_V.isCompact n).image i.hom.continuous) hf_maps
  have hsq :
      relativeChainComplexTowerCoefficientMap K_V'' α ≫ pV ≫
          openRestrictionExcisionTowerMap i hi.injective L K_V =
        openRestrictionExcisionTowerMap i' hi'.injective ((pullback f.hom).obj L) K_V'' ≫ pU := by
    have hc : relativeChainComplexTowerCoefficientMap K_V'' α =
        complChainComplexTowerCoefficientMap K_V'' K_V''.subset_succ α :=
      NatTrans.ext <| funext fun n ↦
        (relativeChainComplexTowerCoefficientMap_app K_V'' α n.unop).trans
          (complChainComplexTowerCoefficientMap_app K_V'' K_V''.subset_succ α n.unop).symm
    rw [hc]
    exact (complChainComplexTowerPairMap_naturality_square i' f f' i L hw.symm
      K_V''.subset_succ (fun n ↦ Set.image_mono (K_V''.subset_succ n))
      K_V.subset_succ (fun n ↦ Set.image_mono (K_V.subset_succ n))
      _ hf_maps hf'_maps _).symm
  symm
  refine eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K_V ?_
  have hchain :
      locallyFiniteChainComplexCoefficientMap α ≫
          locallyFiniteChainComplexMap f' hf' ((pullback i.hom).obj L) ≫
          locallyFiniteChainComplexOpenRestrictionExcision i hi.injective L K_V =
        locallyFiniteChainComplexOpenRestrictionExcision i' hi'.injective
            ((pullback f.hom).obj L) K_V'' ≫
          ComplexTower.limComplexMap pU := by
    rw [locallyFiniteChainComplexOpenRestrictionExcision_def,
      locallyFiniteChainComplexOpenRestrictionExcision_def,
      ← Category.assoc (locallyFiniteChainComplexMap f' hf' _), hpushV,
      Category.assoc, Category.assoc,
      ← Category.assoc (locallyFiniteChainComplexCoefficientMap α),
      locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom,
      Category.assoc, ← ComplexTower.limComplexMap_comp,
      ← ComplexTower.limComplexMap_comp, hsq, ComplexTower.limComplexMap_comp,
      ← Category.assoc]
  rw [Category.assoc, Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, hchain, HomologicalComplex.homologyMap_comp,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp, ← hpushU, HomologicalComplex.homologyMap_comp]

/-- **Base change between proper pushforward and open restriction.** -/
@[reassoc]
theorem borelMooreHomologyMap_comp_borelMooreHomologyOpenRestriction
    {V' V U' U : TopCat.{v}} [T2Space U'] [T2Space U]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    [WeaklyLocallyCompactSpace V'] [SigmaCompactSpace V']
    (i : V ⟶ U) (hi : IsOpenEmbedding i.hom) (i' : V' ⟶ U') (hi' : IsOpenEmbedding i'.hom)
    (f : U' ⟶ U) (hf : IsProperMap f.hom) (f' : V' ⟶ V) (hf' : IsProperMap f'.hom)
    (hw : f' ≫ i = i' ≫ f) (hcart : f ⁻¹' Set.range i ⊆ Set.range i')
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (j : ℕ) :
    borelMooreHomologyMap f hf L j ≫ borelMooreHomologyOpenRestriction i hi L j =
      borelMooreHomologyOpenRestriction i' hi' ((pullback f.hom).obj L) j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso f'.hom i.hom).app L).hom j ≫
        borelMooreHomologyMap f' hf' ((pullback i.hom).obj L) j :=
  borelMooreHomologyMap_comp_borelMooreHomologyOpenRestrictionOfExhaustion
    i hi i' hi' f hf f' hf' hw hcart L
    (CompactExhaustion.choice V) (CompactExhaustion.choice V') j

end Functoriality

end TauCeti.LocalCoefficientSystem
