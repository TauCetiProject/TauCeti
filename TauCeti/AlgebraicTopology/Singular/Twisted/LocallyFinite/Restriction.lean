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
`C(U, (i '' K n)ᶜ; L)` form a tower `openRestrictionTower i L K` with surjective shifts. Locally
finite chains of `U` map to `(openRestrictionTower i L K).limComplex`, while excision with local
coefficients (`TopPair.quasiIso_twistedChainComplexMap_of_open_cover`) and
`ComplexTower.quasiIso_limComplexMap` make the map from `locallyFiniteChainComplex ((pullback
i.hom).obj L)` to `(openRestrictionTower i L K).limComplex` a quasi-isomorphism. Inverting the
induced homology isomorphism defines `borelMooreHomologyOpenRestrictionOfExhaustion` and, for weakly
locally compact `σ`-compact `V`, `borelMooreHomologyOpenRestriction`, together with exhaustion
independence, coefficient naturality, compatibility with finite chains, identity, and contravariant
functoriality.

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

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] (P : TopPair.{v})
  {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R P.fst}

private lemma twistedChainComplexCoeff_twistedChainComplexCoefficientMap_f_apply
    (η : L₁ ⟶ L₂) {k : ℕ} (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map)
    (y : (P.twistedChainComplex L₁).X k) :
    (P.twistedChainComplexCoeff L₂ σ hσ).hom (((P.twistedChainComplexCoefficientMap η).f k).hom y) =
      (η.app (initialVertex σ)).hom ((P.twistedChainComplexCoeff L₁ σ hσ).hom y) := by
  obtain ⟨a, rfl⟩ := P.twistedChainComplexπ_f_surjective L₁ y
  have hπ := congrArg (fun g ↦ (g.f k).hom a)
    (P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hπ
  rw [hπ, P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply,
    P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply]
  have ha : (LocalCoefficientSystem.twistedChainComplexCoefficientMap η).f k ≫
      LocalCoefficientSystem.twistedChainComplexCoeff L₂ σ =
        LocalCoefficientSystem.twistedChainComplexCoeff L₁ σ ≫ η.app (initialVertex σ) := by
    refine LocalCoefficientSystem.twistedChainComplex_hom_ext L₁ fun τ ↦ ?_
    rw [LocalCoefficientSystem.ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc]
    by_cases h : τ = σ
    · subst h; simp
    · rw [LocalCoefficientSystem.ιTwistedChainComplex_twistedChainComplexCoeff_of_ne L₂ h,
        ← Category.assoc,
        LocalCoefficientSystem.ιTwistedChainComplex_twistedChainComplexCoeff_of_ne L₁ h,
        comp_zero, zero_comp]
  exact congrArg (fun g ↦ g.hom a) ha

/-- Taking relative classes of locally finite chains commutes with morphisms of local coefficient
systems. -/
@[reassoc]
theorem locallyFiniteChainComplexToRelative_naturality
    (hP : IsCompact (Set.range P.map)ᶜ) (η : L₁ ⟶ L₂) :
    P.locallyFiniteChainComplexToRelative L₁ hP ≫ P.twistedChainComplexCoefficientMap η =
      locallyFiniteChainComplexCoefficientMap η ≫ P.locallyFiniteChainComplexToRelative L₂ hP := by
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X L₁ k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    P.twistedChainComplex_ext_coeff L₂ fun σ hσ ↦ ?_
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexCoefficientMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  rw [P.twistedChainComplexCoeff_twistedChainComplexCoefficientMap_f_apply η σ hσ,
    P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply,
    P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply,
    coe_locallyFiniteChainsCoefficientMap_apply]

end TopPair

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section CoefficientTower

variable {X : TopCat.{v}} {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R X}
  (η : L₁ ⟶ L₂) (K : CompactExhaustion X)

/-- A morphism of local coefficient systems induces a morphism of relative chain towers. -/
def relativeChainComplexTowerCoefficientMap :
    relativeChainComplexTower L₁ K ⟶ relativeChainComplexTower L₂ K where
  app n := (TopPair.ofSubset (K n.unop)ᶜ).twistedChainComplexCoefficientMap η
  naturality {m n} f := by
    apply (TopPair.ofSubset (K m.unop)ᶜ).twistedChainComplex_hom_ext L₁
    exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc L₁ K f _).trans <|
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
        (TopPair.ofSubset (K n.unop)ᶜ) η).trans <|
        ((TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
          (TopPair.ofSubset (K m.unop)ᶜ) η _).trans
          (congrArg (_ ≫ ·) (twistedChainComplexπ_comp_relativeChainComplexTower_map L₂ K f))).symm

@[simp]
lemma relativeChainComplexTowerCoefficientMap_app (n : ℕ) :
    (relativeChainComplexTowerCoefficientMap η K).app (op n) =
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap η := (rfl)

/-- The identification of locally finite chains with the limit of the relative chain tower is
natural in the local coefficient system. -/
@[reassoc]
theorem locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom :
    locallyFiniteChainComplexCoefficientMap η ≫
        (locallyFiniteChainComplexIsoLimComplex L₂ K).hom =
      (locallyFiniteChainComplexIsoLimComplex L₁ K).hom ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerCoefficientMap η K) := by
  refine (relativeChainComplexTower L₂ K).limComplex_hom_ext fun n ↦
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·)
        (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ L₂ K n)).trans <|
        ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative_naturality _ η).symm.trans <|
          ((locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc L₁ K n _).symm.trans
            (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π
              (relativeChainComplexTowerCoefficientMap η K) n).symm)).trans
              (Category.assoc _ _ _).symm

end CoefficientTower

section AmbientTower

variable {V U : TopCat.{v}} (i : V ⟶ U)
  (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V)

/-- The tower of ambient relative twisted chain complexes `C(U, (i '' K n)ᶜ; L)` associated to a
map `i : V ⟶ U` and a compact exhaustion `K` of `V`. -/
@[expose]
def openRestrictionTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  Functor.ofOpSequence (X := fun n ↦ (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplex L)
    fun n ↦ TopTriple.twistedChainComplexTotalToOuter
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L

lemma openRestrictionTower_obj (n : ℕ) :
    (openRestrictionTower i L K).obj (op n) =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplex L := (rfl)

@[simp]
lemma openRestrictionTower_map_succ (n : ℕ) :
    (openRestrictionTower i L K).map (homOfLE (Nat.le_succ n)).op =
      TopTriple.twistedChainComplexTotalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

@[reassoc, simp]
lemma twistedChainComplexπ_comp_openRestrictionTower_map {m n : ℕ} (f : op m ⟶ op n) :
    (TopPair.ofSubset (i '' K m)ᶜ).twistedChainComplexπ L ≫
        (openRestrictionTower i L K).map f =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexπ L := by
  have hnm : n ≤ m := leOfHom f.unop
  induction m, hnm using Nat.le_induction with
  | base =>
    obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (_ ≫ ·) ((openRestrictionTower i L K).map_id _)).trans (Category.comp_id _)
  | succ m hnm ih =>
    obtain rfl : f = (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    refine (congrArg (_ ≫ ·) ((openRestrictionTower i L K).map_comp _ _)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) ?_).trans (ih _)
    exact (congrArg (_ ≫ ·) (openRestrictionTower_map_succ i L K m)).trans
      ((TopTriple.ofSubset _).twistedChainComplexπ_comp_totalToOuter L)

lemma openRestrictionTower_transition_surjective (k n : ℕ) :
    Function.Surjective (((openRestrictionTower i L K).term k).transition n) := by
  rw [ModuleTower.transition_def, Functor.comp_map, HomologicalComplex.eval_map]
  intro y
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexπ_f_surjective L y
  exact ⟨(((TopPair.ofSubset (i '' K (n + 1))ᶜ).twistedChainComplexπ L).f k).hom a,
    congrArg (fun g ↦ (g.f k).hom a)
      (twistedChainComplexπ_comp_openRestrictionTower_map i L K (homOfLE (Nat.le_succ n)).op)⟩

/-- The ambient relative tower of an open restriction has surjective shifts in every degree. -/
lemma openRestrictionTower_shift_surjective (k : ℕ) :
    Function.Surjective ((openRestrictionTower i L K).term k).shift :=
  ModuleTower.shift_surjective _ (openRestrictionTower_transition_surjective i L K k)

/-- The cone from locally finite chains on `U` to `openRestrictionTower i L K` whose legs take
relative classes modulo `(i '' K n)ᶜ`. -/
@[expose]
def locallyFiniteChainComplexOpenRestrictionCone : Cone (openRestrictionTower i L K) where
  pt := locallyFiniteChainComplex L
  π := NatTrans.ofOpSequence
    (fun n ↦ (TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
      ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map)
    fun n ↦ (Category.id_comp _).trans <|
      ((congrArg (_ ≫ ·) (openRestrictionTower_map_succ i L K n)).trans
        (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L
          ((K.isCompact (n + 1)).image i.hom.continuous).compl_range_ofSubset_compl_map
          ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map)).symm

/-- The canonical chain map from locally finite chains on `U` to the limit complex of
`openRestrictionTower i L K`. -/
def locallyFiniteChainComplexToOpenRestrictionLim :
    locallyFiniteChainComplex L ⟶ (openRestrictionTower i L K).limComplex :=
  (openRestrictionTower i L K).isLimitLimComplexCone.lift
    (locallyFiniteChainComplexOpenRestrictionCone i L K)

@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToOpenRestrictionLim_comp_π (n : ℕ) :
    locallyFiniteChainComplexToOpenRestrictionLim i L K ≫
        (openRestrictionTower i L K).limComplexπ n =
      (TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
        ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map :=
  (openRestrictionTower i L K).isLimitLimComplexCone.fac
    (locallyFiniteChainComplexOpenRestrictionCone i L K) (op n)

variable {K} in
/-- Enlarging the exhaustion `K` on `V` induces a quotient morphism of ambient relative towers. -/
def openRestrictionTowerMap {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    openRestrictionTower i L K' ⟶ openRestrictionTower i L K where
  app n := (TopTriple.ofSubset
    (Set.compl_subset_compl.2 (Set.image_mono (h n.unop)))).twistedChainComplexTotalToOuter L
  naturality {m n} f := by
    apply (TopPair.ofSubset (i '' K' m.unop)ᶜ).twistedChainComplex_hom_ext L
    exact (twistedChainComplexπ_comp_openRestrictionTower_map_assoc i L K' f _).trans <|
      (TopTriple.twistedChainComplexπ_comp_totalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (h n.unop)))) L).trans <|
        ((TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (h m.unop)))) L _).trans
          (twistedChainComplexπ_comp_openRestrictionTower_map i L K f)).symm

variable {K} in
@[simp]
lemma openRestrictionTowerMap_app {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (openRestrictionTowerMap i L h).app (op n) =
      (TopTriple.ofSubset
        (Set.compl_subset_compl.2 (Set.image_mono (h n)))).twistedChainComplexTotalToOuter L :=
  (rfl)

variable {K} in
@[reassoc]
lemma twistedChainComplexπ_comp_openRestrictionTowerMap_app {K' : CompactExhaustion V}
    (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (TopPair.ofSubset (i '' K' n)ᶜ).twistedChainComplexπ L ≫
        (openRestrictionTowerMap i L h).app (op n) =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexπ L :=
  (TopTriple.ofSubset _).twistedChainComplexπ_comp_totalToOuter L

variable {K} in
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToOpenRestrictionLim_comp_limComplexMap
    {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexToOpenRestrictionLim i L K' ≫
        ComplexTower.limComplexMap (openRestrictionTowerMap i L h) =
      locallyFiniteChainComplexToOpenRestrictionLim i L K := by
  refine (openRestrictionTower i L K).limComplex_hom_ext fun n ↦
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
        (locallyFiniteChainComplexToOpenRestrictionLim_comp_π_assoc i L K' n _).trans <|
          (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
            (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (h n)))) L _ _).trans
            (locallyFiniteChainComplexToOpenRestrictionLim_comp_π i L K n).symm

variable {L} in
/-- Morphism of ambient relative towers induced by a morphism of local coefficient systems. -/
def openRestrictionTowerCoefficientMap {L' : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L ⟶ L') :
    openRestrictionTower i L K ⟶ openRestrictionTower i L' K where
  app n := (TopPair.ofSubset (i '' K n.unop)ᶜ).twistedChainComplexCoefficientMap η
  naturality {m n} f := by
    apply (TopPair.ofSubset (i '' K m.unop)ᶜ).twistedChainComplex_hom_ext L
    exact (twistedChainComplexπ_comp_openRestrictionTower_map_assoc i L K f _).trans <|
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
        (TopPair.ofSubset (i '' K n.unop)ᶜ) η).trans <|
        ((TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
          (TopPair.ofSubset (i '' K m.unop)ᶜ) η _).trans
          (congrArg (_ ≫ ·) (twistedChainComplexπ_comp_openRestrictionTower_map i L' K f))).symm

variable {L} in
@[simp]
lemma openRestrictionTowerCoefficientMap_app {L' : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L ⟶ L') (n : ℕ) :
    (openRestrictionTowerCoefficientMap i K η).app (op n) =
      (TopPair.ofSubset (i '' K n)ᶜ).twistedChainComplexCoefficientMap η := (rfl)

variable {L} in
@[reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp_toOpenRestrictionLim
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') :
    locallyFiniteChainComplexCoefficientMap η ≫
        locallyFiniteChainComplexToOpenRestrictionLim i L' K =
      locallyFiniteChainComplexToOpenRestrictionLim i L K ≫
        ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap i K η) := by
  refine (openRestrictionTower i L' K).limComplex_hom_ext fun n ↦
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·)
        (locallyFiniteChainComplexToOpenRestrictionLim_comp_π i L' K n)).trans <|
        ((TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative_naturality
          _ η).symm.trans <|
          ((locallyFiniteChainComplexToOpenRestrictionLim_comp_π_assoc i L K n _).symm.trans
            (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π
              (openRestrictionTowerCoefficientMap i K η) n).symm)).trans
              (Category.assoc _ _ _).symm

end AmbientTower

section ExcisionTower

variable {V U : TopCat.{v}} (i : V ⟶ U)

/-- For an injective map `i : V ⟶ U` and a subset `S : Set V`, `i` carries `Sᶜ` into `(i '' S)ᶜ`,
giving a map of pairs `(V, Sᶜ) ⟶ (U, (i '' S)ᶜ)`. -/
@[expose]
def openRestrictionSetPairMap (hinj : Function.Injective i) (S : Set V) :
    TopPair.ofSubset Sᶜ ⟶ TopPair.ofSubset (i '' S)ᶜ :=
  have h : Set.MapsTo i Sᶜ (i '' S)ᶜ := fun _ hx hmem ↦ hx (hinj.mem_set_image.1 hmem)
  TopPair.ofHom i (TopCat.ofHom ⟨h.restrict, i.hom.continuous.restrict h⟩) rfl

@[simp]
lemma openRestrictionSetPairMap_fst (hinj : Function.Injective i) (S : Set V) :
    TopPair.Hom.fst (openRestrictionSetPairMap i hinj S) = i := (rfl)

/-- The tower morphism from the relative chain tower of `V` to `openRestrictionTower i L K`
induced by the pair maps `(V, (K n)ᶜ) ⟶ (U, (i '' K n)ᶜ)`. -/
def openRestrictionExcisionTowerMap (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) :
    relativeChainComplexTower ((pullback i.hom).obj L) K ⟶ openRestrictionTower i L K where
  app n := TopPair.twistedChainComplexMap (openRestrictionSetPairMap i hinj (K n.unop)) L
  naturality {m n} f := by
    apply (TopPair.ofSubset (K m.unop)ᶜ).twistedChainComplex_hom_ext ((pullback i.hom).obj L)
    exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc _ K f _).trans <|
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (openRestrictionSetPairMap i hinj (K n.unop)) L).trans <|
        ((congrArg (_ ≫ ·)
          (twistedChainComplexπ_comp_openRestrictionTower_map i L K f).symm).trans
          (Category.assoc _ _ _).symm).trans
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
            (openRestrictionSetPairMap i hinj (K m.unop)) L _).symm

@[simp]
lemma openRestrictionExcisionTowerMap_app (hinj : Function.Injective i)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) (n : ℕ) :
    (openRestrictionExcisionTowerMap i hinj L K).app (op n) =
      TopPair.twistedChainComplexMap (openRestrictionSetPairMap i hinj (K n)) L := (rfl)

/-- Enlarging `K` commutes with `openRestrictionExcisionTowerMap`. -/
@[reassoc]
lemma relativeChainComplexTowerMap_comp_openRestrictionExcisionTowerMap
    (hinj : Function.Injective i) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    relativeChainComplexTowerMap ((pullback i.hom).obj L) h ≫
        openRestrictionExcisionTowerMap i hinj L K =
      openRestrictionExcisionTowerMap i hinj L K' ≫ openRestrictionTowerMap i L h := by
  refine NatTrans.ext (funext fun n ↦ ?_)
  apply (TopPair.ofSubset (K' n.unop)ᶜ).twistedChainComplex_hom_ext ((pullback i.hom).obj L)
  exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc _ h n.unop _).trans <|
    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
      (openRestrictionSetPairMap i hinj (K n.unop)) L).trans <|
      ((congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_openRestrictionTowerMap_app i L h n.unop).symm).trans
        (Category.assoc _ _ _).symm).trans
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
          (openRestrictionSetPairMap i hinj (K' n.unop)) L _).symm

/-- `openRestrictionExcisionTowerMap` is natural in the local coefficient system. -/
@[reassoc]
lemma openRestrictionExcisionTowerMap_naturality (hinj : Function.Injective i)
    {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R U} (η : L₁ ⟶ L₂)
    (K : CompactExhaustion V) :
    openRestrictionExcisionTowerMap i hinj L₁ K ≫ openRestrictionTowerCoefficientMap i K η =
      relativeChainComplexTowerCoefficientMap ((pullback i.hom).map η) K ≫
        openRestrictionExcisionTowerMap i hinj L₂ K :=
  NatTrans.ext <| funext fun n ↦
    TopPair.twistedChainComplexMap_naturality (openRestrictionSetPairMap i hinj (K n.unop)) L₁ η

/-- **Excision at each stage of an open restriction.** -/
theorem quasiIso_openRestrictionExcisionTowerMap_app [T2Space U] (hi : IsOpenEmbedding i.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) (n : ℕ) :
    QuasiIso ((openRestrictionExcisionTowerMap i hi.injective L K).app (op n)) := by
  rw [openRestrictionExcisionTowerMap_app]
  refine TopPair.quasiIso_twistedChainComplexMap_of_open_cover
    (openRestrictionSetPairMap i hi.injective (K n)) L hi.isEmbedding
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

/-- The composite chain map from `locallyFiniteChainComplex ((pullback i.hom).obj L)` to the limit
complex of `openRestrictionTower i L K` is a quasi-isomorphism. -/
theorem quasiIso_locallyFiniteToOpenRestrictionLim [T2Space U] (hi : IsOpenEmbedding i.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V) :
    QuasiIso ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
      ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) := by
  have := quasiIso_limComplexMap_openRestrictionExcisionTowerMap i hi L K; infer_instance

/-- In every degree `j`, the homology map from `borelMooreHomology ((pullback i.hom).obj L) j` to
the homology of `(openRestrictionTower i L K).limComplex` is an isomorphism. -/
theorem isIso_homologyMap_locallyFiniteToOpenRestrictionLim [T2Space U]
    (hi : IsOpenEmbedding i.hom) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K : CompactExhaustion V) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
        ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) j) := by
  have := quasiIso_locallyFiniteToOpenRestrictionLim i hi L K; infer_instance

end ExcisionTower

section OpenRestriction

variable {V U : TopCat.{v}} [T2Space U] (i : V ⟶ U) (hi : IsOpenEmbedding i.hom)
  (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V)

/-- **Contravariant open restriction of Borel–Moore homology**, defined with respect to an explicit
compact exhaustion `K` of `V` (and independent of `K` by
`borelMooreHomologyOpenRestrictionOfExhaustion_eq`). -/
def borelMooreHomologyOpenRestrictionOfExhaustion (j : ℕ) :
    borelMooreHomology L j ⟶ borelMooreHomology ((pullback i.hom).obj L) j :=
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim i hi L K j
  HomologicalComplex.homologyMap (locallyFiniteChainComplexToOpenRestrictionLim i L K) j ≫
    inv (HomologicalComplex.homologyMap
      ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
        ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) j)

/-- Characterizing equation of `borelMooreHomologyOpenRestrictionOfExhaustion`: followed by the
excision isomorphism into the homology of `(openRestrictionTower i L K).limComplex`, it is the map
induced by `locallyFiniteChainComplexToOpenRestrictionLim`. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        HomologicalComplex.homologyMap
          ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
            ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) j =
      HomologicalComplex.homologyMap (locallyFiniteChainComplexToOpenRestrictionLim i L K) j := by
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim i hi L K j
  simp [borelMooreHomologyOpenRestrictionOfExhaustion]

/-- Uniqueness criterion for `borelMooreHomologyOpenRestrictionOfExhaustion`. -/
theorem eq_borelMooreHomologyOpenRestrictionOfExhaustion {M : ModuleCat.{max v w} R} {j : ℕ}
    {g : M ⟶ borelMooreHomology L j}
    {f : M ⟶ borelMooreHomology ((pullback i.hom).obj L) j}
    (hf : f ≫ HomologicalComplex.homologyMap
        ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
          ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) j =
      g ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToOpenRestrictionLim i L K) j) :
    f = g ≫ borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j := by
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim i hi L K j
  apply (cancel_mono (HomologicalComplex.homologyMap
    ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
      ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) j)).1
  rw [Category.assoc, borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap, hf]

/-- At each finite stage `n` of the exhaustion `K`, the relative class of the open-restricted
Borel–Moore homology class in `H_j(V, (K n)ᶜ; i^*L)` maps under excision to the relative class of
the ambient Borel–Moore homology class in `H_j(U, (i '' K n)ᶜ; L)`. -/
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp_toRelative (j n : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
            ((pullback i.hom).obj L) (K.isCompact n).compl_range_ofSubset_compl_map) j ≫
          TopPair.twistedHomologyMap (openRestrictionSetPairMap i hi.injective (K n)) L j =
      HomologicalComplex.homologyMap
        ((TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map) j := by
  have hchain :
      ((locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
          ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i hi.injective L K)) ≫
        (openRestrictionTower i L K).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
          ((pullback i.hom).obj L) (K.isCompact n).compl_range_ofSubset_compl_map ≫
        TopPair.twistedChainComplexMap (openRestrictionSetPairMap i hi.injective (K n)) L :=
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans
        (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc _ K n _)
  exact (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j).symm).trans <|
    (congrArg (fun φ ↦ _ ≫ HomologicalComplex.homologyMap φ j) hchain.symm).trans <|
      (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j)).trans <|
        (borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_assoc i hi L K j _).trans <|
          (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
            (congrArg (HomologicalComplex.homologyMap · j)
              (locallyFiniteChainComplexToOpenRestrictionLim_comp_π i L K n))

private lemma borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset
    {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K' j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j := by
  refine (eq_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K (g := 𝟙 _) ?_).trans
    (Category.id_comp _)
  rw [Category.id_comp, ← locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap
      ((pullback i.hom).obj L) h,
    Category.assoc, ← ComplexTower.limComplexMap_comp,
    relativeChainComplexTowerMap_comp_openRestrictionExcisionTowerMap,
    ComplexTower.limComplexMap_comp, ← Category.assoc, HomologicalComplex.homologyMap_comp,
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
  refine eq_borelMooreHomologyOpenRestrictionOfExhaustion i hi L' K ?_
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← Category.assoc (locallyFiniteChainComplexCoefficientMap _),
    locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom,
    Category.assoc, ← ComplexTower.limComplexMap_comp,
    ← openRestrictionExcisionTowerMap_naturality,
    ComplexTower.limComplexMap_comp, ← Category.assoc, HomologicalComplex.homologyMap_comp,
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
  refine (eq_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K
    (g := twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j) ?_).trans
      (Category.assoc _ _ _).symm
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  refine (openRestrictionTower i L K).limComplex_hom_ext fun n ↦
    ((Category.assoc _ _ _).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π
        (openRestrictionExcisionTowerMap i hi.injective L K) n))).trans <|
        (congrArg (_ ≫ ·)
          (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc _ K n _)).trans <|
          (TopPair.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative_assoc
            (TopPair.ofSubset (K n)ᶜ) ((pullback i.hom).obj L) _ _).trans
            (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
              (openRestrictionSetPairMap i hi.injective (K n)) L)).trans
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

@[simp]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V] (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      borelMooreHomologyOpenRestriction i hi L j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_eq i hi L K (CompactExhaustion.choice V) j

@[reassoc]
theorem borelMooreHomologyOpenRestriction_naturality
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') (j : ℕ) :
    borelMooreHomologyCoefficientMap η j ≫
        borelMooreHomologyOpenRestriction i hi L' j =
      borelMooreHomologyOpenRestriction i hi L j ≫
        borelMooreHomologyCoefficientMap ((pullback i.hom).map η) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_naturality i hi L (CompactExhaustion.choice V) η j

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
  refine (eq_borelMooreHomologyOpenRestrictionOfExhaustion (𝟙 U) hi L K
    (g := 𝟙 _) ?_).trans (Category.id_comp _)
  rw [Category.id_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  apply (openRestrictionTower (𝟙 U) L K).limComplex_hom_ext
  intro n
  have hsub : (K n)ᶜ ⊆ ((𝟙 U : U ⟶ U) '' K n)ᶜ := by simp
  have hrel :
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap ((pullbackIdIso U).inv.app L) ≫
          TopPair.twistedChainComplexMap (openRestrictionSetPairMap (𝟙 U) hi.injective (K n)) L =
        (TopTriple.ofSubset hsub).twistedChainComplexTotalToOuter L := by
    apply (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_hom_ext L
    refine (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
      (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso U).inv.app L) _).trans <|
      (congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (openRestrictionSetPairMap (𝟙 U) hi.injective (K n)) L)).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) ?_).trans <|
          (Category.id_comp _).trans
            ((TopTriple.ofSubset hsub).twistedChainComplexπ_comp_totalToOuter L).symm
    exact (congrArg (_ ≫ ·) (twistedChainComplexMap_id L)).trans <|
      (twistedChainComplexCoefficientMap_comp _ _).symm.trans <|
        (congrArg twistedChainComplexCoefficientMap ((pullbackIdIso U).inv_hom_id_app L)).trans
          (twistedChainComplexCoefficientMap_id L)
  exact (Category.assoc _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π
      (openRestrictionExcisionTowerMap (𝟙 U) hi.injective L K) n))).trans <|
      (congrArg (_ ≫ ·)
        (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc _ K n _)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ _) (TopPair.locallyFiniteChainComplexToRelative_naturality
            (TopPair.ofSubset (K n)ᶜ) _ ((pullbackIdIso U).inv.app L)).symm).trans <|
            (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hrel).trans <|
              (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
                (TopTriple.ofSubset hsub) L _ _).trans
                (locallyFiniteChainComplexToOpenRestrictionLim_comp_π (𝟙 U) L K n).symm

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
  let qV : relativeChainComplexTower ((pullback i₂.hom).obj L) K_V' ⟶
      openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W :=
    { app n := (TopTriple.ofSubset
        (Set.compl_subset_compl.2 (hWV n.unop))).twistedChainComplexTotalToOuter _
      naturality {m n} f := by
        apply (TopPair.ofSubset (K_V' m.unop)ᶜ).twistedChainComplex_hom_ext _
        exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc _ K_V' f _).trans <|
          (TopTriple.twistedChainComplexπ_comp_totalToOuter
            (TopTriple.ofSubset (Set.compl_subset_compl.2 (hWV n.unop))) _).trans <|
            ((TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc
              (TopTriple.ofSubset (Set.compl_subset_compl.2 (hWV m.unop))) _ _).trans
              (twistedChainComplexπ_comp_openRestrictionTower_map i₁ _ K_W f)).symm }
  let qU : openRestrictionTower i₂ L K_V' ⟶ openRestrictionTower (i₁ ≫ i₂) L K_W :=
    { app n := (TopTriple.ofSubset
        (Set.compl_subset_compl.2 (hUW n.unop))).twistedChainComplexTotalToOuter L
      naturality {m n} f := by
        apply (TopPair.ofSubset (i₂ '' K_V' m.unop)ᶜ).twistedChainComplex_hom_ext L
        exact (twistedChainComplexπ_comp_openRestrictionTower_map_assoc i₂ L K_V' f _).trans <|
          (TopTriple.twistedChainComplexπ_comp_totalToOuter
            (TopTriple.ofSubset (Set.compl_subset_compl.2 (hUW n.unop))) L).trans <|
            ((TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc
              (TopTriple.ofSubset (Set.compl_subset_compl.2 (hUW m.unop))) L _).trans
              (twistedChainComplexπ_comp_openRestrictionTower_map (i₁ ≫ i₂) L K_W f)).symm }
  have hMaps (n : ℕ) : Set.MapsTo i₂ (i₁ '' K_W n)ᶜ ((i₁ ≫ i₂) '' K_W n)ᶜ :=
    fun _ hy ⟨x, hx, hxy⟩ ↦ hy ⟨x, hx, hi₂.injective hxy⟩
  let pMap (n : ℕ) :
      TopPair.ofSubset (i₁ '' K_W n)ᶜ ⟶ TopPair.ofSubset ((i₁ ≫ i₂) '' K_W n)ᶜ :=
    TopPair.ofHom i₂ (TopCat.ofHom ⟨(hMaps n).restrict, i₂.hom.continuous.restrict (hMaps n)⟩) rfl
  let eUW : openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W ⟶
      openRestrictionTower (i₁ ≫ i₂) L K_W :=
    { app n := TopPair.twistedChainComplexMap (pMap n.unop) L
      naturality {m n} f := by
        apply (TopPair.ofSubset (i₁ '' K_W m.unop)ᶜ).twistedChainComplex_hom_ext _
        exact (twistedChainComplexπ_comp_openRestrictionTower_map_assoc i₁ _ K_W f _).trans <|
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (pMap n.unop) L).trans <|
            ((congrArg (_ ≫ ·)
              (twistedChainComplexπ_comp_openRestrictionTower_map (i₁ ≫ i₂) L K_W f).symm).trans
              (Category.assoc _ _ _).symm).trans
              (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
                (pMap m.unop) L _).symm }
  have hqV : (locallyFiniteChainComplexIsoLimComplex ((pullback i₂.hom).obj L) K_V').hom ≫
      ComplexTower.limComplexMap qV =
        locallyFiniteChainComplexToOpenRestrictionLim i₁ ((pullback i₂.hom).obj L) K_W :=
    (openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W).limComplex_hom_ext fun n ↦
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π qV n)).trans <|
          (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc _ K_V' n _).trans <|
            (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
              (TopTriple.ofSubset (Set.compl_subset_compl.2 (hWV n))) _ _ _).trans
              (locallyFiniteChainComplexToOpenRestrictionLim_comp_π i₁ _ K_W n).symm
  have hqU : locallyFiniteChainComplexToOpenRestrictionLim i₂ L K_V' ≫
      ComplexTower.limComplexMap qU =
        locallyFiniteChainComplexToOpenRestrictionLim (i₁ ≫ i₂) L K_W :=
    (openRestrictionTower (i₁ ≫ i₂) L K_W).limComplex_hom_ext fun n ↦
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π qU n)).trans <|
          (locallyFiniteChainComplexToOpenRestrictionLim_comp_π_assoc i₂ L K_V' n _).trans <|
            (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
              (TopTriple.ofSubset (Set.compl_subset_compl.2 (hUW n))) L _ _).trans
              (locallyFiniteChainComplexToOpenRestrictionLim_comp_π (i₁ ≫ i₂) L K_W n).symm
  have hSq1 : openRestrictionExcisionTowerMap i₂ hi₂.injective L K_V' ≫ qU = qV ≫ eUW :=
    NatTrans.ext <| funext fun n ↦
      (TopPair.ofSubset (K_V' n.unop)ᶜ).twistedChainComplex_hom_ext ((pullback i₂.hom).obj L) <|
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
          (openRestrictionSetPairMap i₂ hi₂.injective (K_V' n.unop)) L (qU.app n)).trans <|
          (congrArg (_ ≫ ·) (TopTriple.twistedChainComplexπ_comp_totalToOuter
            (TopTriple.ofSubset (Set.compl_subset_compl.2 (hUW n.unop))) L)).trans <|
            (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (pMap n.unop) L).symm.trans
              (TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc
                (TopTriple.ofSubset (Set.compl_subset_compl.2 (hWV n.unop))) _ (eUW.app n)).symm
  have hSq2 : openRestrictionExcisionTowerMap (i₁ ≫ i₂) (hi₂.comp hi₁).injective L K_W =
      relativeChainComplexTowerCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) K_W ≫
        openRestrictionExcisionTowerMap i₁ hi₁.injective ((pullback i₂.hom).obj L) K_W ≫ eUW :=
    NatTrans.ext <| funext fun n ↦
      let PKW := TopPair.ofSubset (K_W n.unop)ᶜ
      PKW.twistedChainComplex_hom_ext ((pullback (i₁ ≫ i₂).hom).obj L) <|
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
          (openRestrictionSetPairMap (i₁ ≫ i₂) (hi₂.comp hi₁).injective (K_W n.unop)) L).trans
          ((PKW.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
            ((pullbackCompIso i₁.hom i₂.hom).hom.app L) _).trans <|
            (congrArg (_ ≫ ·) <|
              (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
                (openRestrictionSetPairMap i₁ hi₁.injective (K_W n.unop))
                ((pullback i₂.hom).obj L) _).trans
                (congrArg (_ ≫ ·)
                  (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
                    (pMap n.unop) L))).trans <|
              (Category.assoc _ _ _).symm.trans <| (Category.assoc _ _ _).symm.trans
                (congrArg (· ≫ _) (twistedChainComplexMap_comp i₁ i₂ L).symm)).symm
  let cIso : borelMooreHomology ((pullback (i₁ ≫ i₂).hom).obj L) j ≅
      borelMooreHomology ((pullback i₁.hom).obj ((pullback i₂.hom).obj L)) j :=
    { hom := borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j
      inv := borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).inv.app L) j
      hom_inv_id := by
        rw [← borelMooreHomologyCoefficientMap_comp, Iso.hom_inv_id_app]
        exact borelMooreHomologyCoefficientMap_id j
      inv_hom_id := by
        rw [← borelMooreHomologyCoefficientMap_comp, Iso.inv_hom_id_app]
        exact borelMooreHomologyCoefficientMap_id j }
  suffices hmain :
      borelMooreHomologyOpenRestrictionOfExhaustion i₂ hi₂ L K_V' j ≫
          borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ ((pullback i₂.hom).obj L) K_W j ≫
            cIso.inv =
        borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W j by
    rw [← hmain, Category.assoc, Category.assoc, cIso.inv_hom_id, Category.comp_id]
  refine (eq_borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W
    (g := 𝟙 _) ?_).trans (Category.id_comp _)
  have hlim2 :
      (locallyFiniteChainComplexIsoLimComplex ((pullback (i₁ ≫ i₂).hom).obj L) K_W).hom ≫
          ComplexTower.limComplexMap
            (openRestrictionExcisionTowerMap (i₁ ≫ i₂) (hi₂.comp hi₁).injective L K_W) =
        locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) ≫
          ((locallyFiniteChainComplexIsoLimComplex
              ((pullback i₁.hom).obj ((pullback i₂.hom).obj L)) K_W).hom ≫
            ComplexTower.limComplexMap
              (openRestrictionExcisionTowerMap i₁ hi₁.injective ((pullback i₂.hom).obj L) K_W)) ≫
            ComplexTower.limComplexMap eUW := by
    rw [hSq2, ComplexTower.limComplexMap_comp, ComplexTower.limComplexMap_comp]
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom
        ((pullbackCompIso i₁.hom i₂.hom).hom.app L) K_W).symm).trans
        (by simp only [Functor.comp_obj, Category.assoc])
  have hc : HomologicalComplex.homologyMap
      (locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L)) j =
        cIso.hom := rfl
  rw [Category.id_comp, hlim2, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, hc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc cIso,
    ← Category.assoc (borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ _ K_W j),
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap,
    ← HomologicalComplex.homologyMap_comp, ← hqV, Category.assoc,
    ← ComplexTower.limComplexMap_comp, ← hSq1, ComplexTower.limComplexMap_comp,
    ← Category.assoc, HomologicalComplex.homologyMap_comp,
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

end Functoriality

end TauCeti.LocalCoefficientSystem
