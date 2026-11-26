/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower.Basic

/-!
# Naturality and comparison for relative twisted chain complex towers

This file develops functoriality and exhaustion comparison for the relative twisted chain complex
towers of `TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower.Basic`.

* Naturality of `TopPair.locallyFiniteChainComplexToRelative` in morphisms of local coefficient
  systems
  (`TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative`)
  and proper maps of pairs
  (`TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative`).
* Constructing morphisms of relative chain complex towers from levelwise maps intertwining a fixed
  ambient chain map (`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerHomMk`), with
  applications to morphisms of local coefficient systems
  (`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerCoefficientMap`,
  `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplex_naturality`) and pointwise
  enlargement of monotone sequences of subsets
  (`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerMap`,
  `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplex_comp_limComplexMap`).
* Chain-level comparison of nested compact exhaustions `K n ⊆ K' n`
  (`TauCeti.LocalCoefficientSystem.isIso_limComplexMap_relativeChainComplexTowerMap`).

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite SimplexCategory Topology

open scoped Simplicial

universe u v w

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section ToRelativeNaturality

/-- Taking relative classes of locally finite chains commutes with morphisms of local coefficient
systems. -/
@[reassoc]
theorem locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative
    (P : TopPair.{v}) {L K : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L ⟶ K)
    (hP : IsCompact (Set.range P.map)ᶜ) :
    locallyFiniteChainComplexCoefficientMap η ≫ P.locallyFiniteChainComplexToRelative K hP =
      P.locallyFiniteChainComplexToRelative L hP ≫ P.twistedChainComplexCoefficientMap η := by
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X L k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    P.twistedChainComplex_ext_coeff K fun σ hσ ↦ ?_
  have hL : (P.twistedChainComplexCoefficientMap η).f k ≫ P.twistedChainComplexCoeff K σ hσ =
      P.twistedChainComplexCoeff L σ hσ ≫ η.app (initialVertex σ) :=
    P.twistedChainComplexCoefficientMap_f_comp_twistedChainComplexCoeff η σ hσ
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexCoefficientMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply K hP _ σ hσ,
    ModuleCat.hom_ofHom, coe_locallyFiniteChainsCoefficientMap_apply]
  have h1 := congrArg (fun f ↦ f.hom (((P.locallyFiniteChainComplexToRelative L hP).f k).hom
    ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c))) hL
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply L hP c σ hσ]

/-- Pushing a locally finite chain forward along a proper map of pairs commutes with taking
relative classes modulo subspaces with compact complements. -/
@[reassoc]
theorem locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative
    {P Q : TopPair.{v}} (g : P ⟶ Q)
    (hg : IsProperMap (Hom.fst g).hom) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (hP : IsCompact (Set.range P.map)ᶜ) (hQ : IsCompact (Set.range Q.map)ᶜ) :
    locallyFiniteChainComplexMap (Hom.fst g) hg L ≫ Q.locallyFiniteChainComplexToRelative L hQ =
      P.locallyFiniteChainComplexToRelative
          ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj L) hP ≫
        TopPair.twistedChainComplexMap g L := by
  -- Check equality degreewise and coefficientwise on each simplex `ρ` of `Q` not contained in
  -- `Set.range Q.map`: represent the relative class of `c` on `P` as the projection of its finite
  -- restriction to simplices meeting `(Set.range P.map)ᶜ`, push that finite sum forward along `g`,
  -- and verify that every simplex `σ` contributing to the `ρ`-coefficient lies in that finite set.
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X _ k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    Q.twistedChainComplex_ext_coeff L fun ρ hρ ↦ ?_
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexMap_f, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  rw [Q.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply L hQ _ ρ hρ,
    coe_locallyFiniteChainsMap_apply]
  have hright : ((P.locallyFiniteChainComplexToRelative _ hP).f k).hom
      ((eqToHom (locallyFiniteChainComplex_X _ k).symm).hom c) =
      ((P.twistedChainComplexπ _).f k).hom
        (∑ σ ∈ ((mem_locallyFiniteChains.1 c.property).finite_setOf_inter_nonempty hP).toFinset,
          (ιTwistedChainComplex _ k σ).hom (c.val σ)) := by
    rw [P.locallyFiniteChainComplexToRelative_f_apply, P.locallyFiniteChainsToRelative_eq]
  rw [hright, TopPair.twistedChainComplexMap_f_twistedChainComplexπ_f_apply,
    Q.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L ρ hρ, map_sum, map_sum]
  simp only [twistedChainComplexMap_f_ι_apply]
  refine finsum_eq_sum_of_support_subset _ fun σ hσ ↦ ?_
  rw [Function.mem_support] at hσ
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  refine ⟨fun hc0 ↦ hσ ?_, ?_⟩
  · -- `((pullback (Hom.fst g).hom).obj L).obj (initialVertex σ)` is definitionally
    -- `L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))`, since `pullback`
    -- composes with `FundamentalGroupoid.map` and `initialVertex` commutes with `toSSet.map`.
    have hc0' :
        (c.val σ :
          L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))) = 0 := hc0
    trans (L.twistedChainComplexCoeff ρ).hom
        ((L.ιTwistedChainComplex k _).hom
          (0 : L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))))
    · exact congrArg (fun x ↦ (L.twistedChainComplexCoeff ρ).hom
        ((L.ιTwistedChainComplex k _).hom x)) hc0'
    · simp
  rw [Set.inter_compl_nonempty_iff]
  intro hsub
  have hEq : (TopCat.toSSet.map (Hom.fst g)).app _ σ = ρ := by
    by_contra hne
    exact hσ (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne _)
  apply hρ
  rw [← hEq, TopCat.simplexMap_app, ContinuousMap.coe_comp, Set.range_comp]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := hsub hx
  exact ⟨Hom.snd g y, by
    have hw := congrArg (fun f : P.snd ⟶ Q.fst ↦ f y) (Hom.w g)
    simpa [hy] using hw⟩

/-- Pushing a locally finite chain forward along a proper map `f : P.fst ⟶ Q.fst` underlying a
map of pairs `g : P ⟶ Q` (`hf : Hom.fst g = f`) commutes with taking relative classes modulo
subspaces with compact complements. -/
@[reassoc]
theorem locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative_ofFstEq
    {P Q : TopPair.{v}} (g : P ⟶ Q) {f : P.fst ⟶ Q.fst} (hf : Hom.fst g = f)
    (hf' : IsProperMap f.hom) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (hP : IsCompact (Set.range P.map)ᶜ) (hQ : IsCompact (Set.range Q.map)ᶜ) :
    locallyFiniteChainComplexMap f hf' L ≫ Q.locallyFiniteChainComplexToRelative L hQ =
      P.locallyFiniteChainComplexToRelative ((LocalCoefficientSystem.pullback f.hom).obj L) hP ≫
        TopPair.twistedChainComplexMapOfFstEq g hf L := by
  subst hf
  rw [TopPair.twistedChainComplexMapOfFstEq_rfl]
  exact locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative g hf' L hP hQ

end ToRelativeNaturality

end TopPair

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section TowerHom

/-- Construct a morphism of relative chain complex towers from levelwise chain maps intertwining a
fixed ambient chain map through the quotient projections. -/
def relativeChainComplexTowerHomMk {X Y : TopCat.{v}}
    {L₁ : LocalCoefficientSystem.{u, v, max v w} R X}
    {L₂ : LocalCoefficientSystem.{u, v, max v w} R Y}
    {S₁ : ℕ → Set X} {S₂ : ℕ → Set Y}
    (hS₁ : ∀ n, S₁ n ⊆ S₁ (n + 1)) (hS₂ : ∀ n, S₂ n ⊆ S₂ (n + 1))
    (ambient : L₁.twistedChainComplex ⟶ L₂.twistedChainComplex)
    (level : ∀ n, (TopPair.ofSubset (S₁ n)ᶜ).twistedChainComplex L₁ ⟶
      (TopPair.ofSubset (S₂ n)ᶜ).twistedChainComplex L₂)
    (hcomm : ∀ n, (TopPair.ofSubset (S₁ n)ᶜ).twistedChainComplexπ L₁ ≫ level n =
      ambient ≫ (TopPair.ofSubset (S₂ n)ᶜ).twistedChainComplexπ L₂) :
    relativeChainComplexTower L₁ S₁ hS₁ ⟶ relativeChainComplexTower L₂ S₂ hS₂ :=
  NatTrans.ofOpSequence level fun n ↦ by
    apply (TopPair.ofSubset (S₁ (n + 1))ᶜ).twistedChainComplex_hom_ext L₁
    -- `(TopPair.ofSubset _).fst` is only definitionally `X`/`Y`, so explicit `trans` steps let
    -- elaboration align the ambient types.
    trans (TopPair.ofSubset (S₁ n)ᶜ).twistedChainComplexπ L₁ ≫ level n
    · exact twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc L₁ S₁ hS₁
        (homOfLE (Nat.le_succ n)).op _
    trans ambient ≫ (TopPair.ofSubset (S₂ n)ᶜ).twistedChainComplexπ L₂
    · exact hcomm n
    trans ambient ≫ (TopPair.ofSubset (S₂ (n + 1))ᶜ).twistedChainComplexπ L₂ ≫
        (relativeChainComplexTower L₂ S₂ hS₂).map (homOfLE (Nat.le_succ n)).op
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTower_map L₂ S₂ hS₂
          (homOfLE (Nat.le_succ n)).op).symm
    · exact (congrArg (· ≫ _) (hcomm (n + 1)).symm).trans (Category.assoc _ _ _)

/-- The components of `relativeChainComplexTowerHomMk` are the given levelwise chain maps. -/
@[simp]
lemma relativeChainComplexTowerHomMk_app {X Y : TopCat.{v}}
    {L₁ : LocalCoefficientSystem.{u, v, max v w} R X}
    {L₂ : LocalCoefficientSystem.{u, v, max v w} R Y}
    {S₁ : ℕ → Set X} {S₂ : ℕ → Set Y}
    (hS₁ : ∀ n, S₁ n ⊆ S₁ (n + 1)) (hS₂ : ∀ n, S₂ n ⊆ S₂ (n + 1))
    (ambient : L₁.twistedChainComplex ⟶ L₂.twistedChainComplex)
    (level : ∀ n, (TopPair.ofSubset (S₁ n)ᶜ).twistedChainComplex L₁ ⟶
      (TopPair.ofSubset (S₂ n)ᶜ).twistedChainComplex L₂)
    (hcomm : ∀ n, (TopPair.ofSubset (S₁ n)ᶜ).twistedChainComplexπ L₁ ≫ level n =
      ambient ≫ (TopPair.ofSubset (S₂ n)ᶜ).twistedChainComplexπ L₂) (n : ℕ) :
    (relativeChainComplexTowerHomMk hS₁ hS₂ ambient level hcomm).app (op n) = level n :=
  NatTrans.ofOpSequence_app _ _ (op n)

end TowerHom

section CoefficientNaturality

variable {X : TopCat.{v}}

/-- A morphism of local coefficient systems induces a morphism of relative chain complex towers. -/
def relativeChainComplexTowerCoefficientMap
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (S : ℕ → Set X)
    (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTower L S hS ⟶ relativeChainComplexTower K S hS :=
  relativeChainComplexTowerHomMk hS hS (twistedChainComplexCoefficientMap η)
    (fun n ↦ (TopPair.ofSubset (S n)ᶜ).twistedChainComplexCoefficientMap η)
    fun n ↦ TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
      (TopPair.ofSubset (S n)ᶜ) η

/-- On each level, `relativeChainComplexTowerCoefficientMap` is the relative coefficient map. -/
@[simp]
lemma relativeChainComplexTowerCoefficientMap_app
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (S : ℕ → Set X)
    (hS : ∀ n, S n ⊆ S (n + 1)) (n : ℕ) :
    (relativeChainComplexTowerCoefficientMap η S hS).app (op n) =
      (TopPair.ofSubset (S n)ᶜ).twistedChainComplexCoefficientMap η :=
  relativeChainComplexTowerHomMk_app hS hS _ _ _ n

/-- The identity morphism of local coefficient systems induces the identity morphism of relative
chain complex towers. -/
@[simp]
lemma relativeChainComplexTowerCoefficientMap_id
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (S : ℕ → Set X)
    (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTowerCoefficientMap (𝟙 L) S hS =
      𝟙 (relativeChainComplexTower L S hS) := by
  apply NatTrans.ext
  funext ⟨n⟩
  exact TopPair.twistedChainComplexCoefficientMap_id (TopPair.ofSubset (S n)ᶜ) L

/-- Composition of morphisms of local coefficient systems induces the composite of the morphisms
of relative chain complex towers. -/
@[simp, reassoc]
lemma relativeChainComplexTowerCoefficientMap_comp
    {L K J : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (θ : K ⟶ J)
    (S : ℕ → Set X) (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTowerCoefficientMap (η ≫ θ) S hS =
      relativeChainComplexTowerCoefficientMap η S hS ≫
        relativeChainComplexTowerCoefficientMap θ S hS := by
  apply NatTrans.ext
  funext ⟨n⟩
  exact TopPair.twistedChainComplexCoefficientMap_comp (TopPair.ofSubset (S n)ᶜ) η θ

/-- Congruence of relative classes of locally finite chains along an equality of subsets. -/
lemma locallyFiniteChainComplexToRelative_congr
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {S T : Set X} (h : S = T)
    (hS : IsCompact (Set.range (TopPair.ofSubset S).map)ᶜ)
    (hT : IsCompact (Set.range (TopPair.ofSubset T).map)ᶜ) :
    (TopPair.ofSubset S).locallyFiniteChainComplexToRelative L hS ≫
        eqToHom (congrArg (fun A : Set X ↦ (TopPair.ofSubset A).twistedChainComplex L) h) =
      (TopPair.ofSubset T).locallyFiniteChainComplexToRelative L hT := by
  subst h
  simp

/-- The map from locally finite chains to the limit complex of a tower of compact subsets is
natural in morphisms of local coefficient systems. -/
@[reassoc]
theorem locallyFiniteChainComplexToLimComplex_naturality
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K)
    (S : ℕ → Set X) (hS : ∀ n, S n ⊆ S (n + 1)) (hSc : ∀ n, IsCompact (S n)) :
    locallyFiniteChainComplexCoefficientMap η ≫
        locallyFiniteChainComplexToLimComplex K S hS hSc =
      locallyFiniteChainComplexToLimComplex L S hS hSc ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerCoefficientMap η S hS) := by
  apply (relativeChainComplexTower K S hS).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ_assoc]
  rw [relativeChainComplexTowerCoefficientMap_app]
  exact TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative
    (TopPair.ofSubset (S n)ᶜ) η (hSc n).compl_range_ofSubset_compl_map

end CoefficientNaturality

section MonotoneSequence

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)
  {S S' S'' : ℕ → Set X}

/-- Pointwise enlargement of a monotone sequence of subsets induces a map of relative chain towers
in the opposite direction, by taking further relative quotients. -/
def relativeChainComplexTowerMap (hS : ∀ n, S n ⊆ S (n + 1)) (hS' : ∀ n, S' n ⊆ S' (n + 1))
    (h : ∀ n, S n ⊆ S' n) :
    relativeChainComplexTower L S' hS' ⟶ relativeChainComplexTower L S hS :=
  relativeChainComplexTowerHomMk hS' hS (𝟙 L.twistedChainComplex)
    (fun n ↦
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexTotalToOuter L)
    fun n ↦ ((TopTriple.ofSubset
      (Set.compl_subset_compl.2 (h n))).twistedChainComplexπ_comp_totalToOuter L).trans
      (Category.id_comp _).symm

/-- A component of the comparison is the quotient map for the corresponding triple. -/
@[simp]
theorem relativeChainComplexTowerMap_app (hS : ∀ n, S n ⊆ S (n + 1))
    (hS' : ∀ n, S' n ⊆ S' (n + 1)) (h : ∀ n, S n ⊆ S' n) (n : ℕ) :
    (relativeChainComplexTowerMap L hS hS' h).app (op n) =
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexTotalToOuter L :=
  relativeChainComplexTowerHomMk_app hS' hS _ _ _ n

/-- The comparison preserves the classes of finite ambient chains. -/
@[reassoc]
theorem twistedChainComplexπ_comp_relativeChainComplexTowerMap_app (hS : ∀ n, S n ⊆ S (n + 1))
    (hS' : ∀ n, S' n ⊆ S' (n + 1)) (h : ∀ n, S n ⊆ S' n) (n : ℕ) :
    (TopPair.ofSubset (S' n)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L hS hS' h).app (op n) =
      (TopPair.ofSubset (S n)ᶜ).twistedChainComplexπ L :=
  (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexπ_comp_totalToOuter L

/-- Enlarging a monotone sequence by the reflexive inclusion induces the identity map of relative
chain towers. -/
@[simp]
theorem relativeChainComplexTowerMap_refl (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTowerMap L hS hS (fun n ↦ Set.Subset.refl (S n)) = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply (TopPair.ofSubset (S n.unop)ᶜ).twistedChainComplex_hom_ext L
  exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L hS hS _ n.unop).trans
    (Category.comp_id _).symm

/-- Taking further relative quotients is transitive. -/
@[reassoc (attr := simp)]
theorem relativeChainComplexTowerMap_comp (hS : ∀ n, S n ⊆ S (n + 1))
    (hS' : ∀ n, S' n ⊆ S' (n + 1)) (hS'' : ∀ n, S'' n ⊆ S'' (n + 1))
    (h : ∀ n, S n ⊆ S' n) (h' : ∀ n, S' n ⊆ S'' n) :
    relativeChainComplexTowerMap L hS' hS'' h' ≫ relativeChainComplexTowerMap L hS hS' h =
      relativeChainComplexTowerMap L hS hS'' (fun n ↦ (h n).trans (h' n)) := by
  apply NatTrans.ext
  funext n
  apply (TopPair.ofSubset (S'' n.unop)ᶜ).twistedChainComplex_hom_ext L
  exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc L hS' hS'' h' n.unop
      _).trans <|
    (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L hS hS' h n.unop).trans
      (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L hS hS''
        (fun n ↦ (h n).trans (h' n)) n.unop).symm

/-- Relative classes of locally finite chains commute with enlargement of the compact sets. -/
@[reassoc]
theorem locallyFiniteChainComplexToRelative_comp_relativeChainComplexTowerMap_app
    (hS : ∀ n, S n ⊆ S (n + 1)) (hS' : ∀ n, S' n ⊆ S' (n + 1))
    (hSc : ∀ n, IsCompact (S n)) (hS'c : ∀ n, IsCompact (S' n))
    (h : ∀ n, S n ⊆ S' n) (n : ℕ) :
    (TopPair.ofSubset (S' n)ᶜ).locallyFiniteChainComplexToRelative L
        (hS'c n).compl_range_ofSubset_compl_map ≫
        (relativeChainComplexTowerMap L hS hS' h).app (op n) =
      (TopPair.ofSubset (S n)ᶜ).locallyFiniteChainComplexToRelative L
        (hSc n).compl_range_ofSubset_compl_map :=
  TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
    (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))) L
    (hS'c n).compl_range_ofSubset_compl_map (hSc n).compl_range_ofSubset_compl_map

/-- The map from locally finite chains to the limit complex of a tower of compact subsets commutes
with pointwise enlargement of the subsets. -/
@[reassoc]
theorem locallyFiniteChainComplexToLimComplex_comp_limComplexMap
    (hS : ∀ n, S n ⊆ S (n + 1)) (hS' : ∀ n, S' n ⊆ S' (n + 1))
    (hSc : ∀ n, IsCompact (S n)) (hS'c : ∀ n, IsCompact (S' n)) (h : ∀ n, S n ⊆ S' n) :
    locallyFiniteChainComplexToLimComplex L S' hS' hS'c ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L hS hS' h) =
      locallyFiniteChainComplexToLimComplex L S hS hSc := by
  apply (relativeChainComplexTower L S hS).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc, ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ_assoc,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ]
  exact locallyFiniteChainComplexToRelative_comp_relativeChainComplexTowerMap_app
    L hS hS' hSc hS'c h n

end MonotoneSequence

section ExhaustionComparison

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)
  {K K' : CompactExhaustion X}

/-- The map of limit complexes is the identity on locally finite chains, through the canonical
identifications with the limits of the two relative towers. -/
@[reassoc (attr := simp)]
theorem locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap
    (h : ∀ n, K n ⊆ K' n) :
    (locallyFiniteChainComplexIsoLimComplex L K').hom ≫
        ComplexTower.limComplexMap
          (relativeChainComplexTowerMap L K.subset_succ K'.subset_succ h) =
      (locallyFiniteChainComplexIsoLimComplex L K).hom := by
  rw [locallyFiniteChainComplexIsoLimComplex_hom_eq, locallyFiniteChainComplexIsoLimComplex_hom_eq]
  exact locallyFiniteChainComplexToLimComplex_comp_limComplexMap L K.subset_succ K'.subset_succ
    K.isCompact K'.isCompact h

/-- The comparison on limit complexes preserves the inverse identification with locally finite
chains. -/
@[reassoc (attr := simp)]
theorem limComplexMap_relativeChainComplexTowerMap_comp_locallyFiniteChainComplexIsoLimComplex_inv
    (h : ∀ n, K n ⊆ K' n) :
    ComplexTower.limComplexMap (relativeChainComplexTowerMap L K.subset_succ K'.subset_succ h) ≫
        (locallyFiniteChainComplexIsoLimComplex L K).inv =
      (locallyFiniteChainComplexIsoLimComplex L K').inv := by
  apply (cancel_epi (locallyFiniteChainComplexIsoLimComplex L K').hom).1
  simp

/-- Although the relative quotient maps need not be quasi-isomorphisms individually, their
map on limit complexes is an isomorphism. -/
instance isIso_limComplexMap_relativeChainComplexTowerMap (h : ∀ n, K n ⊆ K' n) :
    IsIso (ComplexTower.limComplexMap
      (relativeChainComplexTowerMap L K.subset_succ K'.subset_succ h)) := by
  have heq : ComplexTower.limComplexMap
        (relativeChainComplexTowerMap L K.subset_succ K'.subset_succ h) =
      (locallyFiniteChainComplexIsoLimComplex L K').inv ≫
        (locallyFiniteChainComplexIsoLimComplex L K).hom := by
    rw [← locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap L h,
      Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

end ExhaustionComparison

end TauCeti.LocalCoefficientSystem
