/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.ExhaustionComparison
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Functoriality
import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.QuasiIso
import TauCeti.AlgebraicTopology.Singular.Twisted.Excision

/-!
# Open restriction in Borel–Moore homology

Borel–Moore homology is contravariant for open embeddings `j : V ⟶ X`. Unlike finite singular
chains, locally finite chains cannot be restricted directly to an open subset at the chain level,
because simplices in `X` may cross the boundary of `V`. Instead, given a compact exhaustion `K` of
`V` whose images in `X` have closure inside `Set.range j` (automatic when `X` is Hausdorff), the
restriction on homology is defined by the excision zigzag

`C^lf(X; L) ⟶ limₙ C(X, X \ j '' Kₙ; L) ⟵ limₙ C(V, V \ Kₙ; j⁎L) ≅ C^lf(V; j⁎L)`.

The left chain map sends a locally finite chain on `X` to the compatible family of its relative
classes modulo `X \ j '' Kₙ`
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToAmbientTower`).
The right chain map is induced on inverse limits by the levelwise excision maps of pairs
`(V, V \ Kₙ) ⟶ (X, X \ j '' Kₙ)`
(`TauCeti.LocalCoefficientSystem.excisionRelativeChainComplexTowerMap`).
Because `Set.range j` is open and contains the closure of `j '' Kₙ`, each level map is a
quasi-isomorphism (`TopPair.quasiIso_twistedChainComplexMap_of_open_cover`). Both towers have
degreewise surjective transitions, so
`TauCeti.ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso` upgrades this to a
quasi-isomorphism of limit complexes. Inverting the resulting isomorphism on homology yields
`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion`.

Any two compact exhaustions `K` and `K'` of `V` are dominated by their pointwise union
`K.union K'`, and enlarging the compact sets induces compatible triple-quotient maps on both
towers, so the restriction morphism is independent of the chosen exhaustion
(`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_eq`). When `X` is Hausdorff
and `V` is weakly locally compact and sigma-compact, choosing `CompactExhaustion.choice V` defines
the canonical open restriction `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`.

Functoriality, naturality in local coefficients, and a degree-zero discrete verification are in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Functoriality`. Proper-map
base change is in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.BaseChange`.

## Main declarations

* `CompactExhaustion.union` and `CompactExhaustion.unionImage`: pointwise union of compact
  exhaustions and enlargement along a continuous open map.
* `TopPair.locallyFiniteChainComplexCoefficientMap_comp_toRelative` and
  `TopPair.locallyFiniteChainComplexMap_comp_toRelative`: naturality of relative classes of
  locally finite chains under coefficient morphisms and proper maps of pairs.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyCoefficientIso`: change of local coefficients
  along an isomorphism of local coefficient systems.
* `TauCeti.LocalCoefficientSystem.ambientRelativeChainComplexTower`: the tower
  `n ↦ C(X, X \ j '' Kₙ; L)` for a compact exhaustion `K` of `V`.
* `TauCeti.LocalCoefficientSystem.excisionRelativeChainComplexTowerMap` and
  `TauCeti.LocalCoefficientSystem.quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap`: the
  levelwise excision map of towers and its quasi-isomorphism on limit complexes.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_eq`: open restriction via
  an explicit compact exhaustion and its exhaustion independence.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`: canonical open restriction for an
  open embedding into a Hausdorff space from a weakly locally compact sigma-compact space.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite SimplexCategory Topology
open scoped Simplicial

universe u v w

namespace CompactExhaustion

/-- The pointwise union of two compact exhaustions is a compact exhaustion. -/
def union {X : Type*} [TopologicalSpace X] (K K' : CompactExhaustion X) :
    CompactExhaustion X where
  toFun n := K n ∪ K' n
  isCompact' n := (K.isCompact n).union (K'.isCompact n)
  subset_interior_succ' n :=
    Set.union_subset
      ((K.subset_interior_succ n).trans (interior_mono Set.subset_union_left))
      ((K'.subset_interior_succ n).trans (interior_mono Set.subset_union_right))
  iUnion_eq' := by
    rw [Set.iUnion_union_distrib, K.iUnion_eq, Set.univ_union]

@[simp]
lemma union_apply {X : Type*} [TopologicalSpace X] (K K' : CompactExhaustion X) (n : ℕ) :
    (K.union K') n = K n ∪ K' n := (rfl)

/-- Enlarging a compact exhaustion of `V` by the images of a compact exhaustion of `W` along a
continuous open map `i : W → V` yields a compact exhaustion of `V`. -/
def unionImage {W V : Type*} [TopologicalSpace W] [TopologicalSpace V]
    (K : CompactExhaustion V) (L : CompactExhaustion W) {i : W → V}
    (hi_cont : Continuous i) (hi_open : IsOpenMap i) : CompactExhaustion V where
  toFun n := K n ∪ i '' L n
  isCompact' n := (K.isCompact n).union ((L.isCompact n).image hi_cont)
  subset_interior_succ' n := by
    refine Set.union_subset
      ((K.subset_interior_succ n).trans (interior_mono Set.subset_union_left)) ?_
    calc i '' L n ⊆ i '' interior (L (n + 1)) := Set.image_mono (L.subset_interior_succ n)
      _ ⊆ interior (i '' L (n + 1)) :=
          interior_maximal (Set.image_mono interior_subset) (hi_open _ isOpen_interior)
      _ ⊆ interior (K (n + 1) ∪ i '' L (n + 1)) := interior_mono Set.subset_union_right
  iUnion_eq' := by
    rw [Set.iUnion_union_distrib, K.iUnion_eq, Set.univ_union]

@[simp]
lemma unionImage_apply {W V : Type*} [TopologicalSpace W] [TopologicalSpace V]
    (K : CompactExhaustion V) (L : CompactExhaustion W) {i : W → V}
    (hi_cont : Continuous i) (hi_open : IsOpenMap i) (n : ℕ) :
    (K.unionImage L hi_cont hi_open) n = K n ∪ i '' L n := (rfl)

end CompactExhaustion

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section ToRelativeNaturality

/-- Taking relative classes of locally finite chains commutes with morphisms of local coefficient
systems. -/
@[reassoc]
theorem locallyFiniteChainComplexCoefficientMap_comp_toRelative (P : TopPair.{v})
    {L K : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L ⟶ K)
    (hP : IsCompact (Set.range P.map)ᶜ) :
    locallyFiniteChainComplexCoefficientMap η ≫ P.locallyFiniteChainComplexToRelative K hP =
      P.locallyFiniteChainComplexToRelative L hP ≫ P.twistedChainComplexCoefficientMap η := by
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X L k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    P.twistedChainComplex_ext_coeff K fun σ hσ ↦ ?_
  have hL : (P.twistedChainComplexCoefficientMap η).f k ≫ P.twistedChainComplexCoeff K σ hσ =
      P.twistedChainComplexCoeff L σ hσ ≫ η.app (initialVertex σ) := by
    apply (cancel_epi ((P.twistedChainComplexπ L).f k)).1
    have hπ := congrArg (fun φ ↦ φ.f k)
      (P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)
    simp only [HomologicalComplex.comp_f] at hπ
    rw [← Category.assoc, hπ, Category.assoc, P.twistedChainComplexπ_f_twistedChainComplexCoeff,
      P.twistedChainComplexπ_f_twistedChainComplexCoeff_assoc]
    refine LocalCoefficientSystem.twistedChainComplex_hom_ext L fun τ ↦ ?_
    rw [ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc]
    by_cases hτ : τ = σ
    · subst hτ
      simp [ιTwistedChainComplex_twistedChainComplexCoeff]
    · simp [ιTwistedChainComplex_twistedChainComplexCoeff_of_ne, hτ]
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
theorem locallyFiniteChainComplexMap_comp_toRelative {P Q : TopPair.{v}} (g : P ⟶ Q)
    (hg : IsProperMap (Hom.fst g).hom) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (hP : IsCompact (Set.range P.map)ᶜ) (hQ : IsCompact (Set.range Q.map)ᶜ) :
    locallyFiniteChainComplexMap (Hom.fst g) hg L ≫ Q.locallyFiniteChainComplexToRelative L hQ =
      P.locallyFiniteChainComplexToRelative
          ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj L) hP ≫
        TopPair.twistedChainComplexMap g L := by
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
        (∑ σ ∈ ((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).toFinset,
          (ιTwistedChainComplex _ k σ).hom (c.1 σ)) := by
    refine P.twistedChainComplex_ext_coeff _ fun τ hτ ↦ ?_
    rw [P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply _ hP c τ hτ,
      P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply _ τ hτ,
      twistedChainComplexCoeff_sum_ιTwistedChainComplex_apply]
    intro hnot
    by_contra hc0
    exact hnot (((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).mem_toFinset.2
      ⟨hc0, Set.inter_compl_nonempty_iff.2 hτ⟩)
  rw [hright, TopPair.twistedChainComplexMap_f_twistedChainComplexπ_f_apply,
    Q.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L ρ hρ, map_sum, map_sum]
  simp only [twistedChainComplexMap_f_ι_apply]
  refine finsum_eq_sum_of_support_subset _ fun σ hσ ↦ ?_
  rw [Function.mem_support] at hσ
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  refine ⟨fun hc0 ↦ hσ ?_, ?_⟩
  · have hc0' :
        (c.1 σ :
          L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))) = 0 := hc0
    exact (congrArg
      (fun x : L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ)) ↦
        (L.twistedChainComplexCoeff ρ).hom ((L.ιTwistedChainComplex k _).hom x))
      hc0').trans <|
      (congrArg (L.twistedChainComplexCoeff ρ).hom
        (map_zero (L.ιTwistedChainComplex k _).hom)).trans
        (map_zero (L.twistedChainComplexCoeff ρ).hom)
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

end ToRelativeNaturality

end TopPair

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Helpers

/-- Change of local coefficients on Borel–Moore homology along an isomorphism of systems. -/
def borelMooreHomologyCoefficientIso {X : TopCat.{v}}
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (e : L ≅ K) (k : ℕ) :
    borelMooreHomology L k ≅ borelMooreHomology K k where
  hom := borelMooreHomologyCoefficientMap e.hom k
  inv := borelMooreHomologyCoefficientMap e.inv k
  hom_inv_id := by
    rw [← borelMooreHomologyCoefficientMap_comp, e.hom_inv_id,
      borelMooreHomologyCoefficientMap_id]
  inv_hom_id := by
    rw [← borelMooreHomologyCoefficientMap_comp, e.inv_hom_id,
      borelMooreHomologyCoefficientMap_id]

@[simp]
lemma borelMooreHomologyCoefficientIso_hom {X : TopCat.{v}}
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (e : L ≅ K) (k : ℕ) :
    (borelMooreHomologyCoefficientIso e k).hom = borelMooreHomologyCoefficientMap e.hom k :=
  (rfl)

@[simp]
lemma borelMooreHomologyCoefficientIso_inv {X : TopCat.{v}}
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (e : L ≅ K) (k : ℕ) :
    (borelMooreHomologyCoefficientIso e k).inv = borelMooreHomologyCoefficientMap e.inv k :=
  (rfl)

/-- In a Hausdorff codomain, the closure of the image of every stage of a compact exhaustion lies
in the range of the continuous map. -/
lemma closure_image_compactExhaustion_subset_range {V X : TopCat.{v}} [T2Space X]
    (j : V ⟶ X) (K : CompactExhaustion V) (n : ℕ) :
    closure (j.hom '' K n) ⊆ Set.range j.hom := by
  rw [((K.isCompact n).image j.hom.continuous).isClosed.closure_eq]
  exact Set.image_subset_range _ _


end Helpers

section AmbientTower

variable {V X : TopCat.{v}} (j : V ⟶ X)
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion V)

/-- The tower of ambient relative twisted chain complexes `C(X, X \ j '' Kₙ; L)` associated to a
map `j : V ⟶ X` and a compact exhaustion `K` of `V`. -/
-- Exposed so that the terms of the tower are definitionally the relative chain complexes, matching
-- `relativeChainComplexTower`.
@[expose]
def ambientRelativeChainComplexTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  Functor.ofOpSequence (X := fun n ↦ (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplex L)
    fun n ↦ TopTriple.twistedChainComplexTotalToOuter
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L

/-- The `n`-th term of the ambient relative tower is `C(X, X \ j '' Kₙ; L)`. -/
lemma ambientRelativeChainComplexTower_obj (n : ℕ) :
    (ambientRelativeChainComplexTower j L K).obj (op n) =
      (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplex L :=
  (rfl)

/-- The transitions of the ambient relative tower are the triple quotient maps. -/
@[simp]
lemma ambientRelativeChainComplexTower_map_succ (n : ℕ) :
    (ambientRelativeChainComplexTower j L K).map (homOfLE (Nat.le_succ n)).op =
      TopTriple.twistedChainComplexTotalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Every transition in the ambient relative tower is induced by the identity of ambient chains. -/
@[reassoc, simp]
lemma twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map {m n : ℕ}
    (f : op m ⟶ op n) :
    (TopPair.ofSubset (j.hom '' K m)ᶜ).twistedChainComplexπ L ≫
        (ambientRelativeChainComplexTower j L K).map f =
      (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ L := by
  have hnm : n ≤ m := leOfHom f.unop
  induction m, hnm using Nat.le_induction with
  | base =>
    obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (_ ≫ ·) ((ambientRelativeChainComplexTower j L K).map_id _)).trans
      (Category.comp_id _)
  | succ m hnm ih =>
    obtain rfl : f = (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    refine (congrArg (_ ≫ ·) ((ambientRelativeChainComplexTower j L K).map_comp _ _)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) ?_).trans (ih _)
    exact (congrArg (_ ≫ ·) (ambientRelativeChainComplexTower_map_succ j L K m)).trans
      ((TopTriple.ofSubset _).twistedChainComplexπ_comp_totalToOuter L)

/-- The transitions of the ambient relative tower are surjective in every degree. -/
lemma ambientRelativeChainComplexTower_transition_surjective (i n : ℕ) :
    Function.Surjective (((ambientRelativeChainComplexTower j L K).term i).transition n) := by
  rw [ModuleTower.transition_def, Functor.comp_map, HomologicalComplex.eval_map]
  intro y
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ_f_surjective L y
  exact ⟨(((TopPair.ofSubset (j.hom '' K (n + 1))ᶜ).twistedChainComplexπ L).f i).hom a,
    congrArg (fun g ↦ (g.f i).hom a)
      (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map j L K
        (homOfLE (Nat.le_succ n)).op)⟩

/-- The ambient relative tower has surjective shift maps in every degree. -/
lemma ambientRelativeChainComplexTower_shift_surjective (i : ℕ) :
    Function.Surjective ((ambientRelativeChainComplexTower j L K).term i).shift :=
  ModuleTower.shift_surjective _ (ambientRelativeChainComplexTower_transition_surjective j L K i)

private def locallyFiniteChainComplexToAmbientTowerCone :
    Cone (ambientRelativeChainComplexTower j L K) where
  pt := locallyFiniteChainComplex L
  π := NatTrans.ofOpSequence
    (fun n ↦ (TopPair.ofSubset (j.hom '' K n)ᶜ).locallyFiniteChainComplexToRelative L
      ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map)
    fun n ↦ (Category.id_comp _).trans <|
      ((congrArg (_ ≫ ·) (ambientRelativeChainComplexTower_map_succ j L K n)).trans
        (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (K.subset_succ n)))) L
          ((K.isCompact (n + 1)).image j.hom.continuous).compl_range_ofSubset_compl_map
          ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map)).symm

/-- The chain map `C^lf(X; L) ⟶ limₙ C(X, X \ j '' Kₙ; L)` forming the left leg of the open
restriction zigzag. -/
def locallyFiniteChainComplexToAmbientTower :
    locallyFiniteChainComplex L ⟶ (ambientRelativeChainComplexTower j L K).limComplex :=
  (ambientRelativeChainComplexTower j L K).isLimitLimComplexCone.lift
    (locallyFiniteChainComplexToAmbientTowerCone j L K)

/-- The `n`-th projection of `locallyFiniteChainComplexToAmbientTower` takes relative classes modulo
`X \ j '' Kₙ`. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToAmbientTower_comp_limComplexπ (n : ℕ) :
    locallyFiniteChainComplexToAmbientTower j L K ≫
        (ambientRelativeChainComplexTower j L K).limComplexπ n =
      (TopPair.ofSubset (j.hom '' K n)ᶜ).locallyFiniteChainComplexToRelative L
        ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map :=
  (ambientRelativeChainComplexTower j L K).isLimitLimComplexCone.fac
    (locallyFiniteChainComplexToAmbientTowerCone j L K) (op n)

end AmbientTower

section ExcisionTower

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion V)

/-- For an injective continuous map `j : V ⟶ X` and a subset `S ⊆ V`, the induced map of pairs
`(V, V \ S) ⟶ (X, X \ j '' S)`. -/
-- Exposed so that `TopPair.Hom.fst (injectivePairMap hj S)` is definitionally `j`, avoiding
-- transport of `pullback j.hom` in relative chain complex types.
@[expose]
def injectivePairMap (hj : Function.Injective j.hom) (S : Set V) :
    TopPair.ofSubset Sᶜ ⟶ TopPair.ofSubset (j.hom '' S)ᶜ :=
  TopPair.ofHom j
    (TopCat.ofHom ⟨Set.MapsTo.restrict j.hom Sᶜ (j.hom '' S)ᶜ
        (fun _ hx ⟨_, hy, hxy⟩ ↦ hx (hj hxy ▸ hy)),
      j.hom.continuous.restrict _⟩)

/-- The levelwise excision map of towers
`C(V, V \ Kₙ; j⁎L) ⟶ C(X, X \ j '' Kₙ; L)`. -/
def excisionRelativeChainComplexTowerMap (hj : Function.Injective j.hom) :
    relativeChainComplexTower ((pullback j.hom).obj L) K ⟶
      ambientRelativeChainComplexTower j L K where
  app n := TopPair.twistedChainComplexMap (injectivePairMap hj (K n.unop)) L
  naturality {m n} f := by
    apply (TopPair.ofSubset (K m.unop)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc _ K f _).trans <|
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (injectivePairMap hj (K n.unop)) L).trans <|
        ((TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
          (injectivePairMap hj (K m.unop)) L _).trans <|
          congrArg (_ ≫ ·)
            (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map j L K f)).symm

@[simp]
lemma excisionRelativeChainComplexTowerMap_app (hj : Function.Injective j.hom) (n : ℕ) :
    (excisionRelativeChainComplexTowerMap L K hj).app (op n) =
      TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L :=
  (rfl)

/-- For an open embedding `j : V ⟶ X` and a subset `S ⊆ V` whose image has closure inside
`Set.range j`, the pair map `(V, V \ S) ⟶ (X, X \ j '' S)` induces a quasi-isomorphism of
relative twisted chains. -/
theorem quasiIso_twistedChainComplexMap_injectivePairMap (hj : IsOpenEmbedding j.hom)
    {S : Set V} (hS : closure (j.hom '' S) ⊆ Set.range j.hom) :
    QuasiIso (TopPair.twistedChainComplexMap (injectivePairMap hj.injective S) L) := by
  refine TopPair.quasiIso_twistedChainComplexMap_of_open_cover
    (injectivePairMap hj.injective S) L hj.isEmbedding
    (fun x hx ↦ by
      rw [TopPair.range_ofSubset_map] at hx ⊢
      exact fun hxS ↦ hx ⟨x, hxS, rfl⟩)
    (fun b : Bool ↦ bif b then Set.range j.hom else (closure (j.hom '' S))ᶜ)
    (fun b ↦ by cases b <;> [exact isClosed_closure.isOpen_compl; exact hj.isOpen_range])
    ?_ (fun b ↦ by
      cases b
      · exact Or.inl ((Set.compl_subset_compl.2 subset_closure).trans
          (TopPair.range_ofSubset_map (B := (j.hom '' S)ᶜ)).ge)
      · exact Or.inr Set.Subset.rfl)
  rw [← Set.union_eq_iUnion, Set.union_comm]
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_cases hx : x ∈ closure (j.hom '' S)
  · exact Or.inr (hS hx)
  · exact Or.inl hx

/-- If `j : V ⟶ X` is an open embedding and `closure (j '' Kₙ) ⊆ Set.range j` for every `n`,
then the excision map of towers induces a quasi-isomorphism on limit complexes. -/
theorem quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap (hj : IsOpenEmbedding j.hom)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) :
    QuasiIso (ComplexTower.limComplexMap
      (excisionRelativeChainComplexTowerMap L K hj.injective)) :=
  ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso _
    (relativeChainComplexTower_shift_surjective ((pullback j.hom).obj L) K)
    (ambientRelativeChainComplexTower_shift_surjective j L K)
    fun n ↦ quasiIso_twistedChainComplexMap_injectivePairMap L hj (hK n)

/-- The right leg `C^lf(V; j⁎L) ⟶ limₙ C(X, X \ j '' Kₙ; L)` of the open restriction
zigzag. -/
def openEmbeddingRightLeg (hj : Function.Injective j.hom) :
    locallyFiniteChainComplex ((pullback j.hom).obj L) ⟶
      (ambientRelativeChainComplexTower j L K).limComplex :=
  (locallyFiniteChainComplexIsoLimComplex ((pullback j.hom).obj L) K).hom ≫
    ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L K hj)

/-- The `n`-th projection of the right leg takes relative classes on `V` and pushes them along
the excision map of pairs. -/
@[reassoc (attr := simp)]
lemma openEmbeddingRightLeg_comp_limComplexπ (hj : Function.Injective j.hom) (n : ℕ) :
    openEmbeddingRightLeg L K hj ≫ (ambientRelativeChainComplexTower j L K).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map ≫
        TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L :=
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
      locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc _ K n _

/-- For an open embedding `j : V ⟶ X` and a compact exhaustion `K` with
`closure (j '' Kₙ) ⊆ Set.range j`, the right leg of the open restriction zigzag is a
quasi-isomorphism. -/
theorem quasiIso_openEmbeddingRightLeg (hj : IsOpenEmbedding j.hom)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) :
    QuasiIso (openEmbeddingRightLeg L K hj.injective) := by
  have := quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap L K hj hK
  exact quasiIso_comp _ _

end ExcisionTower

section ExhaustionRestriction

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- **Open restriction in Borel–Moore homology via a compact exhaustion.** Given an open embedding
`j : V ⟶ X` and a compact exhaustion `K` of `V` with `closure (j '' Kₙ) ⊆ Set.range j`, this
morphism `Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)` is obtained by inverting the excision quasi-isomorphism
on the right leg of the zigzag. By `borelMooreHomologyRestrictOfExhaustion_eq`, it does not depend
on the choice of `K`. -/
def borelMooreHomologyRestrictOfExhaustion (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k :=
  have := quasiIso_openEmbeddingRightLeg L K hj hK
  HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j L K) k ≫
    inv (HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k)

/-- The defining zigzag equation for `borelMooreHomologyRestrictOfExhaustion`. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyRestrictOfExhaustion_comp_rightLeg (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K hK k ≫
        HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k =
      HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j L K) k := by
  have := quasiIso_openEmbeddingRightLeg L K hj hK
  simp [borelMooreHomologyRestrictOfExhaustion]

/-- Uniqueness characterization of `borelMooreHomologyRestrictOfExhaustion`: a morphism
`Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)` equals open restriction if and only if postcomposing with the
right leg yields the left leg. -/
theorem eq_borelMooreHomologyRestrictOfExhaustion_iff (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ)
    (φ : borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k) :
    φ = borelMooreHomologyRestrictOfExhaustion L hj K hK k ↔
      φ ≫ HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k =
        HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j L K) k := by
  have := quasiIso_openEmbeddingRightLeg L K hj hK
  constructor
  · rintro rfl
    exact borelMooreHomologyRestrictOfExhaustion_comp_rightLeg L hj K hK k
  · intro h
    rw [← cancel_mono (HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k),
      h, borelMooreHomologyRestrictOfExhaustion_comp_rightLeg]

/-- Enlargement of the compact exhaustion induces a map of ambient relative towers in the opposite
direction. -/
def ambientRelativeChainComplexTowerMap {K K' : CompactExhaustion V}
    (h : ∀ n, K n ⊆ K' n) :
    ambientRelativeChainComplexTower j L K' ⟶ ambientRelativeChainComplexTower j L K where
  app n := (TopTriple.ofSubset
    (Set.compl_subset_compl.2 (Set.image_mono (h n.unop)))).twistedChainComplexTotalToOuter L
  naturality {m n} f := by
    apply (TopPair.ofSubset (j.hom '' K' m.unop)ᶜ).twistedChainComplex_hom_ext L
    have hsubN : (j.hom '' K' n.unop)ᶜ ⊆ (j.hom '' K n.unop)ᶜ :=
      Set.compl_subset_compl.2 (Set.image_mono (h n.unop))
    have hsubM : (j.hom '' K' m.unop)ᶜ ⊆ (j.hom '' K m.unop)ᶜ :=
      Set.compl_subset_compl.2 (Set.image_mono (h m.unop))
    exact (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map_assoc j L K' f _).trans
      <| ((TopTriple.ofSubset hsubN).twistedChainComplexπ_comp_totalToOuter L).trans <|
        (((TopTriple.ofSubset hsubM).twistedChainComplexπ_comp_totalToOuter_assoc L _).trans
          (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map j L K f)).symm

/-- On each level, `ambientRelativeChainComplexTowerMap` is the triple quotient map induced by
enlarging the compact exhaustion. -/
@[simp]
lemma ambientRelativeChainComplexTowerMap_app {K K' : CompactExhaustion V}
    (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (ambientRelativeChainComplexTowerMap (j := j) L h).app (op n) =
      (TopTriple.ofSubset
        (Set.compl_subset_compl.2 (Set.image_mono (h n)))).twistedChainComplexTotalToOuter L :=
  (rfl)

/-- The canonical map from locally finite chains on `X` to the ambient tower is compatible with
enlargement of the compact exhaustion of `V`. -/
@[reassoc]
lemma locallyFiniteChainComplexToAmbientTower_comp_towerMap
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexToAmbientTower j L K' ≫
        ComplexTower.limComplexMap (ambientRelativeChainComplexTowerMap (j := j) L h) =
      locallyFiniteChainComplexToAmbientTower j L K := by
  apply (ambientRelativeChainComplexTower j L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
      (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ_assoc j L K' n _).trans <|
        (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (Set.image_mono (h n)))) L _ _).trans
          (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ j L K n).symm

/-- The excision right leg is compatible with enlargement of the compact exhaustion of `V`. -/
@[reassoc]
lemma openEmbeddingRightLeg_comp_towerMap (hj : Function.Injective j.hom)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    openEmbeddingRightLeg L K' hj ≫
        ComplexTower.limComplexMap (ambientRelativeChainComplexTowerMap (j := j) L h) =
      openEmbeddingRightLeg L K hj := by
  have hsq : excisionRelativeChainComplexTowerMap L K' hj ≫
        ambientRelativeChainComplexTowerMap (j := j) L h =
      relativeChainComplexTowerMap ((pullback j.hom).obj L) h ≫
        excisionRelativeChainComplexTowerMap L K hj := by
    apply NatTrans.ext
    funext ⟨n⟩
    apply (TopPair.ofSubset (K' n)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hj (K' n)) L _).trans <|
      (congrArg (_ ≫ ·) ((TopTriple.ofSubset
        (Set.compl_subset_compl.2 (Set.image_mono (h n)))).twistedChainComplexπ_comp_totalToOuter
        L)).trans <|
        ((twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc
            ((pullback j.hom).obj L) h n _).trans
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
            (injectivePairMap hj (K n)) L)).symm
  calc openEmbeddingRightLeg L K' hj ≫
        ComplexTower.limComplexMap (ambientRelativeChainComplexTowerMap (j := j) L h)
    _ = (locallyFiniteChainComplexIsoLimComplex ((pullback j.hom).obj L) K').hom ≫
          ComplexTower.limComplexMap (relativeChainComplexTowerMap ((pullback j.hom).obj L) h) ≫
            ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L K hj) := by
        rw [openEmbeddingRightLeg, Category.assoc, ← ComplexTower.limComplexMap_comp, hsq,
          ComplexTower.limComplexMap_comp]
    _ = openEmbeddingRightLeg L K hj := by
        rw [← Category.assoc, locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap,
          openEmbeddingRightLeg]

private lemma borelMooreHomologyRestrictOfExhaustion_eq_of_subset (hj : IsOpenEmbedding j.hom)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hK' : ∀ n, closure (j.hom '' K' n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K' hK' k =
      borelMooreHomologyRestrictOfExhaustion L hj K hK k := by
  rw [eq_borelMooreHomologyRestrictOfExhaustion_iff]
  calc borelMooreHomologyRestrictOfExhaustion L hj K' hK' k ≫
        HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k
    _ = (borelMooreHomologyRestrictOfExhaustion L hj K' hK' k ≫
          HomologicalComplex.homologyMap (openEmbeddingRightLeg L K' hj.injective) k) ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap (ambientRelativeChainComplexTowerMap (j := j) L h)) k := by
        rw [← openEmbeddingRightLeg_comp_towerMap L hj.injective h,
          HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j L K) k := by
        rw [borelMooreHomologyRestrictOfExhaustion_comp_rightLeg,
          ← HomologicalComplex.homologyMap_comp,
          locallyFiniteChainComplexToAmbientTower_comp_towerMap]

/-- **Exhaustion independence of open restriction.** Any two compact exhaustions of `V` whose
images in `X` have closure in `Set.range j` define the same open restriction map on Borel–Moore
homology. -/
theorem borelMooreHomologyRestrictOfExhaustion_eq (hj : IsOpenEmbedding j.hom)
    (K K' : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hK' : ∀ n, closure (j.hom '' K' n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K hK k =
      borelMooreHomologyRestrictOfExhaustion L hj K' hK' k := by
  let K'' := K.union K'
  have hK'' (n : ℕ) : closure (j.hom '' K'' n) ⊆ Set.range j.hom := by
    simp only [K'', CompactExhaustion.union_apply, Set.image_union, closure_union]
    exact Set.union_subset (hK n) (hK' n)
  exact (borelMooreHomologyRestrictOfExhaustion_eq_of_subset L hj
      (fun _ ↦ Set.subset_union_left) hK hK'' k).symm.trans
    (borelMooreHomologyRestrictOfExhaustion_eq_of_subset L hj
      (fun _ ↦ Set.subset_union_right) hK' hK'' k)


end ExhaustionRestriction

section CanonicalRestriction

variable {V X : TopCat.{v}}

/-- **Canonical open restriction in Borel–Moore homology.** For an open embedding `j : V ⟶ X`
into a Hausdorff space `X` from a weakly locally compact, sigma-compact space `V`, this is the
restriction morphism `Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)`. It agrees with
`borelMooreHomologyRestrictOfExhaustion` for every compact exhaustion of `V`. -/
def borelMooreHomologyRestrict [T2Space X] [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k :=
  borelMooreHomologyRestrictOfExhaustion L hj (CompactExhaustion.choice V)
    (closure_image_compactExhaustion_subset_range j (CompactExhaustion.choice V)) k

/-- Canonical open restriction agrees with the exhaustion-explicit restriction for every compact
exhaustion of `V`. -/
theorem borelMooreHomologyRestrict_eq_ofExhaustion [T2Space X] [WeaklyLocallyCompactSpace V]
    [SigmaCompactSpace V] (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrict j hj L k =
      borelMooreHomologyRestrictOfExhaustion L hj K hK k :=
  borelMooreHomologyRestrictOfExhaustion_eq L hj _ K _ hK k


end CanonicalRestriction

end TauCeti.LocalCoefficientSystem
