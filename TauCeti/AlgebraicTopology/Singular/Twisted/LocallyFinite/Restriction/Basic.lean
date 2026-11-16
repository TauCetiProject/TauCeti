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
import TauCeti.Topology.Compactness.SigmaCompact

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
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplex` applied to the monotone
sequence `fun n ↦ j.hom '' K n`). The right chain map
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplexOfInjective`) composes the
limit identification on `V` with the inverse-limit map induced by the levelwise excision maps of
pairs `(V, V \ Kₙ) ⟶ (X, X \ j '' Kₙ)`
(`TauCeti.LocalCoefficientSystem.excisionRelativeChainComplexTowerMap`).
Because `Set.range j` is open and contains the closure of `j '' Kₙ`, each level map is a
quasi-isomorphism (`TopPair.quasiIso_twistedChainComplexMap_of_open_cover`). Both towers have
degreewise surjective transitions, so
`TauCeti.ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso` upgrades this to a
quasi-isomorphism of limit complexes. Inverting the resulting isomorphism on homology yields
`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion`.

Any two compact exhaustions `K` and `K'` of `V` are dominated by their pointwise union
`K.union K'`, and enlarging the compact sets induces compatible triple-quotient maps on both
towers (`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerMap`), so the restriction
morphism is independent of the chosen exhaustion
(`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_eq`). When `X` is Hausdorff
and `V` is weakly locally compact and sigma-compact, choosing `CompactExhaustion.choice V` defines
the canonical open restriction `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`.

Functoriality, naturality in local coefficients, and a degree-zero discrete verification are in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Functoriality`. Proper-map
base change is in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.BaseChange`.

## Main declarations

* `TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative` and
  `TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative`: naturality of
  relative classes of locally finite chains under coefficient morphisms and proper maps of pairs.
* `TauCeti.LocalCoefficientSystem.excisionRelativeChainComplexTowerMap` and
  `TauCeti.LocalCoefficientSystem.quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap`: the
  levelwise excision map of towers and its quasi-isomorphism on limit complexes.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplexOfInjective` and
  `TauCeti.LocalCoefficientSystem.quasiIso_locallyFiniteChainComplexToLimComplexOfInjective`: the
  chain map from locally finite chains on `V` to the limit of the ambient relative tower on `X`
  and its quasi-isomorphism property for open embeddings.
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
  · -- `((pullback (Hom.fst g).hom).obj L).obj (initialVertex σ)` is definitionally
    -- `L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))`, since `pullback`
    -- composes with `FundamentalGroupoid.map` and `initialVertex` commutes with `toSSet.map`.
    have hc0' :
        (c.1 σ :
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

end ToRelativeNaturality

end TopPair

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section ExcisionTower

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- For an injective continuous map `j : V ⟶ X` and a subset `S ⊆ V`, the induced map of pairs
`(V, V \ S) ⟶ (X, X \ j '' S)`. -/
-- Uses `TopPair.ofHom` rather than `TopPair.ofSubsetMap` because `TopPair.ofSubsetMap` is not
-- `@[expose]` in `TopPair.lean`, so across `module` boundaries `Hom.fst (TopPair.ofSubsetMap …)`
-- is not definitionally `j` (needed for `(pullback j.hom).obj L` to match the domain).
@[expose]
def injectivePairMap (hj : Function.Injective j.hom) (S : Set V) :
    TopPair.ofSubset Sᶜ ⟶ TopPair.ofSubset (j.hom '' S)ᶜ :=
  TopPair.ofHom j
    (TopCat.ofHom ⟨Set.MapsTo.restrict j.hom Sᶜ (j.hom '' S)ᶜ
        (fun _ hx ⟨_, hy, hxy⟩ ↦ hx (hj hxy ▸ hy)),
      j.hom.continuous.restrict _⟩)

/-- The levelwise excision map of towers
`C(V, V \ Sₙ; j⁎L) ⟶ C(X, X \ j '' Sₙ; L)` for a monotone sequence of subsets `S` of `V`. -/
def excisionRelativeChainComplexTowerMap (S : ℕ → Set V) (hS : ∀ n, S n ⊆ S (n + 1))
    (hj : Function.Injective j.hom) :
    relativeChainComplexTower ((pullback j.hom).obj L) S hS ⟶
      relativeChainComplexTower L (fun n ↦ j.hom '' S n) (fun n ↦ Set.image_mono (hS n)) where
  app n := TopPair.twistedChainComplexMap (injectivePairMap hj (S n.unop)) L
  naturality {m n} f := by
    apply (TopPair.ofSubset (S m.unop)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    -- `(TopPair.ofSubset _).fst` is only definitionally `V`/`X`, so `rw`/`simp` fail at `implicit`
    -- transparency; explicit `trans` steps let elaboration align the ambient types.
    trans (TopPair.ofSubset (S n.unop)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
        TopPair.twistedChainComplexMap (injectivePairMap hj (S n.unop)) L
    · exact twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc _ S hS f _
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' S n.unop)ᶜ).twistedChainComplexπ L
    · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (injectivePairMap hj (S n.unop)) L
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' S m.unop)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTower L (fun n ↦ j.hom '' S n)
          (fun n ↦ Set.image_mono (hS n))).map f
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTower_map L (fun n ↦ j.hom '' S n)
          (fun n ↦ Set.image_mono (hS n)) f).symm
    · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hj (S m.unop)) L _).symm

/-- On each level, `excisionRelativeChainComplexTowerMap` is the relative twisted chain map along
`injectivePairMap`. -/
@[simp]
lemma excisionRelativeChainComplexTowerMap_app (S : ℕ → Set V) (hS : ∀ n, S n ⊆ S (n + 1))
    (hj : Function.Injective j.hom) (n : ℕ) :
    (excisionRelativeChainComplexTowerMap L S hS hj).app (op n) =
      TopPair.twistedChainComplexMap (injectivePairMap hj (S n)) L :=
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

/-- If `j : V ⟶ X` is an open embedding and `closure (j '' Sₙ) ⊆ Set.range j` for every `n`,
then the excision map of towers induces a quasi-isomorphism on limit complexes. -/
theorem quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap (S : ℕ → Set V)
    (hS : ∀ n, S n ⊆ S (n + 1)) (hj : IsOpenEmbedding j.hom)
    (hScl : ∀ n, closure (j.hom '' S n) ⊆ Set.range j.hom) :
    QuasiIso (ComplexTower.limComplexMap
      (excisionRelativeChainComplexTowerMap L S hS hj.injective)) :=
  ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso _
    (relativeChainComplexTower_shift_surjective ((pullback j.hom).obj L) S hS)
    (relativeChainComplexTower_shift_surjective L (fun n ↦ j.hom '' S n)
      (fun n ↦ Set.image_mono (hS n)))
    fun n ↦ quasiIso_twistedChainComplexMap_injectivePairMap L hj (hScl n)

/-- The chain map `C^lf(V; j⁎L) ⟶ limₙ C(X, X \ j '' Kₙ; L)` formed by composing the limit
identification of locally finite chains on `V` with the excision map of relative towers along an
injective map `j : V ⟶ X`. -/
def locallyFiniteChainComplexToLimComplexOfInjective (K : CompactExhaustion V)
    (hj : Function.Injective j.hom) :
    locallyFiniteChainComplex ((pullback j.hom).obj L) ⟶
      (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n))).limComplex :=
  (locallyFiniteChainComplexIsoLimComplex ((pullback j.hom).obj L) K).hom ≫
    ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L K K.subset_succ hj)

/-- The `n`-th projection of `locallyFiniteChainComplexToLimComplexOfInjective` takes relative
classes on `V` and pushes them along the excision map of pairs. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ (K : CompactExhaustion V)
    (hj : Function.Injective j.hom) (n : ℕ) :
    locallyFiniteChainComplexToLimComplexOfInjective L K hj ≫
        (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n))).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map ≫
        TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L := by
  rw [locallyFiniteChainComplexToLimComplexOfInjective, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc,
    excisionRelativeChainComplexTowerMap_app]
  rfl

/-- For an open embedding `j : V ⟶ X` and a compact exhaustion `K` with
`closure (j '' Kₙ) ⊆ Set.range j`, `locallyFiniteChainComplexToLimComplexOfInjective` is a
quasi-isomorphism. -/
theorem quasiIso_locallyFiniteChainComplexToLimComplexOfInjective (K : CompactExhaustion V)
    (hj : IsOpenEmbedding j.hom) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) :
    QuasiIso (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) := by
  have := quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap L K K.subset_succ hj hK
  exact quasiIso_comp _ _

end ExcisionTower

section ExhaustionRestriction

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- **Open restriction in Borel–Moore homology via a compact exhaustion.** Given an open embedding
`j : V ⟶ X` and a compact exhaustion `K` of `V` with `closure (j '' Kₙ) ⊆ Set.range j`, this
morphism `Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)` is obtained by inverting the excision quasi-isomorphism
`locallyFiniteChainComplexToLimComplexOfInjective`. By
`borelMooreHomologyRestrictOfExhaustion_eq`, it does not depend on the choice of `K`. -/
def borelMooreHomologyRestrictOfExhaustion (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k :=
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n))
        (fun n ↦ (K.isCompact n).image j.hom.continuous)) k ≫
    inv (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k)

/-- The defining zigzag equation for `borelMooreHomologyRestrictOfExhaustion`. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
    (hj : IsOpenEmbedding j.hom) (K : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K hK k ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k =
      HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ (K.isCompact n).image j.hom.continuous)) k := by
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  simp [borelMooreHomologyRestrictOfExhaustion]

/-- Uniqueness characterization of `borelMooreHomologyRestrictOfExhaustion`: a morphism
`Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)` equals open restriction if and only if postcomposing with
`locallyFiniteChainComplexToLimComplexOfInjective` yields
`locallyFiniteChainComplexToLimComplex`. -/
theorem eq_borelMooreHomologyRestrictOfExhaustion_iff (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ)
    (φ : borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k) :
    φ = borelMooreHomologyRestrictOfExhaustion L hj K hK k ↔
      φ ≫ HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k =
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
            (fun n ↦ Set.image_mono (K.subset_succ n))
            (fun n ↦ (K.isCompact n).image j.hom.continuous)) k := by
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  constructor
  · rintro rfl
    exact
      borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
        L hj K hK k
  · intro h
    rw [← cancel_mono (HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k),
      h,
      borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective]

/-- `locallyFiniteChainComplexToLimComplexOfInjective` is compatible with enlargement of the
compact exhaustion of `V`. -/
@[reassoc]
lemma locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexMap
    (hj : Function.Injective j.hom) {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexToLimComplexOfInjective L K' hj ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ Set.image_mono (K'.subset_succ n))
          fun n ↦ Set.image_mono (h n)) =
      locallyFiniteChainComplexToLimComplexOfInjective L K hj := by
  have hsq : excisionRelativeChainComplexTowerMap L K' K'.subset_succ hj ≫
        relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ Set.image_mono (K'.subset_succ n))
          (fun n ↦ Set.image_mono (h n)) =
      relativeChainComplexTowerMap ((pullback j.hom).obj L) K.subset_succ K'.subset_succ h ≫
        excisionRelativeChainComplexTowerMap L K K.subset_succ hj := by
    apply NatTrans.ext
    funext ⟨n⟩
    apply (TopPair.ofSubset (K' n)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    -- `(TopPair.ofSubset _).fst` is only definitionally `V`/`X`, so `rw`/`simp` fail at `implicit`
    -- transparency; explicit `trans` steps let elaboration align the ambient types.
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' K' n)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ Set.image_mono (K'.subset_succ n))
          (fun n ↦ Set.image_mono (h n))).app (op n)
    · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hj (K' n)) L _
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ L
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ Set.image_mono (K'.subset_succ n))
          (fun n ↦ Set.image_mono (h n)) n)
    trans (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
        TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L
    · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (injectivePairMap hj (K n)) L).symm
    · exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc
        ((pullback j.hom).obj L) K.subset_succ K'.subset_succ h n _).symm
  calc locallyFiniteChainComplexToLimComplexOfInjective L K' hj ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ Set.image_mono (K'.subset_succ n))
          fun n ↦ Set.image_mono (h n))
    _ = (locallyFiniteChainComplexIsoLimComplex ((pullback j.hom).obj L) K').hom ≫
          ComplexTower.limComplexMap
            (relativeChainComplexTowerMap ((pullback j.hom).obj L)
              K.subset_succ K'.subset_succ h) ≫
            ComplexTower.limComplexMap
              (excisionRelativeChainComplexTowerMap L K K.subset_succ hj) := by
        rw [locallyFiniteChainComplexToLimComplexOfInjective, Category.assoc,
          ← ComplexTower.limComplexMap_comp, hsq, ComplexTower.limComplexMap_comp]
    _ = locallyFiniteChainComplexToLimComplexOfInjective L K hj := by
        rw [← Category.assoc, locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap,
          locallyFiniteChainComplexToLimComplexOfInjective]

private lemma borelMooreHomologyRestrictOfExhaustion_eq_of_subset (hj : IsOpenEmbedding j.hom)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hK' : ∀ n, closure (j.hom '' K' n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K' hK' k =
      borelMooreHomologyRestrictOfExhaustion L hj K hK k := by
  rw [eq_borelMooreHomologyRestrictOfExhaustion_iff]
  calc borelMooreHomologyRestrictOfExhaustion L hj K' hK' k ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k
    _ = (borelMooreHomologyRestrictOfExhaustion L hj K' hK' k ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToLimComplexOfInjective L K' hj.injective) k) ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap (relativeChainComplexTowerMap L
              (fun n ↦ Set.image_mono (K.subset_succ n))
              (fun n ↦ Set.image_mono (K'.subset_succ n))
              fun n ↦ Set.image_mono (h n))) k := by
        rw [← locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexMap L hj.injective h,
          HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
            (fun n ↦ Set.image_mono (K.subset_succ n))
            (fun n ↦ (K.isCompact n).image j.hom.continuous)) k := by
      simp only [← HomologicalComplex.homologyMap_comp,
        borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      ]
      rw [locallyFiniteChainComplexToLimComplex_comp_limComplexMap]

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
      (fun _ ↦ by simp [K'']) hK hK'' k).symm.trans
    (borelMooreHomologyRestrictOfExhaustion_eq_of_subset L hj
      (fun _ ↦ by simp [K'']) hK' hK'' k)

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
    ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k

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
