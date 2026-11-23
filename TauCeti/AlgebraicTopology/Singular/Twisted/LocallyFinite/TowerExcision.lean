/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.QuasiIso

/-!
# Excision maps on relative twisted chain complex towers

Given an injective continuous map `j : V ⟶ X` and a monotone sequence of subsets `S : ℕ → Set V`
(`S n ⊆ S (n + 1)`), the pair inclusions `(V, V \ Sₙ) ⟶ (X, X \ j '' Sₙ)` assemble into a map of
relative twisted chain complex towers
(`TauCeti.LocalCoefficientSystem.excisionRelativeChainComplexTowerMap`), compatible with pointwise
enlargement of `S` (`excisionRelativeChainComplexTowerMap_comp_relativeChainComplexTowerMap`).

When `j` is an open embedding and `closure (j '' Sₙ) ⊆ Set.range j` for every `n`, each level
map is a quasi-isomorphism by excision
(`TopPair.quasiIso_twistedChainComplexMap_ofSubsetMap_compl_image`). Since both relative towers
have surjective shift maps, the induced map on limit complexes is a quasi-isomorphism
(`TauCeti.LocalCoefficientSystem.quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap`).

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Topology

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The levelwise excision map of towers
`C(V, V \ Sₙ; j⁎L) ⟶ C(X, X \ j '' Sₙ; L)` for a monotone sequence of subsets `S` of `V`. -/
def excisionRelativeChainComplexTowerMap (S : ℕ → Set V) (hS : ∀ n, S n ⊆ S (n + 1))
    (hj : Function.Injective j.hom) :
    relativeChainComplexTower ((pullback j.hom).obj L) S hS ⟶
      relativeChainComplexTower L (fun n ↦ j.hom '' S n) (fun n ↦ Set.image_mono (hS n)) :=
  relativeChainComplexTowerHomMk hS (fun n ↦ Set.image_mono (hS n)) (twistedChainComplexMap j L)
    (fun n ↦ TopPair.twistedChainComplexMapOfFstEq
      (TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (S n)) hj))
      (TopPair.ofSubsetMap_fst _ _) L)
    fun n ↦ TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq
      (TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (S n)) hj))
      (TopPair.ofSubsetMap_fst _ _) L

/-- On each level, `excisionRelativeChainComplexTowerMap` is the relative twisted chain map along
`TopPair.ofSubsetMap j`. -/
@[simp]
lemma excisionRelativeChainComplexTowerMap_app (S : ℕ → Set V) (hS : ∀ n, S n ⊆ S (n + 1))
    (hj : Function.Injective j.hom) (n : ℕ) :
    (excisionRelativeChainComplexTowerMap L S hS hj).app (op n) =
      TopPair.twistedChainComplexMapOfFstEq
        (TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (S n)) hj))
        (TopPair.ofSubsetMap_fst _ _) L :=
  relativeChainComplexTowerHomMk_app hS (fun n ↦ Set.image_mono (hS n)) _ _ _ n

/-- Excision on relative towers commutes with pointwise enlargement of monotone sequences of
subsets. -/
@[reassoc]
theorem excisionRelativeChainComplexTowerMap_comp_relativeChainComplexTowerMap
    {S S' : ℕ → Set V} (hS : ∀ n, S n ⊆ S (n + 1)) (hS' : ∀ n, S' n ⊆ S' (n + 1))
    (h : ∀ n, S n ⊆ S' n) (hj : Function.Injective j.hom) :
    excisionRelativeChainComplexTowerMap L S' hS' hj ≫
        relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (hS n))
          (fun n ↦ Set.image_mono (hS' n)) (fun n ↦ Set.image_mono (h n)) =
      relativeChainComplexTowerMap ((pullback j.hom).obj L) hS hS' h ≫
        excisionRelativeChainComplexTowerMap L S hS hj := by
  apply NatTrans.ext
  funext ⟨n⟩
  apply (TopPair.ofSubset (S' n)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
  -- `(TopPair.ofSubset _).fst` is only definitionally `V`/`X`, so `trans` aligns ambient types.
  trans twistedChainComplexMap j L ≫
      (TopPair.ofSubset (j.hom '' S' n)ᶜ).twistedChainComplexπ L ≫
      (relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (hS n))
        (fun n ↦ Set.image_mono (hS' n)) (fun n ↦ Set.image_mono (h n))).app (op n)
  · rw [NatTrans.comp_app, excisionRelativeChainComplexTowerMap_app]
    exact TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq_assoc
      (TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (S' n)) hj))
      (TopPair.ofSubsetMap_fst _ _) L _
  trans twistedChainComplexMap j L ≫
      (TopPair.ofSubset (j.hom '' S n)ᶜ).twistedChainComplexπ L
  · exact congrArg (_ ≫ ·)
      (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L
        (fun n ↦ Set.image_mono (hS n)) (fun n ↦ Set.image_mono (hS' n))
        (fun n ↦ Set.image_mono (h n)) n)
  trans (TopPair.ofSubset (S n)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
      (excisionRelativeChainComplexTowerMap L S hS hj).app (op n)
  · rw [excisionRelativeChainComplexTowerMap_app]
    exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq
      (TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (S n)) hj))
      (TopPair.ofSubsetMap_fst _ _) L).symm
  · exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc
      ((pullback j.hom).obj L) hS hS' h n _).symm

/-- If `j : V ⟶ X` is an open embedding and `closure (j '' Sₙ) ⊆ Set.range j` for every `n`,
then the excision map of towers induces a quasi-isomorphism on limit complexes. -/
theorem quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap (S : ℕ → Set V)
    (hS : ∀ n, S n ⊆ S (n + 1)) (hj : IsOpenEmbedding j.hom)
    (hScl : ∀ n, closure (j.hom '' S n) ⊆ Set.range j.hom) :
    QuasiIso (ComplexTower.limComplexMap
      (excisionRelativeChainComplexTowerMap L S hS hj.injective)) := by
  refine ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso _
    (relativeChainComplexTower_shift_surjective ((pullback j.hom).obj L) S hS)
    (relativeChainComplexTower_shift_surjective L (fun n ↦ j.hom '' S n)
      (fun n ↦ Set.image_mono (hS n)))
    fun n ↦ ?_
  rw [excisionRelativeChainComplexTowerMap_app]
  refine TopPair.quasiIso_twistedChainComplexMapOfFstEq _ _ _ ?_
  exact TopPair.quasiIso_twistedChainComplexMap_ofSubsetMap_compl_image L hj (hScl n)

/-- Pushing locally finite chains into the relative limit tower along `S'`, excising along an
injective map `j`, and shrinking to `j '' S` agrees with shrinking to `S` and then excising. -/
@[reassoc]
theorem locallyFiniteChainComplexToLimComplex_comp_limComplexMap_excision
    {S S' : ℕ → Set V} (hS : ∀ n, S n ⊆ S (n + 1)) (hS' : ∀ n, S' n ⊆ S' (n + 1))
    (hSc : ∀ n, IsCompact (S n)) (hS'c : ∀ n, IsCompact (S' n))
    (h : ∀ n, S n ⊆ S' n) (hj : Function.Injective j.hom) :
    locallyFiniteChainComplexToLimComplex ((pullback j.hom).obj L) S' hS' hS'c ≫
        ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L S' hS' hj) ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (hS n)) (fun n ↦ Set.image_mono (hS' n))
          fun n ↦ Set.image_mono (h n)) =
      locallyFiniteChainComplexToLimComplex ((pullback j.hom).obj L) S hS hSc ≫
        ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L S hS hj) := by
  rw [← ComplexTower.limComplexMap_comp,
    excisionRelativeChainComplexTowerMap_comp_relativeChainComplexTowerMap L hS hS' h hj,
    ComplexTower.limComplexMap_comp,
    locallyFiniteChainComplexToLimComplex_comp_limComplexMap_assoc]

end TauCeti.LocalCoefficientSystem
