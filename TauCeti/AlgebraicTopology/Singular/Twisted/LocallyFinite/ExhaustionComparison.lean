/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality

/-!
# Comparing monotone sequences and compact exhaustions in Borel–Moore homology

An inclusion `S n ⊆ S' n` of monotone sequences of subsets `S, S' : ℕ → Set X` (with
`S n ⊆ S (n + 1)` and `S' n ⊆ S' (n + 1)`) induces quotient maps
`C(X, X \ S' n; L) ⟶ C(X, X \ S n; L)`. These form a map of towers
(`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerMap`), compatible with the relative
classes of locally finite chains whenever each stage is compact
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplex_comp_limComplexMap`).

For compact exhaustions `K n ⊆ K' n`, the resulting map of limit complexes is an isomorphism:
under the identifications with locally finite chains, it is the identity. No levelwise
quasi-isomorphism is assumed or asserted.

Both squares of the Borel–Moore Milnor sequence commute with this comparison, including the
connecting map from `lim¹` of relative homology. These comparisons allow nested compact
exhaustions to be used in duality constructions without changing the locally finite chain
carrier or the connecting morphism. They do not assert that the induced maps on the limits
of homology or on `lim¹` are isomorphisms.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Topology

namespace TauCeti.LocalCoefficientSystem

universe u v w

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

section MonotoneSequence

variable {S S' S'' : ℕ → Set X}

/-- Pointwise enlargement of a monotone sequence of subsets induces a map of relative chain towers
in the opposite direction, by taking further relative quotients. -/
def relativeChainComplexTowerMap (hS : ∀ n, S n ⊆ S (n + 1)) (hS' : ∀ n, S' n ⊆ S' (n + 1))
    (h : ∀ n, S n ⊆ S' n) :
    relativeChainComplexTower L S' hS' ⟶ relativeChainComplexTower L S hS where
  app n := (TopTriple.ofSubset
    (Set.compl_subset_compl.2 (h n.unop))).twistedChainComplexTotalToOuter L
  naturality {m n} f := by
    apply (TopPair.ofSubset (S' m.unop)ᶜ).twistedChainComplex_hom_ext L
    -- Term composition lets elaboration align the dependent ambient types of the triples.
    exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc L S' hS' f _).trans <|
      (TopTriple.twistedChainComplexπ_comp_totalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n.unop))) L).trans <|
        ((TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (h m.unop))) L _).trans
          (twistedChainComplexπ_comp_relativeChainComplexTower_map L S hS f)).symm

/-- A component of the comparison is the quotient map for the corresponding triple. -/
@[simp]
theorem relativeChainComplexTowerMap_app (hS : ∀ n, S n ⊆ S (n + 1))
    (hS' : ∀ n, S' n ⊆ S' (n + 1)) (h : ∀ n, S n ⊆ S' n) (n : ℕ) :
    (relativeChainComplexTowerMap L hS hS' h).app (op n) =
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexTotalToOuter L :=
  (rfl)

/-- The comparison preserves the classes of finite ambient chains. -/
@[reassoc]
theorem twistedChainComplexπ_comp_relativeChainComplexTowerMap_app (hS : ∀ n, S n ⊆ S (n + 1))
    (hS' : ∀ n, S' n ⊆ S' (n + 1)) (h : ∀ n, S n ⊆ S' n) (n : ℕ) :
    (TopPair.ofSubset (S' n)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L hS hS' h).app (op n) =
      (TopPair.ofSubset (S n)ᶜ).twistedChainComplexπ L :=
  (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexπ_comp_totalToOuter L

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

section Exhaustion

variable {K K' : CompactExhaustion X}

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

/-- The Milnor projection from Borel–Moore homology commutes with the map on inverse limits
induced by enlargement of an exhaustion. -/
theorem borelMooreHomologyToLim_naturality_exhaustion (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    ModuleTower.limMap (Functor.whiskerRight
        (relativeChainComplexTowerMap L K.subset_succ K'.subset_succ h)
        (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) j)) ∘ₗ
        borelMooreHomologyToLim L K' j =
      borelMooreHomologyToLim L K j := by
  rw [borelMooreHomologyToLim_def, borelMooreHomologyToLim_def, ← LinearMap.comp_assoc,
    ← ComplexTower.homologyToLim_naturality, LinearMap.comp_assoc]
  congr 1
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap]

/-- The connecting map from `lim¹` to Borel–Moore homology commutes with the map induced by
enlargement of an exhaustion. Thus comparison retains the actual Milnor connecting morphism. -/
theorem limOneToBorelMooreHomology_naturality_exhaustion
    (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    limOneToBorelMooreHomology L K j ∘ₗ
        ModuleTower.limOneMap (Functor.whiskerRight
          (relativeChainComplexTowerMap L K.subset_succ K'.subset_succ h)
          (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) (j + 1))) =
      limOneToBorelMooreHomology L K' j := by
  rw [limOneToBorelMooreHomology_def, limOneToBorelMooreHomology_def,
    LinearMap.comp_assoc, ← ComplexTower.limOneToHomology_naturality _
      (relativeChainComplexTower_shift_surjective L K' K'.subset_succ)
      (relativeChainComplexTower_shift_surjective L K K.subset_succ),
    ← LinearMap.comp_assoc]
  congr 1
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    limComplexMap_relativeChainComplexTowerMap_comp_locallyFiniteChainComplexIsoLimComplex_inv]

end Exhaustion

end TauCeti.LocalCoefficientSystem
