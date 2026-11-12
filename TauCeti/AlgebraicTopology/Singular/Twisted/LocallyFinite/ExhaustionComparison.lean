/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality

/-!
# Comparing compact exhaustions in Borel–Moore homology

An inclusion `K n ⊆ K' n` of compact exhaustions induces quotient maps
`C(X, X \ K' n; L) ⟶ C(X, X \ K n; L)`. These form a map of towers, compatible
with the relative classes of locally finite chains. The resulting map of limit complexes is
an isomorphism: under the identifications with locally finite chains, it is the identity.
No levelwise quasi-isomorphism is assumed or asserted.

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
  {K K' K'' : CompactExhaustion X}

/-- Pointwise enlargement of a compact exhaustion induces a map of relative chain towers in
the opposite direction, by taking further relative quotients. -/
def relativeChainComplexTowerMap (h : ∀ n, K n ⊆ K' n) :
    relativeChainComplexTower L K' ⟶ relativeChainComplexTower L K where
  app n := (TopTriple.ofSubset
    (Set.compl_subset_compl.2 (h n.unop))).twistedChainComplexTotalToOuter L
  naturality {m n} f := by
    apply (TopPair.ofSubset (K' m.unop)ᶜ).twistedChainComplex_hom_ext L
    -- Term composition lets elaboration align the dependent ambient types of the triples.
    exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc L K' f _).trans <|
      (TopTriple.twistedChainComplexπ_comp_totalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n.unop))) L).trans <|
        ((TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (h m.unop))) L _).trans
          (twistedChainComplexπ_comp_relativeChainComplexTower_map L K f)).symm

/-- A component of the comparison is the quotient map for the corresponding triple. -/
@[simp]
theorem relativeChainComplexTowerMap_app (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (relativeChainComplexTowerMap L h).app (op n) =
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexTotalToOuter L :=
  (rfl)

/-- The comparison preserves the classes of finite ambient chains. -/
@[reassoc]
theorem twistedChainComplexπ_comp_relativeChainComplexTowerMap_app
    (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (TopPair.ofSubset (K' n)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L h).app (op n) =
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ L :=
  (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexπ_comp_totalToOuter L

@[simp]
theorem relativeChainComplexTowerMap_refl :
    relativeChainComplexTowerMap L (fun n ↦ Set.Subset.refl (K n)) = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply (TopPair.ofSubset (K n.unop)ᶜ).twistedChainComplex_hom_ext L
  exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L _ n.unop).trans
    (Category.comp_id _).symm

/-- Taking further relative quotients is transitive. -/
@[reassoc (attr := simp)]
theorem relativeChainComplexTowerMap_comp (h : ∀ n, K n ⊆ K' n)
    (h' : ∀ n, K' n ⊆ K'' n) :
    relativeChainComplexTowerMap L h' ≫ relativeChainComplexTowerMap L h =
      relativeChainComplexTowerMap L (fun n ↦ (h n).trans (h' n)) := by
  apply NatTrans.ext
  funext n
  apply (TopPair.ofSubset (K'' n.unop)ᶜ).twistedChainComplex_hom_ext L
  exact (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc L h' n.unop _).trans <|
    (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L h n.unop).trans
      (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L
        (fun n ↦ (h n).trans (h' n)) n.unop).symm

/-- Relative classes of locally finite chains commute with enlargement of the compact sets. -/
@[reassoc]
theorem locallyFiniteChainComplexToRelative_comp_relativeChainComplexTowerMap_app
    (h : ∀ n, K n ⊆ K' n) (n : ℕ) :
    (TopPair.ofSubset (K' n)ᶜ).locallyFiniteChainComplexToRelative L
        (K'.isCompact n).compl_range_ofSubset_compl_map ≫
        (relativeChainComplexTowerMap L h).app (op n) =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map :=
  TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
    (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))) L
    (K'.isCompact n).compl_range_ofSubset_compl_map (K.isCompact n).compl_range_ofSubset_compl_map

/-- The map of limit complexes is the identity on locally finite chains, through the canonical
identifications with the limits of the two relative towers. -/
@[reassoc (attr := simp)]
theorem locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap
    (h : ∀ n, K n ⊆ K' n) :
    (locallyFiniteChainComplexIsoLimComplex L K').hom ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L h) =
      (locallyFiniteChainComplexIsoLimComplex L K).hom := by
  apply (relativeChainComplexTower L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  -- Term composition aligns the dependent limit-cone and relative-pair wrappers.
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
      (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc L K' n _).trans <|
        (locallyFiniteChainComplexToRelative_comp_relativeChainComplexTowerMap_app L h n).trans
          (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ L K n).symm

/-- The comparison on limit complexes preserves the inverse identification with locally finite
chains. -/
@[reassoc (attr := simp)]
theorem limComplexMap_relativeChainComplexTowerMap_comp_locallyFiniteChainComplexIsoLimComplex_inv
    (h : ∀ n, K n ⊆ K' n) :
    ComplexTower.limComplexMap (relativeChainComplexTowerMap L h) ≫
        (locallyFiniteChainComplexIsoLimComplex L K).inv =
      (locallyFiniteChainComplexIsoLimComplex L K').inv := by
  apply (cancel_epi (locallyFiniteChainComplexIsoLimComplex L K').hom).1
  simp

/-- Although the relative quotient maps need not be quasi-isomorphisms individually, their
map on limit complexes is an isomorphism. -/
instance isIso_limComplexMap_relativeChainComplexTowerMap (h : ∀ n, K n ⊆ K' n) :
    IsIso (ComplexTower.limComplexMap (relativeChainComplexTowerMap L h)) := by
  have heq : ComplexTower.limComplexMap (relativeChainComplexTowerMap L h) =
      (locallyFiniteChainComplexIsoLimComplex L K').inv ≫
        (locallyFiniteChainComplexIsoLimComplex L K).hom := by
    rw [← locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap L h,
      Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- The Milnor projection from Borel–Moore homology commutes with the map on inverse limits
induced by enlargement of an exhaustion. -/
theorem borelMooreHomologyToLim_naturality_exhaustion (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    ModuleTower.limMap (Functor.whiskerRight (relativeChainComplexTowerMap L h)
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
        ModuleTower.limOneMap (Functor.whiskerRight (relativeChainComplexTowerMap L h)
          (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) (j + 1))) =
      limOneToBorelMooreHomology L K' j := by
  rw [limOneToBorelMooreHomology_def, limOneToBorelMooreHomology_def,
    LinearMap.comp_assoc, ← ComplexTower.limOneToHomology_naturality _
      (relativeChainComplexTower_shift_surjective L K')
      (relativeChainComplexTower_shift_surjective L K),
    ← LinearMap.comp_assoc]
  congr 1
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    limComplexMap_relativeChainComplexTowerMap_comp_locallyFiniteChainComplexIsoLimComplex_inv]

end TauCeti.LocalCoefficientSystem
