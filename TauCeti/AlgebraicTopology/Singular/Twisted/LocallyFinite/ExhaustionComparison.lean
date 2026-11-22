/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower

/-!
# Comparing compact exhaustions in Borel–Moore homology

An inclusion `K n ⊆ K' n` of compact exhaustions induces quotient maps
`C(X, X \ K' n; L) ⟶ C(X, X \ K n; L)`. These form a map of towers
`complChainComplexTowerMap`, compatible with the relative classes of locally finite chains. The
resulting map of limit complexes is an isomorphism: under the identifications with locally finite
chains, it is the identity. No levelwise quasi-isomorphism is assumed or asserted.

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
  {K K' : CompactExhaustion X}

/-- The comparison on limit complexes preserves the inverse identification with locally finite
chains. -/
@[reassoc (attr := simp)]
theorem limComplexMap_complChainComplexTowerMap_comp_locallyFiniteChainComplexIsoLimComplex_inv
    (h : ∀ n, K n ⊆ K' n) :
    ComplexTower.limComplexMap (complChainComplexTowerMap L K.subset_succ K'.subset_succ h) ≫
        (locallyFiniteChainComplexIsoLimComplex L K).inv =
      (locallyFiniteChainComplexIsoLimComplex L K').inv := by
  apply (cancel_epi (locallyFiniteChainComplexIsoLimComplex L K').hom).1
  rw [locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K',
    locallyFiniteChainComplexToComplLim_comp_limComplexMap_assoc L K.subset_succ K'.subset_succ
      K.isCompact K'.isCompact h,
    ← locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K,
    ← locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K']
  simp only [Iso.hom_inv_id]

/-- Although the relative quotient maps need not be quasi-isomorphisms individually, their
map on limit complexes is an isomorphism. -/
instance isIso_limComplexMap_complChainComplexTowerMap (h : ∀ n, K n ⊆ K' n) :
    IsIso (ComplexTower.limComplexMap
      (complChainComplexTowerMap L K.subset_succ K'.subset_succ h)) := by
  have heq : ComplexTower.limComplexMap
        (complChainComplexTowerMap L K.subset_succ K'.subset_succ h) =
      (locallyFiniteChainComplexIsoLimComplex L K').inv ≫
        (locallyFiniteChainComplexIsoLimComplex L K).hom := by
    rw [locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K,
      ← locallyFiniteChainComplexToComplLim_comp_limComplexMap L K.subset_succ K'.subset_succ
        K.isCompact K'.isCompact h,
      ← locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K', Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- The Milnor projection from Borel–Moore homology commutes with the map on inverse limits
induced by enlargement of an exhaustion. -/
theorem borelMooreHomologyToLim_naturality_exhaustion (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    ModuleTower.limMap (Functor.whiskerRight
        (complChainComplexTowerMap L K.subset_succ K'.subset_succ h)
        (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) j)) ∘ₗ
        borelMooreHomologyToLim L K' j =
      borelMooreHomologyToLim L K j := by
  rw [borelMooreHomologyToLim_def, borelMooreHomologyToLim_def, ← LinearMap.comp_assoc,
    ← ComplexTower.homologyToLim_naturality, LinearMap.comp_assoc]
  congr 1
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K',
    locallyFiniteChainComplexToComplLim_comp_limComplexMap L K.subset_succ K'.subset_succ
      K.isCompact K'.isCompact h,
    ← locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim L K]

/-- The connecting map from `lim¹` to Borel–Moore homology commutes with the map induced by
enlargement of an exhaustion. Thus comparison retains the actual Milnor connecting morphism. -/
theorem limOneToBorelMooreHomology_naturality_exhaustion
    (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    limOneToBorelMooreHomology L K j ∘ₗ
        ModuleTower.limOneMap (Functor.whiskerRight
          (complChainComplexTowerMap L K.subset_succ K'.subset_succ h)
          (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) (j + 1))) =
      limOneToBorelMooreHomology L K' j := by
  rw [limOneToBorelMooreHomology_def, limOneToBorelMooreHomology_def,
    LinearMap.comp_assoc, ← ComplexTower.limOneToHomology_naturality _
      (complChainComplexTower_shift_surjective L K' K'.subset_succ)
      (complChainComplexTower_shift_surjective L K K.subset_succ),
    ← LinearMap.comp_assoc]
  congr 1
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    limComplexMap_complChainComplexTowerMap_comp_locallyFiniteChainComplexIsoLimComplex_inv]

end TauCeti.LocalCoefficientSystem
