/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower

/-!
# Comparing compact exhaustions in the Borel–Moore Milnor sequence

Both squares of the Borel–Moore Milnor sequence commute with pointwise enlargement `K n ⊆ K' n` of
compact exhaustions, including the connecting map from `lim¹` of relative homology
(`TauCeti.LocalCoefficientSystem.borelMooreHomologyToLim_naturality_exhaustion`,
`TauCeti.LocalCoefficientSystem.limOneToBorelMooreHomology_naturality_exhaustion`). These
comparisons allow nested compact exhaustions to be used in duality constructions without changing
the locally finite chain carrier or the connecting morphism. They do not assert that the induced
maps on the limits of homology or on `lim¹` are isomorphisms.

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

section Exhaustion

variable {K K' : CompactExhaustion X}

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
