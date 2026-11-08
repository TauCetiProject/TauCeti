/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Cubical.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

/-!
# The cubical Hurewicz class in relative cubical homology

A generalized loop `p : Ω^ (Fin (m + 1)) X x` sends the boundary of the cube to `x`, so it is also
a relative cycle of the normalized cubical chains of the pair `(X, {x})`
(`TopPair.cubicalCycleOfCube`). This file shows that the image of the cubical Hurewicz class
`GenLoop.cubicalHurewicz k p` under the map from absolute to relative cubical homology is the class
of this relative cycle (`GenLoop.homologyMap_π_cubicalHurewicz`).

## Main results

* `GenLoop.homologyMap_π_cubicalHurewicz`: the cubical Hurewicz class of `p`, read in the relative
  cubical homology of `(X, {x})`, is the class of `p` as a relative cycle.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti
open scoped Topology.Homotopy

universe u

namespace GenLoop

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X} {m : ℕ}

/-- The cubical Hurewicz class of a generalized loop `p` at `x`, read in the relative cubical
homology of `(X, {x})`, is the class of `p` as a relative cycle. -/
theorem homologyMap_π_cubicalHurewicz (p : Ω^ (Fin (m + 1)) X x) :
    HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset ({x} : Set (TopCat.of X))).map)) (m + 1) (cubicalHurewicz k p) =
      ((TopPair.ofSubset ({x} : Set (TopCat.of X))).cubicalChainComplex k).homologyπ (m + 1)
        (TopPair.cubicalCycleOfCube k _ (mapsTo_boundary_range_ofSubset p)) := by
  let K := (normalizedCubicalChainComplex k).obj (TopPair.ofSubset ({x} : Set (TopCat.of X))).fst
  -- The loop as an absolute cycle.
  let z : K.cycles (m + 1) := K.moduleCatCyclesMk
    (NormalizedCubicalChain.ofCube (TopPair.ofSubset ({x} : Set (TopCat.of X))).fst k p.1) m
    (by simp)
    (by rw [normalizedCubicalChainComplex_obj_d_apply]; exact boundary_ofCube_eq_zero k p)
  rw [← homologyπ_eq_cubicalHurewicz k p (z := z)
    (HomologicalComplex.iCycles_moduleCatCyclesMk ..)]
  -- The ambient space of `TopPair.ofSubset {x}` is `X` only up to unfolding, so the naturality of
  -- the class map is applied to `z` before it is matched with the goal.
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (cokernel.π
    ((normalizedCubicalChainComplex k).map (TopPair.ofSubset ({x} : Set (TopCat.of X))).map))
      (m + 1)) z
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans (congrArg _ ?_)
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  -- Both sides are the image of the chain of `p` in the relative chains.
  refine Eq.trans ?_ ((TopPair.iCycles_cubicalCycleOfCube k _ _).trans
    (TopPair.cubicalChainOfCube_def k _)).symm
  exact congrArg _ ((HomologicalComplex.iCycles_moduleCatCyclesMk ..).trans
    (normalizedCubicalChainComplexXEquiv_symm_apply _ _ _).symm)

end GenLoop
