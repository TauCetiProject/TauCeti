/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Homotopy
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Pair

/-!
# Relative cubical chains and fibre homotopy equivalences

A fibre homotopy equivalence over `B` induces a chain homotopy equivalence of relative
normalized cubical chains, relative to the preimage of any subset of `B`. No openness,
closedness or cofibration assumption on that subset is needed: the inverse homotopies
stay over the base and hence preserve its preimage.

The maps are the relative chain maps of the specified maps of total spaces. This is
useful for relative cell comparisons in a fibrewise homotopy trivialization.
-/

public noncomputable section

open CategoryTheory ContinuousMap

namespace TauCeti.FiberHomotopyEquiv

universe u v

variable {E E' : Type u} {B : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (S : Set B)

variable (R : Type u) [Ring R]

/-- A fibre homotopy equivalence induces a chain homotopy equivalence on normalized cubical
chains relative to the preimage of any subset of the base. -/
def relativeCubicalChainHomotopyEquiv :
    _root_.HomotopyEquiv
      ((TopPair.ofSubset (X := TopCat.of E) (p ⁻¹' S)).cubicalChainComplex R)
      ((TopPair.ofSubset (X := TopCat.of E') (q ⁻¹' S)).cubicalChainComplex R) where
  hom := TopPair.cubicalChainComplexMap R (Φ.preimagePairMap S)
  inv := TopPair.cubicalChainComplexMap R (Φ.symm.preimagePairMap S)
  homotopyHomInvId := by
    simpa only [TopPair.cubicalChainComplexMap_comp, TopPair.cubicalChainComplexMap_id]
      using (Φ.preimagePairCompHomotopy S).cubicalChainComplexMap R
  homotopyInvHomId := by
    simpa only [TopPair.cubicalChainComplexMap_comp, TopPair.cubicalChainComplexMap_id,
      symm_symm]
      using (Φ.symm.preimagePairCompHomotopy S).cubicalChainComplexMap R

@[simp]
theorem relativeCubicalChainHomotopyEquiv_hom :
    (Φ.relativeCubicalChainHomotopyEquiv S R).hom =
      TopPair.cubicalChainComplexMap R (Φ.preimagePairMap S) := (rfl)

@[simp]
theorem relativeCubicalChainHomotopyEquiv_inv :
    (Φ.relativeCubicalChainHomotopyEquiv S R).inv =
      TopPair.cubicalChainComplexMap R (Φ.symm.preimagePairMap S) := (rfl)

/-- The forward relative comparison sends the chain of a cube to the chain of its
composition with the specified map of total spaces. -/
-- These cube formulas are not simp rules: the hom/inv projection rules above simplify
-- their left sides first. Carrier-specialized comparisons can use them as simp rules.
theorem relativeCubicalChainHomotopyEquiv_hom_f_cubicalChainOfCube {n : ℕ}
    (σ : SingularCube E n) :
    (Φ.relativeCubicalChainHomotopyEquiv S R).hom.f n
        (TopPair.cubicalChainOfCube R σ) =
      TopPair.cubicalChainOfCube R
        (P := TopPair.ofSubset (X := TopCat.of E') (q ⁻¹' S))
        (Φ.toFun.comp σ) := by
  rw [relativeCubicalChainHomotopyEquiv_hom]
  have h := TopPair.cubicalChainComplexMap_f_cubicalChainOfCube R (Φ.preimagePairMap S) σ
  simp only [preimagePairMap_fst] at h
  -- The pair's ambient space and E' have the same carrier, but composition packages
  -- the compact-open map through different TopCat wrappers.
  convert h using 1
  congr 1

/-- The inverse relative comparison sends the chain of a cube to the chain of its
composition with the specified inverse map of total spaces. -/
theorem relativeCubicalChainHomotopyEquiv_inv_f_cubicalChainOfCube {n : ℕ}
    (σ : SingularCube E' n) :
    (Φ.relativeCubicalChainHomotopyEquiv S R).inv.f n
        (TopPair.cubicalChainOfCube R σ) =
      TopPair.cubicalChainOfCube R
        (P := TopPair.ofSubset (X := TopCat.of E) (p ⁻¹' S))
        (Φ.invFun.comp σ) := by
  simpa only [relativeCubicalChainHomotopyEquiv_hom, relativeCubicalChainHomotopyEquiv_inv,
    symm_toFun] using Φ.symm.relativeCubicalChainHomotopyEquiv_hom_f_cubicalChainOfCube S R σ

end TauCeti.FiberHomotopyEquiv
