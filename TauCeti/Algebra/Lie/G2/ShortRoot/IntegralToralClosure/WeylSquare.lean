/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.RankOne

/-!
# Squares of the pinned rank-one words in the short-root G₂ carrier

For each Bourbaki node `i` and every unit `u`, the word
`nᵢ(u) = xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` in the seven-dimensional integral toral closure
satisfies `nᵢ(u)² = αᵢ∨(-1)`. The coroot value is the weight-torus point with
coordinate `-1` at `i` and `1` elsewhere. Thus these reflection lifts need not be
involutions, even though their Weyl classes are.

The relation holds over every commutative coefficient ring, including rings with
nilpotents. It is the specialization of the Kostant rank-one relation using the
represented `sl₂` triples, so includes the quadratic short-root terms without
recomputing their matrices. No identification of this carrier with an independently
constructed pinned group scheme is asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.G2ShortRoot.IntegralToralClosure

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-- The square of the pinned rank-one word at any unit is the simple-coroot value at `-1`. -/
@[simp↓]
theorem rootSubgroupPoints_weylWord_sq (i : Fin 2) (A : Type*) [CommRing A] (u : Aˣ) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 2 =
      weightTorusPoints A (Pi.mulSingle i (-1)) := by
  have hpos (j : Fin 2) :
      ⁅TauCeti.serreH ℚ CartanMatrix.G₂ j, TauCeti.serreRootGenerator CartanMatrix.G₂ (.inl i)⁆ =
        ((CartanMatrix.G₂ j i : ℤ) : ℚ) •
          TauCeti.serreRootGenerator CartanMatrix.G₂ (.inl i) :=
    TauCeti.lie_serreH_serreRootGenerator_inl CartanMatrix.G₂ i j
  have hneg (j : Fin 2) :
      ⁅TauCeti.serreH ℚ CartanMatrix.G₂ j, TauCeti.serreRootGenerator CartanMatrix.G₂ (.inr i)⁆ =
        -(((CartanMatrix.G₂ j i : ℤ) : ℚ) •
          TauCeti.serreRootGenerator CartanMatrix.G₂ (.inr i)) := by
    simpa only [Int.cast_neg, neg_smul] using
      TauCeti.lie_serreH_serreRootGenerator_inr CartanMatrix.G₂ i j
  have hsq := kostantToralRootSubgroupPoints_weylWord_sq
      (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂)
      rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
      isNilpotent_rep_serreRootGenerator latticeBasis weight isCartanWeightVector_latticeBasis
      (isSl2Triple_rep_serreRootGenerator i) hpos hneg A u
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul,
    coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix, coe_weightTorusPoints,
    coe_kostantToralRootSubgroupPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val hsq

end TauCeti.G2ShortRoot.IntegralToralClosure
