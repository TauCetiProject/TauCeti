/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Weyl

/-!
# Simple Weyl representatives of the short-root G₂ carrier

The pinned word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the integral seven-dimensional carrier normalizes its
weight torus. Its action is the simple reflection of the numbered simply connected root datum,
and it carries the positive root subgroup at that node to the negative one with parameter negated.
These equations hold over every commutative ring, including in characteristics two and three.
They supply normalizer representatives for transporting the simple root subgroups to other roots.

The construction uses the represented integral `sl₂` triples and the generic Kostant Weyl
conjugation theorems. It does not identify the carrier with an independently constructed pinned
simply connected group scheme. The characteristic-three generated carrier has the same matrix
words, but is treated separately in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Weyl`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The specialization of the Kostant Weyl equations follows
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic`.
-/

public section

namespace TauCeti.G2ShortRoot.IntegralToralClosure

open DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "rootGen" => TauCeti.serreRootGenerator CartanMatrix.G₂
local notation "cartanGen" => TauCeti.serreH ℚ CartanMatrix.G₂
local notation "node" => G2.simpleIndex valid_G2

/-- The simple Weyl representative at Bourbaki node `i`, with the pinned root parameters. -/
def simpleWeylPoint (i : Fin 2) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The simple representative is the word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)`. -/
theorem simpleWeylPoint_def (i : Fin 2) (A : Type v) [CommRing A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

/-- The simple representative exchanges the positive and negative root subgroups at its node,
negating the root parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (kostantToralWeylPoint_conj_rootSubgroupPoints
      rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
      isNilpotent_rep_serreRootGenerator latticeBasis weight
      (isSl2Triple_rep_serreRootGenerator i) A u)
  simpa only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix,
    coe_kostantToralRootSubgroupPoints] using h

/-- Conjugation by the simple representative acts on the weight torus by the reflection at the
named simple root and its simple-coroot coordinate. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 2) (A : Type v) [CommRing A]
    (s : Fin 2 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A
        (weylReflectTorusPoint (κ := Fin 2)
          ((G2.simplyConnectedRootDatum valid_G2).root (node i)) i s) := by
  classical
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (κ := Fin 2) (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := (G2.simplyConnectedRootDatum valid_G2).root (node i))
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator latticeBasis weight
    (isSl2Triple_rep_serreRootGenerator i)
    (lie_cartanGenerator_rootGenerator_inl_eq_root_simpleIndex i)
    (lie_cartanGenerator_rootGenerator_inr_eq_neg_root_simpleIndex i)
    isCartanWeightVector_latticeBasis A s
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_weightTorusPoints,
    coe_weightTorusPoints A (weylReflectTorusPoint (κ := Fin 2)
      ((G2.simplyConnectedRootDatum valid_G2).root (node i)) i s)]
  simpa only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix,
    coe_kostantToralRootSubgroupPoints, coe_kostantToralWeightTorusPoints] using
      congrArg Subtype.val h

/-- Reflection of torus parameters at a named simple root is an involution. -/
theorem weylReflectTorusPoint_root_simpleIndex_involutive (i : Fin 2) (A : Type v)
    [CommRing A] :
    Function.Involutive (weylReflectTorusPoint (κ := Fin 2)
      ((G2.simplyConnectedRootDatum valid_G2).root (node i)) i : (Fin 2 → Aˣ) → _) := by
  intro s
  apply weylReflectTorusPoint_weylReflectTorusPoint
  exact (congrFun (G2.root_simpleIndex valid_G2 i) i).trans
    (G2.cartanMatrix_apply_same i)

/-- Every simple Weyl representative normalizes the integral carrier's weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 2) (A : Type v)
    [CommRing A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range := by
  -- Conjugation maps the torus onto itself because the reflection is an involution.
  exact (weightTorusPoints A).mem_normalizer_range_of_surjective
    (weylReflectTorusPoint_root_simpleIndex_involutive i A).surjective
    (simpleWeylPoint_conj_weightTorusPoints i A)

end

end TauCeti.G2ShortRoot.IntegralToralClosure
