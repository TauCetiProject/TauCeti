/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.E6.Minuscule.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Weyl representatives in the E₆ minuscule carrier

The pinned word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the twenty-seven-dimensional integral carrier
normalizes its weight torus and acts on it by the corresponding simple reflection of the
named simply connected root datum. It sends the positive simple root subgroup at its node
to the negative one, negating the parameter. Products of these representatives realize the
corresponding Weyl-word action on the torus over every commutative ring.

These equations supply the normalizer representatives used to transport numbered simple root
subgroups to nonsimple roots. Representatives are indexed by words, not Weyl-group elements:
no word independence in the carrier or splitting of the normalizer quotient is asserted.
Nor is the carrier identified here with an independently pinned reductive group.

The formal construction specializes the Kostant `sl₂` conjugation theorems, following
`TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic`. The torus reflection and word action are the
root-datum constructions in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic`;
they do not depend on a choice of representation.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

namespace TauCeti.E6Minuscule

open TauCeti.E6 DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)
local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)
local notation "rootGen" => serreRootGenerator weightTable.cartanMatrix
local notation "cartanGen" => serreH ℚ weightTable.cartanMatrix

private theorem representedSl2Triple (i : Fin 6) :
    IsSl2Triple
      (weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGen i)))
      (weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGen (.inl i))))
      (weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGen (.inr i)))) := by
  apply weightTable.isSl2Triple_rep_serreRootGenerator
  obtain ⟨a, ha⟩ := exists_e6MinusculeWeight_apply_eq_neg_one i
  exact ⟨a, by simp only [weightTable_weight, ha]; omega⟩

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the
E₆ minuscule carrier. -/
def simpleWeylPoint (i : Fin 6) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the specified product of pinned root-subgroup points. -/
theorem simpleWeylPoint_def (i : Fin 6) (A : Type v) [CommRing A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

private theorem coe_simpleWeylPoint (i : Fin 6) (A : Type v) [CommRing A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 27) A) =
      (kostantToralWeylPoint rootGen cartanGen weightTable.rep (Λ).toAddSubgroup
        weightTable.rep_kostantForm_mem_lattice weightTable.isNilpotent_rep_serreRootGenerator
        𝓑 weightTable.weight (.inl i) (.inr i) A :
          Matrix.GeneralLinearGroup (Fin 27) A) := by
  simp only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints]

/-- Simple Weyl representatives commute with change of value ring. -/
@[simp↓]
theorem map_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin 6) :
    (pointsPresentation A).map (pointsPresentation B) f (simpleWeylPoint i A) =
      simpleWeylPoint i B := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- Conjugation by the pinned representative sends the positive simple root subgroup
to the negative one and negates its parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 6) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := kostantToralWeylPoint_conj_rootSubgroupPoints
    rootGen cartanGen weightTable.rep (Λ).toAddSubgroup
    weightTable.rep_kostantForm_mem_lattice weightTable.isNilpotent_rep_serreRootGenerator
    𝓑 weightTable.weight (representedSl2Triple i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- Conjugation by a pinned Weyl representative realizes the corresponding simple
reflection of the named simply connected E₆ root datum on the weight torus. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 6) (A : Type v) [CommRing A]
    (s : Fin 6 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A (E6.geckSimpleReflectionTorusPoint valid_E6 i A s) := by
  rw [E6.geckSimpleReflectionTorusPoint_def valid_E6 i A,
    E6.root_simpleIndex valid_E6 i]
  -- Unfold E6.rank to 6, including in instance arguments, so the root-datum indices
  -- match the Kostant conjugation theorem's Fin 6 arguments.
  dsimp (config := { instances := true }) only [rank]
  simp only [cartanMatrix_E6]
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := fun q : Fin 6 ↦ CartanMatrix.E 6 i q)
    rootGen cartanGen weightTable.rep (Λ).toAddSubgroup
    weightTable.rep_kostantForm_mem_lattice weightTable.isNilpotent_rep_serreRootGenerator
    𝓑 weightTable.weight (representedSl2Triple i)
    (fun q ↦ by
      rw [weightTable_cartanMatrix]
      simpa only [E6.rootGeneratorWeight_inl] using lie_serreH_rootGenerator (.inl i) q)
    (fun q ↦ by
      rw [weightTable_cartanMatrix]
      simpa only [E6.rootGeneratorWeight_inr, Int.cast_neg, neg_smul] using
        lie_serreH_rootGenerator (.inr i) q)
    weightTable.isCartanWeightVector_coordinateLatticeBasis A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using congrArg Subtype.val h

/-- Every pinned simple Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 6) (A : Type v)
    [CommRing A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  (weightTorusPoints A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      (E6.geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint valid_E6 i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

/-! ## Products along words -/

/-- The product of the pinned representatives along a word in simple reflections. -/
def weylWordPoint (l : List (Fin 6)) (A : Type v) [CommRing A] : points A :=
  (l.map fun i ↦ simpleWeylPoint i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its simple Weyl representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin 6) (l : List (Fin 6)) (A : Type v) [CommRing A] :
    weylWordPoint (i :: l) A = simpleWeylPoint i A * weylWordPoint l A := by
  simp [weylWordPoint]

/-- Concatenation of words corresponds to multiplication of their representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin 6)) (A : Type v) [CommRing A] :
    weylWordPoint (l ++ l') A = weylWordPoint l A * weylWordPoint l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- Weyl-word representatives commute with change of value ring. -/
@[simp↓]
theorem map_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin 6)) :
    (pointsPresentation A).map (pointsPresentation B) f (weylWordPoint l A) =
      weylWordPoint l B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [weylWordPoint_cons, map_mul, map_simpleWeylPoint, ih, weylWordPoint_cons]

/-- Conjugation by a Weyl-word representative realizes its root-datum word action
on the represented weight torus. -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 6))
    (A : Type v) [CommRing A] (s : Fin 6 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A (E6.geckWeylWordTorusAction valid_E6 l A s) :=
  E6.list_prod_conj_eq_geckWeylWordTorusAction valid_E6 _ _
    (simpleWeylPoint_conj_weightTorusPoints · A) l s

/-- Every Weyl-word representative normalizes the represented weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 6))
    (A : Type v) [CommRing A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints i A)

end

end TauCeti.E6Minuscule
