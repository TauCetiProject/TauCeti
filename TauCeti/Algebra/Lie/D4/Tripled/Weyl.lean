/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.D4.Tripled.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Weyl representatives in the tripled D₄ carrier

The pinned word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` normalizes the rank-four weight torus of the
24-dimensional tripled carrier. Conjugation realizes the simple reflection of the
simply connected type-D₄ root datum and sends the positive simple-root subgroup to its
opposite with negated parameter. These equations hold over every commutative ring.

Products of these representatives give explicit normalizing points for transporting
numbered simple-root subgroups toward nonsimple roots. Their torus action is the
corresponding Weyl-word action. No independence of the representative from the word,
splitting of the torus normalizer, or identification with an independently pinned
reductive group is asserted.

The proofs specialize the generic integral Kostant `sl₂` conjugation theorems. The formal
organization follows `TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
-/

public section

namespace TauCeti.D4Tripled

open DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "rootGen" => serreRootGenerator weightTable.cartanMatrix
local notation "cartanGen" => serreH ℚ weightTable.cartanMatrix

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the tripled D₄ carrier. -/
def simpleWeylPoint (i : Fin 4) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the specified product of pinned root-subgroup points. -/
theorem simpleWeylPoint_def (i : Fin 4) (A : Type v) [CommRing A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

private theorem coe_simpleWeylPoint (i : Fin 4) (A : Type v) [CommRing A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 24) A) =
      (kostantToralWeylPoint rootGen cartanGen rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
        d4TripledWeight (.inl i) (.inr i) A : Matrix.GeneralLinearGroup (Fin 24) A) := by
  simp only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints]

/-- Simple Weyl representatives commute with change of value ring. -/
@[simp↓]
theorem map_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin 4) :
    (pointsPresentation A).map (pointsPresentation B) f (simpleWeylPoint i A) =
      simpleWeylPoint i B := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- The pinned representative sends the positive simple-root subgroup to its opposite,
negating the parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 4) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := kostantToralWeylPoint_conj_rootSubgroupPoints
    rootGen cartanGen rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    d4TripledWeight (isSl2Triple_rep_serreRootGenerator i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- Conjugation by the pinned representative acts on the weight torus through the
matching simple reflection of the simply connected type-D₄ root datum. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 4) (A : Type v) [CommRing A]
    (s : Fin 4 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A ((D 4).geckSimpleReflectionTorusPoint (by decide) i A s) := by
  rw [(D 4).geckSimpleReflectionTorusPoint_def (by decide) i A,
    (D 4).root_simpleIndex (by decide) i]
  dsimp (config := { instances := true }) only [rank]
  simp only [cartanMatrix_D]
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := fun j : Fin 4 ↦ CartanMatrix.D 4 i j)
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
    (isSl2Triple_rep_serreRootGenerator i)
    (fun q ↦ by
      simpa only [TypeDStd.rootGeneratorWeight_inl] using
        lie_serreH_serreRootGenerator (.inl i) q)
    (fun q ↦ by
      simpa only [TypeDStd.rootGeneratorWeight_inr, Int.cast_neg, neg_smul] using
        lie_serreH_serreRootGenerator (.inr i) q)
    isCartanWeightVector_latticeBasis A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val h

/-- Every pinned simple Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 4) (A : Type v)
    [CommRing A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  (weightTorusPoints A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      ((D 4).geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint (by decide) i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

/-! ## Products along words -/

/-- The point of the tripled carrier represented by a word in the simple reflections. -/
def weylWordPoint (l : List (Fin 4)) (A : Type v) [CommRing A] : points A :=
  (l.map fun i ↦ simpleWeylPoint i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its simple Weyl representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin 4) (l : List (Fin 4)) (A : Type v) [CommRing A] :
    weylWordPoint (i :: l) A = simpleWeylPoint i A * weylWordPoint l A := by
  simp [weylWordPoint]

/-- Concatenation of words corresponds to multiplication of their representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin 4)) (A : Type v) [CommRing A] :
    weylWordPoint (l ++ l') A = weylWordPoint l A * weylWordPoint l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- Weyl-word representatives commute with change of value ring. -/
@[simp↓]
theorem map_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin 4)) :
    (pointsPresentation A).map (pointsPresentation B) f (weylWordPoint l A) =
      weylWordPoint l B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [weylWordPoint_cons, map_mul, map_simpleWeylPoint, ih, weylWordPoint_cons]

/-- Conjugation by a Weyl-word representative realizes the corresponding abstract Weyl-word
action on the weight torus. -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A ((D 4).geckWeylWordTorusAction (by decide) l A s) :=
  (D 4).list_prod_conj_eq_geckWeylWordTorusAction (by decide) _ _
    (simpleWeylPoint_conj_weightTorusPoints · A) l s

/-- Every Weyl-word representative normalizes the weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints i A)

end

end TauCeti.D4Tripled
