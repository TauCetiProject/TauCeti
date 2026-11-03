/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Weyl representatives in the doubled minuscule E₆ carrier

`TauCeti.E6DoubledMinuscule.simpleWeylPoint` is the pinned word
`xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the full-weight carrier on `V(ϖ₁) ⊕ V(ϖ₆)`.
Its conjugation sends the positive simple-root parameter to the negative of that
parameter in the opposite subgroup, and acts on the rank-six weight torus by the
corresponding reflection of the named simply connected root datum.

`TauCeti.E6DoubledMinuscule.weylWordPoint` multiplies these representatives along
words. The conjugation and normalizer equations supply Weyl transport for constructing
nonsimple root subgroups. They hold over arbitrary commutative rings and are natural
under change of value ring. Representatives are indexed by words, not by Weyl elements:
no equality of lifts of different expressions, splitting of the torus normalizer, or
identification with an independently pinned reductive group is asserted.

The specialization follows
`TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic`, using the general integral conjugation
theorems `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_rootSubgroupPoints`
and `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_weightTorusPoints`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

namespace TauCeti.E6DoubledMinuscule

open DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "rootGen" => serreRootGenerator (Matrix.transpose (CartanMatrix.E 6))
local notation "cartanGen" => serreH ℚ (Matrix.transpose (CartanMatrix.E 6))

/-- The pinned representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the doubled E₆ carrier. -/
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

/-- The pinned word has the matrix of the generic Kostant representative. -/
private theorem coe_simpleWeylPoint (i : Fin 6) (A : Type v) [CommRing A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 54) A) =
      (kostantToralWeylPoint rootGen cartanGen rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis
        matrixWeight (.inl i) (.inr i) A : Matrix.GeneralLinearGroup (Fin 54) A) := by
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

/-- Conjugation by the pinned representative sends a positive simple-root point to the
matching negative simple-root point with negated parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 6) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := kostantToralWeylPoint_conj_rootSubgroupPoints
    rootGen cartanGen rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis
    matrixWeight (isSl2Triple_rep_serreRootGenerator i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- Conjugation by the pinned representative acts on the weight torus by the simple
reflection of the named simply connected E₆ root datum. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 6) (A : Type v) [CommRing A]
    (s : Fin 6 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A (E6.geckSimpleReflectionTorusPoint valid_E6 i A s) := by
  rw [E6.geckSimpleReflectionTorusPoint_def valid_E6 i A,
    E6.root_simpleIndex valid_E6 i]
  dsimp (config := { instances := true }) only [rank]
  simp only [cartanMatrix_E6]
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := fun j : Fin 6 ↦ CartanMatrix.E 6 i j)
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
    (isSl2Triple_rep_serreRootGenerator i)
    (fun q ↦ by
      simpa only [E6.rootGeneratorWeight_inl] using E6.lie_serreH_rootGenerator (.inl i) q)
    (fun q ↦ by
      simpa only [E6.rootGeneratorWeight_inr, Int.cast_neg, neg_smul] using
        E6.lie_serreH_rootGenerator (.inr i) q)
    isCartanWeightVector_matrixBasis A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val h

/-- Every pinned simple Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 6) (A : Type v)
    [CommRing A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  (weightTorusPoints A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      (E6.geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint valid_E6 i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

/-! ## Products along words -/

/-- The product of pinned Weyl representatives along a word in the six simple nodes. -/
def weylWordPoint (l : List (Fin 6)) (A : Type v) [CommRing A] : points A :=
  (l.map fun i ↦ simpleWeylPoint i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin 6) (l : List (Fin 6)) (A : Type v) [CommRing A] :
    weylWordPoint (i :: l) A = simpleWeylPoint i A * weylWordPoint l A := by
  simp [weylWordPoint]

/-- Concatenation of words corresponds to multiplication of representatives. -/
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

/-- Conjugation by a word representative realizes the corresponding root-datum Weyl-word
action on the weight torus. -/
@[simp↓]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 6))
    (A : Type v) [CommRing A] (s : Fin 6 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A (E6.geckWeylWordTorusAction valid_E6 l A s) :=
  E6.list_prod_conj_eq_geckWeylWordTorusAction valid_E6 _ _
    (simpleWeylPoint_conj_weightTorusPoints · A) l s

/-- Every word representative normalizes the weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 6))
    (A : Type v) [CommRing A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints i A)

end

end TauCeti.E6DoubledMinuscule
