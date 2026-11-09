/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.E7.Minuscule.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Weyl representatives in the E₇ minuscule carrier

The pinned words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` normalize the weight torus of the
56-dimensional integral minuscule carrier. Their conjugation action is the simple
reflection of the named simply connected E₇ root datum. They also carry the positive
simple-root subgroup at their node to the negative one, negating its parameter.
Products along words realize the corresponding Weyl-word action on the torus.
Each representative lies in every subgroup containing the two unit-parameter root points at
its node (`TauCeti.E7Minuscule.simpleWeylPoint_mem`).

These equations supply normalizer representatives for transporting root subgroups and
recognizing the carrier's root datum. They hold over arbitrary commutative value rings,
including nonreduced rings and characteristic two. They do not identify the normalizer
quotient with the Weyl group or identify the carrier with the pinned simply connected
group scheme; transfer to that pinned group requires such an identification.

The construction specializes the Kostant toral-closure Weyl conjugation theorems and
follows `TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic`. The root-datum torus actions
`DynkinType.geckSimpleReflectionTorusPoint` and `DynkinType.geckWeylWordTorusAction`
are independent of the Geck representation and apply here without changing carriers.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

public section

namespace TauCeti.E7Minuscule

open DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "CM" => weightTable.cartanMatrix
local notation "rootGen" => serreRootGenerator CM
local notation "cartanGen" => serreH ℚ CM
local notation "rootWeight" => E7.rootGeneratorWeight valid_E7

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the
E₇ minuscule carrier. -/
def simpleWeylPoint (i : Fin 7) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the specified product of pinned root-subgroup points. -/
theorem simpleWeylPoint_def (i : Fin 7) (A : Type v) [CommRing A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

private theorem coe_simpleWeylPoint (i : Fin 7) (A : Type v) [CommRing A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 56) A) =
      (kostantToralWeylPoint rootGen cartanGen rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
        e7MinusculeWeight (.inl i) (.inr i) A : Matrix.GeneralLinearGroup (Fin 56) A) := by
  simp only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints]

/-- Simple Weyl representatives commute with change of value ring. -/
@[simp↓]
theorem map_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin 7) :
    (pointsPresentation A).map (pointsPresentation B) f (simpleWeylPoint i A) =
      simpleWeylPoint i B := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- Conjugation by the pinned representative sends its positive simple-root subgroup
to the negative one and negates the parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 7) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := kostantToralWeylPoint_conj_rootSubgroupPoints
    rootGen cartanGen rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e7MinusculeWeight (isSl2Triple_rep_serreRootGenerator i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- Conjugation by the pinned representative realizes the simple reflection of the
named simply connected E₇ root datum on weight-torus points. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 7) (A : Type v) [CommRing A]
    (s : Fin 7 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A (E7.geckSimpleReflectionTorusPoint valid_E7 i A s) := by
  rw [E7.geckSimpleReflectionTorusPoint_def valid_E7 i A,
    E7.root_simpleIndex valid_E7 i]
  -- The root-datum action uses Fintype/DecidableEq instances on Fin E7.rank, while the
  -- carrier uses Fin 7. Normalize rank inside those instance arguments too, so both
  -- reflection homomorphisms use the same instances; rewriting rank_E7 alone leaves them.
  dsimp (config := { instances := true }) only [rank]
  simp only [cartanMatrix_E7]
  have hpos (q : Fin 7) : rootWeight (.inl i) q = CartanMatrix.E 7 i q := by
    simpa only [rank_E7, cartanMatrix_E7] using
      E7.rootGeneratorWeight_inl (ht := valid_E7) i q
  have hneg (q : Fin 7) : rootWeight (.inr i) q = -CartanMatrix.E 7 i q := by
    simpa only [rank_E7, cartanMatrix_E7] using
      E7.rootGeneratorWeight_inr (ht := valid_E7) i q
  have h := kostantToralWeylPoint_conj_weightTorusPoints_of_rootWeight
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := fun j : Fin 7 ↦ CartanMatrix.E 7 i j)
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator latticeBasis e7MinusculeWeight
    (isSl2Triple_rep_serreRootGenerator i) rootWeight
    lie_cartanGenerator_rootGenerator hpos hneg
    isCartanWeightVector_latticeBasis A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val h

/-- Every pinned simple Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 7) (A : Type v)
    [CommRing A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  (weightTorusPoints A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      (E7.geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint valid_E7 i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

/-! ## Products along words -/

/-- The product of pinned simple Weyl representatives along a word, in list order. -/
def weylWordPoint (l : List (Fin 7)) (A : Type v) [CommRing A] : points A :=
  (l.map fun i ↦ simpleWeylPoint i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its simple Weyl representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin 7) (l : List (Fin 7)) (A : Type v) [CommRing A] :
    weylWordPoint (i :: l) A = simpleWeylPoint i A * weylWordPoint l A := by
  simp [weylWordPoint]

/-- Concatenation corresponds to multiplication of representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin 7)) (A : Type v) [CommRing A] :
    weylWordPoint (l ++ l') A = weylWordPoint l A * weylWordPoint l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- Weyl-word representatives commute with change of value ring. -/
@[simp↓]
theorem map_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin 7)) :
    (pointsPresentation A).map (pointsPresentation B) f (weylWordPoint l A) =
      weylWordPoint l B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [weylWordPoint_cons, map_mul, map_simpleWeylPoint, ih, weylWordPoint_cons]

/-- Conjugation by a Weyl-word representative realizes the corresponding root-datum
Weyl-word action on the weight torus. -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 7))
    (A : Type v) [CommRing A] (s : Fin 7 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A (E7.geckWeylWordTorusAction valid_E7 l A s) :=
  E7.list_prod_conj_eq_geckWeylWordTorusAction valid_E7 _ _
    (simpleWeylPoint_conj_weightTorusPoints · A) l s

/-- Every Weyl-word representative normalizes the weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 7))
    (A : Type v) [CommRing A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints i A)

/-- Every subgroup containing the unit-parameter root points `xᵢ(1)` and `x₋ᵢ(1)` contains the
simple Weyl representative at `i`. -/
theorem simpleWeylPoint_mem {A : Type v} [CommRing A] {H : Subgroup (points A)} (i : Fin 7)
    (hx : rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) ∈ H)
    (hy : rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd 1) ∈ H) :
    simpleWeylPoint i A ∈ H := by
  rw [simpleWeylPoint_def, ofAdd_neg, map_inv]
  exact H.mul_mem (H.mul_mem hx (H.inv_mem hy)) hx

end

end TauCeti.E7Minuscule
