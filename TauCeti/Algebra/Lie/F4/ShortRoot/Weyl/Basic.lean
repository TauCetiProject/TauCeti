/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.F4.ShortRoot.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Simple Weyl representatives in the short-root F₄ carrier

The pinned word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` normalizes the weight torus of the
twenty-six-dimensional integral carrier. Its action is the simple reflection of the
simply connected type-F₄ root datum, and it sends the corresponding positive
root subgroup to the negative one, negating the parameter. All equations hold over every
commutative ring, including rings with nilpotents and rings of characteristic two.

These explicit representatives allow simple root subgroups to be transported along
reflections when constructing nonsimple root subgroups. Their products along words in the
simple reflections act on the weight torus through the corresponding Weyl-word action and
normalize it. They do not identify the
normalizer quotient with the Weyl group or identify the carrier with a pinned reductive group.

The proofs specialize the integral `sl₂` conjugation results in
`TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_weightTorusPoints`.
The corresponding formal template is
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.F4ShortRoot

open DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "rootGen" => serreRootGenerator CartanMatrix.F₄.transpose
local notation "cartanGen" => serreH ℚ CartanMatrix.F₄.transpose
local notation "rootWeight" => F4.rootGeneratorWeight valid_F4

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the
short-root type-F₄ carrier. -/
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

/-- The matrix of the pinned Weyl word is the matrix of the generic Kostant representative. -/
private theorem coe_simpleWeylPoint (i : Fin 4) (A : Type v) [CommRing A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 26) A) =
      (kostantToralWeylPoint rootGen cartanGen rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
        f4ShortRootWeight (.inl i) (.inr i) A : Matrix.GeneralLinearGroup (Fin 26) A) := by
  simp only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints]

/-- Simple Weyl representatives commute with change of value ring. -/
-- Use `rw`: simplification normalizes the presented carrier coercions before matching this lemma.
theorem map_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin 4) :
    (pointsPresentation A).map (pointsPresentation B) f (simpleWeylPoint i A) =
      simpleWeylPoint i B := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- Conjugation by the pinned representative sends the positive simple root subgroup
to the negative one and negates its parameter. -/
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
    f4ShortRootWeight (isSl2Triple_rep_serreRootGenerator i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- Conjugation by the pinned Weyl representative acts on the weight torus through the
matching simple reflection of the simply connected root datum. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 4) (A : Type v) [CommRing A]
    (s : Fin 4 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A (F4.geckSimpleReflectionTorusPoint valid_F4 i A s) := by
  rw [F4.geckSimpleReflectionTorusPoint_def valid_F4 i A,
    F4.root_simpleIndex valid_F4 i]
  dsimp (config := { instances := true }) only [rank]
  simp only [cartanMatrix_F4]
  have hpos (q : Fin 4) : rootWeight (.inl i) q = CartanMatrix.F₄ i q := by
    simpa only [rank_F4, cartanMatrix_F4] using
      F4.rootGeneratorWeight_inl (ht := valid_F4) i q
  have hneg (q : Fin 4) : rootWeight (.inr i) q = -CartanMatrix.F₄ i q := by
    simpa only [rank_F4, cartanMatrix_F4] using
      F4.rootGeneratorWeight_inr (ht := valid_F4) i q
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := fun j : Fin 4 ↦ CartanMatrix.F₄ i j)
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator latticeBasis f4ShortRootWeight
    (isSl2Triple_rep_serreRootGenerator i)
    (fun q ↦ by rw [← hpos q]; exact lie_cartanGenerator_rootGenerator (.inl i) q)
    (fun q ↦ by
      calc
        ⁅cartanGen q, rootGen (.inr i)⁆ =
            ((rootWeight (.inr i) q : ℤ) : ℚ) • rootGen (.inr i) :=
          lie_cartanGenerator_rootGenerator (.inr i) q
        _ = -((CartanMatrix.F₄ i q : ℤ) : ℚ) • rootGen (.inr i) := by
          rw [hneg q, Int.cast_neg]
        _ = _ := neg_smul _ _)
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
      (F4.geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint valid_F4 i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

/-! ## Products along words -/

/-- **The point of the short-root carrier represented by a word in the simple reflections.** -/
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

/-- **Conjugation by a Weyl-word representative realizes the corresponding abstract Weyl-word
action on the represented weight torus.** -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A (F4.geckWeylWordTorusAction valid_F4 l A s) :=
  F4.list_prod_conj_eq_geckWeylWordTorusAction valid_F4 _ _
    (simpleWeylPoint_conj_weightTorusPoints · A) l s

/-- Every Weyl-word representative normalizes the represented weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints i A)

end

end TauCeti.F4ShortRoot
