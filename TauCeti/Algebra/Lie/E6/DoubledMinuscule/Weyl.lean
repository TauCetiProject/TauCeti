/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor
public import TauCeti.Algebra.Lie.E6.Minuscule.RootDatum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Simple Weyl representatives in the doubled minuscule E₆ carrier

The word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the fifty-four-dimensional carrier realizes the
simple reflection on its rank-six weight torus and carries the positive simple-root
subgroup to its negative, negating the parameter. Products along words realize the
corresponding Weyl-word action on the torus. These representatives supply normalizing
points for transporting numbered simple-root subgroups to other roots.

All equations hold over arbitrary commutative rings, including nonreduced rings and
rings of characteristic two or three. No word independence or splitting of the torus
normalizer is asserted. The carrier is not identified with an independently pinned
simply connected E₆ group scheme; transport to that group requires such an identification.

The construction follows `TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic`, specializing
`TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_weightTorusPoints`
to the doubled minuscule admissible lattice and its represented `sl₂` triples.
The torus action uses the named simply connected root datum, despite the historical
`geck` prefix of the shared root-datum action API.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4, 7.2 and 12.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate V.
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

/-- The pinned simple Weyl word in the doubled minuscule carrier. -/
def simpleWeylPoint (i : Fin 6) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the specified product of its pinned root-subgroup points. -/
theorem simpleWeylPoint_def (i : Fin 6) (A : Type v) [CommRing A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

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

/-- Conjugation by the pinned representative sends the positive simple-root subgroup to
its negative, negating the parameter. -/
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

/-- Conjugation by the pinned representative acts on the weight torus through the
corresponding simple reflection of the simply connected E₆ root datum. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 6) (A : Type v) [CommRing A]
    (s : Fin 6 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A (E6.geckSimpleReflectionTorusPoint valid_E6 i A s) := by
  rw [E6.geckSimpleReflectionTorusPoint_def valid_E6 i A,
    ← E6Minuscule.rootGeneratorWeight_inl_eq_root_simpleIndex valid_E6 i]
  dsimp (config := { instances := true }) only [rank]
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := E6.rootGeneratorWeight (.inl i))
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
    (isSl2Triple_rep_serreRootGenerator i)
    (E6.lie_serreH_rootGenerator (.inl i))
    (fun q ↦ by
      simpa only [E6.rootGeneratorWeight_inr_eq_neg_inl, Pi.neg_apply,
        Int.cast_neg, neg_smul] using E6.lie_serreH_rootGenerator (.inr i) q)
    isCartanWeightVector_matrixBasis A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val h

/-- Each pinned simple Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 6) (A : Type v)
    [CommRing A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  (weightTorusPoints A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      (E6.geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint valid_E6 i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

/-! ## Products along words -/

/-- The carrier point obtained by multiplying pinned representatives along a word. -/
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

/-- Conjugation by a Weyl-word representative realizes the abstract Weyl-word action
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

end TauCeti.E6DoubledMinuscule
