/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Simple Weyl representatives in the full-weight type-D spin carrier

The pinned word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` normalizes the weight torus in the full spin
carrier. Its conjugation action is the simple reflection of the named simply connected
root datum, in Bourbaki numbering, and it sends the positive simple-root subgroup at
that node to the negative one with negated parameter. All equations hold over arbitrary
commutative rings, including nonreduced rings and characteristic two.

Products along words transport torus points by the corresponding Weyl-word action.
These representatives supply the normalizer elements used to transport simple root
subgroups when constructing the other root subgroups. No independence of the chosen
word, normalizer-quotient identification, or identification of the carrier with an
independently pinned simply connected group is asserted.

The proofs specialize the integral Kostant conjugation theorems, using the existing
spin representation's `sl₂` triples and lattice weight equations. The formal organization
follows `TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic` and the Geck Weyl construction.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (hn : 4 ≤ n)

local notation "rootGen" => serreRootGenerator (CartanMatrix.D n)
local notation "cartanGen" => serreH ℚ (CartanMatrix.D n)

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the full spin carrier. -/
def simpleWeylPoint (i : Fin n) (A : Type v) [CommRing A] : points n hn A :=
  rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the specified product of pinned root-subgroup points. -/
theorem simpleWeylPoint_def (i : Fin n) (A : Type v) [CommRing A] :
    simpleWeylPoint n hn i A =
      rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

private theorem coe_simpleWeylPoint (i : Fin n) (A : Type v) [CommRing A] :
    (simpleWeylPoint n hn i A : Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      (kostantToralWeylPoint rootGen cartanGen (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
        (latticeBasis n) (basisWeight n) (.inl i) (.inr i) A :
          Matrix.GeneralLinearGroup (Fin (dimension n)) A) := by
  simp only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints]

/-- Simple Weyl representatives commute with change of value ring. -/
-- Use `rw`: simplification normalizes the presented carrier coercions before matching this lemma.
theorem map_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin n) :
    (pointsPresentation n hn A).map (pointsPresentation n hn B) f
        (simpleWeylPoint n hn i A) = simpleWeylPoint n hn i B := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- Conjugation by the representative sends the positive simple-root subgroup to the
negative one, negating its parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin n) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint n hn i A * rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint n hn i A)⁻¹ =
      rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := kostantToralWeylPoint_conj_rootSubgroupPoints
    rootGen cartanGen (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isSl2Triple_rep_rootGenerator n hn i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- Conjugation by the representative acts on the weight torus by the reflection
at the corresponding row of the type-D Cartan matrix. -/
theorem simpleWeylPoint_conj_weightTorusPoints_eq_weylReflectTorusPoint
    (i : Fin n) (A : Type v) [CommRing A]
    (s : Fin n → Aˣ) :
    simpleWeylPoint n hn i A * weightTorusPoints n hn A s *
        (simpleWeylPoint n hn i A)⁻¹ =
      weightTorusPoints n hn A (weylReflectTorusPoint (CartanMatrix.D n i) i s) := by
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i) (α := CartanMatrix.D n i)
    rootGen cartanGen (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isSl2Triple_rep_rootGenerator n hn i)
    (fun q ↦ by
      simpa only [TypeDStd.rootGeneratorWeight_inl] using
        TypeDStd.lie_serreH_serreRootGenerator n (.inl i) q)
    (fun q ↦ by
      simpa only [TypeDStd.rootGeneratorWeight_inr, Int.cast_neg, neg_smul] using
        TypeDStd.lie_serreH_serreRootGenerator n (.inr i) q)
    (isCartanWeightVector_latticeBasis n hn) A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val h

/-- The torus action is the simple reflection of the named simply connected type-D datum. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin n)
    (A : Type v) [CommRing A] (s : Fin n → Aˣ) :
    simpleWeylPoint n hn i A * weightTorusPoints n hn A s *
        (simpleWeylPoint n hn i A)⁻¹ =
      weightTorusPoints n hn A
        ((D n).geckSimpleReflectionTorusPoint (valid_D.mpr hn) i A s) := by
  -- Explicit indices keep rewriting at the named datum's definitionally equal rank.
  rw [(D n).geckSimpleReflectionTorusPoint_def (valid_D.mpr hn) i A,
    (D n).root_simpleIndex (valid_D.mpr hn) i, cartanMatrix_D]
  exact simpleWeylPoint_conj_weightTorusPoints_eq_weylReflectTorusPoint n hn i A s

/-- Every pinned simple Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin n) (A : Type v)
    [CommRing A] :
    simpleWeylPoint n hn i A ∈ Subgroup.normalizer (weightTorusPoints n hn A).range :=
  (weightTorusPoints n hn A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      ((D n).geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint
        (valid_D.mpr hn) i A))
    (simpleWeylPoint_conj_weightTorusPoints n hn i A)

/-! ## Products along words -/

/-- The full spin carrier point represented by a word in the simple reflections. -/
def weylWordPoint (l : List (Fin n)) (A : Type v) [CommRing A] : points n hn A :=
  (l.map fun i ↦ simpleWeylPoint n hn i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint n hn [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin n) (l : List (Fin n)) (A : Type v) [CommRing A] :
    weylWordPoint n hn (i :: l) A = simpleWeylPoint n hn i A * weylWordPoint n hn l A := by
  simp [weylWordPoint]

/-- Concatenation corresponds to multiplication of the representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin n)) (A : Type v) [CommRing A] :
    weylWordPoint n hn (l ++ l') A = weylWordPoint n hn l A * weylWordPoint n hn l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- Weyl-word representatives commute with change of value ring. -/
@[simp↓]
theorem map_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin n)) :
    (pointsPresentation n hn A).map (pointsPresentation n hn B) f (weylWordPoint n hn l A) =
      weylWordPoint n hn l B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [weylWordPoint_cons, map_mul, map_simpleWeylPoint, ih, weylWordPoint_cons]

/-- Conjugation by a Weyl-word representative realizes its abstract Weyl-word action
on the represented weight torus. -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin n))
    (A : Type v) [CommRing A] (s : Fin n → Aˣ) :
    weylWordPoint n hn l A * weightTorusPoints n hn A s * (weylWordPoint n hn l A)⁻¹ =
      weightTorusPoints n hn A ((D n).geckWeylWordTorusAction (valid_D.mpr hn) l A s) :=
  (D n).list_prod_conj_eq_geckWeylWordTorusAction (valid_D.mpr hn) _ _
    (simpleWeylPoint_conj_weightTorusPoints n hn · A) l s

/-- Every Weyl-word representative normalizes the weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin n))
    (A : Type v) [CommRing A] :
    weylWordPoint n hn l A ∈ Subgroup.normalizer (weightTorusPoints n hn A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints n hn i A)

end

end TauCeti.TypeDSpinCarrier
