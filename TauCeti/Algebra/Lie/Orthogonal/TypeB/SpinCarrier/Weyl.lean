/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Normalizer
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic

/-!
# Weyl representatives in the full-weight type-B spin carrier

The pinned words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` normalize the represented weight torus. Their
conjugation action is the simple reflection attached to the Bourbaki-numbered root and
coroot of the simply connected type-B datum. Conjugation also sends the corresponding
positive simple-root subgroup to the negative one, negating its parameter.

Products of these representatives transport the torus by the existing Weyl-word action.
They provide the normalizer elements needed to transport numbered simple-root subgroups
to nonsimple roots. The representatives and their equations work over arbitrary commutative
rings, including nonreduced rings and characteristic two. No identification of the
normalizer quotient with the Weyl group, or of the carrier with an independently pinned
simply connected group scheme, is asserted.

The proofs specialize the integral Kostant `sl₂` conjugation theorems and follow
`TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic` and
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ)

local notation "rootGen" => TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ)
local notation "cartanGen" => TauCeti.typeBSimpleCorootGenerator (K := ℚ)

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the full-spin carrier. -/
def simpleWeylPoint (i : Fin (n + 1)) (A : Type v) [CommRing A] : points n A :=
  rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the specified word in the pinned root subgroups. -/
theorem simpleWeylPoint_def (i : Fin (n + 1)) (A : Type v) [CommRing A] :
    simpleWeylPoint n i A =
      rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

private theorem coe_simpleWeylPoint (i : Fin (n + 1)) (A : Type v) [CommRing A] :
    (simpleWeylPoint n i A : Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      (kostantToralWeylPoint rootGen cartanGen (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n) (latticeBasis n)
        (basisWeight n) (.inl i) (.inr i) A :
          Matrix.GeneralLinearGroup (Fin (dimension n)) A) := by
  simp only [simpleWeylPoint_def, kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints]

/-- Simple Weyl representatives commute with change of value ring. -/
-- As for `map_rootSubgroupPoints`, use `rw` to avoid premature coercion normalization.
theorem map_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin (n + 1)) :
    (pointsPresentation n A).map (pointsPresentation n B) f (simpleWeylPoint n i A) =
      simpleWeylPoint n i B := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- Conjugation by the pinned representative exchanges the positive simple-root subgroup
with its negative, negating the parameter. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin (n + 1)) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint n i A * rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint n i A)⁻¹ =
      rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := kostantToralWeylPoint_conj_rootSubgroupPoints
    rootGen cartanGen (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n) (latticeBasis n)
    (basisWeight n) (isSl2Triple_rep_rootGenerator n i) A u
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using
    congrArg Subtype.val h

/-- The pinned Weyl representative reflects the weight torus by the corresponding Cartan row
and simple-coroot coordinate. This equation also includes the rank-one spin carrier. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin (n + 1)) (A : Type v) [CommRing A]
    (s : Fin (n + 1) → Aˣ) :
    simpleWeylPoint n i A * weightTorusPoints n A s * (simpleWeylPoint n i A)⁻¹ =
      weightTorusPoints n A (weylReflectTorusPoint (CartanMatrix.B (n + 1) i) i s) := by
  have hpos (q : Fin (n + 1)) :
      ⁅cartanGen q, rootGen (.inl i)⁆ = (CartanMatrix.B (n + 1) i q : ℚ) • rootGen (.inl i) := by
    simpa only [rootGeneratorWeight_inl] using lie_coroot_rootGenerator n (.inl i) q
  have hneg (q : Fin (n + 1)) :
      ⁅cartanGen q, rootGen (.inr i)⁆ = -((CartanMatrix.B (n + 1) i q : ℚ) •
        rootGen (.inr i)) := by
    simpa only [rootGeneratorWeight_inr, Pi.neg_apply, Int.cast_neg, neg_smul] using
      lie_coroot_rootGenerator n (.inr i) q
  have h := kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    rootGen cartanGen (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n) (latticeBasis n)
    (basisWeight n) (isSl2Triple_rep_rootGenerator n i) hpos hneg
    (isCartanWeightVector_latticeBasis n) A s
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using
    congrArg Subtype.val h

/-- Every pinned simple Weyl representative normalizes the represented weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin (n + 1)) (A : Type v)
    [CommRing A] :
    simpleWeylPoint n i A ∈ Subgroup.normalizer (weightTorusPoints n A).range :=
  (weightTorusPoints n A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      (weylReflectTorusPoint_weylReflectTorusPoint _ (CartanMatrix.B_diag _ i)))
    (simpleWeylPoint_conj_weightTorusPoints n i A)

variable (ht : (DynkinType.B (n + 1)).Valid)

/-- On every valid type-B diagram, the torus action is the simple reflection of the named
simply connected root datum, in its existing Bourbaki numbering. -/
theorem simpleWeylPoint_conj_weightTorusPoints_simpleReflection (i : Fin (n + 1))
    (A : Type v) [CommRing A] (s : Fin (n + 1) → Aˣ) :
    simpleWeylPoint n i A * weightTorusPoints n A s * (simpleWeylPoint n i A)⁻¹ =
      weightTorusPoints n A
        ((DynkinType.B (n + 1)).geckSimpleReflectionTorusPoint ht i A s) := by
  rw [(DynkinType.B (n + 1)).geckSimpleReflectionTorusPoint_def ht i A,
    ← rootGeneratorWeight_inl_eq_root_simpleIndex n ht i, rootGeneratorWeight_inl]
  exact simpleWeylPoint_conj_weightTorusPoints n i A s

/-! ## Products along words -/

/-- The point of the full-spin carrier represented by a word in the simple reflections. -/
def weylWordPoint (l : List (Fin (n + 1))) (A : Type v) [CommRing A] : points n A :=
  (l.map fun i ↦ simpleWeylPoint n i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint n [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its simple Weyl representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin (n + 1)) (l : List (Fin (n + 1))) (A : Type v) [CommRing A] :
    weylWordPoint n (i :: l) A = simpleWeylPoint n i A * weylWordPoint n l A := by
  simp [weylWordPoint]

/-- Concatenating words multiplies their representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin (n + 1))) (A : Type v) [CommRing A] :
    weylWordPoint n (l ++ l') A = weylWordPoint n l A * weylWordPoint n l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- Weyl-word representatives commute with change of value ring. -/
@[simp↓]
theorem map_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin (n + 1))) :
    (pointsPresentation n A).map (pointsPresentation n B) f (weylWordPoint n l A) =
      weylWordPoint n l B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [weylWordPoint_cons, map_mul, map_simpleWeylPoint, ih, weylWordPoint_cons]

/-- Conjugation by a word representative realizes the existing Weyl-word action on the torus
of the named simply connected type-B datum. -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin (n + 1)))
    (A : Type v) [CommRing A] (s : Fin (n + 1) → Aˣ) :
    weylWordPoint n l A * weightTorusPoints n A s * (weylWordPoint n l A)⁻¹ =
      weightTorusPoints n A ((DynkinType.B (n + 1)).geckWeylWordTorusAction ht l A s) :=
  (DynkinType.B (n + 1)).list_prod_conj_eq_geckWeylWordTorusAction ht _ _
    (simpleWeylPoint_conj_weightTorusPoints_simpleReflection n ht · A) l s

/-- Every Weyl-word representative normalizes the represented weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin (n + 1)))
    (A : Type v) [CommRing A] :
    weylWordPoint n l A ∈ Subgroup.normalizer (weightTorusPoints n A).range :=
  Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints n i A)

end

end TauCeti.TypeBSpinCarrier
