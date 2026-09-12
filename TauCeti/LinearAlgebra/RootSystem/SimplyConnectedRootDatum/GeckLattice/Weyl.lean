/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Weyl
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PointsFunctor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.RootDatum

/-!
# Weyl words in the Geck carrier

For a valid Dynkin type, the numbered raising and lowering generators in the Geck carrier form an
`sl₂` pair at every Bourbaki node.  The usual product

```text
nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)
```

therefore gives a point of the carrier which normalizes its represented weight torus and acts on
that torus by the corresponding simple reflection.  This file specializes the general Kostant
toral-closure construction to the pinned Geck data and multiplies the resulting representatives
along a word in the simple reflections.

The construction is deliberately indexed by words, not by Weyl-group elements: proving that two
words representing the same Weyl element induce the same torus action is a root-datum calculation,
while equality of their carrier representatives is false without accounting for the torus kernel.
The word-level representative is the input needed to transport the numbered simple root subgroups
to nonsimple roots and to construct the normalizer-to-Weyl-group comparison.

## Main declarations

* `TauCeti.DynkinType.geckSimpleWeylPoint`: the pinned representative attached to one Bourbaki
  node.
* `TauCeti.DynkinType.geckWeylWordPoint`: the product of the pinned representatives along a word.
* `TauCeti.DynkinType.geckWeylWordTorusAction`: the corresponding composite of simple reflections
  on split-torus points.
* `TauCeti.DynkinType.geckWeylWordPoint_conj_geckWeightTorusPoints`: conjugation by the word
  representative realizes that composite action.
* `TauCeti.DynkinType.geckWeylWordPoint_mem_normalizer_geckWeightTorusPoints`: every word
  representative normalizes the represented torus.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.

This advances the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.  Its consumer is the pinned ambient group required by
milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open TensorProduct

namespace TauCeti.DynkinType

universe v v'

noncomputable section

-- Matrices form a Lie ring through their commutator in the defining Geck representation.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-! ## A simple Weyl representative -/

private theorem coe_geckRootSubgroupParam (k : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (UniversalEnvelopingAlgebra.kostantRootSubgroupParam
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) k
        (t.isNilpotent_geckRepresentation_rootGenerator ht k) (CommAlgCat.of ℤ A) u :
      Module.End A (A ⊗[ℤ] (t.geckCoordinateLattice ht).toAddSubgroup)) =
      TauCeti.baseChangeExp
        (t.geckRepresentation ht
          (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator k)))
        (t.geckCoordinateLattice ht).toAddSubgroup
        (fun n _ hv ↦
          UniversalEnvelopingAlgebra.dividedPower_apply_mem_of_kostantForm_apply_mem
            (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
            (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) k n hv)
        (Multiplicative.toAdd u) := by
  apply LinearMap.ext
  intro z
  exact UniversalEnvelopingAlgebra.kostantRootSubgroupParam_val_apply
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) k
    (t.isNilpotent_geckRepresentation_rootGenerator ht k) (CommAlgCat.of ℤ A) u z

/-- The defining representation carries the numbered `sl₂` triple at node `i` to an `sl₂` triple
of endomorphisms of the Geck module.  Faithfulness on the Lie algebra supplies the nonvanishing
condition required when mapping an `sl₂` triple. -/
theorem isSl2Triple_geckRepresentation (i : Fin t.rank) :
    IsSl2Triple
      (t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).h i)))
      (t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator (.inl i))))
      (t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator (.inr i)))) := by
  simpa only [LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
    ((t.lieBasis ht).sl2 i).map
      ((t.geckRepresentation ht).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))
      (by
        intro hzero
        apply ((t.lieBasis ht).sl2 i).h_ne_zero
        apply t.geckRepresentation_ι_injective ht
        simpa only [LieHom.comp_apply, AlgHom.toLieHom_apply, map_zero] using hzero)

/-- **The pinned simple Weyl representative in the Geck carrier.**  At node `i` this is
`xᵢ(1) x₋ᵢ(-1) xᵢ(1)`. -/
def geckSimpleWeylPoint (i : Fin t.rank) (A : Type v) [CommRing A] : t.geckPoints ht A :=
  t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd 1) *
    t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-1)) *
    t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd 1)

/-- The simple Weyl representative is the product of the three indicated pinned root-subgroup
points. -/
theorem geckSimpleWeylPoint_eq (i : Fin t.rank) (A : Type v) [CommRing A] :
    t.geckSimpleWeylPoint ht i A =
      t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd 1) *
        t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-1)) *
        t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd 1) :=
  by rw [geckSimpleWeylPoint]

/-- In the Geck coordinate basis, the simple Weyl representative is the integral Weyl
automorphism supplied by the corresponding numbered `sl₂` pair. -/
@[simp]
theorem coe_geckSimpleWeylPoint (i : Fin t.rank) (A : Type v) [CommRing A] :
    (t.geckSimpleWeylPoint ht i A :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      Units.map (LinearMap.toMatrixAlgEquiv
          ((t.geckCoordinateBasisFin ht).baseChange A)).toMulEquiv
        (UniversalEnvelopingAlgebra.kostantWeylGL
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
          (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
          (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i)) A) := by
  rw [geckSimpleWeylPoint_eq, Subgroup.coe_mul, Subgroup.coe_mul,
    t.coe_geckRootSubgroupPoints ht (.inl i) A,
    t.coe_geckRootSubgroupPoints ht (.inr i) A]
  let F := Units.map (LinearMap.toMatrixAlgEquiv
    ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom
  rw [← UniversalEnvelopingAlgebra.basisMatrix_kostantRootSubgroupParam
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) A (.inl i) (Multiplicative.ofAdd 1),
    ← UniversalEnvelopingAlgebra.basisMatrix_kostantRootSubgroupParam
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) A (.inr i) (Multiplicative.ofAdd (-1))]
  change F _ * F _ * F _ = F _
  rw [← map_mul, ← map_mul]
  refine congrArg F (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, t.coe_geckRootSubgroupParam ht (.inl i) A,
    t.coe_geckRootSubgroupParam ht (.inr i) A, toAdd_ofAdd,
    UniversalEnvelopingAlgebra.kostantWeylGL_val]
  exact (UniversalEnvelopingAlgebra.kostantWeylPoints_toLinearMap_eq
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i)) (A := A)).symm

/-- The simple Weyl representative is natural in the value ring. -/
@[simp]
theorem geckPointsMap_geckSimpleWeylPoint {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) (i : Fin t.rank) :
    t.geckPointsMap ht f (t.geckSimpleWeylPoint ht i A) =
      t.geckSimpleWeylPoint ht i B := by
  simp [geckSimpleWeylPoint]

/-- Conjugation by the simple Weyl representative exchanges the raising root subgroup at node
`i` with its lowering root subgroup and negates the parameter. -/
theorem geckSimpleWeylPoint_conj_geckRootSubgroupPoints (i : Fin t.rank)
    (A : Type v) [CommRing A] (u : A) :
    t.geckSimpleWeylPoint ht i A *
        t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd u) *
        (t.geckSimpleWeylPoint ht i A)⁻¹ =
      t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_rootSubgroupPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (t.isSl2Triple_geckRepresentation ht i) A u
  have hmatrix := congrArg Subtype.val h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_geckSimpleWeylPoint,
    coe_geckRootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeylPoint,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using hmatrix

/-! ## The action on the represented torus -/

/-- The simple reflection at node `i`, acting on points of the pinned split torus. -/
def geckSimpleReflectionTorusPoint (i : Fin t.rank) (A : Type v) [CommRing A] :
    (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  TauCeti.weylReflectTorusPoint
    ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) i

/-- Conjugation by the simple Weyl representative realizes the corresponding reflection on the
represented weight torus. -/
theorem geckSimpleWeylPoint_conj_geckWeightTorusPoints (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.geckSimpleWeylPoint ht i A * t.geckWeightTorusPoints ht A s *
        (t.geckSimpleWeylPoint ht i A)⁻¹ =
      t.geckWeightTorusPoints ht A (t.geckSimpleReflectionTorusPoint ht i A s) := by
  classical
  have h := UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_weightTorusPoints
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i))
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (t.isSl2Triple_geckRepresentation ht i)
    (fun q ↦ by
      rw [← t.rootGeneratorWeight_inl_eq_root_simpleIndex ht i]
      exact t.lie_lieBasis_h_rootGenerator ht (.inl i) q)
    (fun q ↦ by
      have hneg := t.lie_lieBasis_h_rootGenerator ht (.inr i) q
      rw [t.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i,
        Pi.neg_apply, Int.cast_neg, neg_smul] at hneg
      exact hneg)
    (t.isCartanWeightVector_geckCoordinateBasisFin ht) A s
  apply Subtype.ext
  have hmatrix := congrArg Subtype.val h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_geckSimpleWeylPoint,
    coe_geckWeightTorusPoints, geckSimpleReflectionTorusPoint,
    UniversalEnvelopingAlgebra.coe_kostantToralWeylPoint,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using hmatrix

/-- Every pinned simple Weyl representative normalizes the represented weight torus. -/
theorem geckSimpleWeylPoint_mem_normalizer_geckWeightTorusPoints (i : Fin t.rank)
    (A : Type v) [CommRing A] :
    t.geckSimpleWeylPoint ht i A ∈
      Subgroup.normalizer (t.geckWeightTorusPoints ht A).range := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨t.geckSimpleReflectionTorusPoint ht i A s,
      (t.geckSimpleWeylPoint_conj_geckWeightTorusPoints ht i A s).symm⟩
  · rintro ⟨s, hs⟩
    let r := t.geckSimpleReflectionTorusPoint ht i A
    have hroot :
        (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) i = 2 := by
      rw [t.root_simpleIndex ht]
      exact t.cartanMatrix_apply_same i
    have hinvol : r (r s) = s := by
      exact TauCeti.weylReflectTorusPoint_weylReflectTorusPoint _ hroot s
    have hreflect :=
      t.geckSimpleWeylPoint_conj_geckWeightTorusPoints ht i A (r s)
    change t.geckSimpleWeylPoint ht i A * t.geckWeightTorusPoints ht A (r s) *
        (t.geckSimpleWeylPoint ht i A)⁻¹ = t.geckWeightTorusPoints ht A (r (r s)) at hreflect
    rw [hinvol] at hreflect
    refine ⟨r s, ?_⟩
    apply (MulAut.conj (t.geckSimpleWeylPoint ht i A)).injective
    simpa only [MulAut.conj_apply] using hreflect.trans hs

/-! ## Products along words -/

/-- **The representative in the Geck carrier spelled by a word in the simple reflections.** -/
def geckWeylWordPoint (l : List (Fin t.rank)) (A : Type v) [CommRing A] : t.geckPoints ht A :=
  (l.map fun i ↦ t.geckSimpleWeylPoint ht i A).prod

/-- The empty Weyl word represents the identity point. -/
@[simp]
theorem geckWeylWordPoint_nil (A : Type v) [CommRing A] :
    t.geckWeylWordPoint ht [] A = 1 :=
  by simp [geckWeylWordPoint]

/-- Prepending a node multiplies its simple representative on the left. -/
@[simp]
theorem geckWeylWordPoint_cons (i : Fin t.rank) (l : List (Fin t.rank))
    (A : Type v) [CommRing A] :
    t.geckWeylWordPoint ht (i :: l) A =
      t.geckSimpleWeylPoint ht i A * t.geckWeylWordPoint ht l A :=
  by simp [geckWeylWordPoint]

/-- Concatenation of Weyl words corresponds to multiplication of their representatives. -/
@[simp]
theorem geckWeylWordPoint_append (l l' : List (Fin t.rank))
    (A : Type v) [CommRing A] :
    t.geckWeylWordPoint ht (l ++ l') A =
      t.geckWeylWordPoint ht l A * t.geckWeylWordPoint ht l' A := by
  simp only [geckWeylWordPoint, List.map_append, List.prod_append]

/-- The Weyl-word representative is natural in the value ring. -/
@[simp]
theorem geckPointsMap_geckWeylWordPoint {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) (l : List (Fin t.rank)) :
    t.geckPointsMap ht f (t.geckWeylWordPoint ht l A) =
      t.geckWeylWordPoint ht l B := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- **The action on split-torus points spelled by a word in simple reflections.**  The recursion
has the same multiplication order as `geckWeylWordPoint`: the head reflection acts last on the
parameter obtained from the tail when the corresponding product acts by conjugation. -/
def geckWeylWordTorusAction (l : List (Fin t.rank)) (A : Type v) [CommRing A] :
    (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  l.foldr (fun i f ↦ (t.geckSimpleReflectionTorusPoint ht i A).comp f) (MonoidHom.id _)

/-- The empty word acts identically on split-torus points. -/
@[simp]
theorem geckWeylWordTorusAction_nil (A : Type v) [CommRing A] :
    t.geckWeylWordTorusAction ht [] A = MonoidHom.id _ :=
  by simp [geckWeylWordTorusAction]

/-- Prepending a node composes its simple reflection on the left. -/
@[simp]
theorem geckWeylWordTorusAction_cons (i : Fin t.rank) (l : List (Fin t.rank))
    (A : Type v) [CommRing A] :
    t.geckWeylWordTorusAction ht (i :: l) A =
      (t.geckSimpleReflectionTorusPoint ht i A).comp
        (t.geckWeylWordTorusAction ht l A) :=
  by simp [geckWeylWordTorusAction]

/-- Concatenation of words corresponds to composition of their torus actions. -/
@[simp]
theorem geckWeylWordTorusAction_append (l l' : List (Fin t.rank))
    (A : Type v) [CommRing A] :
    t.geckWeylWordTorusAction ht (l ++ l') A =
      (t.geckWeylWordTorusAction ht l A).comp
        (t.geckWeylWordTorusAction ht l' A) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.cons_append, geckWeylWordTorusAction_cons,
        geckWeylWordTorusAction_cons, ih]
      rfl

/-- **Conjugation by a Weyl-word representative realizes the word's action on the represented
weight torus.** -/
theorem geckWeylWordPoint_conj_geckWeightTorusPoints (l : List (Fin t.rank))
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.geckWeylWordPoint ht l A * t.geckWeightTorusPoints ht A s *
        (t.geckWeylWordPoint ht l A)⁻¹ =
      t.geckWeightTorusPoints ht A (t.geckWeylWordTorusAction ht l A s) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [geckWeylWordPoint_cons]
      calc
        (t.geckSimpleWeylPoint ht i A * t.geckWeylWordPoint ht l A) *
              t.geckWeightTorusPoints ht A s *
              (t.geckSimpleWeylPoint ht i A * t.geckWeylWordPoint ht l A)⁻¹ =
            t.geckSimpleWeylPoint ht i A *
              (t.geckWeylWordPoint ht l A * t.geckWeightTorusPoints ht A s *
                (t.geckWeylWordPoint ht l A)⁻¹) *
              (t.geckSimpleWeylPoint ht i A)⁻¹ := by group
        _ = t.geckSimpleWeylPoint ht i A *
              t.geckWeightTorusPoints ht A (t.geckWeylWordTorusAction ht l A s) *
              (t.geckSimpleWeylPoint ht i A)⁻¹ := by rw [ih]
        _ = t.geckWeightTorusPoints ht A
              (t.geckSimpleReflectionTorusPoint ht i A
                (t.geckWeylWordTorusAction ht l A s)) :=
          t.geckSimpleWeylPoint_conj_geckWeightTorusPoints ht i A _
        _ = t.geckWeightTorusPoints ht A
              (t.geckWeylWordTorusAction ht (i :: l) A s) := by
          rw [geckWeylWordTorusAction_cons]
          rfl

/-- **Every Weyl-word representative normalizes the represented weight torus.** -/
theorem geckWeylWordPoint_mem_normalizer_geckWeightTorusPoints (l : List (Fin t.rank))
    (A : Type v) [CommRing A] :
    t.geckWeylWordPoint ht l A ∈
      Subgroup.normalizer (t.geckWeightTorusPoints ht A).range := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons i l ih =>
      rw [geckWeylWordPoint_cons]
      exact Subgroup.mul_mem _
        (t.geckSimpleWeylPoint_mem_normalizer_geckWeightTorusPoints ht i A) ih

end

end TauCeti.DynkinType
