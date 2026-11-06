/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.TitsSystem
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Borel
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.Data.Fin.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry

/-!
# Standard block weights and classification of general-linear parabolics

A subset of the adjacent coordinate pairs specifies which pairs belong to the same block.
The corresponding normalized integer weight starts at zero and decreases by one exactly at
pairs outside the subset. Over an algebraically closed field these weights classify the
reduced closed subgroups of the general linear group containing the upper-triangular group.
The classification uses the standard-parabolic classification of its Tits system and the
separation of reduced finite-type Hopf algebras by rational points.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§29–30.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 21.91.
-/

public section

namespace TauCeti.GeneralLinear

universe u

variable {n : ℕ}

/-- The normalized decreasing block weight. An adjacent pair has equal weights precisely
when its index belongs to `J`; the complementary indices are the retained flag dimensions. -/
def standardWeight (J : Finset (Fin n)) (i : Fin (n + 1)) : ℤ :=
  -((Finset.univ.filter fun j : Fin n ↦ j.val < i.val ∧ j ∉ J).card : ℤ)

/-- The normalized block weight counts the breaks preceding a coordinate. -/
theorem standardWeight_apply (J : Finset (Fin n)) (i : Fin (n + 1)) :
    standardWeight J i =
      -((Finset.univ.filter fun j : Fin n ↦ j.val < i.val ∧ j ∉ J).card : ℤ) :=
  (rfl)

@[simp]
theorem standardWeight_zero (J : Finset (Fin n)) : standardWeight J 0 = 0 := by
  simp [standardWeight]

/-- Crossing an omitted adjacent pair decreases the normalized weight by one. -/
theorem standardWeight_succ (J : Finset (Fin n)) (i : Fin n) :
    standardWeight J i.succ = standardWeight J i.castSucc - if i ∈ J then 0 else 1 := by
  have hfilter (a : Fin (n + 1)) :
      (Finset.univ.filter fun j : Fin n ↦ j.val < a.val ∧ j ∉ J) =
        (Finset.univ \ J).filter (fun j ↦ j.castSucc < a) := by
    ext j
    simp [and_comm, Fin.lt_def]
  rw [standardWeight_apply, standardWeight_apply, hfilter, hfilter]
  have h := Finset.card_filter_castSucc_lt_succ (Finset.univ \ J) i
  rw [h]
  by_cases hi : i ∈ J <;> simp [hi, sub_eq_add_neg, add_comm]

/-- The block weight is decreasing along the coordinate order. -/
theorem antitone_standardWeight (J : Finset (Fin n)) : Antitone (standardWeight J) := by
  intro i j hij
  simp only [standardWeight, neg_le_neg_iff, Nat.cast_le (α := ℤ)]
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨lt_of_lt_of_le ha.1 hij, ha.2⟩

/-- Equal adjacent weights recover the block label. Use this as a named rewrite: numeral
coordinate indices need not retain their successor presentation during simplification. -/
theorem standardWeight_castSucc_eq_succ_iff (J : Finset (Fin n)) (i : Fin n) :
    standardWeight J i.castSucc = standardWeight J i.succ ↔ i ∈ J := by
  rw [standardWeight_succ, eq_sub_iff_add_eq]
  simp

@[simp]
theorem standardWeight_empty (i : Fin (n + 1)) : standardWeight ∅ i = -(i.val : ℤ) := by
  simp only [standardWeight_apply, Finset.notMem_empty, not_false_eq_true, and_true,
    Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ i.isLt)]

@[simp]
theorem standardWeight_univ (i : Fin (n + 1)) : standardWeight Finset.univ i = 0 := by
  simp [standardWeight]

section Ring

variable (R : Type u) [CommRing R]

/-- Standard block subgroups contain the upper-triangular subgroup. -/
theorem weightParabolicDefiningHopfIdeal_standardWeight_le_upperTriangular
    (J : Finset (Fin n)) :
    weightParabolicDefiningHopfIdeal R (standardWeight J) ≤
      UpperTriangular.definingHopfIdeal R (n + 1) :=
  weightParabolicDefiningHopfIdeal_le_upperTriangular_definingHopfIdeal R
    (antitone_standardWeight J)

/-- No adjacent pairs joined gives the upper-triangular subgroup, independently of the
additive normalization of the strictly decreasing weights. -/
@[simp]
theorem weightParabolicDefiningHopfIdeal_standardWeight_empty :
    weightParabolicDefiningHopfIdeal R (standardWeight (∅ : Finset (Fin n))) =
      UpperTriangular.definingHopfIdeal R (n + 1) := by
  have hrel : weightParabolicRelationSet R (standardWeight (∅ : Finset (Fin n))) =
      UpperTriangular.definingRelationSet R (n + 1) := by
    ext x
    simp only [mem_weightParabolicRelationSet_iff, UpperTriangular.mem_definingRelationSet_iff,
      standardWeight_empty, neg_lt_neg_iff, Nat.cast_lt (α := ℤ), Fin.lt_def]
  apply HopfIdeal.ext
  intro x
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal, UpperTriangular.definingHopfIdeal_toIdeal, hrel]

/-- Joining every adjacent pair gives the whole general linear group. -/
@[simp]
theorem weightParabolicDefiningHopfIdeal_standardWeight_univ :
    weightParabolicDefiningHopfIdeal R (standardWeight (Finset.univ : Finset (Fin n))) = ⊥ := by
  have hrel : weightParabolicRelationSet R (standardWeight (Finset.univ : Finset (Fin n))) =
      ∅ := by
    ext x
    simp only [mem_weightParabolicRelationSet_iff, standardWeight_univ, lt_self_iff_false,
      false_and, exists_false, Set.mem_empty_iff_false]
  apply HopfIdeal.ext
  intro x
  rw [← HopfIdeal.mem_toIdeal, weightParabolicDefiningHopfIdeal_toIdeal, hrel]
  simp

/-- Distinct block labels define distinct closed subgroups, over any nontrivial ring. -/
theorem weightParabolicDefiningHopfIdeal_standardWeight_injective [Nontrivial R] :
    Function.Injective (fun J : Finset (Fin n) ↦
      weightParabolicDefiningHopfIdeal R (standardWeight J)) := by
  intro J K h
  have hpoints : weightParabolicPoints R (standardWeight J) R =
      weightParabolicPoints R (standardWeight K) R := by
    simpa only [weightParabolicPoints_eq_hopfIdealPointsSubgroup] using
      congrArg (fun I ↦ hopfIdealPointsSubgroup (n + 1) I R) h
  ext i
  have hm := congrArg
    (fun P : Subgroup (GL (Fin (n + 1)) R) ↦
      permutationGL (k := R) (Equiv.swap i.castSucc i.succ) ∈ P) hpoints
  simpa only [permutationGL_swap_mem_weightParabolicPoints_iff,
    standardWeight_castSucc_eq_succ_iff] using Iff.of_eq hm

end Ring

section AlgebraicallyClosed

variable (k : Type u) [Field k] [IsAlgClosed k]

local instance : Nontrivial kˣ := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨⟨Units.mk0 a ha.1, 1, fun h ↦ ha.2 (congrArg Units.val h)⟩⟩

/-- Every reduced closed subgroup containing the upper-triangular group is defined by
exactly one normalized standard block weight. -/
theorem exists_unique_standardWeight_eq
    (I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)]
    (hI : I ≤ UpperTriangular.definingHopfIdeal k (n + 1)) :
    ∃! J : Finset (Fin n), I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
  classical
  let P := hopfIdealPointsSubgroup (n + 1) I k
  let T := glTitsSystem k n
  have hB : T.subgroupB ≤ P := by
    simp only [T, glTitsSystem_subgroupB]
    rw [← UpperTriangular.hopfIdealPointsSubgroup_eq k (n + 1) (A := k)]
    exact hopfIdealPointsSubgroup_le_of_le (n + 1) hI k
  -- Classify the matrix subgroup by the simple Bruhat cells it contains.
  let J : Finset (Fin n) := Finset.univ.filter fun i ↦
    T.bruhatCell (QuotientGroup.mk (glTitsSystemSimpleRep k n i)) ⊆ P
  have hsimple : weightParabolicSimple k (standardWeight J) =
      {s : T.simple | T.bruhatCell (s : T.WeylGroup) ⊆ P} := by
    ext s
    rw [mem_weightParabolicSimple_iff_exists]
    constructor
    · rintro ⟨i, hi, hs⟩
      have hiP := (Finset.mem_filter.mp ((standardWeight_castSucc_eq_succ_iff J i).mp hi)).2
      have hsP : T.bruhatCell (s : T.WeylGroup) ⊆ P := by
        rw [hs]
        exact hiP
      exact hsP
    · intro hs
      have hrep := s.property
      simp only [glTitsSystem_simple, Set.mem_range] at hrep
      obtain ⟨i, hi⟩ := hrep
      refine ⟨i, (standardWeight_castSucc_eq_succ_iff J i).mpr ?_, hi.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hi]⟩
  have hpoints : weightParabolicPoints k (standardWeight J) k = P := by
    rw [← standardParabolic_weightParabolicSimple k _ (antitone_standardWeight J), hsimple]
    exact T.standardParabolic_eq_of_subgroupB_le hB
  -- Smoothness of the weight subgroup lets rational points recover its defining ideal.
  have heq : I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
    let _ : Algebra.Smooth k (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
      (smoothCommHopfAlgProperty_iff _).mp
        (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra k (standardWeight J))
    let _ : IsReduced (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
      isReduced_of_smooth k _
    apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := k)
    ext g
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    have h := SetLike.ext_iff.mp hpoints (pointsMulEquiv (n + 1) g)
    simpa only [weightParabolicPoints_eq_hopfIdealPointsSubgroup,
      mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply,
      P] using h.symm
  refine ⟨J, heq, fun K hK ↦ ?_⟩
  exact weightParabolicDefiningHopfIdeal_standardWeight_injective k (hK.symm.trans heq)

/-- Geometric containment of standard block subgroups is inclusion of their labels.
Defining Hopf ideals have the opposite order. -/
theorem weightParabolicDefiningHopfIdeal_standardWeight_le_iff (J K : Finset (Fin n)) :
    weightParabolicDefiningHopfIdeal k (standardWeight K) ≤
      weightParabolicDefiningHopfIdeal k (standardWeight J) ↔ J ⊆ K := by
  classical
  constructor
  · intro h i hi
    have hp : weightParabolicPoints k (standardWeight J) k ≤
        weightParabolicPoints k (standardWeight K) k := by
      rw [weightParabolicPoints_eq_hopfIdealPointsSubgroup,
        weightParabolicPoints_eq_hopfIdealPointsSubgroup]
      exact hopfIdealPointsSubgroup_le_of_le (n + 1) h k
    apply (standardWeight_castSucc_eq_succ_iff K i).mp
    apply (permutationGL_swap_mem_weightParabolicPoints_iff k (standardWeight K) (A := k)
      i.castSucc i.succ).mp
    apply hp
    exact (permutationGL_swap_mem_weightParabolicPoints_iff k (standardWeight J) (A := k)
      i.castSucc i.succ).mpr ((standardWeight_castSucc_eq_succ_iff J i).mpr hi)
  · intro h
    have hs : weightParabolicSimple k (standardWeight J) ⊆
        weightParabolicSimple k (standardWeight K) := by
      intro s hs
      rw [mem_weightParabolicSimple_iff_exists] at hs ⊢
      obtain ⟨i, hi, heq⟩ := hs
      exact ⟨i, (standardWeight_castSucc_eq_succ_iff K i).mpr
        (h ((standardWeight_castSucc_eq_succ_iff J i).mp hi)), heq⟩
    have hp : weightParabolicPoints k (standardWeight J) k ≤
        weightParabolicPoints k (standardWeight K) k := by
      rw [← standardParabolic_weightParabolicSimple k _ (antitone_standardWeight J),
        ← standardParabolic_weightParabolicSimple k _ (antitone_standardWeight K)]
      exact (glTitsSystem k n).standardParabolic_monotone hs
    let _ : Algebra.Smooth k (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
      (smoothCommHopfAlgProperty_iff _).mp
        (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra k (standardWeight J))
    let _ : IsReduced (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
      isReduced_of_smooth k _
    apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := k)
    intro g hg
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
    have hm : pointsMulEquiv (n + 1) g ∈ weightParabolicPoints k (standardWeight J) k := by
      simpa only [weightParabolicPoints_eq_hopfIdealPointsSubgroup,
        mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply] using hg
    simpa only [weightParabolicPoints_eq_hopfIdealPointsSubgroup,
      mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply] using hp hm

/-- Block labels classify reduced closed subgroups containing the upper-triangular group.
The order dual records the reversal between subgroup containment and defining ideals. -/
noncomputable def standardWeightOrderIso :
    Finset (Fin n) ≃o OrderDual
      {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)) //
        I ≤ UpperTriangular.definingHopfIdeal k (n + 1) ∧
          IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)} := by
  classical
  let f : Finset (Fin n) → OrderDual
      {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)) //
        I ≤ UpperTriangular.definingHopfIdeal k (n + 1) ∧
          IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)} := fun J ↦
    ⟨weightParabolicDefiningHopfIdeal k (standardWeight J),
      weightParabolicDefiningHopfIdeal_standardWeight_le_upperTriangular k J, by
        let _ : Algebra.Smooth k
            (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
          (smoothCommHopfAlgProperty_iff _).mp
            (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra k (standardWeight J))
        exact isReduced_of_smooth k _⟩
  refine { Equiv.ofBijective f ⟨?_, ?_⟩ with map_rel_iff' := ?_ }
  · intro J K h
    exact weightParabolicDefiningHopfIdeal_standardWeight_injective k (congrArg Subtype.val h)
  · intro I
    let _ := I.property.2
    obtain ⟨J, hJ, _⟩ := exists_unique_standardWeight_eq k I.val I.property.1
    exact ⟨J, Subtype.ext hJ.symm⟩
  · intro J K
    exact weightParabolicDefiningHopfIdeal_standardWeight_le_iff k J K

/-- The order classification sends a label to its normalized weight ideal. -/
@[simp]
theorem standardWeightOrderIso_apply (J : Finset (Fin n)) :
    (standardWeightOrderIso k J).val =
      weightParabolicDefiningHopfIdeal k (standardWeight J) :=
  (rfl)

/-- The inverse classification recovers the original defining ideal. -/
@[simp]
theorem weightParabolicDefiningHopfIdeal_standardWeightOrderIso_symm
    (I : OrderDual {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)) //
      I ≤ UpperTriangular.definingHopfIdeal k (n + 1) ∧
        IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)}) :
    weightParabolicDefiningHopfIdeal k (standardWeight ((standardWeightOrderIso k).symm I)) =
      I.val := by
  rw [← standardWeightOrderIso_apply, OrderIso.apply_symm_apply]

end AlgebraicallyClosed

end TauCeti.GeneralLinear
