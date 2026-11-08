/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.BlockWeight
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.RingTheory.Smooth.GeometricallyReduced
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
    rw [← standardParabolic_weightParabolicSimple k _ (standardWeight_antitone J), hsimple]
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
  apply (standardWeightParabolicOrderEmbedding k).injective
  simpa only [standardWeightParabolicOrderEmbedding_apply] using
    congrArg OrderDual.toDual (hK.symm.trans heq)

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
    apply (standardWeightParabolicOrderEmbedding k).injective
    simpa only [standardWeightParabolicOrderEmbedding_apply] using
      congrArg OrderDual.toDual (congrArg Subtype.val h)
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
