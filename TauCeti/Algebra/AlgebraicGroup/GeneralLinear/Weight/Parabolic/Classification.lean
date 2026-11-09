/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.BlockWeight
public import TauCeti.Algebra.AlgebraicGroup.Parabolic.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Borel
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.GroupWithZero.Units.Basic
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Standard block weights and classification of general-linear parabolics

A subset of the adjacent coordinate pairs specifies which pairs belong to the same block.
The corresponding normalized integer weight starts at zero and decreases by one exactly at
pairs outside the subset. Over a field `k` these weights classify the reduced closed subgroup
schemes of the general linear group containing the upper-triangular subgroup `B`. Consequently
every such subgroup is smooth and parabolic, and in characteristic zero, where Cartier's theorem
makes every closed subgroup scheme reduced, the reducedness hypothesis can be dropped.

On rational points, the standard-parabolic classification of the Tits system of `GLₙ₊₁(k)`
shows that every subgroup containing the upper-triangular group is the group of points of a
standard block weight parabolic. For a reduced Hopf ideal the proof passes to points over an
algebraic closure `K` of `k`; both quotients are reduced and of finite type, so the separation
of reduced finite-type Hopf algebras by `K`-points recovers the equality of Hopf ideals.

The reducedness hypothesis cannot be dropped in positive characteristic: the Frobenius inverse
image of `B` contains `B` and has the same geometric points, but is not reduced.

## Main declarations

All declarations below are in the `TauCeti.GeneralLinear` namespace.

* `exists_weightParabolicPoints_standardWeight_eq`: a subgroup of `GLₙ₊₁(k)` containing the
  upper-triangular group is the group of points of a standard block weight parabolic.
* `exists_unique_standardWeight_eq`: a reduced Hopf ideal contained in the upper-triangular
  ideal is the defining ideal of exactly one standard block weight parabolic.
* `standardWeightOrderIso`: the order isomorphism between block labels and these ideals.
* `isReduced_and_le_upperTriangular_definingHopfIdeal_iff`: the reduced closed subgroups
  containing `B` are exactly the weight parabolics of decreasing weights.
* `isParabolic_of_le_upperTriangular_definingHopfIdeal` and
  `isParabolicOverAlgClosed_of_le_upperTriangular_definingHopfIdeal`: such subgroups are
  parabolic.
* `exists_unique_standardWeight_eq_of_charZero`: in characteristic zero, every closed subgroup
  scheme containing `B` is a standard block weight parabolic.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§29–30.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 21.91.
-/

public section

namespace TauCeti.GeneralLinear

universe u

variable {n : ℕ}

section Field

variable (k : Type u) [Field k]

/-- **Subgroups of `GLₙ₊₁(k)` containing the upper-triangular group are block triangular.**
Over a field with a nontrivial unit group, every subgroup of `GLₙ₊₁(k)` containing the
invertible upper-triangular matrices is the group of `k`-points of a standard block weight
parabolic: the label records the adjacent transpositions the subgroup contains. -/
theorem exists_weightParabolicPoints_standardWeight_eq [Nontrivial kˣ]
    {H : Subgroup (GL (Fin (n + 1)) k)} (hH : upperTriangularGroup (Fin (n + 1)) k ≤ H) :
    ∃ J : Finset (Fin n), weightParabolicPoints k (standardWeight J) k = H := by
  classical
  rw [← glTitsSystem_subgroupB k n] at hH
  -- Select the adjacent transpositions lying in `H`.
  let J : Finset (Fin n) :=
    Finset.univ.filter fun i ↦ permutationGL (k := k) (Equiv.swap i.castSucc i.succ) ∈ H
  have hw := standardWeight_antitone J
  have hBw : (glTitsSystem k n).subgroupB ≤ weightParabolicPoints k (standardWeight J) k := by
    rw [glTitsSystem_subgroupB]
    exact upperTriangularGroup_le_weightParabolicPoints hw
  refine ⟨J, ?_⟩
  -- Both subgroups are the standard parabolic of the same simple reflections.
  rw [← standardParabolic_weightParabolicSimple k _ hw,
    ← (glTitsSystem k n).standardParabolic_eq_of_subgroupB_le hH]
  congr 1
  ext s
  obtain ⟨i, hi⟩ : (s : (glTitsSystem k n).WeylGroup) ∈ Set.range fun i : Fin n ↦
      (QuotientGroup.mk (glTitsSystemSimpleRep k n i) : (glTitsSystem k n).WeylGroup) := by
    rw [← glTitsSystem_simple]
    exact s.property
  rw [mem_weightParabolicSimple_iff k _ hw, Set.mem_ofPred_eq, ← hi,
    bruhatCell_glTitsSystemSimpleRep_subset_iff k hBw,
    bruhatCell_glTitsSystemSimpleRep_subset_iff k hH,
    permutationGL_swap_mem_weightParabolicPoints_iff, standardWeight_castSucc_eq_succ_iff]
  simp [J]

/-- **Reduced closed overgroups of `B` in `GLₙ₊₁` are standard block weight parabolics.**
Every reduced closed subgroup scheme of `GLₙ₊₁` over a field containing the upper-triangular
group is defined by exactly one normalized standard block weight. -/
theorem exists_unique_standardWeight_eq
    (I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)]
    (hI : I ≤ UpperTriangular.definingHopfIdeal k (n + 1)) :
    ∃! J : Finset (Fin n), I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
  let K := AlgebraicClosure k
  -- The `K`-points of `I` form a subgroup of `GLₙ₊₁(K)` containing the upper-triangular group.
  have hB : upperTriangularGroup (Fin (n + 1)) K ≤ hopfIdealPointsSubgroup (n + 1) I K := by
    rw [← UpperTriangular.hopfIdealPointsSubgroup_eq k (n + 1)]
    exact hopfIdealPointsSubgroup_le_of_le (n + 1) hI K
  obtain ⟨J, hP⟩ := exists_weightParabolicPoints_standardWeight_eq K hB
  -- Membership in a weight parabolic does not depend on the base ring.
  replace hP : weightParabolicPoints k (standardWeight J) K =
      hopfIdealPointsSubgroup (n + 1) I K := by
    rw [← hP]
    ext
    simp only [mem_weightParabolicPoints_iff]
  -- The `K`-points of `I` and of the weight parabolic coincide; both quotients are reduced.
  have heq : I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
    refine HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := K) (SetLike.ext fun g ↦ ?_)
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    have h := SetLike.ext_iff.mp hP (pointsMulEquiv (n + 1) g)
    simpa only [weightParabolicPoints_eq_hopfIdealPointsSubgroup,
      mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply] using h.symm
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
      weightParabolicDefiningHopfIdeal_standardWeight_le_upperTriangular k J, inferInstance⟩
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

/-- **In characteristic zero, every closed overgroup of `B` in `GLₙ₊₁` is a standard block
weight parabolic.** By Cartier's theorem the quotient coordinate algebra is smooth, hence
reduced, so no reducedness hypothesis is needed. -/
theorem exists_unique_standardWeight_eq_of_charZero [CharZero k]
    (I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)))
    (hI : I ≤ UpperTriangular.definingHopfIdeal k (n + 1)) :
    ∃! J : Finset (Fin n), I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
  have := (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k
    (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I))
  have := isReduced_of_smooth k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)
  exact exists_unique_standardWeight_eq k I hI

end Field

section Corollaries

variable {k : Type u} [Field k]

/-- **Characterization of the reduced closed overgroups of `B` in `GLₙ₊₁`.** A closed subgroup
scheme of `GLₙ₊₁` is reduced and contains the upper-triangular subgroup exactly when it is the
weight parabolic of a decreasing integer weight. -/
theorem isReduced_and_le_upperTriangular_definingHopfIdeal_iff
    (I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))) :
    (IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I) ∧
        I ≤ UpperTriangular.definingHopfIdeal k (n + 1)) ↔
      ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ I = weightParabolicDefiningHopfIdeal k w := by
  refine ⟨fun ⟨_, hIB⟩ ↦ ?_, ?_⟩
  · obtain ⟨J, hJ, -⟩ := exists_unique_standardWeight_eq k I hIB
    exact ⟨standardWeight J, standardWeight_antitone J, hJ⟩
  rintro ⟨w, hw, rfl⟩
  exact ⟨inferInstance, weightParabolicDefiningHopfIdeal_le_upperTriangular_definingHopfIdeal k hw⟩

/-- A reduced closed subgroup scheme of `GLₙ₊₁` containing the upper-triangular subgroup is
parabolic; in particular it is smooth. -/
theorem isParabolic_of_le_upperTriangular_definingHopfIdeal
    {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))}
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)] :
    HopfIdeal.IsParabolic k (coordinateHopfAlgebra k (n + 1)) I := by
  obtain ⟨J, rfl, -⟩ := exists_unique_standardWeight_eq k I hIB
  exact isParabolic_weightParabolicDefiningHopfIdeal k _

/-- Over an algebraically closed field, a reduced closed subgroup scheme of `GLₙ₊₁` containing
the upper-triangular subgroup is parabolic. -/
theorem isParabolicOverAlgClosed_of_le_upperTriangular_definingHopfIdeal [IsAlgClosed k]
    {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))}
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)] :
    HopfIdeal.IsParabolicOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k (n + 1))) I := by
  obtain ⟨J, rfl, -⟩ := exists_unique_standardWeight_eq k I hIB
  exact isParabolicOverAlgClosed_weightParabolicDefiningHopfIdeal k _

end Corollaries

end TauCeti.GeneralLinear
