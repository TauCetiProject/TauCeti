/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.BlockWeight
public import TauCeti.Algebra.AlgebraicGroup.Parabolic.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry
import TauCeti.Algebra.GroupWithZero.Units.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Borel
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.TitsSystem
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Reduced closed overgroups of the upper-triangular subgroup of `GLₙ₊₁`

Over a field `k`, every reduced closed subgroup scheme of `GLₙ₊₁` containing the
upper-triangular subgroup `B` is a weight parabolic `P(w)` for a decreasing integer weight `w`:
the subgroup of invertible matrices whose `(i,j)` entry vanishes whenever `w i < w j`. In the
Hopf-ideal language, a reduced Hopf ideal `I ≤ I_B` is `weightParabolicDefiningHopfIdeal k w`
for some antitone `w`. Consequently every such subgroup is smooth and parabolic, and in
characteristic zero, where Cartier's theorem makes every closed subgroup scheme reduced, the
reducedness hypothesis can be dropped.

The proof passes to points over an algebraic closure `K` of `k`. There the points of `I` form a
subgroup of `GLₙ₊₁(K)` containing `B(K)`, which by the Tits-system classification
`exists_antitone_weightParabolicPoints_eq` is the group of `K`-points of a decreasing weight
parabolic `P(w)`. Both quotients are reduced and of finite type, so point separation over `K`
recovers the equality of Hopf ideals.

The reducedness hypothesis cannot be dropped in positive characteristic: the Frobenius inverse
image of `B` contains `B` and has the same geometric points, but is not reduced.

Over an algebraically closed field the weight can be normalized: a subset of the adjacent
coordinate pairs specifies which pairs belong to the same block, and the corresponding
normalized standard block weight starts at zero and decreases by one exactly at pairs outside
the subset. These standard block weights classify the reduced closed subgroups containing the
upper-triangular group, as an order isomorphism.

## Main declarations

All declarations below are in the `TauCeti.GeneralLinear` namespace.

* `exists_antitone_eq_weightParabolicDefiningHopfIdeal`: a reduced Hopf ideal contained in the
  upper-triangular ideal is the defining ideal of the weight parabolic of a decreasing weight.
* `isReduced_and_le_upperTriangular_definingHopfIdeal_iff`: the reduced closed subgroups
  containing `B` are exactly the weight parabolics of decreasing weights.
* `isParabolic_of_le_upperTriangular_definingHopfIdeal` and
  `isParabolicOverAlgClosed_of_le_upperTriangular_definingHopfIdeal`: such subgroups are
  parabolic.
* `exists_antitone_eq_weightParabolicDefiningHopfIdeal_of_charZero`: in characteristic zero,
  every closed subgroup scheme containing `B` is a standard weight parabolic.
* `exists_unique_standardWeight_eq` and `standardWeightOrderIso`: over an algebraically closed
  field, normalized standard block weights classify these subgroups.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§29.2–29.3 and §30.1.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 21.91.
-/

public section

namespace TauCeti.GeneralLinear

universe u

variable {n : ℕ}

section Field

variable {k : Type u} [Field k]

/-- **Reduced closed overgroups of `B` in `GLₙ₊₁` are standard weight parabolics.** Over a
field `k`, a reduced closed subgroup scheme of `GLₙ₊₁` containing the upper-triangular
subgroup is the weight parabolic of a decreasing integer weight. Containment of closed
subgroups is the reversed inequality of their Hopf ideals. -/
theorem exists_antitone_eq_weightParabolicDefiningHopfIdeal
    {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))}
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)] :
    ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ I = weightParabolicDefiningHopfIdeal k w := by
  let K := AlgebraicClosure k
  -- The `K`-points of `I` form a subgroup of `GLₙ₊₁(K)` containing the upper-triangular group.
  have hB : upperTriangularGroup (Fin (n + 1)) K ≤ hopfIdealPointsSubgroup (n + 1) I K := by
    rw [← UpperTriangular.hopfIdealPointsSubgroup_eq k (n + 1)]
    exact hopfIdealPointsSubgroup_le_of_le (n + 1) hIB K
  obtain ⟨w, hw, hP⟩ := exists_antitone_weightParabolicPoints_eq K hB
  -- Membership in a weight parabolic does not depend on the base ring.
  replace hP : weightParabolicPoints k w K = hopfIdealPointsSubgroup (n + 1) I K := by
    rw [← hP]
    ext
    simp only [mem_weightParabolicPoints_iff]
  -- The `K`-points of `I` and of the weight parabolic coincide; both quotients are reduced.
  refine ⟨w, hw, HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := K) (SetLike.ext fun g ↦ ?_)⟩
  have hg := SetLike.ext_iff.mp hP (pointsMulEquiv (n + 1) g)
  rwa [mem_hopfIdealPointsSubgroup_iff, pointsMulEquiv_mem_weightParabolicPoints_iff,
    MulEquiv.symm_apply_apply, ← CommHopfAlgCat.mem_quotientPointsSubgroup_iff, Iff.comm] at hg

/-- **Characterization of the reduced closed overgroups of `B` in `GLₙ₊₁`.** A closed subgroup
scheme of `GLₙ₊₁` is reduced and contains the upper-triangular subgroup exactly when it is the
weight parabolic of a decreasing integer weight. -/
theorem isReduced_and_le_upperTriangular_definingHopfIdeal_iff
    (I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))) :
    (IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I) ∧
        I ≤ UpperTriangular.definingHopfIdeal k (n + 1)) ↔
      ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ I = weightParabolicDefiningHopfIdeal k w := by
  refine ⟨fun ⟨_, hIB⟩ ↦ exists_antitone_eq_weightParabolicDefiningHopfIdeal hIB, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact ⟨inferInstance, weightParabolicDefiningHopfIdeal_le_upperTriangular_definingHopfIdeal k hw⟩

/-- A reduced closed subgroup scheme of `GLₙ₊₁` containing the upper-triangular subgroup is
parabolic; in particular it is smooth. -/
theorem isParabolic_of_le_upperTriangular_definingHopfIdeal
    {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))}
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)] :
    HopfIdeal.IsParabolic k (coordinateHopfAlgebra k (n + 1)) I := by
  obtain ⟨w, -, rfl⟩ := exists_antitone_eq_weightParabolicDefiningHopfIdeal hIB
  exact isParabolic_weightParabolicDefiningHopfIdeal k w

/-- Over an algebraically closed field, a reduced closed subgroup scheme of `GLₙ₊₁` containing
the upper-triangular subgroup is parabolic. -/
theorem isParabolicOverAlgClosed_of_le_upperTriangular_definingHopfIdeal [IsAlgClosed k]
    {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))}
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)] :
    HopfIdeal.IsParabolicOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k (n + 1))) I := by
  obtain ⟨w, -, rfl⟩ := exists_antitone_eq_weightParabolicDefiningHopfIdeal hIB
  exact isParabolicOverAlgClosed_weightParabolicDefiningHopfIdeal k w

/-- **In characteristic zero, every closed overgroup of `B` in `GLₙ₊₁` is a standard weight
parabolic.** By Cartier's theorem the quotient coordinate algebra is smooth, hence reduced, so
no reducedness hypothesis is needed. -/
theorem exists_antitone_eq_weightParabolicDefiningHopfIdeal_of_charZero [CharZero k]
    {I : HopfIdeal k (coordinateHopfAlgebra k (n + 1))}
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1)) :
    ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ I = weightParabolicDefiningHopfIdeal k w := by
  have := (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k
    (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I))
  have := isReduced_of_smooth k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)
  exact exists_antitone_eq_weightParabolicDefiningHopfIdeal hIB

end Field

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
