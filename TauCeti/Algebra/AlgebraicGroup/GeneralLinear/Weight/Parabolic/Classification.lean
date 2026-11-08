/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.BlockWeight
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry
import TauCeti.RingTheory.Smooth.GeometricallyReduced

import all TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
import all TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.TitsSystem

/-!
# Classification of standard general-linear parabolic ideals

The standard block weight `standardWeight J`, for `J : Finset (Fin n)`, selects exactly
the adjacent simple reflections indexed by `J` in the general-linear Tits system.
Over an algebraically closed field, every reduced closed subgroup containing the
upper-triangular subgroup is defined by the weight-parabolic ideal of a unique such label.

The proof classifies the subgroup of rational points with the general-linear Tits system.
Weight-parabolic quotients are smooth, hence reduced, so point separation recovers equality
of the defining Hopf ideals. The standard weights, their antitonicity, and the order
embedding of their defining ideals are supplied by
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.BlockWeight`.
That embedding gives uniqueness of the label. Reducedness of the input quotient is
essential in positive characteristic.

This proves the unique-block-weight theorem of FlagVarieties, Layer 1.1, using the
definition in `TauCetiRoadmap/FlagVarieties/Suggested.lean`.

## Main declarations

All declarations below are in the `TauCeti.GeneralLinear` namespace.

* `weightParabolicSimple_standardWeight` and
  `simpleRep_mem_weightParabolicSimple_standardWeight_iff`: comparison with the simple
  reflections indexed by `glTitsSystemSimpleRep`.
* `exists_unique_standardWeight_eq`: every reduced defining Hopf ideal contained in the
  upper-triangular ideal is the weight-parabolic ideal of a unique standard block weight.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§29–30.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 21.91.
-/

public section

namespace TauCeti.GeneralLinear

noncomputable section

variable {n : ℕ} (k : Type*) [Field k] [Nontrivial kˣ]

/-- The selected simple reflections are those represented by the adjacent indices in `J`. -/
theorem weightParabolicSimple_standardWeight (J : Finset (Fin n)) :
    weightParabolicSimple k (standardWeight J) =
      {s : (glTitsSystem k n).simple | ∃ i ∈ J, (s : (glTitsSystem k n).WeylGroup) =
        QuotientGroup.mk (glTitsSystemSimpleRep k n i)} := by
  ext s
  simp only [weightParabolicSimple, Set.mem_ofPred_eq, standardWeight_castSucc_eq_succ_iff]

/-- Under the standard adjacent-transposition indexing, the `i`-th simple reflection is
selected exactly when `i ∈ J`. -/
theorem simpleRep_mem_weightParabolicSimple_standardWeight_iff (J : Finset (Fin n)) (i : Fin n) :
    (⟨QuotientGroup.mk (glTitsSystemSimpleRep k n i),
      by rw [glTitsSystem_simple]; exact ⟨i, rfl⟩⟩ : (glTitsSystem k n).simple) ∈
      weightParabolicSimple k (standardWeight J) ↔ i ∈ J := by
  constructor
  · intro h
    have hcell := (mem_weightParabolicSimple_iff k (standardWeight J)
      (standardWeight_antitone J) _).mp h
    have hrep : (glTitsSystemSimpleRep k n i : GL (Fin (n + 1)) k) ∈
        (glTitsSystem k n).bruhatCell (QuotientGroup.mk (glTitsSystemSimpleRep k n i)) := by
      rw [TitsSystem.bruhatCell_mk]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    have hm : (glTitsSystemSimpleRep k n i : GL (Fin (n + 1)) k) ∈
        weightParabolicPoints k (standardWeight J) k := hcell hrep
    rw [coe_glTitsSystemSimpleRep, permutationGL_swap_mem_weightParabolicPoints_iff,
      standardWeight_castSucc_eq_succ_iff] at hm
    exact hm
  · intro hi
    exact ⟨i, (standardWeight_castSucc_eq_succ_iff J i).mpr hi, rfl⟩

end

noncomputable section

universe u

/-- Every reduced closed subgroup of `GL_{n+1}` containing the upper-triangular subgroup
has the defining Hopf ideal of a unique standard block weight. -/
theorem exists_unique_standardWeight_eq {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    (I : HopfIdeal k (coordinateHopfAlgebra k (n + 1)))
    (hIB : I ≤ UpperTriangular.definingHopfIdeal k (n + 1))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (n + 1)) I)] :
    ∃! J : Finset (Fin n),
      I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := fun h ↦ ha (by simp [h])
  have ha1 : a ≠ 1 := fun h ↦ ha (by simp [h])
  let _ : Nontrivial kˣ := nontrivial_of_ne (Units.mk0 a ha0) 1
    (fun h ↦ ha1 (congrArg Units.val h))
  let e := pointsMulEquiv (R := k) (A := k) (n + 1)
  let P := (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k (n + 1)) I
    (CommAlgCat.of k k)).map e.toMonoidHom
  have hB : (glTitsSystem k n).subgroupB ≤ P := by
    rw [glTitsSystem_subgroupB]
    intro g hg
    refine ⟨e.symm g, CommHopfAlgCat.quotientPointsSubgroup_antitone
      (coordinateHopfAlgebra k (n + 1)) (CommAlgCat.of k k) hIB ?_, e.apply_symm_apply g⟩
    exact (UpperTriangular.mem_definingPointsSubgroup_iff k (n + 1) _).mpr
      (by simpa only [e, MulEquiv.apply_symm_apply] using hg)
  let J : Finset (Fin n) := Finset.univ.filter fun i ↦
    (glTitsSystem k n).bruhatCell (QuotientGroup.mk (glTitsSystemSimpleRep k n i)) ⊆ P
  have hJ : weightParabolicSimple k (standardWeight J) =
      {s : (glTitsSystem k n).simple | (glTitsSystem k n).bruhatCell s.val ⊆ P} := by
    rw [weightParabolicSimple_standardWeight]
    ext s
    constructor
    · rintro ⟨i, hi, hs⟩
      change (glTitsSystem k n).bruhatCell s.val ⊆ P
      rw [hs]
      exact (Finset.mem_filter.mp hi).2
    · intro hs
      have hsimple := s.property
      simp only [glTitsSystem_simple, Set.mem_range] at hsimple
      obtain ⟨i, hi⟩ := hsimple
      refine ⟨i, ?_, hi.symm⟩
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hi]
  have hP : P = weightParabolicPoints k (standardWeight J) k := by
    have h := (glTitsSystem k n).standardParabolic_eq_of_subgroupB_le hB
    rw [← hJ, standardParabolic_weightParabolicSimple k _ (standardWeight_antitone _)] at h
    exact h.symm
  have hI : I = weightParabolicDefiningHopfIdeal k (standardWeight J) := by
    let _ : Algebra.Smooth k (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
      (smoothCommHopfAlgProperty_iff _).mp
        (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra k _)
    let _ : IsReduced (weightParabolicCoordinateHopfAlgebra k (standardWeight J)) :=
      isReduced_of_smooth k _
    apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := k)
    ext p
    have hp := Iff.of_eq (congrArg (fun Q : Subgroup (GL (Fin (n + 1)) k) ↦ e p ∈ Q) hP)
    simpa only [P, weightParabolicPoints, e, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply] using hp
  refine ⟨J, hI, ?_⟩
  intro K hK
  apply (standardWeightParabolicOrderEmbedding k).injective
  simpa only [standardWeightParabolicOrderEmbedding_apply] using
    congrArg OrderDual.toDual (hK.symm.trans hI)

end

end TauCeti.GeneralLinear
