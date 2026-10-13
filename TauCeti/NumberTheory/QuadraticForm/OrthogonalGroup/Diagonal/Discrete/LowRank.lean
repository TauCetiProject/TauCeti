/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Discrete.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.LowRank

/-!
# Low-rank rational points are discrete in the full adeles

For a rational quadratic space of dimension at most one, the orthogonal, special orthogonal and
Spin groups are finite. Consequently their diagonal images in the corresponding full adelic
groups are discrete for every compatible compact-open tuple, without any comparison between its
local reference subgroups and an integral family.

In dimension zero all three groups are trivial. In dimension one the orthogonal group consists of
the identity and negation, the special orthogonal group is trivial, and the Spin group has at most
the two scalar elements above the identity. These finite descriptions isolate the low-dimensional
part of adelic discreteness from the integral matrix argument needed in higher dimensions.

## Main results

* `OrthogonalCompactOpens.discreteTopology_range_fullAdelicOrthogonalDiagonal_of_finrank_le_one`
  proves discreteness of rational orthogonal points for every compatible tuple.
* `discreteTopology_range_fullAdelicSpecialOrthogonalDiagonal_of_finrank_le_one` proves the
  corresponding statement for proper isometries.
* `OrthogonalCompactOpens.discreteTopology_range_fullAdelicSpinDiagonal_of_finrank_le_one` proves
  the corresponding statement for Spin points.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- **Low-rank rational isometries are discrete in every full adelic orthogonal group.**
No integrality condition on the compatible compact-open tuple is needed. -/
theorem discreteTopology_range_fullAdelicOrthogonalDiagonal_of_finrank_le_one
    (hQ : Q.Nondegenerate) (hV : Module.finrank ℚ V ≤ 1) :
    DiscreteTopology U.fullAdelicOrthogonalDiagonal.range := by
  have hfinite : (Set.univ : Set (orthogonalGroup Q)).Finite := by
    rcases hV.eq_or_lt with hV1 | hV0
    · let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (hV1.symm ▸ Nat.zero_lt_one)
      exact (Set.finite_insert.mpr (Set.finite_singleton Q.negOrthogonal)).subset fun g _ ↦ by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
          eq_one_or_eq_negOrthogonal_of_finrank_eq_one hQ.ne_zero hV1 g
    · have hzero : Module.finrank ℚ V = 0 := by omega
      let _ : Subsingleton V := Module.finrank_zero_iff.mp hzero
      exact (Set.finite_singleton 1).subset fun g _ ↦ by
        simpa only [Set.mem_singleton_iff] using Subsingleton.elim g 1
  apply MonoidHom.discreteTopology_range_of_finite_preimage U.fullAdelicOrthogonalDiagonal
    Filter.univ_mem
  simpa only [Set.preimage_univ] using hfinite

/-- **Low-rank rational proper isometries are discrete in every full adelic special orthogonal
group.** No nondegeneracy or integrality hypothesis is needed. -/
theorem discreteTopology_range_fullAdelicSpecialOrthogonalDiagonal_of_finrank_le_one
    (hV : Module.finrank ℚ V ≤ 1) :
    DiscreteTopology U.fullAdelicSpecialOrthogonalDiagonal.range := by
  have hbot := specialOrthogonalGroup_eq_bot_of_finrank_le_one Q hV
  have hfinite : (Set.univ : Set (specialOrthogonalGroup Q)).Finite :=
    (Set.finite_singleton 1).subset fun g _ ↦ by
      have hg : (g : V ≃ₗ[ℚ] V) ∈ (⊥ : Subgroup (V ≃ₗ[ℚ] V)) := by
        rw [← hbot]
        exact g.2
      simpa only [Set.mem_singleton_iff] using Subtype.ext (show (g : V ≃ₗ[ℚ] V) = 1 by
        simpa only [Subgroup.mem_bot] using hg)
  apply MonoidHom.discreteTopology_range_of_finite_preimage
    U.fullAdelicSpecialOrthogonalDiagonal Filter.univ_mem
  simpa only [Set.preimage_univ] using hfinite

/-- **Low-rank rational Spin points are discrete in every full adelic Spin group.** For a
nondegenerate form of dimension at most one, the rational Spin group has at most two elements, so
no integrality condition on the compatible compact-open tuple is needed. -/
theorem discreteTopology_range_fullAdelicSpinDiagonal_of_finrank_le_one
    (hQ : Q.Nondegenerate) (hV : Module.finrank ℚ V ≤ 1) :
    DiscreteTopology U.fullAdelicSpinDiagonal.range := by
  have hfinite : (Set.univ : Set (spinGroup Q)).Finite := by
    rcases hV.eq_or_lt with hV1 | hV0
    · let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (hV1.symm ▸ Nat.zero_lt_one)
      have hSO := specialOrthogonalGroup_eq_bot_of_finrank_le_one Q hV
      refine ((Set.finite_singleton
        (CliffordAlgebra.spinGroup.negOne Q hQ.ne_zero)).insert (1 : spinGroup Q)).subset
        fun x _ ↦ ?_
      have hSOeq (g : specialOrthogonalGroup Q) : g = 1 := by
        apply Subtype.ext
        have hg : (g : V ≃ₗ[ℚ] V) ∈ (⊥ : Subgroup (V ≃ₗ[ℚ] V)) := by
          rw [← hSO]
          exact g.2
        simpa only [OneMemClass.coe_one, Subgroup.mem_bot] using hg
      have himage : CliffordAlgebra.spinToSpecialOrthogonal Q x =
          CliffordAlgebra.spinToSpecialOrthogonal Q 1 :=
        (hSOeq _).trans (hSOeq _).symm
      rcases CliffordAlgebra.eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq Q hQ x 1
          himage with hx | hx
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hx, true_or]
      · simp only [mul_one, Set.mem_insert_iff, Set.mem_singleton_iff, hx, or_true]
    · have hzero : Module.finrank ℚ V = 0 := by omega
      let _ : Subsingleton V := Module.finrank_zero_iff.mp hzero
      have hinj := (CliffordAlgebra.spinToSpecialOrthogonal_bijective_of_subsingleton Q).injective
      exact (Set.finite_singleton 1).subset fun x _ ↦ by
        simpa only [Set.mem_singleton_iff] using hinj (Subsingleton.elim _ _)
  apply MonoidHom.discreteTopology_range_of_finite_preimage U.fullAdelicSpinDiagonal
    Filter.univ_mem
  simpa only [Set.preimage_univ] using hfinite

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
