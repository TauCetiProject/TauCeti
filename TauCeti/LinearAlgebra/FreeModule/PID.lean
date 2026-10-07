/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Submodules of free modules over principal ideal domains

Every submodule of a free module over a principal ideal domain is free, without a finiteness
hypothesis on the ambient module.  The construction well-orders an ambient basis and chooses one
pivot for each nonzero ideal of possible leading coordinates.  The pivots form a basis of the
submodule by elimination of the greatest coordinate in the finite support of each vector.

This is the arbitrary-rank form of Lang, *Algebra*, Chapter III, Theorem 7.1.  Mathlib's
`Submodule.nonempty_basis_of_pid` is the finite-rank form.
-/

public section

open Module Set Submodule
open Submodule.IsPrincipal

namespace Submodule

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

/-- Every submodule of a free module over a principal ideal domain is free, with no finiteness
assumption on either module. -/
theorem free_of_isPrincipalIdealRing (N : Submodule R M) [Module.Free R M] :
    Module.Free R N := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  let _ : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  let _ : IsWellOrder ι (· < ·) := by
    -- The strict order induced by the preceding `LinearOrder` is definitionally `WellOrderingRel`.
    change IsWellOrder ι WellOrderingRel
    infer_instance
  -- The ideal of possible `i`-th coordinates of vectors of `N` supported at or below `i`.
  let I : ι → Ideal R := fun i ↦
    (N ⊓ span R (b '' Set.Iic i)).map (b.coord i)
  have exists_pivot (i : ι) :
      ∃ x : N, (x : M) ∈ span R (b '' Set.Iic i) ∧
        b.coord i x = generator (I i) := by
    obtain ⟨x, hx, hcoord⟩ := Submodule.mem_map.mp (generator_mem (I i))
    exact ⟨⟨x, hx.1⟩, hx.2, hcoord⟩
  choose x hx_span hx_coord using exists_pivot
  let J : Set ι := {i | generator (I i) ≠ 0}
  let pivot : J → N := fun i ↦ x i
  have coord_pivot_eq (i : J) : b.coord i (pivot i) = generator (I i) := by
    exact hx_coord i
  have coord_pivot_eq_zero {i : J} {j : ι} (hij : i.1 < j) :
      b.coord j (pivot i) = 0 := by
    rw [Basis.coord_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hj
    exact (not_le_of_gt hij) ((b.mem_span_image.mp (hx_span i)) hj)
  have pivot_linearIndependent : LinearIndependent R pivot := by
    rw [linearIndependent_iff']
    intro s
    induction s using Finset.induction_on_max with
    | empty => simp
    | @insert a s hsa ih =>
      have ha_not_mem : a ∉ s := fun ha ↦ (hsa a ha).false
      intro g hsum i hi
      have ha_zero : g a = 0 := by
        have hcoord := congrArg ((b.coord a.1).comp N.subtype) hsum
        have hsum_zero : ∑ j ∈ s, g j * b.coord a.1 (N.subtype (pivot j)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          -- Applying `N.subtype` is definitionally the coercion used by `coord_pivot_eq_zero`.
          rw [show b.coord a.1 (N.subtype (pivot j)) = 0 by
            simpa using coord_pivot_eq_zero (hsa j hj), mul_zero]
        have hprod : g a * generator (I a) = 0 := by
          rw [Finset.sum_insert ha_not_mem] at hcoord
          simp only [map_add, map_sum, map_smul, map_zero, LinearMap.coe_comp,
            Function.comp_apply, smul_eq_mul] at hcoord
          -- Applying `N.subtype` is definitionally the coercion used by `coord_pivot_eq`.
          rw [hsum_zero, add_zero, show b.coord a.1 (N.subtype (pivot a)) = generator (I a) by
            simpa using coord_pivot_eq a] at hcoord
          exact hcoord
        exact (mul_eq_zero.mp hprod).resolve_right a.2
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact ha_zero
      · apply ih g
        · simpa [Finset.sum_insert, ha_not_mem, ha_zero] using hsum
        · exact hi
  let P : Submodule R N := span R (Set.range pivot)
  have repr_support_nonempty {y : N} (hy : y ≠ 0) :
      (b.repr (y : M)).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hsupp
    apply hy
    apply Subtype.ext
    apply b.repr.injective
    simpa using Finsupp.support_eq_empty.mp hsupp
  have mem_P_of_bounded : ∀ i : ι, ∀ y : N,
      (↑(b.repr (y : M)).support : Set ι) ⊆ Set.Iic i → y ∈ P := by
    intro i
    refine (inferInstance : IsWellOrder ι (· < ·)).wf.induction i
      (C := fun i ↦ ∀ y : N,
        (↑(b.repr (y : M)).support : Set ι) ⊆ Set.Iic i → y ∈ P) ?_
    intro i ih y hy
    have lower (z : N) (hz : (↑(b.repr (z : M)).support : Set ι) ⊆ Set.Iic i)
        (hcoord : b.coord i z = 0) : z ∈ P := by
      by_cases hz0 : z = 0
      · simp [hz0]
      have hsupp := repr_support_nonempty hz0
      let j := (b.repr (z : M)).support.max' hsupp
      have hj_mem : j ∈ (b.repr (z : M)).support := Finset.max'_mem _ _
      have hj_le : j ≤ i := hz hj_mem
      have hj_ne : j ≠ i := by
        intro hji
        subst hji
        exact (Finsupp.mem_support_iff.mp hj_mem) hcoord
      have hj_lt : j < i := lt_of_le_of_ne hj_le hj_ne
      apply ih j hj_lt z
      intro k hk
      exact Finset.le_max' _ _ hk
    by_cases hcoord : b.coord i y = 0
    · exact lower y hy hcoord
    have hy_span : (y : M) ∈ span R (b '' Set.Iic i) := by
      rw [b.mem_span_image]
      exact fun j hj ↦ hy hj
    have hy_mem_I : b.coord i y ∈ I i := by
      apply Submodule.mem_map.mpr
      exact ⟨y, ⟨y.2, hy_span⟩, rfl⟩
    obtain ⟨c, hc⟩ := (mem_iff_generator_dvd (I i)).mp hy_mem_I
    have hgen : generator (I i) ≠ 0 := by
      intro hzero
      apply hcoord
      rw [hc, hzero, zero_mul]
    let ji : J := ⟨i, hgen⟩
    let z : N := y - c • pivot ji
    have hz_span : (z : M) ∈ span R (b '' Set.Iic i) := by
      exact sub_mem hy_span (smul_mem _ _ (hx_span i))
    have hz_support : (↑(b.repr (z : M)).support : Set ι) ⊆ Set.Iic i := by
      intro j hj
      exact (b.mem_span_image.mp hz_span) hj
    have hz_coord : b.coord i z = 0 := by
      -- Unfolding `z` through the subtype coercion turns its coordinate into a difference.
      rw [show (z : M) = (y : M) - c • (pivot ji : M) from rfl, map_sub, map_smul]
      -- The value of `ji` is definitionally `i`, so the pivot-coordinate lemma applies.
      rw [show b.coord i (pivot ji : M) = generator (I i) by
        simpa [ji] using coord_pivot_eq ji, hc, smul_eq_mul, mul_comm, sub_self]
    have hz_mem : z ∈ P := lower z hz_support hz_coord
    have hpivot : pivot ji ∈ P := subset_span (Set.mem_range_self ji)
    have : y = z + c • pivot ji := by simp [z]
    rw [this]
    exact add_mem hz_mem (smul_mem P c hpivot)
  have span_pivot_eq_top : P = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy0 : y = 0
    · simp [hy0]
    have hsupp := repr_support_nonempty hy0
    let i := (b.repr (y : M)).support.max' hsupp
    apply mem_P_of_bounded i y
    intro j hj
    exact Finset.le_max' _ _ hj
  apply Module.Free.of_basis
  apply Basis.mk pivot_linearIndependent
  simpa [P] using span_pivot_eq_top.ge

end Submodule
