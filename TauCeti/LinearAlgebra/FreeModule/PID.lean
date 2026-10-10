/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Cardinal.Order

/-!
# Submodules of free modules over principal ideal rings without zero divisors

Every submodule of a free module over a principal ideal ring without zero divisors is free,
without a finiteness hypothesis on the ambient module. The construction well-orders an ambient basis
and chooses a pivot for each nonzero ideal of possible leading coordinates. The pivots form a basis
of the submodule by elimination of the greatest coordinate in the finite support of each vector.

This is the arbitrary-rank form of Lang, *Algebra*, Chapter III, Theorem 7.1.  Mathlib's
`Submodule.nonempty_basis_of_pid` is the finite-rank form.  A projective module embeds in a free
module, so every submodule of a projective module is free as well
(`Submodule.free_of_projective_of_isPrincipalIdealRing`).
-/

public section

open Module Set Submodule
open Submodule.IsPrincipal

namespace Submodule

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [NoZeroDivisors R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

/-- Every submodule of a free module over a principal ideal ring without zero divisors is free,
with no finiteness assumption on either module. -/
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
  -- In a relation among pivots, its greatest index isolates one nonzero coordinate.
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
        have hsum_zero : ∑ j ∈ s, g j * b.coord a.1 (pivot j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp [coord_pivot_eq_zero (hsa j hj)]
        simp only [Finset.sum_insert ha_not_mem, map_add, map_sum, map_smul, map_zero,
          LinearMap.comp_apply, Submodule.subtype_apply, smul_eq_mul,
          coord_pivot_eq, hsum_zero, add_zero] at hcoord
        exact (mul_eq_zero.mp hcoord).resolve_right a.2
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha_zero
      · apply ih g
        · simpa [Finset.sum_insert, ha_not_mem, ha_zero] using hsum
        · exact hi
  let P : Submodule R N := span R (Set.range pivot)
  have repr_support_nonempty {y : N} (hy : y ≠ 0) :
      (b.repr (y : M)).support.Nonempty := by
    simpa only [Finsupp.support_nonempty_iff, LinearEquiv.map_ne_zero_iff,
      ne_eq, Submodule.coe_eq_zero] using hy
  -- Eliminate the greatest coordinate; the well-order makes this termination argument valid
  -- even when the ambient basis has arbitrary cardinality.
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
      simp only [z, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
      rw [hx_coord i, hc, smul_eq_mul, mul_comm, sub_self]
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

/-- Every submodule of a projective module over a principal ideal ring without zero divisors is
free: a projective module `M` embeds in the free module `M →₀ R`, and the image of the submodule
is a submodule of a free module. -/
theorem free_of_projective_of_isPrincipalIdealRing (N : Submodule R M) [Module.Projective R M] :
    Module.Free R N := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp ‹Module.Projective R M›
  have := (N.map s).free_of_isPrincipalIdealRing
  exact .of_equiv (N.equivMapOfInjective s hs.injective).symm

end Submodule
