/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Set.Finite.Lattice

/-!
# Avoiding finitely many linear equations in a coset

Over an infinite domain, finitely many linear equations with torsion-free targets can be
avoided in any coset of a submodule on which none of the linear maps vanishes. This allows
one to perturb an element while preserving a congruence, and simultaneously keep its images
under finitely many derivations nonzero.

The argument chooses a line in the coset: each equation that is not constant on the line
excludes at most one scalar. It works over an infinite domain, without requiring the source
to be a vector space.

This is the coset analogue over a domain of Mathlib's
`Submodule.exists_forall_notMem_of_forall_ne_top`, which treats submodules over an infinite field.
-/

public section

namespace LinearMap

variable {R M ι : Type*} [Ring R] [IsDomain R] [Infinite R]
  [AddCommGroup M] [Module R M]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, Module.IsTorsionFree R (N i)]

/-- Over an infinite domain, finitely many linear maps to torsion-free modules can
simultaneously be made nonzero in any coset of a submodule on which each map is nonzero. -/
theorem exists_mem_forall_apply_add_ne_zero [Finite ι] (f : ∀ i, M →ₗ[R] N i)
    (U : Submodule R M) (hU : ∀ i, ∃ y ∈ U, f i y ≠ 0) (z : M) :
    ∃ x ∈ U, ∀ i, f i (z + x) ≠ 0 := by
  classical
  have aux (s : Finset ι) : ∃ x ∈ U, ∀ i ∈ s, f i (z + x) ≠ 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, U.zero_mem, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨x, hxU, hx⟩ := ih
      obtain ⟨y, hyU, hy⟩ := hU j
      have hfinite (i : ι) (hi : i ∈ insert j s) :
          Set.Finite {c : R | f i (z + x + c • y) = 0} := by
        by_cases hyi : f i y = 0
        · have hxi : f i (z + x) ≠ 0 := by
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact (hy hyi).elim
            · exact hx i hi
          have hempty : {c : R | f i (z + x + c • y) = 0} = ∅ := by
            ext c
            simp only [map_add, map_smul, hyi, smul_zero, add_zero, Set.mem_ofPred_eq,
              Set.mem_empty_iff_false, iff_false]
            simpa only [map_add] using hxi
          rw [hempty]
          exact Set.finite_empty
        · apply Set.Subsingleton.finite
          intro a ha b hb
          apply smul_left_injective R hyi
          have hab : f i (z + x) + a • f i y = f i (z + x) + b • f i y := by
            simpa only [map_add, map_smul] using ha.trans hb.symm
          exact add_left_cancel hab
      obtain ⟨c, hc⟩ := (Set.Finite.biUnion (s := (↑(insert j s) : Set ι))
        (Set.toFinite _) hfinite).exists_notMem
      refine ⟨x + c • y, U.add_mem hxU (U.smul_mem c hyU), ?_⟩
      intro i hi hzero
      apply hc
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, by
        simpa only [Set.mem_ofPred_eq, add_assoc] using hzero⟩⟩
  let := Fintype.ofFinite ι
  obtain ⟨x, hxU, hx⟩ := aux Finset.univ
  exact ⟨x, hxU, fun i ↦ hx i (Finset.mem_univ i)⟩

end LinearMap
