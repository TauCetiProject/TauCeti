/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Set.Finite.Lattice

/-!
# Avoiding finitely many linear equations

Over an infinite domain, finitely many linear equations `f i x = w i` with torsion-free
targets can be avoided simultaneously, provided that none of them holds identically. Applied
to linear maps precomposed with multiplication by a scalar, this allows one to perturb an
element while preserving a congruence, and simultaneously keep its images under finitely many
derivations nonzero.

The argument chooses a line through a point avoiding all but one of the equations: each
equation that is not constant on the line excludes at most one scalar. It works over an
infinite domain, without requiring the source to be a vector space.

This is an affine analogue over a domain of Mathlib's
`Submodule.exists_forall_notMem_of_forall_ne_top`, which treats submodules over an infinite field.
-/
public section

namespace LinearMap

variable {R M ι : Type*} [Ring R] [IsDomain R] [Infinite R]
  [AddCommGroup M] [Module R M]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, Module.IsTorsionFree R (N i)]

/-- Over an infinite domain, finitely many linear equations `f i x = w i` with torsion-free
targets can be avoided simultaneously, provided that each of them fails somewhere. -/
theorem exists_forall_apply_ne [Finite ι] (f : ∀ i, M →ₗ[R] N i) (w : ∀ i, N i)
    (h : ∀ i, ∃ y, f i y ≠ w i) : ∃ x, ∀ i, f i x ≠ w i := by
  classical
  have aux (s : Finset ι) : ∃ x, ∀ i ∈ s, f i x ≠ w i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hy⟩ := h j
      have hfinite (i : ι) (hi : i ∈ insert j s) :
          Set.Finite {c : R | f i (x + c • (y - x)) = w i} := by
        by_cases hyi : f i (y - x) = 0
        · have hxi : f i x ≠ w i := by
            rcases Finset.mem_insert.mp hi with rfl | hi
            · rw [map_sub, sub_eq_zero, eq_comm] at hyi
              rwa [hyi]
            · exact hx i hi
          have hempty : {c : R | f i (x + c • (y - x)) = w i} = ∅ := by
            ext c
            simp only [map_add, map_smul, hyi, smul_zero, add_zero, Set.mem_ofPred_eq,
              Set.mem_empty_iff_false, iff_false]
            exact hxi
          rw [hempty]
          exact Set.finite_empty
        · apply Set.Subsingleton.finite
          intro a ha b hb
          apply smul_left_injective R hyi
          have hab : f i x + a • f i (y - x) = f i x + b • f i (y - x) := by
            simpa only [map_add, map_smul] using ha.trans hb.symm
          exact add_left_cancel hab
      obtain ⟨c, hc⟩ := (Set.Finite.biUnion (s := (↑(insert j s) : Set ι))
        (Set.toFinite _) hfinite).exists_notMem
      refine ⟨x + c • (y - x), fun i hi hzero ↦ hc ?_⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hzero⟩⟩
  let := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ := aux Finset.univ
  exact ⟨x, fun i ↦ hx i (Finset.mem_univ i)⟩

end LinearMap
