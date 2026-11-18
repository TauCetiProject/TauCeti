/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coordinate bounds from linear forms at an absolute value

If finitely many linear forms `l k` span the dual of `R^ι`, every coordinate projection is a
combination of them. At an absolute value `v`, a bound `v (l k x) ≤ M` on all the forms therefore
bounds every coordinate of `x` by a constant times `M`, where the constant depends on `v` and `l`
but not on `x` or `M` (`AbsoluteValue.exists_one_le_forall_apply_le_mul`).
-/

public section

open Finset

namespace AbsoluteValue

/-- If finitely many linear forms `l k` span the dual of `R^ι`, then some constant `C ≥ 1`
(depending only on `v` and `l`) bounds every coordinate `v (x j)` by `C * M` whenever `0 ≤ M` and
`v (l k x) ≤ M` for all `k`. -/
theorem exists_one_le_forall_apply_le_mul {R S ι κ : Type*} [CommSemiring R] [Semiring S]
    [PartialOrder S] [IsOrderedRing S] [Finite ι] [Finite κ] (v : AbsoluteValue R S)
    {l : κ → Module.Dual R (ι → R)} (hl : Submodule.span R (Set.range l) = ⊤) :
    ∃ C : S, 1 ≤ C ∧ ∀ ⦃M : S⦄, 0 ≤ M → ∀ ⦃x : ι → R⦄, (∀ k, v (l k x) ≤ M) →
      ∀ j, v (x j) ≤ C * M := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  -- Write each coordinate form as a combination of the forms `l k`.
  choose a ha using fun j : ι ↦ (Submodule.mem_span_range_iff_exists_fun R).mp
    (hl ▸ Submodule.mem_top : LinearMap.proj (φ := fun _ : ι ↦ R) j ∈ _)
  refine ⟨1 + ∑ j, ∑ k, v (a j k),
    le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ v.nonneg _),
    fun M hM x hx j ↦ ?_⟩
  have hxj : x j = ∑ k, a j k * l k x := by
    simpa using (LinearMap.congr_fun (ha j) x).symm
  calc v (x j) ≤ ∑ k, v (a j k) * v (l k x) := by
        rw [hxj]
        exact (v.sum_le _ _).trans_eq (by simp only [map_mul])
    _ ≤ ∑ k, v (a j k) * M := sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hx k) (v.nonneg _)
    _ = (∑ k, v (a j k)) * M := (sum_mul _ _ _).symm
    _ ≤ (1 + ∑ j, ∑ k, v (a j k)) * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        refine (single_le_sum (f := fun j ↦ ∑ k, v (a j k))
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ v.nonneg _) (mem_univ j)).trans ?_
        exact le_add_of_nonneg_left zero_le_one

end AbsoluteValue
