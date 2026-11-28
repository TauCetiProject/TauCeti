/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent initial segments of an orbit

For any map `F : V → V` on a finite-dimensional vector space and a nonzero vector `v`, the orbit
`v, F v, F² v, …` cannot stay linearly independent forever. Its longest independent initial
segment `v, F v, …, Fⁿ v` therefore spans the next iterate `Fⁿ⁺¹ v`. No linearity of `F` is
assumed, so this applies to semilinear maps, such as Frobenius-semilinear ones.

## Main results

* `Function.exists_linearIndependent_iterate_mem_span`: some initial segment `v, …, Fⁿ v` of the
  orbit is linearly independent and spans `Fⁿ⁺¹ v`.
-/

public section

open Function Submodule Module

namespace Function

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- For a map `F` and a nonzero vector `v` of a finite-dimensional space, some initial segment
`v, F v, …, Fⁿ v` of the orbit is linearly independent and spans `Fⁿ⁺¹ v`. -/
theorem exists_linearIndependent_iterate_mem_span [FiniteDimensional K V] (F : V → V) {v : V}
    (hv : v ≠ 0) :
    ∃ n, LinearIndependent K (fun i : Fin (n + 1) ↦ F^[i] v) ∧
      F^[n + 1] v ∈ span K (Set.range fun i : Fin (n + 1) ↦ F^[i] v) := by
  classical
  have key (m : ℕ) (h : ∀ j < m, F^[j] v ∉ span K (Set.range fun i : Fin j ↦ F^[i] v)) :
      LinearIndependent K (fun i : Fin m ↦ F^[i] v) := by
    induction m with
    | zero => exact linearIndependent_empty_type
    | succ m ih =>
      have hsnoc : (fun i : Fin (m + 1) ↦ F^[i] v) =
          Fin.snoc (fun i : Fin m ↦ F^[i] v) (F^[m] v) := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
      rw [hsnoc, linearIndependent_finSnoc]
      exact ⟨ih fun j hj ↦ h j (by omega), h m (by omega)⟩
  have hex : ∃ m, F^[m] v ∈ span K (Set.range fun i : Fin m ↦ F^[i] v) := by
    by_contra! h
    have := LinearIndependent.fintype_card_le_finrank (key (finrank K V + 1) fun j _ ↦ h j)
    simp at this
  obtain ⟨m, hm, hmin⟩ : ∃ m, F^[m] v ∈ span K (Set.range fun i : Fin m ↦ F^[i] v) ∧
      ∀ j < m, F^[j] v ∉ span K (Set.range fun i : Fin j ↦ F^[i] v) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ Nat.find_min hex hj⟩
  obtain _ | n := m
  · simp [hv] at hm
  · exact ⟨n, key _ hmin, hm⟩

end Function
