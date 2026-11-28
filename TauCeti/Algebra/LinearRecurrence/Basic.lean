/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.Ring

/-!
# Basic facts about linear recurrences

Explicit formula for `LinearRecurrence.charPoly` on an order-two recurrence `⟨2, ![a, b]⟩` over a
commutative ring.

## Main results

* `LinearRecurrence.charPoly_mk_two`:
  `(⟨2, ![a, b]⟩ : LinearRecurrence R).charPoly = X ^ 2 - C b * X - C a`.
* `LinearRecurrence.isSolution_sum_mul_pow`: a finite sum of geometric sequences with
  characteristic roots as bases is a solution.
* `LinearRecurrence.finrank_solSpace_eq_natDegree_charPoly`: the solution space has dimension
  equal to the degree of the characteristic polynomial.
-/

public section

open Polynomial

namespace LinearRecurrence

/-- The characteristic polynomial of the order-two linear recurrence `⟨2, ![a, b]⟩`
(`u (n + 2) = a * u n + b * u (n + 1)`) is `X ^ 2 - C b * X - C a`. -/
theorem charPoly_mk_two {R : Type*} [CommRing R] (a b : R) :
    (⟨2, ![a, b]⟩ : LinearRecurrence R).charPoly = X ^ 2 - C b * X - C a := by
  simp only [charPoly, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.val_zero, Fin.val_one, ← C_mul_X_pow_eq_monomial, pow_zero,
    pow_one, map_one, one_mul, mul_one]
  ring

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- Every finite linear combination of geometric sequences based at characteristic roots
solves the recurrence. -/
theorem isSolution_sum_mul_pow (s : Finset R) (hs : ∀ θ ∈ s, E.charPoly.IsRoot θ)
    (g : R → R) : E.IsSolution fun n ↦ ∑ θ ∈ s, g θ * θ ^ n := by
  have : (fun n ↦ ∑ θ ∈ s, g θ * θ ^ n) = ∑ θ ∈ s, g θ • fun n : ℕ ↦ θ ^ n := by
    ext n
    simp [Finset.sum_apply]
  rw [this, E.is_sol_iff_mem_solSpace]
  refine Submodule.sum_mem _ fun θ hθ ↦ Submodule.smul_mem _ _ ?_
  rw [← E.is_sol_iff_mem_solSpace, geom_sol_iff_root_charPoly]
  exact hs θ hθ

/-- The solution space has dimension equal to the degree of the characteristic polynomial. -/
theorem finrank_solSpace_eq_natDegree_charPoly [Nontrivial R] :
    Module.finrank R E.solSpace = E.charPoly.natDegree := by
  rw [Module.finrank_eq_of_rank_eq E.solSpace_rank,
    natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order]

/-- If the constant coefficient is nonzero, then every characteristic root is nonzero. -/
theorem ne_zero_of_mem_charPoly_roots [IsDomain R] {θ : R} (hθ : θ ∈ E.charPoly.roots)
    (h0 : E.charPoly.coeff 0 ≠ 0) : θ ≠ 0 := by
  rintro rfl
  exact h0 (coeff_zero_eq_zero_of_zero_isRoot (isRoot_of_mem_roots hθ))

end LinearRecurrence
