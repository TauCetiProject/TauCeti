/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Finite recursion for nilpotent endomorphisms

If `U ^ r = 0`, the equation `x = a + U x` has the unique solution
`∑ j ∈ Finset.range r, (U ^ j) a`. The solution is linear in `a`, independent
of the nilpotency bound, and natural under intertwining linear maps.

The proofs work over a semiring on an additive commutative monoid: neither
subtraction nor additive cancellation is needed. In particular, the comparison
of two independently established recursions applies to semimodule coefficients.
Any additive submonoid preserved by the endomorphism is preserved by finite
recursion and contains the nilpotent recursion solution whenever it contains the input.
A finite-length filtration raised by the endomorphism supplies the nilpotence bound through
`Module.End.pow_eq_zero_of_map_le`. No decreasingness or completeness assumption is needed
for that finite-length criterion.

## Attribution

Adapted from `Mei/LinearAlgebra/End/Recursion.lean` in Mei at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/LinearAlgebra/End/Recursion.lean
-/

public section

namespace Module.End

variable {R M N : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (U : Module.End R M)

/-- The finite geometric sum, regarded as a linear solution operator. -/
def finiteRecursion (r : ℕ) : Module.End R M :=
  ∑ j ∈ Finset.range r, U ^ j

/-- A recursion with no iterations has zero solution operator. -/
@[simp]
theorem finiteRecursion_zero : U.finiteRecursion 0 = 0 := by
  simp [finiteRecursion]

/-- Evaluating the solution operator gives the finite sum of iterates. -/
theorem finiteRecursion_apply (r : ℕ) (a : M) :
    U.finiteRecursion r a = ∑ j ∈ Finset.range r, (U ^ j) a := by
  simp only [finiteRecursion, LinearMap.sum_apply]

/-- Finite recursion preserves any additive submonoid preserved by the endomorphism.
No nilpotence, grading, or order on the coefficient semiring is required. -/
theorem finiteRecursion_mem (S : AddSubmonoid M) (hS : ∀ x ∈ S, U x ∈ S)
    (r : ℕ) {a : M} (ha : a ∈ S) : U.finiteRecursion r a ∈ S := by
  rw [finiteRecursion_apply]
  exact S.sum_mem (fun j _ => (pow_apply_eq_iterate U j a).symm ▸
    Set.MapsTo.iterate (f := U) (s := S) hS j ha)

/-- A nilpotency bound makes the solution operator satisfy `1 + U * S = S`. -/
theorem finiteRecursion_eq_one_add_mul {r : ℕ} (hU : U ^ r = 0) :
    U.finiteRecursion r = 1 + U * U.finiteRecursion r := by
  rw [finiteRecursion, add_comm 1, ← geom_sum_succ, Finset.sum_range_succ, hU, add_zero]

/-- A nilpotency bound makes the finite geometric sum solve the recursion. -/
theorem finiteRecursion_eq_add {r : ℕ} (hU : U ^ r = 0) (a : M) :
    U.finiteRecursion r a = a + U (U.finiteRecursion r a) :=
  LinearMap.congr_fun (U.finiteRecursion_eq_one_add_mul hU) a

/-- Any solution equals the finite geometric sum. -/
theorem eq_finiteRecursion_of_eq_add {r : ℕ} (hU : U ^ r = 0)
    {a x : M} (hx : x = a + U x) : x = U.finiteRecursion r a := by
  -- Unrolling retains the remainder `U ^ n x`, so no cancellation is needed.
  have expand (n : ℕ) :
      x = (∑ j ∈ Finset.range n, (U ^ j) a) + (U ^ n) x := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : (U ^ n) x = (U ^ n) a + (U ^ (n + 1)) x := by
        simpa only [map_add, pow_succ, mul_apply_eq_comp] using congrArg (U ^ n) hx
      calc
        x = (∑ j ∈ Finset.range n, (U ^ j) a) + (U ^ n) x := ih
        _ = (∑ j ∈ Finset.range (n + 1), (U ^ j) a) + (U ^ (n + 1)) x := by
          rw [hn, Finset.sum_range_succ, add_assoc]
  simpa [hU, finiteRecursion_apply] using expand r

/-- Two independently constructed solutions of the same nilpotent recursion agree. -/
theorem eq_of_eq_add_of_pow_eq_zero {r : ℕ} (hU : U ^ r = 0)
    {a x y : M} (hx : x = a + U x) (hy : y = a + U y) : x = y :=
  (U.eq_finiteRecursion_of_eq_add hU hx).trans
    (U.eq_finiteRecursion_of_eq_add hU hy).symm

/-- Nilpotent linear recursions have exactly one solution over semimodules. -/
theorem existsUnique_eq_add_of_pow_eq_zero {r : ℕ} (hU : U ^ r = 0) (a : M) :
    ∃! x, x = a + U x :=
  ⟨U.finiteRecursion r a, U.finiteRecursion_eq_add hU a,
    fun _ hx => U.eq_finiteRecursion_of_eq_add hU hx⟩

/-- Every solution of a nilpotent recursion belongs to an additive submonoid
containing its input and preserved by the endomorphism. -/
theorem mem_of_eq_add_of_pow_eq_zero (S : AddSubmonoid M)
    (hS : ∀ x ∈ S, U x ∈ S) {r : ℕ} (hnil : U ^ r = 0)
    {a x : M} (ha : a ∈ S) (hx : x = a + U x) : x ∈ S := by
  rw [U.eq_finiteRecursion_of_eq_add hnil hx]
  exact U.finiteRecursion_mem S hS r ha

/-- The solution operator does not depend on the chosen nilpotency bound. -/
theorem finiteRecursion_eq {r s : ℕ} (hr : U ^ r = 0) (hs : U ^ s = 0) :
    U.finiteRecursion r = U.finiteRecursion s := by
  ext a
  exact U.eq_of_eq_add_of_pow_eq_zero hr
    (U.finiteRecursion_eq_add hr a) (U.finiteRecursion_eq_add hs a)

/-- Intertwining maps preserve solutions, even with different nilpotency bounds. -/
theorem comp_finiteRecursion (V : Module.End R N) (f : M →ₗ[R] N)
    (hf : f.comp U = V.comp f) {r s : ℕ} (hU : U ^ r = 0) (hV : V ^ s = 0) :
    f.comp (U.finiteRecursion r) = (V.finiteRecursion s).comp f := by
  ext a
  apply V.eq_finiteRecursion_of_eq_add hV
  have h := congrArg f (U.finiteRecursion_eq_add hU a)
  have hf' (x : M) : f (U x) = V (f x) := LinearMap.congr_fun hf x
  simpa only [map_add, hf', LinearMap.comp_apply] using h

end Module.End
