/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.End.Recursion
public import TauCeti.LinearAlgebra.Graded.History.Expansion
public import Mathlib.Combinatorics.Quiver.SingleObj
import TauCeti.LinearAlgebra.Graded.History.Filtration

/-!
# Homogeneous histories of finite recursions

The finite geometric solution operator is the sum of its homogeneous histories.
For a finitely generated input range the same finite supports describe every input,
also after a linear output map. If every component transfer raises a finite-length
filtration, selected sums stabilize once they reach its length, since all later
histories vanish individually.

Adapted from `Mei/LinearAlgebra/GradedModule/History/Recursion.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public noncomputable section

open Quiver TauCeti

namespace Module.End

/-- The path recording `n` applications of a single endomorphism. -/
abbrev recursionPath (n : ℕ) : Path (SingleObj.star Unit) (SingleObj.star Unit) :=
  SingleObj.listToPath (List.replicate n ())

/-- The number of arrows in the recursion path is the number of iterations. -/
@[simp]
theorem length_recursionPath (n : ℕ) : (recursionPath n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [recursionPath, List.replicate_succ, SingleObj.listToPath, Path.length_cons]
    exact congrArg Nat.succ ih

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (U : Module.End R M)

private theorem composeLinear_recursionPath (n : ℕ) :
    (recursionPath n).composeLinear (M := fun _ => M) (fun _ => U) = U ^ n := by
  induction n with
  | zero => simp [recursionPath, one_eq_id]
  | succ n ih =>
    simp only [recursionPath, List.replicate_succ, SingleObj.listToPath,
      Path.composeLinear_cons, pow_succ']
    rw [ih, Module.End.mul_eq_comp]

variable [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The finite geometric solution is the sum of all contributing homogeneous
histories of lengths below the cutoff. -/
theorem sum_homogeneousHistory_eq_finiteRecursion (r : ℕ) (x : M) :
    (∑ j ∈ Finset.range r,
      ∑ d ∈ (recursionPath j).historySupport (fun _ => U) (fun _ => ℳ) x,
        (recursionPath j).homogeneousHistory (fun _ => U) (fun _ => ℳ) d x) =
      U.finiteRecursion r x := by
  rw [finiteRecursion_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Path.sum_homogeneousHistory, composeLinear_recursionPath]

/-- A family solving a nilpotent linear recursion on a finitely generated
input range has finite history supports common to every input. The resulting
linear identity holds after every linear output map, with the same supports. -/
theorem exists_uniform_history_expansion_of_eq_add {E : Type*}
    [AddCommMonoid E] [Module R E] (a x : E →ₗ[R] M) (ha : (LinearMap.range a).FG)
    {r : ℕ} (hU : U ^ r = 0) (hx : x = a + U.comp x) :
    ∃ S : (j : ℕ) → Finset ((recursionPath j).Degrees (fun _ => ι)),
      (∀ j < r, ∀ d ∉ S j,
        ((recursionPath j).homogeneousHistory (fun _ => U) (fun _ => ℳ) d).comp a = 0) ∧
      ∀ {O : Type*} [AddCommMonoid O] [Module R O] (b : M →ₗ[R] O),
        (∑ j ∈ Finset.range r, ∑ d ∈ S j,
          b.comp (((recursionPath j).homogeneousHistory (fun _ => U) (fun _ => ℳ) d).comp a)) =
          b.comp x := by
  classical
  have hs (j : ℕ) :=
    Path.exists_uniform_historySupport (fun _ => U) (fun _ => ℳ) (recursionPath j) a ha
  choose S hS using hs
  have hsol : x = (U.finiteRecursion r).comp a := by
    ext y
    exact U.eq_finiteRecursion_of_eq_add hU (LinearMap.congr_fun hx y)
  refine ⟨S, fun j _ => hS j, ?_⟩
  intro O _ _ b
  calc
    _ = ∑ j ∈ Finset.range r, b.comp ((U ^ j).comp a) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Path.sum_comp_homogeneousHistory_comp_eq _ _ _ _ _ _ (hS j),
        composeLinear_recursionPath]
    _ = b.comp x := by
      rw [hsol]
      ext y
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, finiteRecursion_apply, map_sum]

open Classical in
/-- Selected history sums stabilize above the vanishing step of a decreasing
filtration. The input need only lie in its zeroth step, and the selected sets
need not cover all contributing histories. -/
theorem sum_selected_homogeneousHistory_eq_of_components_raise
    {F : ℕ → Submodule R M} (hanti : Antitone F)
    (hF : ∀ i k {x : M}, x ∈ F k → homogeneousComponent ℳ i (U x) ∈ F (k + 1))
    {r s : ℕ} (hr : F r = ⊥) (hrs : r ≤ s) {x : M} (hx : x ∈ F 0)
    (S : (j : ℕ) → Finset ((recursionPath j).Degrees (fun _ => ι))) :
    (∑ j ∈ Finset.range s,
      ∑ d ∈ S j, (recursionPath j).homogeneousHistory (fun _ => U) (fun _ => ℳ) d x) =
    ∑ j ∈ Finset.range r,
      ∑ d ∈ S j, (recursionPath j).homogeneousHistory (fun _ => U) (fun _ => ℳ) d x := by
  symm
  apply Finset.sum_subset (Finset.range_mono hrs)
  intro j _ hj
  have hjr : r ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  apply Finset.sum_eq_zero
  intro d _
  exact Path.homogeneousHistory_eq_zero_of_le_length (fun _ => U) (fun _ => ℳ)
    (F := fun _ => F) (fun {_ _} _ i k {_} h => hF i k h) (recursionPath j) d hanti hr
    (by simpa only [Nat.zero_add, length_recursionPath] using hjr) hx

end Module.End
