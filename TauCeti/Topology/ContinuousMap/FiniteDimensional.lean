/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Separation.Connected

/-!
# Finite-dimensional subalgebras of continuous functions

An element `f` of a finite-dimensional subalgebra of `C(X, 𝕜)` satisfies a nonzero polynomial
equation: the powers `f, f², f³, …` are linearly dependent. So `f` takes only finitely many
values. If `X` is preconnected and `𝕜` is a T1 space, the range of `f` is a finite preconnected
subset of `𝕜`, hence a point, and `f` is constant.

## Main statements

* `ContinuousMap.finite_range_of_mem_finiteDimensional`: elements of a finite-dimensional
  subalgebra of `C(X, 𝕜)` have finite range.
* `ContinuousMap.apply_eq_apply_of_mem_finiteDimensional`: on a preconnected space, with `𝕜` a
  T1 space, they are constant.
-/

public section

namespace ContinuousMap

variable {X 𝕜 : Type*} [TopologicalSpace X] [Field 𝕜] [TopologicalSpace 𝕜]
  [IsTopologicalRing 𝕜]

/-- An element of a finite-dimensional subalgebra of `C(X, 𝕜)` takes finitely many values: its
powers are linearly dependent, so its values are roots of a nonzero polynomial. -/
theorem finite_range_of_mem_finiteDimensional (S : NonUnitalSubalgebra 𝕜 C(X, 𝕜))
    [FiniteDimensional 𝕜 S] {f : C(X, 𝕜)} (hf : f ∈ S) : (Set.range f).Finite := by
  have hpow (k : ℕ) : f ^ (k + 1) ∈ S := by
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [pow_succ]; exact mul_mem ih hf
  obtain ⟨s, g, hsum, i, hi, hgi⟩ := not_linearIndependent_iff.1
    (Module.Finite.not_linearIndependent_of_infinite (R := 𝕜)
      (fun k : ℕ ↦ (⟨f ^ (k + 1), hpow k⟩ : S)))
  set P : Polynomial 𝕜 := ∑ k ∈ s, Polynomial.C (g k) * Polynomial.X ^ (k + 1)
  have hP : P ≠ 0 := by
    intro h0
    have := congrArg (fun p : Polynomial 𝕜 ↦ p.coeff (i + 1)) h0
    exact hgi (by simpa [P, hi] using this)
  refine (Polynomial.finite_setOfPred_isRoot hP).subset ?_
  rintro _ ⟨x, rfl⟩
  have := congrArg (fun h : S ↦ (h : C(X, 𝕜)) x) hsum
  simpa [P, Polynomial.eval_finsetSum] using this

/-- On a preconnected space, with `𝕜` a T1 space, an element of a finite-dimensional subalgebra of
`C(X, 𝕜)` is constant. -/
theorem apply_eq_apply_of_mem_finiteDimensional [PreconnectedSpace X] [T1Space 𝕜]
    (S : NonUnitalSubalgebra 𝕜 C(X, 𝕜)) [FiniteDimensional 𝕜 S] {f : C(X, 𝕜)} (hf : f ∈ S)
    (x y : X) : f x = f y := by
  by_contra h
  exact (isPreconnected_range f.continuous).infinite_of_nontrivial
    ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, h⟩ (finite_range_of_mem_finiteDimensional S hf)

end ContinuousMap
