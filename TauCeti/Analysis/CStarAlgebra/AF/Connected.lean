/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Topology.Separation.Connected
public import TauCeti.Analysis.CStarAlgebra.AF.Basic

/-!
# Continuous functions on a connected space are not AF

An element `f` of a finite-dimensional subalgebra of `C(X, 𝕜)` satisfies a nonzero polynomial
equation: the powers `f, f², f³, …` are linearly dependent. So `f` takes only finitely many
values (`ContinuousMap.finite_range_of_mem_finiteDimensional`). If `X` is preconnected, the range
of `f` is preconnected, hence a point, and `f` is constant
(`ContinuousMap.apply_eq_apply_of_mem_finiteDimensional`). Consequently, if `X` is compact and
preconnected and `C(X, ℂ)` is AF, then the dense union of its finite-dimensional stages consists
of constant functions, and so does `C(X, ℂ)` (`TauCeti.IsAF.continuousMap_apply_eq_apply`). For
instance `C([0, 1], ℂ)` is not AF.

## Main statements

* `ContinuousMap.finite_range_of_mem_finiteDimensional`: elements of a finite-dimensional
  subalgebra of `C(X, 𝕜)` have finite range.
* `ContinuousMap.apply_eq_apply_of_mem_finiteDimensional`: on a preconnected space they are
  constant.
* `TauCeti.IsAF.continuousMap_apply_eq_apply`: if `X` is compact and preconnected and `C(X, ℂ)`
  is AF, then every continuous function `X → ℂ` is constant.
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

/-- On a preconnected space, an element of a finite-dimensional subalgebra of `C(X, 𝕜)` is
constant. -/
theorem apply_eq_apply_of_mem_finiteDimensional [PreconnectedSpace X] [T1Space 𝕜]
    (S : NonUnitalSubalgebra 𝕜 C(X, 𝕜)) [FiniteDimensional 𝕜 S] {f : C(X, 𝕜)} (hf : f ∈ S)
    (x y : X) : f x = f y := by
  by_contra h
  exact (isPreconnected_range f.continuous).infinite_of_nontrivial
    ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, h⟩ (finite_range_of_mem_finiteDimensional S hf)

end ContinuousMap

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **`C(X, ℂ)` is not AF for connected `X`**: if `X` is compact and preconnected and `C(X, ℂ)` is
AF, then every continuous function `X → ℂ` is constant. The finite-dimensional stages consist of
constant functions, and the constant functions form a closed set. -/
theorem IsAF.continuousMap_apply_eq_apply [PreconnectedSpace X] (h : IsAF C(X, ℂ))
    (f : C(X, ℂ)) (x y : X) : f x = f y := by
  obtain ⟨S, -, hS, hdense⟩ := isAF_iff.1 h
  have hclosed : IsClosed {g : C(X, ℂ) | g x = g y} :=
    isClosed_eq (continuous_eval_const x) (continuous_eval_const y)
  refine (hclosed.closure_subset_iff.2 ?_) (hdense f)
  simp only [Set.iUnion_subset_iff]
  intro n g hg
  have := hS n
  exact ContinuousMap.apply_eq_apply_of_mem_finiteDimensional
    (S n).toNonUnitalSubalgebra hg x y

end TauCeti
