/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import TauCeti.Analysis.CStarAlgebra.AF.Basic
public import TauCeti.Topology.ContinuousMap.FiniteDimensional

/-!
# AF algebras of continuous functions on a connected space are trivial

Every element of a finite-dimensional subalgebra of `C(X, 𝕜)` is constant when `X` is
preconnected and `𝕜` is a T1 space such as `ℂ`
(`ContinuousMap.apply_eq_apply_of_mem_finiteDimensional`). Consequently, if `X` is
compact and preconnected and `C(X, ℂ)` is AF, then the dense union of its finite-dimensional
stages consists of constant functions, and so does `C(X, ℂ)`. So `C(X, ℂ)` is not AF once some
continuous `X → ℂ` is non-constant, e.g. when `X` is compact Hausdorff, connected and has two
points; for instance `C([0, 1], ℂ)` is not AF.

## Main statements

* `TauCeti.IsAF.continuousMap_apply_eq_apply`: if `X` is compact and preconnected and `C(X, ℂ)`
  is AF, then every continuous function `X → ℂ` is constant.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- If `X` is compact and preconnected and `C(X, ℂ)` is AF, then every continuous function
`X → ℂ` is constant. So `C(X, ℂ)` is not AF when `X` is compact and preconnected and some
continuous `X → ℂ` is non-constant. -/
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
