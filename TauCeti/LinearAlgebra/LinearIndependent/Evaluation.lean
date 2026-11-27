/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Evaluation determinants and linear independence of functions

A finite family of functions on an arbitrary set is linearly independent exactly when some
square evaluation matrix is invertible. The domain need not be finite.

## Provenance

`TauCeti.det_eval_eq_zero_iff_not_linearIndependent` adapts
`New.det_eval_eq_zero_iff_not_linearIndependent` in
`src/Lib/General/LinearAlgebra/MatrixPolynomials.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC).

## References

This is the usual dual spanning criterion, applied to the determinant.
-/

public section

open Matrix Function

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

/-- Functions `v j : X → k` to a field, indexed by the finite type `n`, are linearly dependent if
and only if, for every family of points `x : n → X`, the determinant of the square evaluation
matrix `of (flip v ∘ x)`, with entries `v j (x i)`, is zero. -/
theorem TauCeti.det_eval_eq_zero_iff_not_linearIndependent {X : Type*} {v : n → X → k} :
    (∀ x : n → X, det (of (flip v ∘ x)) = 0) ↔ ¬LinearIndependent k v := by
  refine ⟨fun h_det h_indep ↦ ?_, fun h_dep x ↦ ?_⟩
  · -- If `v` is independent, the vectors `(v i x)_i` span `n → k`, so the determinant, which is
    -- multilinear in the rows and vanishes on all families of them, would be zero.
    have h_span : Submodule.span k (Set.range (flip v)) = ⊤ :=
      span_flip_eq_top_iff_linearIndependent.2 h_indep
    have h_zero : (detRowAlternating (n := n) (R := k)).toMultilinearMap = 0 :=
      MultilinearMap.ext_of_span_eq_top (fun _ ↦ h_span) h_det
    have h_one : det (1 : Matrix n n k) = 0 := DFunLike.congr_fun h_zero (1 : Matrix n n k)
    simp at h_one
  · -- A relation among the `v i` is a relation among the columns.
    exact det_eq_zero_of_not_linearIndependent_cols fun h_cols ↦
      h_dep (.of_comp (LinearMap.funLeft k k x) h_cols)
