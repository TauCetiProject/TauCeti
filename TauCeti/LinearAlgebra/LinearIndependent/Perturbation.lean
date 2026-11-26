/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Order.Filter.Cofinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import TauCeti.LinearAlgebra.Matrix.Determinant.Pencil

/-!
# Linear independence survives generic perturbations

Let `x` be a finite linearly independent family in a vector space over a field `K`, and let `y`
be any family with the same index type. Then `x + c • y` is linearly independent for all but
finitely many scalars `c`. In coordinates dual to `x`, the family `x + c • y` has the matrix
`1 + c • B`, whose determinant is a polynomial in `c` with constant term `1`; it therefore
vanishes at only finitely many `c`.

Over an infinite field this produces a perturbation of a prescribed shape, for instance with `c`
a nonzero natural number in characteristic zero, that keeps the family independent. This is how
an independent family of iterates is enlarged in the proof of the cyclic-vector theorem.

## Main results

* `LinearIndependent.eventually_cofinite_add_smul`: `x + c • y` is linearly independent for all
  but finitely many `c`.
-/

public section

open Polynomial

namespace LinearIndependent

variable {ι K V : Type*} [Finite ι] [Field K] [AddCommGroup V] [Module K V]

/-- A finite linearly independent family `x` stays linearly independent when perturbed to
`x + c • y`, for all but finitely many scalars `c`. -/
theorem eventually_cofinite_add_smul {x : ι → V} (hx : LinearIndependent K x) (y : ι → V) :
    ∀ᶠ c : K in Filter.cofinite, LinearIndependent K (x + c • y) := by
  classical
  have := Fintype.ofFinite ι
  -- Coordinate functionals dual to `x`, extended from the span of `x` to all of `V`.
  choose φ hφ using fun i ↦ LinearMap.exists_extend ((Module.Basis.span hx).coord i)
  have hφx (i j : ι) : φ i (x j) = (1 : Matrix ι ι K) i j := by
    have h := LinearMap.congr_fun (hφ i) ⟨x j, Submodule.subset_span (Set.mem_range_self j)⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, ← Module.Basis.span_apply hx j]
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  let B : Matrix ι ι K := Matrix.of fun i j ↦ φ i (y j)
  let P : K[X] := (1 + (X : K[X]) • B.map C).det
  have hP (c : K) : P.eval c = (1 + c • B).det := by
    simpa [P, add_comm] using eval_det_X_add_C B 1 c
  have hP0 : P ≠ 0 := fun h ↦ by
    have h0 := hP 0
    rw [h, eval_zero, zero_smul, add_zero, Matrix.det_one] at h0
    exact zero_ne_one h0
  filter_upwards [eventually_eval_ne_zero_cofinite hP0] with c hc
  rw [hP] at hc
  refine LinearIndependent.of_comp (LinearMap.pi φ) ?_
  convert Matrix.linearIndependent_cols_of_det_ne_zero hc using 1
  ext j i
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, LinearMap.pi_apply, map_add,
    map_smul, hφx, Matrix.col, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, B,
    Matrix.of_apply, smul_eq_mul]

end LinearIndependent
