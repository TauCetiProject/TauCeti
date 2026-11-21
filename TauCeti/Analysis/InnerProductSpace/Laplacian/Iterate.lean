/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# Iterated Laplacians

On a finite-dimensional real inner product space `E`, the `r`-th iterated Laplacian `Δ^[r] f`
of a map of class `C^n` is of class `C^(n - 2r)`, and its derivatives are controlled by those of
`f`: pointwise, `‖D^m Δ^[r] f x‖ ≤ (dim E)^r ‖D^(m + 2r) f x‖`, and the same bound holds for the
differences of these derivatives at two points. In particular a Hölder bound on `D^(m + 2r) f`
gives one on `D^m Δ^[r] f`. These bound the data `D^m Δ^r g` whose Cauchy potentials are the time
derivatives `∂ₜ^r D^m u` of the solution of the heat equation with initial datum `g`.

## Main declarations

* `ContDiff.iterate_laplacian`: `Δ^[r]` loses `2r` derivatives.
* `TauCeti.norm_iteratedFDeriv_iterate_laplacian_le`: the pointwise bound.
* `TauCeti.norm_iteratedFDeriv_iterate_laplacian_sub_le`: the bound on differences.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `r`-th iterated Laplacian of a map of class `C^n`, `2r ≤ n`, is of class `C^(n - 2r)`. -/
theorem _root_.ContDiff.iterate_laplacian {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f) {r : ℕ}
    (h : 2 * r ≤ n) : ContDiff ℝ (n - 2 * r : ℕ) (Δ^[r] f) := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (ih (by omega)).laplacian (by norm_cast; omega)

/-- The derivatives of an iterated Laplacian are pointwise controlled by those of the map:
`‖D^m Δ^[r] f x‖ ≤ (dim E)^r ‖D^(m + 2r) f x‖` for `f` of class `C^n`, `m + 2r ≤ n`. -/
theorem norm_iteratedFDeriv_iterate_laplacian_le {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f)
    {r m : ℕ} (h : m + 2 * r ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ m (Δ^[r] f) x‖ ≤
      Module.finrank ℝ E ^ r * ‖iteratedFDeriv ℝ (m + 2 * r) f x‖ := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
    have hφ : ContDiff ℝ (m + 2 : ℕ) (Δ^[r] f) :=
      (hf.iterate_laplacian (r := r) (by omega)).of_le (by norm_cast; omega)
    rw [Function.iterate_succ_apply', ← hφ.laplacian_iteratedFDeriv]
    refine (norm_laplacian_le _ x).trans ?_
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_iteratedFDeriv,
      pow_succ', mul_assoc, show m + 2 * (r + 1) = 1 + 1 + m + 2 * r by omega]
    exact mul_le_mul_of_nonneg_left (ih (by omega)) (Nat.cast_nonneg _)

/-- The differences of the derivatives of an iterated Laplacian are controlled by those of the
map: `‖D^m Δ^[r] f x - D^m Δ^[r] f y‖ ≤ (dim E)^r ‖D^(m + 2r) f x - D^(m + 2r) f y‖` for `f` of
class `C^n`, `m + 2r ≤ n`. -/
theorem norm_iteratedFDeriv_iterate_laplacian_sub_le {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f)
    {r m : ℕ} (h : m + 2 * r ≤ n) (x y : E) :
    ‖iteratedFDeriv ℝ m (Δ^[r] f) x - iteratedFDeriv ℝ m (Δ^[r] f) y‖ ≤
      Module.finrank ℝ E ^ r *
        ‖iteratedFDeriv ℝ (m + 2 * r) f x - iteratedFDeriv ℝ (m + 2 * r) f y‖ := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
    have hφ : ContDiff ℝ (m + 2 : ℕ) (Δ^[r] f) :=
      (hf.iterate_laplacian (r := r) (by omega)).of_le (by norm_cast; omega)
    rw [Function.iterate_succ_apply', ← hφ.laplacian_iteratedFDeriv]
    refine (norm_laplacian_sub_laplacian_le _ x y).trans ?_
    rw [norm_fderiv_fderiv_sub, norm_iteratedFDeriv_two_iteratedFDeriv_sub,
      pow_succ', mul_assoc, show m + 2 * (r + 1) = m + 2 + 2 * r by omega]
    exact mul_le_mul_of_nonneg_left (ih (by omega)) (Nat.cast_nonneg _)

end TauCeti
