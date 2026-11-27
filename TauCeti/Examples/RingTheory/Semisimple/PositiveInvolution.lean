/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.PositiveInvolution
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Positive involutions: examples

* On `ℚ` the identity is a positive involution: `Trd(x x) = x² > 0`.
* On `M_n(ℚ)` the transpose is a positive involution: `Trd(x xᵀ) = Σ_{i,j} x_{ij}² > 0`.
* On `M_2(ℚ)` the canonical involution `x ↦ adj x` is not positive: `x adj x = det x · 1`, and at
  `x = diag(1, -1)` the reduced trace of `x adj x` is `-2` and its regular trace (the trace of
  left multiplication on the `4`-dimensional space `M_2(ℚ)`) is `-4`.
* On `ℚ(i)`, realised as `QuadraticAlgebra ℚ (-1) 0`, the identity is not positive
  (`Trd(i · i) = -2`), while complex conjugation is (`Trd(x x*) = 2 |x|²`).
-/

public section

open Matrix TauCeti TauCeti.Algebra

namespace TauCeti.PositiveInvolutionExamples

/-! ### The identity of `ℚ` -/

/-- The identity of `ℚ` is a positive involution: `Trd_{ℚ/ℚ}(x x) = x² > 0` for `x ≠ 0`. -/
def rat : PositiveInvolution ℚ :=
  PositiveInvolution.ofStarRing fun x hx ↦ by
    simpa [Algebra.trace_self_apply] using mul_self_pos.2 hx

example (x : ℚ) : rat.toStarRing.star x = x :=
  star_trivial x

/-! ### The transpose on `M_n(ℚ)` -/

/-- The transpose (the conjugate transpose of `ℚ`-matrices) is a positive involution of
`M_n(ℚ)`. -/
def transpose (n : Type*) [Fintype n] [DecidableEq n] :
    PositiveInvolution (Matrix n n ℚ) :=
  PositiveInvolution.ofStarRing fun x hx ↦ by
    rw [star_eq_conjTranspose, semisimpleReducedTrace_matrix]
    exact (posSemidef_self_mul_conjTranspose x).trace_nonneg.lt_of_ne'
      (trace_mul_conjTranspose_self_eq_zero_iff.not.2 hx)

example {n : Type*} [Fintype n] [DecidableEq n] (x : Matrix n n ℚ) :
    (transpose n).toStarRing.star x = xᵀ :=
  conjTranspose_eq_transpose_of_trivial x

/-! ### The canonical involution of `M_2(ℚ)` is not positive -/

/-- At `x = diag(1, -1)`, the reduced trace of `x adj x = det x · 1` is `2 det x = -2`. -/
theorem semisimpleReducedTrace_diag_one_neg_one_mul_adjugate :
    semisimpleReducedTrace ℚ (Matrix (Fin 2) (Fin 2) ℚ)
      (!![1, 0; 0, -1] * adjugate !![1, 0; 0, -1]) = -2 := by
  rw [semisimpleReducedTrace_matrix, adjugate_fin_two]
  norm_num [Matrix.trace]

/-- The canonical involution `x ↦ adj x` of `M_2(ℚ)` is not positive. -/
theorem not_positiveInvolution_adjugate :
    ¬ ∃ P : PositiveInvolution (Matrix (Fin 2) (Fin 2) ℚ),
      ∀ x, P.toStarRing.star x = adjugate x := by
  rintro ⟨P, hP⟩
  have h := P.semisimpleReducedTrace_mul_star_pos !![1, 0; 0, -1] fun h ↦ by
    simpa using congrFun (congrFun h 0) 0
  rw [hP, semisimpleReducedTrace_diag_one_neg_one_mul_adjugate] at h
  norm_num at h

/-- At `x = diag(1, -1)`, the regular trace of `x adj x = -1`, the trace of left multiplication
on `M_2(ℚ)`, is `-4`. -/
theorem trace_mulLeft_diag_one_neg_one_mul_adjugate :
    LinearMap.trace ℚ (Matrix (Fin 2) (Fin 2) ℚ)
      (LinearMap.mulLeft ℚ (!![1, 0; 0, -1] * adjugate !![1, 0; 0, -1])) = -4 := by
  have h : (!![1, 0; 0, -1] * adjugate !![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ) = -1 := by
    rw [adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hL : LinearMap.mulLeft ℚ (-1 : Matrix (Fin 2) (Fin 2) ℚ) = -LinearMap.id := by
    ext1 x
    simp
  rw [h, hL, map_neg, LinearMap.trace_id, Module.finrank_matrix]
  norm_num

/-- The canonical involution of `M_2(ℚ)` also fails positivity for the regular trace. -/
example : ¬ ∃ P : PositiveInvolution (Matrix (Fin 2) (Fin 2) ℚ),
    ∀ x, P.toStarRing.star x = adjugate x := by
  rintro ⟨P, hP⟩
  have h := P.trace_mulLeft_mul_star_pos (x := !![1, 0; 0, -1]) fun h ↦ by
    simpa using congrFun (congrFun h 0) 0
  rw [hP, trace_mulLeft_diag_one_neg_one_mul_adjugate] at h
  norm_num at h

/-! ### Involutions of `ℚ(i)` -/

/-- `-1` is not a square in `ℚ`, so `QuadraticAlgebra ℚ (-1) 0` is the field `ℚ(i)`. -/
local instance instFactNotIsSquareNegOneRat : Fact (¬ IsSquare (-1 : ℚ)) :=
  ⟨fun ⟨r, hr⟩ ↦ by nlinarith [mul_self_nonneg r]⟩

/-- The Gaussian rationals `ℚ(i)`. -/
abbrev GaussianRat := QuadraticAlgebra ℚ (-1) 0

/-- The reduced trace of a rational number in `ℚ(i)` is twice that number. -/
theorem semisimpleReducedTrace_algebraMap (q : ℚ) :
    semisimpleReducedTrace ℚ GaussianRat (algebraMap ℚ GaussianRat q) = 2 * q := by
  rw [semisimpleReducedTrace_eq_trace, Algebra.trace_algebraMap]
  simp [QuadraticAlgebra.finrank_eq_two]

/-- The identity of `ℚ(i)` is not positive: `Trd(i · i) = -2`. -/
theorem not_positiveInvolution_id :
    ¬ ∃ P : PositiveInvolution GaussianRat, ∀ x, P.toStarRing.star x = x := by
  rintro ⟨P, hP⟩
  have h := P.semisimpleReducedTrace_mul_star_pos (QuadraticAlgebra.omega : GaussianRat) fun h ↦ by
    simpa using congrArg QuadraticAlgebra.im h
  have hω : (QuadraticAlgebra.omega : GaussianRat) * QuadraticAlgebra.omega =
      algebraMap ℚ GaussianRat (-1) := by
    rw [map_neg, map_one]
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [hP, hω, semisimpleReducedTrace_algebraMap] at h
  norm_num at h

/-- Complex conjugation is a positive involution of `ℚ(i)`: `Trd(x x*) = 2 (re x² + im x²)`. -/
def conj : PositiveInvolution GaussianRat :=
  PositiveInvolution.ofStarRing fun x hx ↦ by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, semisimpleReducedTrace_algebraMap]
    have hn : QuadraticAlgebra.norm x = x.re * x.re + x.im * x.im := by
      simp [QuadraticAlgebra.norm_def]
    have : x.re ≠ 0 ∨ x.im ≠ 0 := by
      by_contra! h
      exact hx (QuadraticAlgebra.ext h.1 h.2)
    rw [hn]
    rcases this with h | h
    · nlinarith [mul_self_pos.2 h, mul_self_nonneg x.im]
    · nlinarith [mul_self_pos.2 h, mul_self_nonneg x.re]

end TauCeti.PositiveInvolutionExamples
