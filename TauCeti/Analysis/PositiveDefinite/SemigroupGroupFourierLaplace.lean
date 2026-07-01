/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroupProduct
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Laplace--Fourier atoms for semigroup-group positive-definite functions

This file records the atomic positive-definite functions that appear inside the
Berg--Christensen--Ressel Laplace--Fourier representation. For a nonnegative Laplace parameter
`p : ℝ≥0` and a spatial frequency `q : V`, the separated function

`(t, v) ↦ exp (-t p) * exp (-2πi ⟪v, q⟫)`

is semigroup-group positive definite on `ℝ≥0 × V`, and is continuous when `V` is topological.
The proof is just the rank-one-kernel calculation for each factor, followed by the existing
separated-product constructor.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"): the representing integrand in the target theorem is a finite-measure
mixture of these atoms.

## Main declarations

* `TauCeti.isPositiveDefiniteKernel_laplaceAtom`: the time kernel
  `(t, u) ↦ exp (-(t + u) p)` is positive definite.
* `TauCeti.isPositiveDefiniteKernel_fourierAtom`: the spatial kernel
  `(v, w) ↦ exp (-2πi ⟪v - w, q⟫)` is positive definite.
* `TauCeti.isSemigroupGroupPD_laplaceFourierAtom`: the separated BCR atom is positive definite.
* `TauCeti.isSemigroupGroupPD_laplaceFourierAtom_and_continuous`: the same result packaged with
  continuity.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

@[expose] public section

open Complex ComplexConjugate
open scoped ComplexOrder NNReal

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Laplace atom at `p : ℝ≥0`, as a complex-valued function on nonnegative time. -/
public noncomputable def laplaceAtom (p : ℝ≥0) (t : ℝ≥0) : ℂ :=
  (Real.exp (-(t : ℝ) * (p : ℝ)) : ℂ)

/-- The Fourier atom at frequency `q`, using Mathlib's `2π` Fourier convention. -/
public noncomputable def fourierAtom (q : V) (v : V) : ℂ :=
  (Real.fourierChar (-(inner ℝ v q)) : ℂ)

/-- The definitional exponential form of a Laplace atom. -/
@[simp]
theorem laplaceAtom_def (p : ℝ≥0) (t : ℝ≥0) :
    laplaceAtom p t = (Real.exp (-(t : ℝ) * (p : ℝ)) : ℂ) :=
  rfl

/-- The `Real.fourierChar` form of a Fourier atom. -/
theorem fourierAtom_eq_fourierChar (q : V) (v : V) :
    fourierAtom q v = (Real.fourierChar (-(inner ℝ v q)) : ℂ) :=
  rfl

/-- The raw exponential form of a Fourier atom. -/
@[simp]
theorem fourierAtom_def (q : V) (v : V) :
    fourierAtom q v =
      Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ)) := by
  rw [fourierAtom_eq_fourierChar, Real.fourierChar_apply]
  congr 1
  norm_num [Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- Laplace atoms turn time addition into a rank-one positive-definite kernel. -/
theorem laplaceAtom_add (p t u : ℝ≥0) :
    laplaceAtom p (t + u) = conj (laplaceAtom p t) * laplaceAtom p u := by
  simp only [laplaceAtom_def, Complex.conj_ofReal]
  norm_cast
  rw [← Real.exp_add]
  congr 1
  rw [NNReal.coe_add]
  ring

/-- Fourier atoms turn spatial subtraction into a rank-one positive-definite kernel. -/
theorem fourierAtom_sub (q v w : V) :
    fourierAtom q (v - w) =
      conj (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ))) *
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ w q : ℝ) : ℂ)) := by
  rw [fourierAtom_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, Complex.ofReal_sub, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring_nf

/-- The time kernel supplied by a Laplace atom is positive definite. -/
theorem isPositiveDefiniteKernel_laplaceAtom (p : ℝ≥0) :
    IsPositiveDefiniteKernel fun t u : ℝ≥0 => laplaceAtom p (t + u) := by
  simp_rw [laplaceAtom_add]
  exact isPositiveDefiniteKernel_conj_mul (fun t : ℝ≥0 => laplaceAtom p t)

/-- The spatial subtraction kernel supplied by a Fourier atom is positive definite. -/
theorem isPositiveDefiniteKernel_fourierAtom (q : V) :
    IsPositiveDefiniteKernel fun v w : V => fourierAtom q (v - w) := by
  simp_rw [fourierAtom_sub]
  exact isPositiveDefiniteKernel_conj_mul
    (fun v : V => Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ)))

/-- Laplace atoms are continuous in the nonnegative time variable. -/
theorem continuous_laplaceAtom (p : ℝ≥0) : Continuous (laplaceAtom p) := by
  convert
    (by fun_prop :
      Continuous fun t : ℝ≥0 => (Real.exp (-(t : ℝ) * (p : ℝ)) : ℂ)) using 1
  ext t
  exact (laplaceAtom_def p t).symm

/-- Fourier atoms are continuous in the spatial variable. -/
theorem continuous_fourierAtom (q : V) : Continuous (fourierAtom q) := by
  convert
    (by fun_prop :
      Continuous fun v : V => ((Real.fourierChar (-(inner ℝ v q)) : Circle) : ℂ)) using 1
  ext v
  exact (fourierAtom_eq_fourierChar q v).symm

/-- The separated Laplace--Fourier atom is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_laplaceFourierAtom (p : ℝ≥0) (q : V) :
    IsSemigroupGroupPD fun x : ℝ≥0 × V => laplaceAtom p x.1 * fourierAtom q x.2 :=
  isSemigroupGroupPD_mul_time_spatial_of_kernels
    (isPositiveDefiniteKernel_laplaceAtom p) (isPositiveDefiniteKernel_fourierAtom q)

/-- The separated Laplace--Fourier atom is semigroup-group positive definite and continuous. -/
theorem isSemigroupGroupPD_laplaceFourierAtom_and_continuous (p : ℝ≥0) (q : V) :
    IsSemigroupGroupPD (fun x : ℝ≥0 × V => laplaceAtom p x.1 * fourierAtom q x.2) ∧
      Continuous (fun x : ℝ≥0 × V => laplaceAtom p x.1 * fourierAtom q x.2) :=
  isSemigroupGroupPD_mul_time_spatial_of_kernels_and_continuous
    (isPositiveDefiniteKernel_laplaceAtom p) (isPositiveDefiniteKernel_fourierAtom q)
    (continuous_laplaceAtom p) (continuous_fourierAtom q)

end TauCeti
