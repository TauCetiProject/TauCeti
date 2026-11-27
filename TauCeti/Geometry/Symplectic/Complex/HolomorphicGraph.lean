/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Prod.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Graphs of holomorphic functions are symplectic curves

The standard symplectic form of `ℂ²` is the direct sum `ω ⊕ ω` of two copies of the area form
`ω = stdComplexSymplecticForm` of `ℂ`. The graph `z ↦ (z, g z)` of a function `g : ℂ → ℂ` has
derivative `v ↦ (v, Dg v)`. When `g` is complex-differentiable at `z` with derivative `c`, the form
`ω ⊕ ω` evaluates on the images `(1, c)` and `(I, c I)` of the oriented frame `(1, I)` as
`1 + |c|² > 0`. So the graph of a holomorphic function is a symplectic curve in `ℂ²`.

## Main declarations

* `TauCeti.prod_stdComplexSymplecticForm_one_I`: `ω ⊕ ω` on the vectors `(1, a)` and `(I, b)` is
  `1 + Im (conj a b)`.
* `HasDerivAt.prod_stdComplexSymplecticForm_fderiv`: if `g` has complex derivative `c` at `z`,
  then `ω ⊕ ω` on `(1, Dg 1)` and `(I, Dg I)` is `1 + |c|²`.
* `DifferentiableAt.prod_stdComplexSymplecticForm_fderiv_pos`: the graph of a complex-differentiable
  function is a symplectic curve.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Section 2.1 (the standard structures on `ℂⁿ`).
-/

public section

open scoped ComplexConjugate

namespace TauCeti

/-- The standard symplectic form `ω ⊕ ω` of `ℂ²` on the vectors `(1, a)` and `(I, b)` is
`1 + Im (conj a b)`. -/
theorem prod_stdComplexSymplecticForm_one_I (a b : ℂ) :
    stdComplexSymplecticForm.prod stdComplexSymplecticForm (1, a) (Complex.I, b) =
      1 + (conj a * b).im := by
  rw [SymplecticForm.prod_apply, stdComplexSymplecticForm_eq_im_conj_mul,
    stdComplexSymplecticForm_eq_im_conj_mul]
  simp

end TauCeti

open TauCeti

/-- **The graph of a holomorphic function is a symplectic curve, quantitatively.** If `g : ℂ → ℂ`
has complex derivative `c` at `z`, the standard symplectic form `ω ⊕ ω` of `ℂ²` evaluates on the
images `(1, Dg 1)` and `(I, Dg I)` of the oriented frame `(1, I)` under the derivative of the graph
`z ↦ (z, g z)` as `1 + |c|²`. -/
theorem HasDerivAt.prod_stdComplexSymplecticForm_fderiv {g : ℂ → ℂ} {c z : ℂ}
    (h : HasDerivAt g c z) :
    stdComplexSymplecticForm.prod stdComplexSymplecticForm
        (1, fderiv ℝ g z 1) (Complex.I, fderiv ℝ g z Complex.I) =
      1 + Complex.normSq c := by
  rw [(h.hasFDerivAt.restrictScalars ℝ).fderiv, prod_stdComplexSymplecticForm_one_I]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, one_mul, mul_left_comm (conj c), ← Complex.normSq_eq_conj_mul_self]
  simp

/-- **The graph of a holomorphic function is a symplectic curve.** If `g : ℂ → ℂ` is
complex-differentiable at `z`, the standard symplectic form `ω ⊕ ω` of `ℂ²` is positive on the
images `(1, Dg 1)` and `(I, Dg I)` of the oriented frame `(1, I)` under the derivative of the graph
`z ↦ (z, g z)`. -/
theorem DifferentiableAt.prod_stdComplexSymplecticForm_fderiv_pos {g : ℂ → ℂ} {z : ℂ}
    (h : DifferentiableAt ℂ g z) :
    0 < stdComplexSymplecticForm.prod stdComplexSymplecticForm
      (1, fderiv ℝ g z 1) (Complex.I, fderiv ℝ g z Complex.I) := by
  rw [h.hasDerivAt.prod_stdComplexSymplecticForm_fderiv]
  linarith [Complex.normSq_nonneg (deriv g z)]
