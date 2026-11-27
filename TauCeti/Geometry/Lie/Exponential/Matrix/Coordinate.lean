/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Geometry.Lie.Exponential.Units.Basic
public import Mathlib.Analysis.Matrix.Normed
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.PointSeparation
import TauCeti.Analysis.Calculus.Deriv.AlgHomCurve
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Geometry.Lie.Exponential.OneParameter
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Analytic

/-!
# Coordinate functions along the exponential curve of `GLₙ(ℝ)`

For a real matrix `X`, the exponential curve `t ↦ exp (t • X)` is a curve of real points of the
algebraic group `GLₙ`, so each element `f` of the coordinate Hopf algebra `O(GLₙ)` gives the
scalar coordinate function `t ↦ f (exp (t • X))`. This file shows:

* these coordinate functions are real-analytic
  (`TauCeti.GeneralLinear.analyticAt_generalLinearToPoint_expUnit_apply`): they are rational
  functions on `GLₙ(ℝ)` composed with the analytic curve `t ↦ exp (t • X)`;
* when `X` is the matrix of a tangent vector `d` at the identity, the exponential curve is an
  integral curve of the left-invariant vector field `D` of `d`: the derivative of
  `t ↦ f (exp (t • X))` is `t ↦ (D f) (exp (t • X))`
  (`TauCeti.GeneralLinear.hasDerivAt_generalLinearToPoint_expUnit_apply`). The generic entries and
  the inverse determinant generate `O(GLₙ)`, so this is checked on the entries, where `D` is right
  multiplication by `X` and the derivative of `exp (t • X)` is `exp (t • X) * X`.

## Main results

* `TauCeti.GeneralLinear.analyticAt_generalLinearToPoint_expUnit_apply`: the coordinate functions
  of the exponential curve are analytic.
* `TauCeti.GeneralLinear.hasDerivAt_generalLinearToPoint_expUnit_apply`: the derivatives of the
  coordinate functions of the exponential curve of a tangent vector are the coordinate functions
  of its left-invariant vector field.
-/

public section

open scoped Matrix.Norms.Operator

noncomputable section

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace TauCeti.GeneralLinear

open WithConv

variable {n : ℕ}

/-- **The coordinate functions of the exponential curve are analytic.** For every element `f` of
the coordinate Hopf algebra of `GLₙ` over `ℝ` and every real matrix `X`, the function
`u ↦ f (exp (u • X))` is real-analytic: it is a rational function on `GLₙ(ℝ)` composed with the
analytic curve `u ↦ exp (u • X)`. -/
theorem analyticAt_generalLinearToPoint_expUnit_apply (X : Matrix (Fin n) (Fin n) ℝ)
    (f : coordinateHopfAlgebra ℝ n) (t : ℝ) :
    AnalyticAt ℝ (fun u ↦ (generalLinearToPoint (R := ℝ) n (expUnit (u • X))).ofConv f) t := by
  have hf := TauCeti.Matrix.GeneralLinearGroup.contMDiff_of_mem_rationalFunctions
    ((mem_rationalFunctions_iff_exists_generalLinearToPoint_apply_eq (k := ℝ)).2 ⟨f, fun _ ↦ rfl⟩)
  exact (contMDiff_iff_contDiff.1 (hf.comp (contMDiff_expUnit_smul X))).contDiffAt.analyticAt

/-- **The exponential curve of a tangent vector is an integral curve of its left-invariant vector
field.** Let `d` be a tangent vector at the identity of `GLₙ` over `ℝ`, with matrix `X` and
left-invariant vector field `D`. For every element `f` of the coordinate Hopf algebra, the function
`u ↦ f (exp (u • X))` has derivative `(D f) (exp (t • X))` at every `t`. -/
theorem hasDerivAt_generalLinearToPoint_expUnit_apply
    (d : Derivation ℝ (coordinateHopfAlgebra ℝ n)
      (Bialgebra.CounitAlgebra ℝ (coordinateHopfAlgebra ℝ n) ℝ))
    (f : coordinateHopfAlgebra ℝ n) (t : ℝ) :
    HasDerivAt (fun u ↦
        (generalLinearToPoint (R := ℝ) n (expUnit (u • tangentMatrix n d))).ofConv f)
      ((generalLinearToPoint (R := ℝ) n (expUnit (t • tangentMatrix n d))).ofConv
        (Bialgebra.leftInvariantDerivation d f)) t := by
  set X := tangentMatrix n d
  set D := Bialgebra.leftInvariantDerivation d
  -- The curve of characters `u ↦ exp (u • X)` of `O(GLₙ)`; the motive below is the statement with
  -- this local abbreviation, which unfolds by `let`-reduction.
  let p (u : ℝ) := (generalLinearToPoint (R := ℝ) n (expUnit (u • X))).ofConv
  refine coordinateHopfAlgebra_induction ℝ n
    (motive := fun f ↦ ∀ t, HasDerivAt (p · f) (p t (D f)) t)
    (fun s hs a ha t ↦ D.hasDerivAt_apply_of_mem_adjoin p (fun b hb ↦ hs b hb t) ha)
    (fun a _ h t ↦ D.hasDerivAt_apply_ringInverse p (h t)) (fun i j t ↦ ?_) f t
  -- On a generic entry `D x_ij = ∑ₖ X_kj x_ik`, and `exp (u • X)` has derivative
  -- `exp (t • X) * X`.
  have h := Matrix.hasDerivAt_exp_smul_apply X i j t
  rw [Matrix.mul_apply] at h
  simp only [p, D, leftInvariantDerivation_genericMatrix]
  simp only [map_sum, map_smul, smul_eq_mul, genericMatrix_apply, generalLinearToPoint_apply,
    expUnit_coe]
  -- Write the summands `X_kj * exp (t • X)_ik` in the order `exp (t • X)_ik * X_kj` of `h`.
  rw [Finset.sum_congr rfl fun k _ ↦ mul_comm (X k j) _]
  -- `expUnit_coe` gives the exponential for the topology of the operator norm on matrices, while
  -- `h` uses the entrywise topology; the two topologies agree.
  convert h using 4 <;> exact Matrix.linftyOpTopologicalSpace_eq _ _ _

end TauCeti.GeneralLinear
