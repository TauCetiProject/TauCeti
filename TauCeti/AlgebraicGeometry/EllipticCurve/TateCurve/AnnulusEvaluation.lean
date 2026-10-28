/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.FormalPoint
public import TauCeti.Topology.Algebra.InfiniteSum.IntegralCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Evaluation of the formal Tate point on an annulus

The formal Tate coordinates are power series in two variables `u` and `v`, with the Tate parameter
specialized to `q = u v`. When both variables have norm less than one, their iterated evaluation
converges, and `TauCeti.evalIntBivariateSeries` evaluates them as a ring homomorphism. This file
transfers the formal Tate equation to the resulting values.

For a point of the strict annulus `|q| < |u| < 1`, one takes `v = q / u`; then both `u` and `v`
belong to the open unit ball. The module `TateCurve.CoordinateEvaluation` identifies these
evaluated formal coordinates with the bilateral series `tateUniformizationX` and
`tateUniformizationY`, and deduces their specialized Tate equation on the strict annulus.

## Main results

* `TauCeti.evalIntBivariateSeries_comp_tateParamHom`: the substitution `q = u v` commutes with
  convergent evaluation.
* `TauCeti.equation_eval_tateFormalX_tateFormalY`: the evaluated formal coordinates satisfy the
  specialized Tate equation.
-/

public section

open PowerSeries

namespace TauCeti

variable {K : Type*} [NormedCommRing K] [CompleteSpace K]
  [IsUltrametricDist K]

/-- Evaluating after the formal substitution `q = u v` agrees with directly evaluating at the
product `u v`. -/
theorem evalIntBivariateSeries_tateParamHom (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1)
    (f : ℤ⟦X⟧) :
    evalIntBivariateSeries u hu v hv (tateParamHom ℤ f) =
      evalIntSeries (u * v) (norm_mul_lt_one u v hu hv) f := by
  rw [evalIntBivariateSeries_apply, evalIntSeries_apply]
  apply tsum_congr
  intro b
  have hinner : (∑' a : ℕ, ((coeff a (coeff b (tateParamHom ℤ f)) : ℤ) : K) * u ^ a) =
      ((coeff b f : ℤ) : K) * u ^ b := by
    rw [tsum_eq_single b]
    · simp
    · intro a ha
      simp [ha]
  rw [hinner, mul_pow]
  ring

/-- The composite of bivariate evaluation with formal Tate-parameter substitution is evaluation
at the product of the two parameters. -/
theorem evalIntBivariateSeries_comp_tateParamHom (u : K) (hu : ‖u‖ < 1)
    (v : K) (hv : ‖v‖ < 1) :
    (evalIntBivariateSeries u hu v hv).comp (tateParamHom ℤ) =
      evalIntSeries (u * v) (norm_mul_lt_one u v hu hv) := by
  ext f
  exact evalIntBivariateSeries_tateParamHom u hu v hv f

/-- **The convergently evaluated formal Tate point satisfies the specialized Tate equation.** -/
theorem equation_eval_tateFormalX_tateFormalY (u : K) (hu : ‖u‖ < 1)
    (v : K) (hv : ‖v‖ < 1) :
    (tateCurve.map (evalIntSeries (u * v) (norm_mul_lt_one u v hu hv))).toAffine.Equation
      (evalIntBivariateSeries u hu v hv (tateFormalX ℤ))
      (evalIntBivariateSeries u hu v hv (tateFormalY ℤ)) := by
  have h := (equation_tateFormalX_tateFormalY ℤ).map (evalIntBivariateSeries u hu v hv)
  dsimp only [WeierstrassCurve.Affine.map] at h
  rwa [WeierstrassCurve.map_map, evalIntBivariateSeries_comp_tateParamHom] at h

end TauCeti

end
