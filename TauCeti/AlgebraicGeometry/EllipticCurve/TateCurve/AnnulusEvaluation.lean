/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.FormalPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Evaluation of the formal Tate point on an annulus

The formal Tate coordinates are power series in two variables `u` and `v`, with the Tate parameter
specialized to `q = u v`. When both variables have norm less than one, their iterated evaluation
converges. This file constructs that evaluation as a ring homomorphism and transfers the formal
Tate equation to the resulting values.

For a point of the strict annulus `|q| < |u| < 1`, one takes `v = q / u`; then both `u` and `v`
belong to the open unit ball. Identifying the two evaluated formal coordinates here with the
bilateral series `tateUniformizationX` and `tateUniformizationY` is the remaining analytic
reindexing step.

## Main definitions

* `TauCeti.evalIntBivariateSeries`: convergent evaluation of an integral power series in `u` and
  `v` inside the open unit bidisc.

## Main results

* `TauCeti.evalIntBivariateSeries_comp_tateParamHom`: the substitution `q = u v` commutes with
  convergent evaluation.
* `TauCeti.equation_eval_tateFormalX_tateFormalY`: the evaluated formal coordinates satisfy the
  specialized Tate equation.
-/

public section

open PowerSeries

namespace TauCeti

variable {K : Type*} [NormedCommRing K] [NormOneClass K] [CompleteSpace K]
  [IsUltrametricDist K]

/-- Iterated evaluation of an integral bivariate power series at two parameters in the open unit
ball. The inner variable is evaluated at `u`, and the outer variable at `v`. -/
@[expose] noncomputable def evalIntBivariateSeries (u : K) (hu : ‖u‖ < 1)
    (v : K) (hv : ‖v‖ < 1) :
    ℤ⟦X⟧⟦X⟧ →+* K :=
  evalBoundedSeries (evalIntSeries u hu) (norm_evalIntSeries_le_one u hu) v hv

/-- Bivariate integral evaluation is the iterated convergent sum of the coefficients. -/
theorem evalIntBivariateSeries_apply (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1)
    (f : ℤ⟦X⟧⟦X⟧) :
    evalIntBivariateSeries u hu v hv f =
      ∑' b : ℕ, (∑' a : ℕ, ((coeff a (coeff b f) : ℤ) : K) * u ^ a) * v ^ b := by
  rw [evalIntBivariateSeries, evalBoundedSeries_apply]
  apply tsum_congr
  intro b
  rw [evalIntSeries_apply]

/-- Bivariate evaluation of a series constant in the outer variable is its evaluation at the
inner parameter. -/
@[simp]
theorem evalIntBivariateSeries_C (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1)
    (f : ℤ⟦X⟧) : evalIntBivariateSeries u hu v hv (C f) = evalIntSeries u hu f := by
  exact evalBoundedSeries_C _ _ v hv f

/-- Bivariate evaluation sends the outer formal parameter to the outer chosen element. -/
@[simp]
theorem evalIntBivariateSeries_X (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) :
    evalIntBivariateSeries u hu v hv (X : ℤ⟦X⟧⟦X⟧) = v := by
  exact evalBoundedSeries_X _ _ v hv

omit [NormOneClass K] [CompleteSpace K] [IsUltrametricDist K] in
/-- A product of two elements in the open unit ball again belongs to the open unit ball. -/
theorem norm_mul_lt_one (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) : ‖u * v‖ < 1 := by
  calc
    ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.le (norm_nonneg u)
    _ < 1 := hu

/-- Evaluating after the formal substitution `q = u v` agrees with directly evaluating at the
product `u v`. -/
theorem evalIntBivariateSeries_tateParamHom (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1)
    (f : ℤ⟦X⟧) :
    evalIntBivariateSeries u hu v hv (tateParamHom ℤ f) =
      evalIntSeries (u * v) (norm_mul_lt_one u v hu hv) f := by
  rw [evalIntBivariateSeries_apply, evalIntSeries_apply]
  apply tsum_congr
  intro b
  rw [show (∑' a : ℕ, ((coeff a (coeff b (tateParamHom ℤ f)) : ℤ) : K) * u ^ a) =
      ((coeff b f : ℤ) : K) * u ^ b by
    rw [tsum_eq_single b]
    · simp
    · intro a ha
      simp [ha]]
  rw [mul_pow]
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
