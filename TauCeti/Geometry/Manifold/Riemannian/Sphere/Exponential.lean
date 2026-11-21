/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar.ConstantCurvature
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Compact
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The differential of the exponential map of the round sphere

The exponential map of the unit sphere `Sⁿ ⊆ E` at `p` is, in ambient coordinates,
`exp_p(v) = cos ‖v‖ p + (sin ‖v‖ / ‖v‖) v`, where `v` is read in `E` through the differential
of the inclusion (`TauCeti.coe_riemannianExp_sphere`).

Differentiating this formula at a nonzero `x` in a direction `h` orthogonal to `x` only
differentiates the linear factor, leaving its coefficient fixed, because the norm is stationary
along `h`:
`d(exp_p)_x(h) = (sin ‖x‖ / ‖x‖) h` in ambient coordinates. For `x = r v` and `h = r w`, with
`v` a unit vector and `w ⊥ v`, this has norm `|sin r| ‖w‖`: the angular Jacobian of geodesic
polar coordinates on the round sphere is `|sin r|` on unit angular directions, and equals
`sin r` for `0 ≤ r ≤ π`.

The polar Jacobian formula is derived from the general constant-curvature formula and the
unit sphere's sectional curvature `1`.

## Main results

* `TauCeti.mvfderiv_coe_mfderiv_riemannianExp_sphere_of_inner_eq_zero`: the ambient
  differential of the exponential map in a direction orthogonal to the base vector.
* `TauCeti.polarJacobian_sphere`: the polar Jacobian of the unit sphere is `|sin r|` on unit
  angular directions.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapter 5
  (geodesics of the round sphere) and Chapter 10 (Jacobi fields of constant curvature spaces).
-/

public section

open Bundle ContinuousLinearMap Metric Module Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

local notation "ι" => ((↑) : sphere (0 : E) 1 → E)

/-- The differential of the round-sphere exponential map in a direction orthogonal to a nonzero
base vector, in ambient coordinates: `d(exp_p)_x(h) = (sin ‖x‖ / ‖x‖) h`. -/
theorem mvfderiv_coe_mfderiv_riemannianExp_sphere_of_inner_eq_zero (p : sphere (0 : E) 1)
    {x h : TangentSpace (𝓡 n) p} (hx : x ≠ 0) (hxh : ⟪x, h⟫_ℝ = 0) :
    mvfderiv (𝓡 n) ι (riemannianExp (𝓡 n) (sphere (0 : E) 1) p x)
        (mfderiv 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) (riemannianExp (𝓡 n) (sphere (0 : E) 1) p)
          x h) =
      (Real.sin ‖x‖ / ‖x‖) • mvfderiv (𝓡 n) ι p h := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hN := hasFDerivAt_norm_of_ne hx
  have hs := ((Real.hasDerivAt_sin ‖x‖).fun_div (hasDerivAt_id' ‖x‖) hx').comp_hasFDerivAt x hN
  have hD : HasFDerivAt (fun y ↦ Real.cos ‖y‖ • (p : E) +
      (Real.sin ‖y‖ / ‖y‖) • mvfderiv (𝓡 n) ι p y) _ x :=
    (hN.cos.smul_const (p : E)).add (hs.smul (mvfderiv (𝓡 n) ι p).hasFDerivAt)
  have hDh : (fderiv ℝ (fun y ↦ Real.cos ‖y‖ • (p : E) +
      (Real.sin ‖y‖ / ‖y‖) • mvfderiv (𝓡 n) ι p y) x) h =
        (Real.sin ‖x‖ / ‖x‖) • mvfderiv (𝓡 n) ι p h := by
    rw [hD.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
      innerSL_apply_apply, hxh, smul_eq_mul, mul_zero, zero_smul, add_zero, zero_add,
      Function.comp_apply]
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n)
      (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) x :=
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    (contMDiffAt_riemannianExp
      (by rw [expDomain_eq_univ_of_compactSpace]; trivial)).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ι (riemannianExp (𝓡 n) (sphere (0 : E) 1) p x) :=
    (contMDiff_coe_sphere (m := 1) _).mdifferentiableAt one_ne_zero
  -- The chain rule takes a vector in T_x(T_p Sⁿ); use the canonical identification explicitly
  -- so the normed-space derivative rewrites with the original fibre instances.
  have hcomp := mvfderiv_comp_apply x hι hexp
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm h)
  rw [Function.comp_def, funext (coe_riemannianExp_sphere p),
    mvfderiv_eq_fderiv_apply, NormedSpace.fromTangentSpace_symm_apply, hDh] at hcomp
  exact hcomp.symm

/-- The polar Jacobian of the unit sphere: for a unit vector `v` and `w ⊥ v`,
`j(r) = ‖d(exp_p)_(r v)(r w)‖ = |sin r| ‖w‖`. -/
theorem polarJacobian_sphere (p : sphere (0 : E) 1) {v w : TangentSpace (𝓡 n) p} (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫_ℝ = 0) (r : ℝ) : polarJacobian p v w r = |Real.sin r| * ‖w‖ := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hmem : r • v ∈ expDomain (𝓡 n) (sphere (0 : E) 1) p := by
    rw [expDomain_eq_univ_of_compactSpace]
    trivial
  simpa only [curvatureSine_of_pos zero_lt_one, Real.sqrt_one, one_mul, div_one] using
    polarJacobian_of_inner_eq_zero_of_hasSectionalCurvatureAt hmem
      (fun _ _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt _) hv hvw

end TauCeti
