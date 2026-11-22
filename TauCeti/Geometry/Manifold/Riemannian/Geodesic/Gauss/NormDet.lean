/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic

/-!
# The geometric Jacobian `normDet` of the Riemannian exponential map

Gauss's lemma implies that at every vector `v ∈ expDomain I M p`, the differential `d(exp_p)_v`
preserves the radial length `‖v‖` and maps the angular hyperplane `(ℝ ∙ v)ᗮ` orthogonally to
`d(exp_p)_v v`. Factoring `LinearMap.normDet` along the orthogonal splitting
`T_p M = (ℝ ∙ v) ⊕ (ℝ ∙ v)ᗮ` therefore reduces the `n`-dimensional Jacobian of `d(exp_p)_v` to the
`(n - 1)`-dimensional Jacobian of its restriction to `(ℝ ∙ v)ᗮ`. At the origin `v = 0`, `d(exp_p)_0`
is the identity isometry, so its Jacobian is `1`.

These identities depend only on Gauss's lemma and require no curvature bounds, Jacobi-field
estimates, or completeness hypotheses.

## Main results

* `TauCeti.Manifold.normDet_mfderiv_riemannianExp_zero`: at the origin of `T_p M`,
  `normDet (d(exp_p)_0) = 1`.
* `TauCeti.Manifold.normDet_mfderiv_riemannianExp_eq_orthogonal`: for nonzero `v ∈ expDomain I M p`,
  `normDet (d(exp_p)_v)` equals the `normDet` of `d(exp_p)_v` restricted to `(ℝ ∙ v)ᗮ`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 6.
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p}

/-- At the origin of `T_p M`, the differential of `exp_p` is the identity, so its `normDet` is
`1`. -/
@[simp]
theorem normDet_mfderiv_riemannianExp_zero (p : M) :
    LinearMap.normDet (U := TangentSpace I p)
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0).toLinearMap = 1 := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p 0) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0
  let Φ : TangentSpace I p →ₗᵢ[ℝ] TangentSpace I (riemannianExp I M p 0) :=
    { toLinearMap := L.toLinearMap
      norm_map' := fun w ↦ by
        rw [ContinuousLinearMap.coe_coe]
        -- Read `T_0 (T_p M)` as `T_p M` so `mfderiv_riemannianExp_apply_zero` matches.
        change ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 w‖ = ‖w‖
        rw [mfderiv_riemannianExp_apply_zero, riemannianExp_zero] }
  exact Φ.normDet_eq_one

/-- **Radial-angular factorization of the exponential Jacobian.** By Gauss's lemma, at every
nonzero `v ∈ expDomain I M p`, the differential `d(exp_p)_v` preserves the length of `v` and maps
`(ℝ ∙ v)ᗮ` orthogonally to `d(exp_p)_v v`, so its `normDet` equals the `normDet` of its
restriction to `(ℝ ∙ v)ᗮ`. -/
theorem normDet_mfderiv_riemannianExp_eq_orthogonal
    (hv : v ∈ expDomain I M p) (hv0 : v ≠ 0) :
    LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap =
      LinearMap.normDet
        (((mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v :
          TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v)).toLinearMap) ∘ₗ
          (ℝ ∙ v)ᗮ.subtype) := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  have horth : ∀ w ∈ (ℝ ∙ v)ᗮ, ⟪L v, L w⟫_ℝ = 0 := by
    intro w hw
    have hvw : ⟪v, w⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
    exact (inner_mfderiv_riemannianExp_radial hv).trans hvw
  have hrad : ‖L.toLinearMap v‖ / ‖v‖ = 1 := by
    have hn : ‖L v‖ = ‖v‖ := norm_mfderiv_riemannianExp_radial hv
    simpa only [ContinuousLinearMap.coe_coe, hn] using div_self (norm_ne_zero_iff.mpr hv0)
  -- Read `T_v (T_p M)` as `T_p M` so `LinearMap.normDet` acts on `L.toLinearMap`.
  change L.toLinearMap.normDet = (L.toLinearMap ∘ₗ (ℝ ∙ v)ᗮ.subtype).normDet
  rw [L.toLinearMap.normDet_eq_div_mul_normDet_orthogonal hv0 horth, hrad, one_mul]

end TauCeti.Manifold
