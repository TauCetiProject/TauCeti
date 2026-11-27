/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Conformal

/-!
# The boundary under a conformal change of metric

Let `M` be a manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, `g` a `C¹`
Riemannian metric on `M` and `ĝ = f g` its rescaling by a positive `C¹` function `f`
(`Bundle.ContMDiffRiemannianMetric.rescale`). For `f = e^{2φ}` this is the conformal change
`ĝ = e^{2φ} g`. At a boundary point `q`, with `h_q(u, w) = g(dι u, dι w)` the induced metric of the
boundary:

* the gradient of every function is divided by `f`
  (`Bundle.ContMDiffRiemannianMetric.mgradient_rescale`, in `Riemannian/Conformal.lean`);
* the unit normals are divided by `√f`: `ν_out^ĝ = f(q)^(-1/2) ν_out` and
  `ν_in^ĝ = f(q)^(-1/2) ν_in` (`outwardUnitNormal_rescale`, `inwardUnitNormal_rescale`), while the
  induced metric is multiplied by `f(q)` (`boundaryInducedForm_rescale`);
* the second fundamental form of the boundary changes by
  `II^ĝ_q(u, w) = √(f q) (II_q(u, w) - (2 f q)⁻¹ df_q(ν_in) h_q(u, w))`
  (`boundarySecondFundamentalForm_rescale`). For `f = e^{2φ}` this is
  `II^ĝ_q = e^{φ(q)} (II_q - dφ_q(ν_in) h_q)`.

In particular a constant factor `c² > 0` gives `II^{c² g} = c II`
(`boundarySecondFundamentalForm_rescale_const`), and when `df_q(ν_in) = 0` the second fundamental
form is multiplied by `√(f q)`, so the sign of `II_q(u, u)` is preserved
(`boundarySecondFundamentalForm_rescale_of_mvfderiv_inwardUnitNormal_eq_zero`). All declarations
of this file are in the `Bundle.ContMDiffRiemannianMetric` namespace, for dot notation on `g`.

The proof writes `II` through the normal coordinate `x⁰` of the preferred chart at `q`,
`II_q(u, w) = Hess ψ(dι u, dι w) / |grad ψ(q)|` for `ψ = -x⁰`, and combines the conformal Hessian
formula `Bundle.ContMDiffRiemannianMetric.hessian_rescale` (whose correction terms involving
`dψ(dι u)` and `dψ(dι w)` vanish) with `|grad_ĝ ψ|_ĝ = f^(-1/2) |grad_g ψ|_g`
(`Bundle.ContMDiffRiemannianMetric.norm_mgradient_rescale`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace Bundle.ContMDiffRiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] {k : ℕ∞ω}

/-! ### The induced metric -/

section InducedForm

variable [IsManifold (𝓡∂ (n + 1)) 1 M]
  (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
  {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)

/-- **The induced metric of the boundary under a rescaling**: for `ĝ = f g`,
`h^ĝ_q = f(q) h_q`. -/
theorem boundaryInducedForm_rescale (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      boundaryInducedForm q u w) =
    f q * (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨g.toRiemannianMetric⟩; boundaryInducedForm q u w) := by
  simp only [boundaryInducedForm_apply, inner_riemannianBundle, rescale_inner]

end InducedForm

/-! ### The unit normals -/

section UnitNormal

variable [IsManifold (𝓡∂ (n + 1)) 1 M]
  (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
  {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)

/-- **The outward unit normal under a rescaling**: for `ĝ = f g`,
`ν_out^ĝ(q) = f(q)^(-1/2) ν_out(q)`. -/
theorem outwardUnitNormal_rescale (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      outwardUnitNormal q) =
    (√(f q))⁻¹ • (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨g.toRiemannianMetric⟩; outwardUnitNormal q) := by
  set ν := (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩; outwardUnitNormal q)
  have hnorm : (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩; ‖ν‖) = 1 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
    exact norm_outwardUnitNormal q
  have hout : IsOutwardPointing (q : M) ν := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
    exact isOutwardPointing_outwardUnitNormal q
  have horth (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
      g.inner q ν (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
    rw [← inner_riemannianBundle]
    exact inner_outwardUnitNormal_mfderiv_subtypeVal q w
  have hs : 0 < √(f q) := Real.sqrt_pos.2 (hf_pos q)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  refine (eq_outwardUnitNormal_iff.2 ⟨?_, hout.smul_pos (inv_pos.2 hs), fun w ↦ ?_⟩).symm
  · rw [norm_smul, g.norm_rescale f hf hf_pos, hnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hs), mul_one, inv_mul_cancel₀ hs.ne']
  · rw [inner_riemannianBundle, rescale_inner, map_smul, smul_apply, horth]
    simp

/-- **The inward unit normal under a rescaling**: for `ĝ = f g`,
`ν_in^ĝ(q) = f(q)^(-1/2) ν_in(q)`. -/
theorem inwardUnitNormal_rescale (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      inwardUnitNormal q) =
    (√(f q))⁻¹ • (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨g.toRiemannianMetric⟩; inwardUnitNormal q) := by
  have h := outwardUnitNormal_rescale g hf hf_pos q
  have hg : (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩; inwardUnitNormal q) =
      -(letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨g.toRiemannianMetric⟩; outwardUnitNormal q) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
    exact inwardUnitNormal_def q
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  rw [inwardUnitNormal_def, h, hg, smul_neg]

end UnitNormal

/-! ### The second fundamental form -/

section SecondFundamentalForm

variable [IsManifold (𝓡∂ (n + 1)) 2 M]
  (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
  {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)

/-- **The second fundamental form of the boundary under a rescaling.** For `ĝ = f g` with `f`
positive and `C¹` and a `C¹` metric `g`, at `q ∈ ∂M`,
`II^ĝ_q(u, w) = √(f q) (II_q(u, w) - (2 f q)⁻¹ df_q(ν_in) g(dι u, dι w))`, where `ν_in` is the
inward unit normal of `g`. For `f = e^{2φ}` this is `II^ĝ_q = e^{φ(q)} (II_q - dφ_q(ν_in) h_q)`. -/
theorem boundarySecondFundamentalForm_rescale (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundarySecondFundamentalForm q u w) =
    √(f q) * ((letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundarySecondFundamentalForm q u w) -
      (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
            ⟨g.toRiemannianMetric⟩; inwardUnitNormal q) *
        g.inner q
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)) := by
  simp only [boundarySecondFundamentalForm_apply]
  rw [g.norm_mgradient_rescale hf hf_pos,
    g.hessian_rescale hk hf hf_pos (contMDiffAt_neg_chartAt_normal (mem_chart_source _ _))]
  set ψ : M → ℝ := fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).val 0
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  -- For `g`, the gradient of `ψ` is `N ν_out` with `N = |grad ψ(q)| > 0`.
  set N := ‖TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) ψ q‖
  have hgrad : TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) ψ q = N • outwardUnitNormal q := by
    rw [outwardUnitNormal_eq_normalize_mgradient (IsManifold.chart_mem_maximalAtlas (q : M))
      (mem_chart_source _ _), NormedSpace.norm_smul_normalize]
  have hN : N ≠ 0 :=
    norm_ne_zero_iff.2 (mgradient_neg_chartAt_normal_ne_zero q.property (mem_chart_source _ _))
  -- `dψ` vanishes on the tangent vectors `dι v` of the boundary.
  have hdψ (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
      mvfderiv (𝓡∂ (n + 1)) ψ q (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q v) = 0 := by
    rw [← TauCeti.Manifold.inner_mgradient, hgrad, inner_smul_left,
      inner_outwardUnitNormal_mfderiv_subtypeVal, mul_zero]
  rw [hdψ u, hdψ w, hgrad, inner_smul_right, TauCeti.Manifold.inner_mgradient,
    inwardUnitNormal_def, map_neg, ← inner_riemannianBundle g]
  -- Write `f q = s ^ 2` with `s = √(f q) > 0` and clear denominators.
  have hs : 0 < √(f q) := Real.sqrt_pos.2 (hf_pos q)
  have hf' : f q = √(f q) ^ 2 := (Real.sq_sqrt (hf_pos q).le).symm
  generalize √(f q) = s at hs hf' ⊢
  rw [hf']
  field_simp
  ring

/-- If `df_q(ν_in) = 0`, rescaling the metric by `f` multiplies the second fundamental form at `q`
by `√(f q)`; in particular the sign of `II_q(u, u)` is preserved. -/
theorem boundarySecondFundamentalForm_rescale_of_mvfderiv_inwardUnitNormal_eq_zero (hk : 1 ≤ k)
    {q : (𝓡∂ (n + 1)).boundary M}
    (hq : mvfderiv (𝓡∂ (n + 1)) f q
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨g.toRiemannianMetric⟩; inwardUnitNormal q) = 0)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundarySecondFundamentalForm q u w) =
    √(f q) * (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundarySecondFundamentalForm q u w) := by
  rw [boundarySecondFundamentalForm_rescale g hf hf_pos hk q u w, hq, mul_zero, zero_mul,
    sub_zero]

/-- **Constant rescaling**: for a constant `c > 0`, `II^{c² g} = c II`. -/
theorem boundarySecondFundamentalForm_rescale_const (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c)
    (q : (𝓡∂ (n + 1)).boundary M) (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale (fun _ ↦ c ^ 2) contMDiff_const fun _ ↦ pow_pos hc 2).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundarySecondFundamentalForm q u w) =
    c * (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundarySecondFundamentalForm q u w) := by
  rw [boundarySecondFundamentalForm_rescale_of_mvfderiv_inwardUnitNormal_eq_zero g _ _ hk
    (by rw [mvfderiv_const, zero_apply]), Real.sqrt_sq hc.le]

end SecondFundamentalForm

end Bundle.ContMDiffRiemannianMetric
