/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Conformal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Convexity of the boundary under a conformal change of metric

Let `M` be a manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, `g` a `C¹`
Riemannian metric on `M` and `ĝ = f g` its rescaling by a positive `C¹` function `f`
(`Bundle.ContMDiffRiemannianMetric.rescale`); for `f = e^{2φ}` this is the conformal change
`ĝ = e^{2φ} g`. At `q ∈ ∂M` the second fundamental form of the boundary changes by
`II^ĝ_q = √(f q) (II_q - (2 f q)⁻¹ df_q(ν_in) h_q)`
(`Bundle.ContMDiffRiemannianMetric.boundarySecondFundamentalForm_rescale`), where `ν_in` is the
inward unit normal and `h_q` the induced metric of `g`. Since `√(f q) > 0`, the convexity
predicates of the boundary for `ĝ` are those of the symmetric form
`II_q - (2 f q)⁻¹ df_q(ν_in) h_q` (`Bundle.ContMDiffRiemannianMetric.conformalBoundaryForm`):

* `∂M` is strictly convex at `q` for `ĝ` iff `II_q - (2 f q)⁻¹ df_q(ν_in) h_q` is positive definite
  (`Bundle.ContMDiffRiemannianMetric.isStrictlyConvexAt_rescale_iff`); for `f = e^{2φ}` the
  coefficient `(2 f q)⁻¹ df_q(ν_in)` is `dφ_q(ν_in)`
  (`Bundle.ContMDiffRiemannianMetric.conformalBoundaryForm_exp`), so `∂M` is strictly convex at `q`
  for `e^{2φ} g` iff `II_q - dφ_q(ν_in) h_q` is positive definite;
* `∂M` is convex at `q` for `ĝ` iff that form is nonnegative
  (`Bundle.ContMDiffRiemannianMetric.isConvexAt_rescale_iff`), and strictly concave iff its
  negative is positive definite
  (`Bundle.ContMDiffRiemannianMetric.isStrictlyConcaveAt_rescale_iff`).

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Definition 3.1.7.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) 2 M]
  (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
  {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)

variable (f) in
/-- The symmetric form `II_q - (2 f q)⁻¹ df_q(ν_in) h_q` on the tangent space of the boundary at
`q ∈ ∂M`, for the metric `g`: the second fundamental form of the boundary for `ĝ = f g`, divided by
`√(f q)`. For `f = e^{2φ}` it is `II_q - dφ_q(ν_in) h_q`. -/
def conformalBoundaryForm (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
  boundarySecondFundamentalForm q -
    ((2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q)) • boundaryInducedForm q

/-- The defining formula of `Bundle.ContMDiffRiemannianMetric.conformalBoundaryForm`. -/
@[simp]
theorem conformalBoundaryForm_apply (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    conformalBoundaryForm g f hk q u w =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundarySecondFundamentalForm q u w -
          (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) *
            boundaryInducedForm q u w) :=
  (rfl)

/-- `Bundle.ContMDiffRiemannianMetric.conformalBoundaryForm` is symmetric. -/
theorem conformalBoundaryForm_isSymm (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M) :
    (conformalBoundaryForm g f hk q).IsSymm := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
  exact (boundarySecondFundamentalForm_isSymm q).sub ((boundaryInducedForm_isSymm q).smul _)

/-- The second fundamental form of the boundary for `ĝ = f g` is `√(f q)` times
`Bundle.ContMDiffRiemannianMetric.conformalBoundaryForm`. -/
theorem boundarySecondFundamentalForm_rescale_eq_smul (hk : 1 ≤ k)
    (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundarySecondFundamentalForm q) =
    √(f q) • conformalBoundaryForm g f hk q := by
  ext u w
  rw [boundarySecondFundamentalForm_rescale g hf hf_pos hk q u w]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  simp [conformalBoundaryForm_apply, boundaryInducedForm_apply, inner_riemannianBundle]

/-- For `f = e^{2φ}`, the coefficient `(2 f q)⁻¹ df_q(ν_in)` of
`Bundle.ContMDiffRiemannianMetric.conformalBoundaryForm` is `dφ_q(ν_in)`: the form is
`II_q - dφ_q(ν_in) h_q`. -/
theorem conformalBoundaryForm_exp (hk : 1 ≤ k) (φ : M → ℝ) (q : (𝓡∂ (n + 1)).boundary M) :
    conformalBoundaryForm g (fun x ↦ Real.exp (2 * φ x)) hk q =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundarySecondFundamentalForm q -
          mvfderiv (𝓡∂ (n + 1)) φ q (inwardUnitNormal q) • boundaryInducedForm q) := by
  rcases em' (MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) φ q) with hφ | hφ
  · -- Then `e^{2φ}` is not differentiable at `q` either, as `φ = 2⁻¹ log e^{2φ}`: both
    -- derivatives vanish.
    have hf : ¬MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) (fun x ↦ Real.exp (2 * φ x)) q := by
      refine fun h ↦ hφ ?_
      convert ((Real.differentiableAt_log (Real.exp_pos (2 * φ q)).ne').const_mul
        (2⁻¹ : ℝ)).comp_mdifferentiableAt (f := fun x ↦ Real.exp (2 * φ x)) h using 1
      ext x
      simp [Real.log_exp]
    simp [conformalBoundaryForm, mvfderiv_eq_zero_iff.2 (mfderiv_zero_of_not_mdifferentiableAt hφ),
      mvfderiv_eq_zero_iff.2 (mfderiv_zero_of_not_mdifferentiableAt hf)]
  have hexp : HasDerivAt (fun t : ℝ ↦ Real.exp (2 * t)) (Real.exp (2 * φ q) * (2 * 1)) (φ q) :=
    ((hasDerivAt_id (φ q)).const_mul 2).exp
  have hd := mvfderiv_scalar_comp (I := 𝓡∂ (n + 1)) hφ hexp.differentiableAt
  rw [hexp.deriv, Function.comp_def] at hd
  have he : Real.exp (2 * φ q) ≠ 0 := (Real.exp_pos _).ne'
  simp only [conformalBoundaryForm, hd, smul_apply, smul_eq_mul]
  congr 2
  field_simp

/-- **Strict convexity under a conformal change.** For `ĝ = f g`, the boundary is strictly convex
at `q` iff `II_q - (2 f q)⁻¹ df_q(ν_in) h_q` is positive definite; for `f = e^{2φ}` this is
`II_q - dφ_q(ν_in) h_q`. -/
theorem isStrictlyConvexAt_rescale_iff (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      IsStrictlyConvexAt q) ↔ (conformalBoundaryForm g f hk q).toQuadraticMap.PosDef := by
  have hs : 0 < √(f q) := Real.sqrt_pos.2 (hf_pos q)
  have h := boundarySecondFundamentalForm_rescale_eq_smul g hf hf_pos hk q
  simp only [isStrictlyConvexAt_iff_posDef, h, QuadraticMap.PosDef,
    LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.smul_apply, smul_eq_mul,
    mul_pos_iff_of_pos_left hs]

/-- **Convexity under a conformal change.** For `ĝ = f g`, the boundary is convex at `q` iff
`II_q - (2 f q)⁻¹ df_q(ν_in) h_q` is nonnegative. -/
theorem isConvexAt_rescale_iff (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      IsConvexAt q) ↔ LinearMap.IsNonneg (conformalBoundaryForm g f hk q) := by
  have hs : 0 < √(f q) := Real.sqrt_pos.2 (hf_pos q)
  have h := boundarySecondFundamentalForm_rescale_eq_smul g hf hf_pos hk q
  simp only [isConvexAt_iff_isNonneg, h, LinearMap.isNonneg_def, LinearMap.smul_apply,
    smul_eq_mul, mul_nonneg_iff_of_pos_left hs]

/-- **Strict concavity under a conformal change.** For `ĝ = f g`, the boundary is strictly concave
at `q` iff `-(II_q - (2 f q)⁻¹ df_q(ν_in) h_q)` is positive definite. -/
theorem isStrictlyConcaveAt_rescale_iff (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      IsStrictlyConcaveAt q) ↔ (-(conformalBoundaryForm g f hk q).toQuadraticMap).PosDef := by
  have hs : 0 < √(f q) := Real.sqrt_pos.2 (hf_pos q)
  have h := boundarySecondFundamentalForm_rescale_eq_smul g hf hf_pos hk q
  have hneg (x : ℝ) : √(f q) * x < 0 ↔ x < 0 := by
    rw [← neg_pos, ← mul_neg, mul_pos_iff_of_pos_left hs, neg_pos]
  simp only [isStrictlyConcaveAt_iff_posDef, h, QuadraticMap.PosDef, neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.smul_apply, smul_eq_mul, neg_pos, hneg]

end Bundle.ContMDiffRiemannianMetric
