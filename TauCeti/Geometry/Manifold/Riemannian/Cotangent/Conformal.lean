/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Conformal
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz

/-!
# The inverse metric under conformal rescaling

For a positive conformal factor `f`, the inverse metric of `f g` is `f⁻¹` times that of `g`.
We prove this for arbitrary covectors, not only differentials of functions: raising a covector's
index multiplies its representing tangent vector by `f⁻¹`, the inverse-metric pairing scales by
`f⁻¹`, and the covector norm scales by `1 / √f`. We also give the inverse Gram matrix formula in
chart coordinates. These identities compare cotangent energies for conformally related metrics.

The metrics live on the distinct copies `TauCeti.WithMetric g` and
`TauCeti.WithMetric (g.rescale f hf hf_pos)`. Covectors on the underlying manifold are pulled
back by the differential of `ofWithMetric`, and tangent vectors are transported back by that same
differential. Thus no two metric instances are installed on one carrier. All results hold for
`Cⁿ` metrics and positive `Cⁿ` factors, including `n = 0`.

The proofs use the characteristic inner-product identity of `Riemannian.Tensor.rieszDual` and
`TauCeti.WithMetric.inner_rescale`, and the coordinate identity
`TauCeti.WithMetric.chartGramMatrix_rescale`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2 (the dual metric).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

noncomputable section

open Bundle Riemannian.Tensor
open scoped Manifold ContDiff

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f} {hf_pos : ∀ x, 0 < f x}

/-- Raising the index of a covector for `f g` gives `f⁻¹` times its Riesz dual for `g`,
with both vectors transported to the underlying manifold. -/
theorem mfderiv_ofWithMetric_rieszDual_rescale (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)
        (rieszDual (I := I) (toWithMetric (g.rescale f hf hf_pos) x)
          (φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)))) =
      (f x)⁻¹ • mfderiv I I ofWithMetric (toWithMetric g x)
        (rieszDual (I := I) (toWithMetric g x)
          (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))) := by
  set v := mfderiv I I ofWithMetric (toWithMetric g x)
    (rieszDual (I := I) (toWithMetric g x)
      (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))))
  suffices h : mfderiv I I (toWithMetric (g.rescale f hf hf_pos)) x ((f x)⁻¹ • v) =
      rieszDual (I := I) (toWithMetric (g.rescale f hf hf_pos) x)
        (φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))) by
    rw [← h, mfderiv_ofWithMetric_mfderiv_toWithMetric]
  rw [eq_rieszDual_iff_inner_eq]
  intro w
  have h := inner_rieszDual
    (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))
    (mfderiv I I (toWithMetric g) x
      (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x) w))
  rw [inner_def, mfderiv_ofWithMetric_mfderiv_toWithMetric] at h
  rw [inner_rescale, mfderiv_ofWithMetric_mfderiv_toWithMetric]
  simp only [v, map_smul, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply] at h ⊢
  rw [mul_inv_cancel_left₀ (hf_pos x).ne', h]
  rw [mfderiv_ofWithMetric_apply, mfderiv_toWithMetric_apply]

/-- The inverse-metric pairing `φ(ψ♯)` of two covectors scales by `f⁻¹` under `g ↦ f g`. -/
theorem apply_rieszDual_rescale (x : M) (φ ψ : TangentSpace I x →L[ℝ] ℝ) :
    (φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)))
        (rieszDual (I := I) (toWithMetric (g.rescale f hf hf_pos) x)
          (ψ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)))) =
      (f x)⁻¹ * (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))
        (rieszDual (I := I) (toWithMetric g x)
          (ψ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))) := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [mfderiv_ofWithMetric_rieszDual_rescale (g := g) (hf := hf) (hf_pos := hf_pos),
    map_smul, smul_eq_mul]

/-- The squared operator norm of an arbitrary covector scales by `f⁻¹` under `g ↦ f g`. -/
theorem norm_sq_covector_rescale (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))‖ ^ 2 =
      (f x)⁻¹ * ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))‖ ^ 2 := by
  simp only [norm_sq_eq_apply_rieszDual]
  exact apply_rieszDual_rescale x φ φ

/-- The operator norm of a covector for `f g` is its norm for `g` divided by `√f`. -/
theorem norm_covector_rescale (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))‖ =
      (Real.sqrt (f x))⁻¹ * ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))‖ := by
  have h := congrArg Real.sqrt (norm_sq_covector_rescale (g := g) (hf := hf) (hf_pos := hf_pos) x φ)
  -- Use operator-norm positivity directly: each domain carries its own metric norm.
  have h₁ : 0 ≤ ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have h₂ : 0 ≤ ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  simpa only [Real.sqrt_mul (inv_nonneg.mpr (hf_pos x).le), Real.sqrt_inv,
    Real.sqrt_sq h₁, Real.sqrt_sq h₂] using h

/-- In chart coordinates, the inverse Gram matrix of `f g` is `f⁻¹` times that of `g`. -/
theorem chartInvGramMatrix_rescale (α x : M) (hx : x ∈ (chartAt H α).source) :
    chartInvGramMatrix (I := I) (toWithMetric (g.rescale f hf hf_pos) α)
        (toWithMetric (g.rescale f hf hf_pos) x) =
      (f x)⁻¹ • chartInvGramMatrix (I := I) (toWithMetric g α) (toWithMetric g x) := by
  rw [chartInvGramMatrix_def, chartInvGramMatrix_def, chartGramMatrix_rescale]
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (hf_pos x).ne', one_smul,
    ← chartInvGramMatrix_def, chartInvGramMatrix_mul_chartGramMatrix]
  exact (mem_chartAt_source_iff (toWithMetric g α) (toWithMetric g x)).2 hx

end TauCeti.WithMetric
