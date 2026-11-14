/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
public import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The positive-radius parametrization of a cone

The regular part of the cone over a map `f` is parametrized by `C(r,x)=r f(x)` for `r>0`.
For a spherical isometric immersion its first fundamental form is the warped product
`dr²+r²g`. The radial domain excludes the vertex and carries the inherited real metric.
-/

public noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff TauCeti

namespace TauCeti.Manifold.Cone

/-- The open positive-radius parameter domain. -/
def radiusDomain : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

/-- Membership in the radial domain is positivity. -/
@[simp]
theorem mem_radiusDomain {r : ℝ} : r ∈ radiusDomain ↔ 0 < r :=
  (Iff.rfl)

/-- Every radius in the regular cone domain is positive. -/
theorem radius_pos (r : radiusDomain) : 0 < (r : ℝ) :=
  r.property

/-- The inherited real inner product on the radial tangent line is the product of its
ordinary radial coordinate derivatives.

After restriction to the open radial domain, the ambient real metric's `g.inner` is
definitionally the native tangent inner product. The explicit `change` exposes this form
to `inner_tangentSpace_vectorSpace` without changing the installed metric. -/
theorem inner_radiusDomain (r : radiusDomain)
    (v w : TangentSpace 𝓘(ℝ) r) :
    inner ℝ v w =
      mvfderiv 𝓘(ℝ) (Subtype.val : radiusDomain → ℝ) r v *
        mvfderiv 𝓘(ℝ) (Subtype.val : radiusDomain → ℝ) r w := by
  rw [inner_tangentSpace_open radiusDomain r v w]
  change inner ℝ (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r v)
    (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r w) = _
  simpa only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, Real.inner_apply] using
    (inner_tangentSpace_vectorSpace (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r v)
      (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r w))

/-- The outward radial tangent vector with coordinate velocity one. -/
def radialVector (r : radiusDomain) : TangentSpace 𝓘(ℝ) r :=
  (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r).symm
    ((NormedSpace.fromTangentSpace (r : ℝ)).symm 1)

/-- The radial coordinate has derivative one on the outward radial vector. -/
@[simp]
theorem mvfderiv_radius_radialVector (r : radiusDomain) :
    mvfderiv 𝓘(ℝ) (Subtype.val : radiusDomain → ℝ) r (radialVector r) = 1 := by
  simp only [radialVector, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The positive-radius cone parametrization of a vector-valued map. -/
def parametrization (f : M → F) (p : radiusDomain × M) : F :=
  (p.1 : ℝ) • f p.2

omit [TopologicalSpace M] in
/-- Evaluation of the cone parametrization. -/
theorem parametrization_def (f : M → F) (p : radiusDomain × M) :
    parametrization f p = (p.1 : ℝ) • f p.2 :=
  (rfl)

/-- Smoothness of a cone parametrization follows from smoothness of its link. -/
theorem contMDiff_parametrization {f : M → F} {k : ℕ∞ω}
    (hf : ContMDiff I 𝓘(ℝ, F) k f) :
    ContMDiff ((𝓘(ℝ)).prod I) 𝓘(ℝ, F) k (parametrization f) := by
  unfold parametrization
  exact (contMDiff_subtype_val.comp contMDiff_fst).smul (hf.comp contMDiff_snd)

/-- Local differentiability of a cone parametrization only requires local differentiability
of its link. -/
theorem mdifferentiableAt_parametrization {f : M → F} {p : radiusDomain × M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p.2) :
    MDifferentiableAt ((𝓘(ℝ)).prod I) 𝓘(ℝ, F) (parametrization f) p := by
  unfold parametrization
  exact ((contMDiff_subtype_val.comp contMDiff_fst).mdifferentiableAt one_ne_zero).smul
    (hf.comp p mdifferentiableAt_snd)

/-- The differential of the cone parametrization is the sum of its radial and link parts. -/
theorem mvfderiv_parametrization {f : M → F} {p : radiusDomain × M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p.2)
    (v : TangentSpace ((𝓘(ℝ)).prod I) p) :
    mvfderiv ((𝓘(ℝ)).prod I) (parametrization f) p v =
      (p.1 : ℝ) • mvfderiv I f p.2 (tangentSpaceProdEquiv p v).2 +
        mvfderiv 𝓘(ℝ) (Subtype.val : radiusDomain → ℝ) p.1
          (tangentSpaceProdEquiv p v).1 • f p.2 := by
  have hr : MDifferentiableAt ((𝓘(ℝ)).prod I) 𝓘(ℝ)
      (fun q : radiusDomain × M ↦ (q.1 : ℝ)) p := by
    exact (contMDiff_subtype_val.comp contMDiff_fst).mdifferentiableAt one_ne_zero
  have hF : MDifferentiableAt ((𝓘(ℝ)).prod I) 𝓘(ℝ, F)
      (fun q : radiusDomain × M ↦ f q.2) p := hf.comp p mdifferentiableAt_snd
  have h₁ := mvfderiv_comp_apply (g := (Subtype.val : radiusDomain → ℝ)) p
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) mdifferentiableAt_fst v
  have h₂ := mvfderiv_comp_apply (g := f) p hf mdifferentiableAt_snd v
  unfold parametrization
  rw [mvfderiv_fun_smul hr hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  simp only [Function.comp_def, mfderiv_fst, mfderiv_snd] at h₁ h₂
  rw [h₁, h₂, tangentSpaceProdEquiv_apply]
  rfl

/-- The outward radial direction maps to the link's position vector. -/
theorem mvfderiv_parametrization_radial {f : M → F} {p : radiusDomain × M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p.2) :
    mvfderiv ((𝓘(ℝ)).prod I) (parametrization f) p
      ((tangentSpaceProdEquiv p).symm (radialVector p.1, 0)) = f p.2 := by
  rw [mvfderiv_parametrization hf, ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_zero, smul_zero, mvfderiv_radius_radialVector, one_smul, zero_add]

variable [IsManifold I 1 M]

/-- The smooth warped metric `dr²+r²g` on the positive-radius cone parameter domain. -/
def metric (g : ContMDiffRiemannianMetric I 1 E (fun x : M ↦ TangentSpace I x)) :
    ContMDiffRiemannianMetric ((𝓘(ℝ)).prod I) 1 (ℝ × E)
      (fun p : radiusDomain × M ↦ TangentSpace ((𝓘(ℝ)).prod I) p) :=
  ContMDiffRiemannianMetric.warpedProdTangentSpace
    (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle :
      ContMDiffRiemannianMetric 𝓘(ℝ) 1 ℝ (fun r : radiusDomain ↦ TangentSpace 𝓘(ℝ) r))
    (fun r : radiusDomain ↦ (r : ℝ)) contMDiff_subtype_val (fun r ↦ (radius_pos r).ne') g

/-- The cone metric is the orthogonal sum of the radial metric and the link metric
multiplied by radius squared. -/
theorem metric_inner (g : ContMDiffRiemannianMetric I 1 E (fun x : M ↦ TangentSpace I x))
    (p : radiusDomain × M) (v w : TangentSpace ((𝓘(ℝ)).prod I) p) :
    (metric g).inner p v w =
      inner ℝ (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
        (p.1 : ℝ) ^ 2 * g.inner p.2
          (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 := by
  rw [metric, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

/-- Installing the constructed metric gives the native warped-product structure of the
regular cone. -/
theorem isWarpedProduct_metric
    (g : ContMDiffRiemannianMetric I 1 E (fun x : M ↦ TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle
        (fun p : radiusDomain × M ↦ TangentSpace ((𝓘(ℝ)).prod I) p) :=
      ⟨(metric g).toRiemannianMetric⟩
    IsWarpedProduct 𝓘(ℝ) I M (fun r : radiusDomain ↦ (r : ℝ)) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle
      (fun p : radiusDomain × M ↦ TangentSpace ((𝓘(ℝ)).prod I) p) :=
    ⟨(metric g).toRiemannianMetric⟩
  exact ⟨metric_inner g⟩

end TauCeti.Manifold.Cone
