/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Riccardo Brasca
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The gradient on a normed space

On a flat inner product space with its standard Riemannian metric, the manifold gradient agrees
with Mathlib's `gradient`; the squared norm therefore has the expected radial gradient. For an
arbitrary Riemannian metric on a normed space, the gradient is read in linear coordinates through
its pairing with constant vectors, and its squared length is `|dφ|² = dφ(g⁻¹ dφ)` for the metric
coefficient field `g`.

Every nonzero continuous linear functional has nonzero gradient for any positive Riemannian
metric. In particular, the first-coordinate function has nonzero gradient, whose normalization
gives the inward unit normal of a linear boundary chart. These nonvanishing results are ported
from Riccardo Brasca's original `ForTauCeti` formalization.

The standard metric is analytic (`IsContMDiffRiemannianBundle.vectorSpace`), so the manifold
results on gradient flows apply to it, and a classical solution of `γ' = -∇ f (γ)` on an open
interval around `0` is the maximal integral curve of `-grad f` there
(`TauCeti.Manifold.eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt`).
-/

public section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

open Riemannian.Tensor

/-- On a flat inner product space with its standard Riemannian metric, the manifold gradient is
Mathlib's `gradient`. -/
theorem mgradient_eq_gradient {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : F → ℝ) (x : F) :
    let _ : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
      ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩
    mgradient 𝓘(ℝ, F) f x = gradient f x := by
  dsimp only
  apply (NormedSpace.fromTangentSpace x).injective
  apply ext_inner_right ℝ
  intro v
  calc
    inner ℝ (NormedSpace.fromTangentSpace x (mgradient 𝓘(ℝ, F) f x)) v =
      inner ℝ (mgradient 𝓘(ℝ, F) f x) ((NormedSpace.fromTangentSpace x).symm v) := by
        simpa using (inner_tangentSpace_vectorSpace (mgradient 𝓘(ℝ, F) f x)
          ((NormedSpace.fromTangentSpace x).symm v)).symm
    _ = inner ℝ (gradient f x) v := by
      rw [inner_mgradient, ← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      rw [mvfderiv_eq_fderiv]
      simp

/-- If the installed fibre metric is the standard one, the manifold gradient is Mathlib's
`gradient`. This transports `mgradient_eq_gradient` along an equality of fibre metrics, such as
`toRiemannianMetric_ofLE`, which cannot be rewritten inside the instance-dependent arguments. -/
theorem mgradient_eq_gradient_of_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [inst : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    (hg : RiemannianBundle.g = (riemannianMetricVectorSpace F).toRiemannianMetric)
    (f : F → ℝ) (x : F) :
    mgradient 𝓘(ℝ, F) f x = gradient f x := by
  obtain ⟨_⟩ := inst
  subst hg
  exact mgradient_eq_gradient f x

/-- If the installed fibre metric is the standard one, the manifold gradient has the norm of
Mathlib's `gradient`. The norm on the tangent space is itself induced by the installed metric, so
this is transported along `hg` together with `mgradient_eq_gradient_of_eq`. -/
theorem norm_mgradient_eq_norm_gradient_of_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [inst : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    (hg : RiemannianBundle.g = (riemannianMetricVectorSpace F).toRiemannianMetric)
    (f : F → ℝ) (x : F) :
    ‖mgradient 𝓘(ℝ, F) f x‖ = ‖gradient f x‖ := by
  rw [mgradient_eq_gradient_of_eq hg]
  obtain ⟨_⟩ := inst
  subst hg
  exact norm_tangentSpace_vectorSpace

/-- The gradient of the squared norm in the standard flat metric is the radial vector field.

Source: `Mathlib.Analysis.InnerProductSpace.Calculus.fderiv_norm_sq_apply`.
-/
@[simp]
theorem mgradient_norm_sq_model_space {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (x : F) :
    let _ : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
      ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩
    mgradient 𝓘(ℝ, F) (fun y : F ↦ ‖y‖ ^ 2) x = 2 • x := by
  dsimp only
  have hx : (InnerProductSpace.toDual ℝ F).symm ((innerSL ℝ) x) = x := by
    have hdual : (innerSL ℝ) x = (InnerProductSpace.toDual ℝ F) x := by
      ext y
      rw [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    rw [hdual]
    exact (InnerProductSpace.toDual ℝ F).symm_apply_apply x
  rw [mgradient_eq_gradient]
  simp [gradient, fderiv_norm_sq_apply, hx]
  rfl

/-- A genuine nonzero linear defining functional has nonzero native metric gradient. -/
theorem _root_.ContinuousLinearMap.mgradient_ne_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    (L : F →L[ℝ] ℝ) (hL : L ≠ 0) (x : F) :
    mgradient 𝓘(ℝ, F) L x ≠ 0 := by
  intro hz
  apply hL
  ext v
  have hd := mgradient_eq_zero_iff.mp hz
  have he := congrArg
    (fun A : TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ ↦
      A ((NormedSpace.fromTangentSpace x).symm v)) hd
  rw [zero_apply] at he
  have hval : mvfderiv 𝓘(ℝ, F) L x
      ((NormedSpace.fromTangentSpace x).symm v) = L v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    exact NormedSpace.fromTangentSpace_symm_apply (L x) (L v)
  exact hval.symm.trans he

/-- The actual normal-coordinate differential has nonzero native gradient in every
positive Riemannian metric. -/
theorem mgradient_fst_ne_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G]
    [RiemannianBundle (fun x : ℝ × G ↦ TangentSpace 𝓘(ℝ, ℝ × G) x)] (x : ℝ × G) :
    mgradient 𝓘(ℝ, ℝ × G) (Prod.fst : ℝ × G → ℝ) x ≠ 0 := by
  apply (ContinuousLinearMap.fst ℝ ℝ G).mgradient_ne_zero ?_ x
  intro hzero
  have he := congrArg (fun A : (ℝ × G) →L[ℝ] ℝ ↦ A (1, 0)) hzero
  simp only [ContinuousLinearMap.coe_fst', zero_apply] at he
  exact one_ne_zero he

/-- On a normed space with any Riemannian metric, pairing the gradient with a constant vector `v`
gives the Fréchet derivative in the direction `v`. -/
theorem inner_mgradient_model_space {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    (f : F → ℝ) (x v : F) :
    inner ℝ (mgradient 𝓘(ℝ, F) f x) ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm v) =
      fderiv ℝ f x v := by
  rw [inner_mgradient, mvfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace x` is `tangentSpaceCastModel 𝓘(ℝ, F) x` by definition.
  simp [NormedSpace.fromTangentSpace]

/-- On a normed space whose Riemannian metric at `x` is the bilinear form `g x` in linear
coordinates, the squared length of the gradient is `|df|² = df(g⁻¹ df)`. -/
theorem norm_mgradient_sq_model_space {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    {g : F → F →L[ℝ] F →L[ℝ] ℝ} {x : F}
    (hg : ∀ v w : TangentSpace 𝓘(ℝ, F) x, inner ℝ v w =
      g x (tangentSpaceCastModel 𝓘(ℝ, F) x v) (tangentSpaceCastModel 𝓘(ℝ, F) x w))
    (f : F → ℝ) :
    ‖mgradient 𝓘(ℝ, F) f x‖ ^ 2 = fderiv ℝ f x ((g x).inverse (fderiv ℝ f x)) := by
  have hinv : (g x).IsInvertible := ContinuousLinearMap.isInvertible_of_pos fun v hv ↦ by
    have h := hg ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm v)
      ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm v)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h ▸ real_inner_self_pos.2 (by simpa using hv)
  have h : g x (tangentSpaceCastModel 𝓘(ℝ, F) x (mgradient 𝓘(ℝ, F) f x)) = fderiv ℝ f x := by
    ext v
    rw [← inner_mgradient_model_space f x v, hg]
    simp
  rw [← h, hinv.inverse_apply_self, ← real_inner_self_eq_norm_sq, hg]

/-- **Negative gradient trajectories of a flat space.** On a finite-dimensional real inner product
space with its standard metric, let `f` be `C²` and let `γ` solve `γ' = -∇ f (γ)` on an open
interval around `0`. Then `γ` is the maximal integral curve of `-grad f` through `γ 0` on that
interval. -/
theorem eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    {γ : ℝ → F} {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (-gradient f (γ t)) t) :
    EqOn (maximalIntegralCurve (-mgradient 𝓘(ℝ, F) f) (γ 0)) γ (Ioo a b) := by
  refine IsMIntegralCurveOn.eqOn_maximalIntegralCurve
    (contMDiff_neg_mgradient_one hf.contMDiff) ?_ h0 rfl
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn]
  intro t ht
  -- The tangent space of `F` at `γ t` is `F` itself, with the same negation.
  exact (hγ t ht).hasDerivWithinAt.congr_deriv
    (congrArg (fun w : F ↦ -w) (mgradient_eq_gradient_of_eq rfl f (γ t))).symm

end TauCeti.Manifold
