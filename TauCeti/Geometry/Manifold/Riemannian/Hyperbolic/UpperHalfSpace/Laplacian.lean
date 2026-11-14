/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
-- Expose that `UpperHalfSpace E` is the open subset `upperHalfSpaceOpens E` and that its metric
-- is the restricted Euclidean metric `euclideanMetric` rescaled by `t⁻²`.
import all TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic

/-!
# The Laplacian of the height in the upper half-space

On the upper half-space model `{(x, t) | 0 < t}` of `E × ℝ` with the hyperbolic metric
`(‖dx‖² + dt²) / t²`, compute the gradient and the Laplace–Beltrami operator `Δ = div ∘ grad` of
the height `t` and of its real powers:

* `TauCeti.UpperHalfSpace.mgradient_height`: the gradient of `t` is `t² ∂_t`, so it has
  hyperbolic length `t` (`TauCeti.UpperHalfSpace.norm_mgradient_height`);
* `TauCeti.UpperHalfSpace.laplaceBeltrami_height`: `Δ t = (1 - dim E) t`;
* `TauCeti.UpperHalfSpace.laplaceBeltrami_height_rpow`: `Δ t^β = β (β - dim E) t^β`.

The hyperbolic metric is the Euclidean metric rescaled by `t⁻²`, and the Laplacian of `t` is read
off from the conformal change of the Laplacian; the powers follow from the chain rule.

In the hyperbolic plane (`dim E = 1`) the metric `(dθ² + dt²) / t²` is the standard cusp metric:
functions of `t` alone are invariant under `θ ↦ θ + 2π`, so they descend to the cusp end
`{t > a} × ℝ/2πℤ`, which is the punctured disc `0 < |z| < e^(-a)` with `t = -log |z|`. The
linearization of the curvature equation `Δ⁺u + K + e^(2u) = 0` at a hyperbolic metric is
`Δ⁺ + 2`, where `Δ⁺ = -Δ` is the nonnegative Laplacian. It multiplies `t^β` by
`(β + 1) (2 - β)` (`TauCeti.UpperHalfSpace.neg_laplaceBeltrami_height_rpow_add_two_mul`). Hence
its indicial roots on the cusp are `-1` and `2`
(`TauCeti.UpperHalfSpace.neg_laplaceBeltrami_height_rpow_add_two_mul_eq_zero_iff`), and every
power `t^β` with `-1 < β < 2`, in particular the weights `t^δ` and `t^(-δ)` for `0 < δ < 1`, is a
strict supersolution (`TauCeti.UpperHalfSpace.neg_laplaceBeltrami_height_rpow_add_two_mul_pos`).
These are the barriers for weighted estimates of `Δ⁺ + 2` near a cusp.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3
  (the upper half-space model).
* R. Mazzeo and M. Taylor, *Curvature and uniformization*, Israel J. Math. **130** (2002),
  323–346, for the linearized curvature equation on cusp ends.
-/

public section

open Bundle Manifold TauCeti.Manifold
open scoped ContDiff Manifold InnerProductSpace Gradient Laplacian

noncomputable section

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "P" => WithLp 2 (E × ℝ)
local notation "J" => 𝓘(ℝ, P)

/-- The gradient of the height function for the hyperbolic metric is `t² ∂_t`. -/
theorem mgradient_height (x : UpperHalfSpace E) :
    mgradient J height x =
      (tangentSpaceCastModel J x).symm (height x ^ 2 • WithLp.toLp 2 (0, 1)) := by
  symm
  rw [eq_mgradient_iff]
  intro v
  rw [inner_def, mvfderiv_height_apply, ContinuousLinearEquiv.apply_symm_apply, inner_smul_left,
    WithLp.prod_inner_apply]
  simp
  field_simp [(height_pos x).ne']

/-- The gradient of the height function has hyperbolic length equal to the height. -/
theorem norm_mgradient_height (x : UpperHalfSpace E) :
    ‖mgradient J height x‖ = height x := by
  rw [mgradient_height, norm_def, ContinuousLinearEquiv.apply_symm_apply, norm_smul]
  simp
  field_simp [(height_pos x).ne']

omit [FiniteDimensional ℝ E] in
/-- The Euclidean metric `euclideanMetric` of the upper half-space is the metric that open
submanifolds inherit from `E × ℝ`. -/
private theorem euclidean_eq_instRiemannianBundleOpen :
    (⟨euclideanMetric.toRiemannianMetric⟩ :
      RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace J x)) =
      instRiemannianBundleOpen (upperHalfSpaceOpens E) :=
  ((riemannianMetricVectorSpace P).riemannianBundle_restrictOpenTangentSpace_eq _).symm

/-- Transport the Laplace–Beltrami operator along an equality of installed metrics. -/
private theorem laplaceBeltrami_congr
    {i₁ i₂ : RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace J x)} (h : i₁ = i₂)
    (c₁ : letI := i₁
      IsContMDiffRiemannianBundle J 1 P (fun x : UpperHalfSpace E ↦ TangentSpace J x))
    (c₂ : letI := i₂
      IsContMDiffRiemannianBundle J 1 P (fun x : UpperHalfSpace E ↦ TangentSpace J x))
    (u : UpperHalfSpace E → ℝ) (x : UpperHalfSpace E) :
    (letI := i₁; letI := c₁; laplaceBeltrami J u x) =
      (letI := i₂; letI := c₂; laplaceBeltrami J u x) := by
  subst h
  rfl

/-- Transport the length of a gradient along an equality of installed metrics. -/
private theorem norm_mgradient_congr
    {i₁ i₂ : RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace J x)} (h : i₁ = i₂)
    (u : UpperHalfSpace E → ℝ) (x : UpperHalfSpace E) :
    (letI := i₁; ‖mgradient J u x‖) = (letI := i₂; ‖mgradient J u x‖) := by
  subst h
  rfl

/-- For the Euclidean metric the height function is harmonic. -/
private theorem laplaceBeltrami_height_euclidean (x : UpperHalfSpace E) :
    (letI : RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace J x) :=
        ⟨euclideanMetric.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle J 1 P (fun x : UpperHalfSpace E ↦ TangentSpace J x) :=
        (Bundle.instIsContMDiffRiemannianBundle euclideanMetric).of_le le_top;
      laplaceBeltrami J height x) = 0 := by
  refine (laplaceBeltrami_congr euclidean_eq_instRiemannianBundleOpen _
    (instIsContMDiffRiemannianBundleOpen (I := J) (n := 1) _) height x).trans ?_
  have hiso := IsLocalRiemannianIsometry.subtype_val (I := J) (upperHalfSpaceOpens E)
  refine (hiso.laplaceBeltrami_comp (u := WithLp.sndL 2 ℝ E ℝ) (x := x)
    (WithLp.sndL 2 ℝ E ℝ).contDiff.contMDiff.contMDiffAt).trans ?_
  rw [laplaceBeltrami_eq_laplacian (WithLp.sndL 2 ℝ E ℝ).contDiff,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  -- A continuous linear map has vanishing second derivative.
  have hL : fderiv ℝ (WithLp.sndL 2 ℝ E ℝ) = fun _ ↦ WithLp.sndL 2 ℝ E ℝ :=
    funext fun _ ↦ ContinuousLinearMap.fderiv _
  simp [iteratedFDeriv_two_apply, hL]

/-- For the Euclidean metric the gradient of the height function has unit length. -/
private theorem norm_mgradient_height_euclidean (x : UpperHalfSpace E) :
    (letI : RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace J x) :=
        ⟨euclideanMetric.toRiemannianMetric⟩;
      ‖mgradient J height x‖) = 1 := by
  refine (norm_mgradient_congr euclidean_eq_instRiemannianBundleOpen height x).trans ?_
  have hiso := IsLocalRiemannianIsometry.subtype_val (I := J) (upperHalfSpaceOpens E)
  refine (hiso.norm_mgradient_comp (φ := WithLp.sndL 2 ℝ E ℝ) (x := x)
    (WithLp.sndL 2 ℝ E ℝ).differentiableAt.mdifferentiableAt).trans ?_
  -- The Euclidean gradient of the last coordinate is the unit vector `(0, 1)`.
  have hgrad : ∇ (WithLp.sndL 2 ℝ E ℝ) x = WithLp.toLp 2 (0, 1) := by
    refine HasGradientAt.gradient ?_
    have h : InnerProductSpace.toDual ℝ P (WithLp.toLp 2 (0, 1)) = WithLp.sndL 2 ℝ E ℝ := by
      ext v
      simp [WithLp.prod_inner_apply]
    rw [hasGradientAt_iff_hasFDerivAt, h]
    exact (WithLp.sndL 2 ℝ E ℝ).hasFDerivAt
  have h1 : ‖(WithLp.toLp 2 ((0 : E), (1 : ℝ)) : P)‖ = 1 := by simp
  exact ((congrArg norm ((mgradient_eq_gradient _ _).trans hgrad)).trans
    norm_tangentSpace_vectorSpace).trans h1

/-- The hyperbolic Laplacian of the height function is `Δ t = (1 - dim E) t`. -/
theorem laplaceBeltrami_height (x : UpperHalfSpace E) :
    laplaceBeltrami J height x = (1 - Module.finrank ℝ E) * height x := by
  have hpos : ∀ y : UpperHalfSpace E, 0 < (height y ^ 2)⁻¹ :=
    fun y ↦ inv_pos.mpr (pow_pos (height_pos y) 2)
  have ht := height_pos x
  -- By definition the hyperbolic metric is the Euclidean metric rescaled by `t⁻²`.
  refine ((euclideanMetric (E := E)).laplaceBeltrami_rescale (show (1 : ℕ∞ω) ≤ ω from le_top)
    contMDiff_inv_height_sq hpos ((contMDiff_height x).of_le le_top)).trans ?_
  let _ : RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace J x) :=
    ⟨euclideanMetric.toRiemannianMetric⟩
  have hgrad : mgradient J (fun y : UpperHalfSpace E ↦ (height y ^ 2)⁻¹) x =
      (-2 / height x ^ 3) • mgradient J height x := by
    have hd : HasDerivAt (fun s : ℝ ↦ (s ^ 2)⁻¹) (-2 / height x ^ 3) (height x) := by
      convert ((hasDerivAt_pow 2 (height x)).inv (pow_ne_zero 2 ht.ne')) using 1
      field_simp
      ring
    exact mgradient_comp_hasDerivAt (f := height) hd
      ((contMDiff_height x).mdifferentiableAt (by simp))
  have hfin : (Module.finrank ℝ P : ℝ) = Module.finrank ℝ E + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq, Module.finrank_prod, Module.finrank_self]
    push_cast
    ring
  rw [laplaceBeltrami_height_euclidean, hgrad, inner_smul_left, real_inner_self_eq_norm_sq,
    norm_mgradient_height_euclidean, hfin, starRingEnd_apply, star_trivial]
  field_simp
  ring

/-- The hyperbolic Laplacian of a power of the height: `Δ t^β = β (β - dim E) t^β`. -/
theorem laplaceBeltrami_height_rpow (β : ℝ) (x : UpperHalfSpace E) :
    laplaceBeltrami J (fun y ↦ height y ^ β) x =
      β * (β - Module.finrank ℝ E) * height x ^ β := by
  have ht := height_pos x
  have hh : ContDiffOn ℝ 2 (fun s : ℝ ↦ s ^ β) (Set.Ioi 0) := fun s hs ↦
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hs)).contDiffWithinAt
  have h := laplaceBeltrami_comp (I := J) isOpen_Ioi hh (contMDiff_height.of_le le_top)
    (fun y ↦ height_pos y) x
  have hd : deriv (deriv fun s : ℝ ↦ s ^ β) (height x) =
      β * ((β - 1) * height x ^ (β - 1 - 1)) := by
    rw [Real.deriv_rpow_const', deriv_const_mul_field']
    exact congrArg (β * ·) (Real.deriv_rpow_const _ _)
  refine h.trans ?_
  rw [hd, Real.deriv_rpow_const, laplaceBeltrami_height, norm_mgradient_height,
    Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_one]
  field_simp
  ring

/-! ### The linearized curvature operator on powers of the height in the hyperbolic plane -/

section Plane

variable (hE : Module.finrank ℝ E = 1)
include hE

/-- In the hyperbolic plane, the operator `Δ⁺ + 2`, with `Δ⁺ = -Δ` the nonnegative Laplacian,
multiplies `t^β` by `(β + 1) (2 - β)`. -/
theorem neg_laplaceBeltrami_height_rpow_add_two_mul (β : ℝ) (x : UpperHalfSpace E) :
    -laplaceBeltrami J (fun y ↦ height y ^ β) x + 2 * height x ^ β =
      (β + 1) * (2 - β) * height x ^ β := by
  rw [laplaceBeltrami_height_rpow, hE, Nat.cast_one]
  ring

/-- **Indicial roots.** In the hyperbolic plane, `t^β` solves `(Δ⁺ + 2) t^β = 0` exactly when
`β = -1` or `β = 2`. -/
theorem neg_laplaceBeltrami_height_rpow_add_two_mul_eq_zero_iff (β : ℝ)
    (x : UpperHalfSpace E) :
    -laplaceBeltrami J (fun y ↦ height y ^ β) x + 2 * height x ^ β = 0 ↔ β = -1 ∨ β = 2 := by
  rw [neg_laplaceBeltrami_height_rpow_add_two_mul hE, mul_eq_zero, mul_eq_zero,
    or_iff_left (Real.rpow_pos_of_pos (height_pos x) β).ne', add_eq_zero_iff_eq_neg, sub_eq_zero,
    eq_comm (a := (2 : ℝ))]

/-- **Barriers between the indicial roots.** In the hyperbolic plane, `(Δ⁺ + 2) t^β > 0` for
`-1 < β < 2`. For `0 < δ < 1` this applies to both `t^δ` and `t^(-δ)`. -/
theorem neg_laplaceBeltrami_height_rpow_add_two_mul_pos {β : ℝ} (hβ : β ∈ Set.Ioo (-1) 2)
    (x : UpperHalfSpace E) :
    0 < -laplaceBeltrami J (fun y ↦ height y ^ β) x + 2 * height x ^ β := by
  rw [neg_laplaceBeltrami_height_rpow_add_two_mul hE]
  have h1 : 0 < β + 1 := by linarith [hβ.1]
  have h2 : 0 < 2 - β := by linarith [hβ.2]
  exact mul_pos (mul_pos h1 h2) (Real.rpow_pos_of_pos (height_pos x) β)

end Plane

end TauCeti.UpperHalfSpace
