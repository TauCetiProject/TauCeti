/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import TauCeti.Analysis.InnerProductSpace.Harmonic.RemovableSingularity
import TauCeti.Analysis.InnerProductSpace.Laplacian.Comp
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Euclidean.Inversion

/-!
# The Kelvin transform

Let `E` be a finite-dimensional real inner product space of dimension `n`, and write
`x* = inversion 0 1 x = x / ‖x‖²` for the inversion in the unit sphere. The **Kelvin transform**
of a function `f : E → F` is

`K[f](x) = ‖x‖ ^ (2 - n) f(x*)`

(`TauCeti.kelvinTransform`). Away from the origin it is an involution
(`TauCeti.kelvinTransform_kelvinTransform`), and it transforms the Laplacian by

`Δ K[f](x) = ‖x‖ ^ (-n - 2) Δf(x*)`

(`TauCeti.laplacian_kelvinTransform`). Hence `K[f]` is harmonic at `x ≠ 0` exactly when `f` is
harmonic at `x*` (`TauCeti.harmonicAt_kelvinTransform_iff`): the Kelvin transform exchanges
harmonic functions near infinity with harmonic functions on punctured neighbourhoods of the
origin.

The identity follows from the conformality of inversion, whose derivative at `x` is `‖x‖⁻²`
times the reflection in the hyperplane orthogonal to `x`. By the chain rule for a conformal change
of variables (`ContDiffAt.laplacian_fun_comp_of_fderiv_eq_smul`),
`Δ(f ∘ inversion)(x) = ‖x‖⁻⁴ Δf(x*) + Df(x*)(Δ inversion(x))`, where
`Δ inversion(x) = 2 (2 - n) ‖x‖⁻⁴ x` (`TauCeti.laplacian_inversion_zero_one`). The factor
`‖x‖ ^ (2 - n)` is harmonic, and in the Leibniz rule its gradient term cancels the first-order
term exactly.

In dimension `n ≥ 2`, a harmonic function `f` on an exterior region `‖x‖ > R` whose rescaling
`‖x‖ ^ (n - 2) f(x)` tends to `a` at infinity has a Kelvin transform tending to `a` at the origin
(`TauCeti.tendsto_kelvinTransform_nhdsNE_zero`), so by the removable singularity theorem
`K[f]`, with the value `a` at the origin, is harmonic on the whole ball `‖x‖ < R⁻¹`
(`TauCeti.harmonicOnNhd_update_kelvinTransform`). Away from the origin `K[f]` is positive wherever
`f` is positive at the inverted point (`TauCeti.kelvinTransform_pos`), so for `f > 0` and `a > 0`
the extension is positive on the ball (`TauCeti.update_kelvinTransform_pos`). This is the
analytic step in closing off a harmonically flat end of a Riemannian manifold, where the metric is
`u ^ (4 / (n - 2)) δ` with `u` harmonic and `u = a ‖x‖ ^ (2 - n) + o(‖x‖ ^ (2 - n))` at infinity:
inversion turns the end into a punctured ball, and the conformal factor becomes the Kelvin
transform of `u`, which extends across the puncture.

## Main declarations

* `TauCeti.kelvinTransform`: the Kelvin transform `K[f](x) = ‖x‖ ^ (2 - n) f(x / ‖x‖²)`.
* `TauCeti.kelvinTransform_kelvinTransform`: `K[K[f]] = f` away from the origin.
* `TauCeti.laplacian_inversion_zero_one`: the Laplacian of the inversion in the unit sphere.
* `TauCeti.laplacian_kelvinTransform`: `Δ K[f](x) = ‖x‖ ^ (-n - 2) Δf(x*)`.
* `TauCeti.harmonicAt_kelvinTransform_iff`, `InnerProductSpace.HarmonicOnNhd.kelvinTransform`:
  the Kelvin transform preserves harmonicity away from the origin.
* `TauCeti.tendsto_kelvinTransform_nhdsNE_zero`: the limit of `K[f]` at the origin is the limit of
  `‖x‖ ^ (n - 2) f(x)` at infinity.
* `TauCeti.harmonicOnNhd_update_kelvinTransform`: the Kelvin transform of a harmonic function on
  an exterior region with this limit extends harmonically across the origin.
* `TauCeti.update_kelvinTransform_pos`: for `f > 0` and `a > 0` this extension is positive.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137, 2001,
  Chapter 4 (the Kelvin transform).
-/

public section

namespace TauCeti

open EuclideanGeometry Filter InnerProductSpace Laplacian Metric Module Set Topology
open scoped Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **Kelvin transform** `K[f](x) = ‖x‖ ^ (2 - n) f(x / ‖x‖²)` of a function `f` on a real
inner product space of dimension `n`, where `x / ‖x‖² = inversion 0 1 x` is the inversion in the
unit sphere. Away from the origin it is an involution which preserves harmonicity. -/
noncomputable def kelvinTransform (f : E → F) (x : E) : F :=
  ‖x‖ ^ (2 - finrank ℝ E : ℝ) • f (inversion 0 1 x)

theorem kelvinTransform_apply (f : E → F) (x : E) :
    kelvinTransform f x = ‖x‖ ^ (2 - finrank ℝ E : ℝ) • f (inversion 0 1 x) :=
  (rfl)

@[simp]
theorem kelvinTransform_add (f g : E → F) :
    kelvinTransform (f + g) = kelvinTransform f + kelvinTransform g := by
  funext x
  simp [kelvinTransform_apply]

@[simp]
theorem kelvinTransform_smul (c : ℝ) (f : E → F) :
    kelvinTransform (c • f) = c • kelvinTransform f := by
  funext x
  simp [kelvinTransform_apply, smul_comm c]

/-- **The Kelvin transform is an involution** away from the origin. -/
theorem kelvinTransform_kelvinTransform (f : E → F) {x : E} (hx : x ≠ 0) :
    kelvinTransform (kelvinTransform f) x = f x := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  simp [kelvinTransform_apply, inversion_inversion _ one_ne_zero, smul_smul, Real.inv_rpow hx'.le,
    (Real.rpow_pos_of_pos hx' _).ne']

/-- A positive function has a positive Kelvin transform away from the origin. -/
theorem kelvinTransform_pos {f : E → ℝ} {x : E} (hx : x ≠ 0) (hf : 0 < f (inversion 0 1 x)) :
    0 < kelvinTransform f x := by
  rw [kelvinTransform_apply, smul_eq_mul]
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _) hf

/-- **The Kelvin transform at the origin.** If `‖x‖ ^ (n - 2) f(x)` tends to `a` at infinity, then
the Kelvin transform `K[f]` tends to `a` at the origin. -/
theorem tendsto_kelvinTransform_nhdsNE_zero {f : E → F} {a : F}
    (ha : Tendsto (fun x ↦ ‖x‖ ^ (finrank ℝ E - 2 : ℝ) • f x) (Bornology.cobounded E) (𝓝 a)) :
    Tendsto (kelvinTransform f) (𝓝[≠] 0) (𝓝 a) := by
  refine (ha.comp (tendsto_inversion_nhdsNE_center_cobounded one_ne_zero)).congr fun y ↦ ?_
  rw [Function.comp_apply, kelvinTransform_apply, norm_inversion_zero_one,
    Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _), neg_sub]

variable [FiniteDimensional ℝ E]

/-- **The Laplacian of the inversion in the unit sphere.** Away from the origin,
`Δ (x ↦ x / ‖x‖²) = 2 (2 - n) ‖x‖⁻⁴ x`, where `n` is the dimension. -/
theorem laplacian_inversion_zero_one {x : E} (hx : x ≠ 0) :
    Δ (inversion (0 : E) 1) x = (2 * (2 - finrank ℝ E) * ‖x‖ ^ (-4 : ℝ)) • x := by
  have hid : Δ (fun y : E ↦ y) x = 0 := by
    simpa [ContinuousLinearMap.coe_id', Function.id_def] using
      congrFun (ContinuousLinearMap.id ℝ E).laplacian x
  -- The inversion is `y ↦ ‖y‖ ^ (-2) y`, including at the origin, where both sides vanish.
  have hinv : inversion (0 : E) 1 = fun y ↦ ‖y‖ ^ (-2 : ℝ) • y := by
    funext y
    simp [inversion_def, Real.rpow_neg (norm_nonneg y)]
  rw [hinv, (contDiffAt_norm_rpow_of_ne _ hx).laplacian_fun_smul (g := fun y : E ↦ y)
    contDiffAt_id, hid, laplacian_norm_rpow_of_ne _ hx, gradient_norm_rpow_of_ne _ hx,
    fderiv_fun_id, ContinuousLinearMap.id_apply]
  match_scalars
  norm_num
  ring

/-- **The Laplacian of a Kelvin transform.** If `f` is twice differentiable at `x* = x / ‖x‖²`,
`x ≠ 0`, then `Δ K[f](x) = ‖x‖ ^ (-n - 2) Δf(x*)`, where `n` is the dimension. -/
theorem laplacian_kelvinTransform {f : E → F} {x : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f (inversion 0 1 x)) :
    Δ (kelvinTransform f) x = ‖x‖ ^ (-(finrank ℝ E : ℝ) - 2) • Δ f (inversion 0 1 x) := by
  set n : ℝ := (finrank ℝ E : ℝ)
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have ha : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ (2 - n)) x := contDiffAt_norm_rpow_of_ne _ hx
  have hι : ContDiffAt ℝ 2 (inversion (0 : E) 1) x := contDiffAt_inversion hx
  -- The derivative of the inversion is `‖x‖⁻²` times the reflection orthogonal to `x`.
  have hι' : fderiv ℝ (inversion (0 : E) 1) x =
      (‖x‖⁻¹ ^ 2) • ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E) := by
    simp [fderiv_inversion]
  have hDg : fderiv ℝ (fun y ↦ f (inversion 0 1 y)) x =
      (fderiv ℝ f (inversion 0 1 x)).comp (fderiv ℝ (inversion (0 : E) 1) x) :=
    fderiv_comp x (hf.differentiableAt (by norm_num)) (hι.differentiableAt (by norm_num))
  rw [show kelvinTransform f = fun y ↦ ‖y‖ ^ (2 - n) • f (inversion 0 1 y) from
      funext (kelvinTransform_apply f),
    ha.laplacian_fun_smul (g := fun y ↦ f (inversion 0 1 y)) (hf.comp x hι),
    hf.laplacian_fun_comp_of_fderiv_eq_smul hι hι', hDg,
    gradient_norm_rpow_of_ne _ hx, laplacian_norm_rpow_of_ne _ hx, laplacian_inversion_zero_one hx,
    hι']
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg, map_neg, smul_neg]
  -- Express every power of `‖x‖` through `‖x‖ ^ (-n)` and natural powers.
  have h2 : ‖x‖ ^ (2 - n - 2) = ‖x‖ ^ (-n) := by ring_nf
  have h4 : ‖x‖ ^ (-n - 2) = ‖x‖ ^ (-n) * (‖x‖ ^ 2)⁻¹ := by
    rw [Real.rpow_sub hr, Real.rpow_two, div_eq_mul_inv]
  have h1 : ‖x‖ ^ (2 - n) = ‖x‖ ^ 2 * ‖x‖ ^ (-n) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_two]
  have h3 : ‖x‖ ^ (-4 : ℝ) = (‖x‖ ^ 4)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_cast
  rw [h2, h4, h1, h3]
  match_scalars <;> field_simp <;> ring

/-- **The Kelvin transform preserves harmonicity.** If `f` is harmonic at `x* = x / ‖x‖²`, with
`x ≠ 0`, then its Kelvin transform is harmonic at `x`. -/
theorem _root_.InnerProductSpace.HarmonicAt.kelvinTransform {f : E → F} {x : E}
    (hf : HarmonicAt f (inversion 0 1 x)) (hx : x ≠ 0) : HarmonicAt (kelvinTransform f) x := by
  have hι : ContDiffAt ℝ 2 (inversion (0 : E) 1) x := contDiffAt_inversion hx
  refine ⟨(contDiffAt_norm_rpow_of_ne _ hx).smul (hf.1.comp x hι), ?_⟩
  filter_upwards [eventually_ne_nhds hx, hι.continuousAt.tendsto.eventually hf.eventually]
    with y hy hfy
  rw [laplacian_kelvinTransform hy hfy.1, hfy.2.self_of_nhds, Pi.zero_apply, smul_zero,
    Pi.zero_apply]

/-- Away from the origin, the Kelvin transform `K[f]` is harmonic at `x` if and only if `f` is
harmonic at `x* = x / ‖x‖²`. -/
theorem harmonicAt_kelvinTransform_iff {f : E → F} {x : E} (hx : x ≠ 0) :
    HarmonicAt (kelvinTransform f) x ↔ HarmonicAt f (inversion 0 1 x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.kelvinTransform hx⟩
  have hx' : inversion (0 : E) 1 x ≠ 0 := (inversion_eq_center one_ne_zero).not.2 hx
  rw [← inversion_inversion (0 : E) one_ne_zero x] at h
  refine (harmonicAt_congr_nhds ?_).1 (h.kelvinTransform hx')
  filter_upwards [eventually_ne_nhds hx'] with y hy using kelvinTransform_kelvinTransform f hy

/-- The Kelvin transform of a function harmonic on `s` is harmonic on the inverse image of `s`
under the inversion `x ↦ x / ‖x‖²`, with the origin removed. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.kelvinTransform {f : E → F} {s : Set E}
    (hf : HarmonicOnNhd f s) :
    HarmonicOnNhd (kelvinTransform f) (inversion (0 : E) 1 ⁻¹' s \ {0}) :=
  fun _ hx ↦ (hf _ hx.1).kelvinTransform hx.2

/-- **Closing off a harmonic end.** In dimension `n ≥ 2`, let `f` be harmonic on the exterior
region `‖x‖ > R`, with `‖x‖ ^ (n - 2) f(x) → a` at infinity. Then the Kelvin transform of `f`,
with the value `a` at the origin, is harmonic on the ball `‖x‖ < R⁻¹`. -/
theorem harmonicOnNhd_update_kelvinTransform [DecidableEq E] (hn : 2 ≤ finrank ℝ E) {f : E → ℝ}
    {R a : ℝ} (hf : HarmonicOnNhd f {x | R < ‖x‖})
    (ha : Tendsto (fun x ↦ ‖x‖ ^ (finrank ℝ E - 2 : ℝ) * f x) (Bornology.cobounded E) (𝓝 a)) :
    HarmonicOnNhd (Function.update (kelvinTransform f) 0 a) (ball 0 R⁻¹) := by
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 (inv_nonpos.2 hR)]
    exact fun _ h ↦ h.elim
  refine harmonicOnNhd_update_of_tendsto hn (ball_mem_nhds 0 (inv_pos.2 hR)) (fun y hy ↦ ?_)
    (tendsto_kelvinTransform_nhdsNE_zero (by simpa only [smul_eq_mul] using ha))
  have hy0 : y ≠ 0 := hy.2
  refine (hf _ ?_).kelvinTransform hy0
  simpa only [mem_ofPred_eq, inv_inv] using
    (inv_lt_norm_inversion_iff (inv_pos.2 hR) hy0).2 (mem_ball_zero_iff.1 hy.1)

omit [FiniteDimensional ℝ E] in
/-- **Positivity of the closed-off end.** If `f` is positive on the exterior region `‖x‖ > R` and
`a > 0`, then the Kelvin transform of `f`, with the value `a` at the origin, is positive on the
ball `‖x‖ < R⁻¹`. -/
theorem update_kelvinTransform_pos [DecidableEq E] {f : E → ℝ} {R a : ℝ}
    (hf : ∀ x, R < ‖x‖ → 0 < f x) (ha : 0 < a) {y : E} (hy : y ∈ ball (0 : E) R⁻¹) :
    0 < Function.update (kelvinTransform f) 0 a y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa
  have hR : 0 < R := inv_pos.1 (pos_of_mem_ball hy)
  rw [Function.update_of_ne hy0]
  refine kelvinTransform_pos hy0 (hf _ ?_)
  simpa only [inv_inv] using
    (inv_lt_norm_inversion_iff (inv_pos.2 hR) hy0).2 (mem_ball_zero_iff.1 hy)

end TauCeti
