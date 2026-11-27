/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.LinearAlgebra.Determinant.RankOne

/-!
# Radial rescalings of a real inner product space

For a *radial profile* `b : ℝ → ℝ`, the radial rescaling `TauCeti.radialRescale b` of a real
normed space `E` is `ρ x = b ‖x‖ • x`: it moves each point along its ray from the origin,
to `b r` times its position at radius `r = ‖x‖`. Only the values of `b` on `[0, ∞)` matter.
The support conditions, the derivative at the origin and non-injectivity hold in any real normed
space; the derivative away from the origin, smoothness and the Jacobian use an inner product.

Away from the origin, at a radius where `b` is differentiable, the derivative of `ρ` is
`b r • id + (b' r / r) • ⟪x, ·⟫ x`: multiplication by `b r` on the orthogonal complement of `x` and
by `b r + r b' r` along `x`. Its Jacobian determinant is therefore

`det (Dρ x) = b r ^ (n - 1) * (b r + r * b' r)`,  `n = dim E`

(`TauCeti.det_fderiv_radialRescale`); in the plane, `ℂ` or `ℝ²`, this is `b r (b r + r b' r)`.
When `b` vanishes near `0` and is smooth on `(0, ∞)`, the map `ρ` is smooth, including at the
origin, where it vanishes identically nearby. When moreover `b` is nondecreasing on `(0, ∞)`, it is
nonnegative there and the Jacobian is nonnegative everywhere
(`TauCeti.det_fderiv_radialRescale_nonneg`).

With a profile vanishing on `[0, δ]` and equal to `1` on `[R, ∞)`, the rescaling collapses the
closed ball of radius `δ` to the origin, is the identity off the open ball of radius `R`, maps
every ball about the origin into itself, and has nonnegative Jacobian
(`TauCeti.exists_radialRescale`). Such a map is not injective, so a nonnegative Jacobian does not
make it a diffeomorphism (`TauCeti.not_injective_radialRescale`). In a disc coordinate centred at
a point of a surface, it collapses a small disc to the point without leaving a larger disc and
without reversing orientation anywhere. This is the radial modification in the proof of the
recognition theorem for symplectic manifolds that are standard at infinity, which straightens a
diffeomorphism of `S² × S²` on neighbourhoods of the two cap spheres while keeping both coordinate
planes positive for the pulled-back symplectic form.

## Main declarations

* `TauCeti.radialRescale`: the radial rescaling `x ↦ b ‖x‖ • x`.
* `TauCeti.hasFDerivAt_radialRescale`, `TauCeti.hasFDerivAt_radialRescale_zero`: its derivative
  away from and at the origin.
* `TauCeti.contDiff_radialRescale`: smoothness for a profile smooth on `(0, ∞)` and vanishing near
  `0`.
* `TauCeti.det_fderiv_radialRescale`: the Jacobian `b r ^ (n - 1) * (b r + r * b' r)`.
* `TauCeti.det_fderiv_radialRescale_nonneg`: the Jacobian is nonnegative for a nondecreasing
  profile vanishing near `0`.
* `TauCeti.exists_radialRescale`: a smooth radial rescaling collapsing a closed ball, fixing the
  complement of a larger ball, preserving balls about the origin, with nonnegative Jacobian.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  American Mathematical Society Colloquium Publications **52** (2012), the proof of
  Theorem 9.4.7 (the radial cutoff `ρ(ζ) = b(|ζ|) ζ` in a disc coordinate).
-/

public section

open Set Metric Filter Module
open scoped Topology ContDiff

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : ℝ → ℝ} {x : E}

/-- The radial rescaling `x ↦ b ‖x‖ • x` of a real normed space with radial profile
`b : ℝ → ℝ`. Only the values of `b` on `[0, ∞)` matter. -/
noncomputable def radialRescale (b : ℝ → ℝ) (x : E) : E := b ‖x‖ • x

theorem radialRescale_apply (b : ℝ → ℝ) (x : E) : radialRescale b x = b ‖x‖ • x := (rfl)

@[simp]
theorem radialRescale_zero (b : ℝ → ℝ) : radialRescale b (0 : E) = 0 := by
  simp [radialRescale_apply]

theorem norm_radialRescale (b : ℝ → ℝ) (x : E) : ‖radialRescale b x‖ = |b ‖x‖| * ‖x‖ := by
  rw [radialRescale_apply, norm_smul, Real.norm_eq_abs]

theorem radialRescale_of_eq_zero (h : b ‖x‖ = 0) : radialRescale b x = 0 := by
  simp [radialRescale_apply, h]

theorem radialRescale_of_eq_one (h : b ‖x‖ = 1) : radialRescale b x = x := by
  simp [radialRescale_apply, h]

/-- A profile vanishing on `[0, δ]` collapses the closed ball of radius `δ` to the origin. -/
theorem eqOn_radialRescale_closedBall {δ : ℝ} (h : ∀ r ∈ Icc 0 δ, b r = 0) :
    EqOn (radialRescale b) 0 (closedBall (0 : E) δ) := fun x hx =>
  radialRescale_of_eq_zero (h _ ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩)

/-- A profile equal to `1` on `[R, ∞)` gives the identity outside the open ball of radius `R`. -/
theorem eqOn_radialRescale_compl_ball {R : ℝ} (h : ∀ r, R ≤ r → b r = 1) :
    EqOn (radialRescale b) id (ball (0 : E) R)ᶜ := fun x hx =>
  radialRescale_of_eq_one (h _ (by simpa using hx))

/-- A radial rescaling does not increase the norm of `x` when `|b ‖x‖| ≤ 1`. -/
theorem norm_radialRescale_le (h : |b ‖x‖| ≤ 1) : ‖radialRescale b x‖ ≤ ‖x‖ := by
  rw [norm_radialRescale]
  exact mul_le_of_le_one_left (norm_nonneg x) h

/-- A profile with `|b| ≤ 1` on `[0, ∞)` maps every open ball about the origin into itself. -/
theorem mapsTo_radialRescale_ball (h : ∀ r, 0 ≤ r → |b r| ≤ 1) (R : ℝ) :
    MapsTo (radialRescale b) (ball (0 : E) R) (ball 0 R) := fun x hx => by
  rw [mem_ball_zero_iff] at hx ⊢
  exact (norm_radialRescale_le (h _ (norm_nonneg x))).trans_lt hx

/-- A profile with `|b| ≤ 1` on `[0, ∞)` maps every closed ball about the origin into itself. -/
theorem mapsTo_radialRescale_closedBall (h : ∀ r, 0 ≤ r → |b r| ≤ 1) (R : ℝ) :
    MapsTo (radialRescale b) (closedBall (0 : E) R) (closedBall 0 R) := fun x hx => by
  rw [mem_closedBall_zero_iff] at hx ⊢
  exact (norm_radialRescale_le (h _ (norm_nonneg x))).trans hx

/-- A radial rescaling whose profile vanishes at a positive radius `δ` is not injective on a
nontrivial space, whatever the sign of its Jacobian: it sends the sphere of radius `δ` and the
origin to the origin. -/
theorem not_injective_radialRescale [Nontrivial E] {δ : ℝ} (hδ : 0 < δ) (h : b δ = 0) :
    ¬Function.Injective (radialRescale (E := E) b) := by
  obtain ⟨v, hv⟩ := exists_norm_eq E hδ.le
  have hv0 : v ≠ 0 := norm_pos_iff.1 (hv ▸ hδ)
  intro hinj
  refine hv0 (hinj ?_)
  rw [radialRescale_zero, radialRescale_of_eq_zero (hv ▸ h)]

/-- At the origin, the derivative of `x ↦ b ‖x‖ • x` is multiplication by `b 0`, as soon as `b` is
right-continuous at `0`. -/
theorem hasFDerivAt_radialRescale_zero (hb : ContinuousWithinAt b (Ici 0) 0) :
    HasFDerivAt (radialRescale b) (b 0 • ContinuousLinearMap.id ℝ E) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have ht : Tendsto (fun h : E => b ‖h‖ - b 0) (𝓝 0) (𝓝 0) := by
    simpa using (hb.tendsto.comp (by simpa using tendsto_norm_sub_self_nhdsGE (0 : E))).sub_const
      (b 0)
  refine (((Asymptotics.isLittleO_one_iff ℝ).2 ht).smul_isBigO
    (Asymptotics.isBigO_refl id (𝓝 (0 : E)))).congr (fun h => ?_) fun h => ?_
  · simp [radialRescale_apply, sub_smul]
  · simp

/-- A profile vanishing near `0` (on the right) gives a rescaling vanishing near the origin. -/
theorem radialRescale_eventuallyEq_zero (h0 : b =ᶠ[𝓝[≥] 0] 0) :
    radialRescale b =ᶠ[𝓝 (0 : E)] 0 := by
  have : Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝[≥] 0) := by
    simpa using tendsto_norm_sub_self_nhdsGE (0 : E)
  filter_upwards [this.eventually h0] with y hy
  exact radialRescale_of_eq_zero hy

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {b : ℝ → ℝ} {x : E}

/-- Away from the origin, the derivative of `x ↦ b ‖x‖ • x` is
`b ‖x‖ • id + (b' / ‖x‖) • ⟪x, ·⟫ x`, where `b'` is the derivative of `b` at `‖x‖`. -/
theorem hasFDerivAt_radialRescale {b' : ℝ} (hx : x ≠ 0) (hb : HasDerivAt b b' ‖x‖) :
    HasFDerivAt (radialRescale b)
      (b ‖x‖ • ContinuousLinearMap.id ℝ E + ((b' / ‖x‖) • innerSL ℝ x).smulRight x) x := by
  have h := (hb.comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx)).smul (hasFDerivAt_id x)
  rw [smul_smul, ← div_eq_mul_inv] at h
  exact h

/-- Away from the origin, the radial rescaling is `C^n` wherever its profile is. -/
theorem contDiffAt_radialRescale {n : WithTop ℕ∞} (hx : x ≠ 0) (hb : ContDiffAt ℝ n b ‖x‖) :
    ContDiffAt ℝ n (radialRescale b) x :=
  (hb.comp x (contDiffAt_norm ℝ hx)).smul contDiffAt_id

/-- A profile that is `C^n` on `(0, ∞)` and vanishes near `0` gives a `C^n` radial rescaling. -/
theorem contDiff_radialRescale {n : WithTop ℕ∞} (hb : ContDiffOn ℝ n b (Ioi 0))
    (h0 : b =ᶠ[𝓝[≥] 0] 0) : ContDiff ℝ n (radialRescale (E := E) b) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact contDiffAt_const.congr_of_eventuallyEq (radialRescale_eventuallyEq_zero h0)
  · exact contDiffAt_radialRescale hx (hb.contDiffAt (Ioi_mem_nhds (norm_pos_iff.2 hx)))

/-- The Jacobian determinant of `x ↦ b ‖x‖ • x` away from the origin is
`b r ^ (n - 1) * (b r + r * b')`, for `r = ‖x‖`, `n = dim E` and `b'` the derivative of `b` at `r`.
In the plane it is `b r * (b r + r * b')`. -/
theorem det_fderiv_radialRescale [FiniteDimensional ℝ E] {b' : ℝ} (hx : x ≠ 0)
    (hb : HasDerivAt b b' ‖x‖) :
    (fderiv ℝ (radialRescale b) x).det = b ‖x‖ ^ (finrank ℝ E - 1) * (b ‖x‖ + ‖x‖ * b') := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hcoe : ((b ‖x‖ • ContinuousLinearMap.id ℝ E + ((b' / ‖x‖) • innerSL ℝ x).smulRight x :
      E →L[ℝ] E) : E →ₗ[ℝ] E) =
      b ‖x‖ • 1 + (((b' / ‖x‖) • innerSL ℝ x : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ).smulRight x := by
    ext y
    simp
  rw [(hasFDerivAt_radialRescale hx hb).fderiv, ContinuousLinearMap.det, hcoe,
    LinearMap.det_smul_one_add_smulRight finrank_pos]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  congr 2
  simp only [ContinuousLinearMap.coe_coe, FunLike.coe_smul, Pi.smul_apply,
    innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul]
  field_simp

/-- For a profile differentiable and nondecreasing on `(0, ∞)` and vanishing near `0`, the radial
rescaling has nonnegative Jacobian determinant everywhere. -/
theorem det_fderiv_radialRescale_nonneg [FiniteDimensional ℝ E]
    (hb : DifferentiableOn ℝ b (Ioi 0)) (h0 : b =ᶠ[𝓝[≥] 0] 0) (hmono : MonotoneOn b (Ioi 0))
    (x : E) : 0 ≤ (fderiv ℝ (radialRescale b) x).det := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [(radialRescale_eventuallyEq_zero h0).fderiv_eq, fderiv_zero, Pi.zero_apply,
      ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
    positivity
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hd : HasDerivAt b (deriv b ‖x‖) ‖x‖ :=
    ((hb ‖x‖ hr).differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  have hb' : 0 ≤ deriv b ‖x‖ := by
    rw [← derivWithin_of_isOpen isOpen_Ioi (mem_Ioi.mpr hr)]
    exact hmono.derivWithin_nonneg
  -- `b` vanishes at some radius in `(0, ‖x‖)`, so monotonicity gives `0 ≤ b ‖x‖`.
  have hbx : 0 ≤ b ‖x‖ := by
    obtain ⟨s, hs0, hs⟩ := ((h0.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)).and
      (Ioo_mem_nhdsGT hr)).exists
    have h := hmono hs.1 hr hs.2.le
    rwa [hs0, Pi.zero_apply] at h
  rw [det_fderiv_radialRescale hx hd]
  positivity

/-- For radii `0 < δ < R` there is a smooth radial rescaling of a finite-dimensional real inner
product space that collapses the closed ball of radius `δ` to the origin, is the identity outside
the open ball of radius `R`, maps every open ball about the origin into itself, and has nonnegative
Jacobian determinant everywhere. Its profile is `r ↦ smoothTransition ((r - δ) / (R - δ))`. -/
theorem exists_radialRescale [FiniteDimensional ℝ E] {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ (radialRescale (E := E) b) ∧
      EqOn (radialRescale b) 0 (closedBall (0 : E) δ) ∧
      EqOn (radialRescale b) id (ball (0 : E) R)ᶜ ∧
      (∀ r, MapsTo (radialRescale b) (ball (0 : E) r) (ball 0 r)) ∧
      ∀ x : E, 0 ≤ (fderiv ℝ (radialRescale b) x).det := by
  have hRδ : 0 < R - δ := sub_pos.2 hδR
  let b : ℝ → ℝ := fun r => Real.smoothTransition ((r - δ) / (R - δ))
  have hb : ContDiff ℝ ∞ b :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hzero : ∀ r ≤ δ, b r = 0 := fun r hr =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hRδ.le)
  have h0 : b =ᶠ[𝓝[≥] 0] 0 :=
    mem_nhdsWithin_of_mem_nhds <| mem_of_superset (Iio_mem_nhds hδ) fun r hr => hzero r hr.le
  have hmono : Monotone b := Real.smoothTransition.monotone.comp fun r s hrs =>
    div_le_div_of_nonneg_right (by linarith) hRδ.le
  have hone : ∀ r, R ≤ r → b r = 1 := fun r hr =>
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hRδ).2 (by linarith))
  have habs : ∀ r, 0 ≤ r → |b r| ≤ 1 := fun r _ =>
    abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg ((r - δ) / (R - δ))],
      Real.smoothTransition.le_one _⟩
  exact ⟨b, contDiff_radialRescale hb.contDiffOn h0,
    eqOn_radialRescale_closedBall fun r hr => hzero r hr.2, eqOn_radialRescale_compl_ball hone,
    mapsTo_radialRescale_ball habs,
    det_fderiv_radialRescale_nonneg (hb.differentiable (by simp)).differentiableOn h0
      (hmono.monotoneOn _)⟩

end InnerProductSpace

end TauCeti
