/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# The Siegel domain and the Cayley transform of the ball

For a complex normed space `E`, the *Siegel domain* is the open set
`𝔖 = {(u, v) ∈ E × ℂ | ρ(u, v) > 0}` cut out by the height function `ρ(u, v) = Im v - ‖u‖²`.
The *Cayley transform*

`C(w', wₙ) = ((1 - wₙ)⁻¹ • w', i (1 + wₙ) / (1 - wₙ))`

is an analytic isomorphism from `{wₙ ≠ 1}` onto `{v ≠ -i}`, with inverse
`C⁻¹(u, v) = ((2 i / (v + i)) • u, (v - i) / (v + i))`. Here points `w = (w', wₙ)` of the source
live in `WithLp 2 (E × ℂ)`, whose norm is `‖w‖² = ‖w'‖² + ‖wₙ‖²`. The key identity is

`ρ(C(w)) = (1 - ‖w‖²) / ‖1 - wₙ‖²`,

so `C` maps the open unit ball onto `𝔖`, the unit sphere minus the point `b₀ = (0, 1)` onto the
boundary `{ρ = 0}`, and the closed ball minus `b₀` onto the closure `{ρ ≥ 0}`; the point `b₀` goes
to infinity. For finite-dimensional `E`, sending `b₀` to `∞` extends `C` to a homeomorphism from
the closed unit ball onto the closure of `𝔖` in the one-point compactification of `E × ℂ`.

For `E = ℂⁿ⁻¹` with its Euclidean norm, `WithLp 2 (E × ℂ)` is `ℂⁿ` and the open unit ball is the
bounded model of complex hyperbolic `n`-space; the Siegel domain is its unbounded model, in which
the stabiliser of the boundary point `b₀` acts by affine maps: the Heisenberg translations,
which preserve `ρ`, and the dilations `(u, v) ↦ (s u, s² v)`, which multiply it by `s²`. For
`E = 0` the transform is the classical map `w ↦ i (1 + w) / (1 - w)` from the unit disc onto the
upper half-plane.

## Main definitions

* `TauCeti.siegelHeight`: the height function `ρ(u, v) = Im v - ‖u‖²`.
* `TauCeti.siegelDomain E`: the Siegel domain `{ρ > 0}` in `E × ℂ`.
* `TauCeti.siegelCayley`: the Cayley transform, as an open partial homeomorphism from
  `WithLp 2 (E × ℂ)` to `E × ℂ` with source `{wₙ ≠ 1}` and target `{v ≠ -i}`.
* `TauCeti.ballHomeomorphSiegelDomain`: its restriction, a homeomorphism from the open unit ball
  onto the Siegel domain.
* `TauCeti.siegelCayleyOnePoint`: the Cayley transform with values in the one-point
  compactification `OnePoint (E × ℂ)`, sending `b₀` to `∞`.
* `TauCeti.closedBallHomeomorphClosureSiegelDomain`: for finite-dimensional `E`, its restriction,
  a homeomorphism from the closed unit ball onto the closure of the Siegel domain in
  `OnePoint (E × ℂ)`.

## Main results

* `TauCeti.siegelHeight_siegelCayley`: `ρ(C(w)) = (1 - ‖w‖²) / ‖1 - wₙ‖²`.
* `TauCeti.one_sub_norm_sq_siegelCayley_symm`: `1 - ‖C⁻¹(p)‖² = 4 ρ(p) / ‖v + i‖²`.
* `TauCeti.siegelCayley_image_ball`, `TauCeti.siegelCayley_image_sphere_diff` and
  `TauCeti.siegelCayley_image_closedBall_diff`: the images of the open ball, of the sphere minus
  `b₀` and of the closed ball minus `b₀`.
* `TauCeti.closure_siegelDomain` and `TauCeti.frontier_siegelDomain`: the closure `{ρ ≥ 0}` and
  the boundary `{ρ = 0}` of the Siegel domain.
* `TauCeti.analyticOnNhd_siegelCayley` and `TauCeti.analyticOnNhd_siegelCayley_symm`: the
  transform and its inverse are analytic, so `C` is a biholomorphism from the ball onto `𝔖`.
* `TauCeti.tendsto_siegelCayley_nhdsWithin_source` and
  `TauCeti.tendsto_siegelCayley_symm_cobounded`: `C` sends `b₀` to infinity, and `C⁻¹` sends
  infinity in `{ρ ≥ 0}` to `b₀`.
* `TauCeti.continuousOn_siegelCayleyOnePoint`, `TauCeti.injOn_siegelCayleyOnePoint` and
  `TauCeti.siegelCayleyOnePoint_image_closedBall`: the extension to the closed ball is continuous
  and injective, with image the closure of the Siegel domain when `E` is finite-dimensional.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford University Press, 1999.
* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. (2) 197 (2023), §2.
* N. Mok, *Projective algebraicity of minimal compactifications of complex-hyperbolic space forms
  of finite volume*, in *Perspectives in Analysis, Geometry, and Topology*, Progr. Math. 296,
  Birkhäuser, 2012.
-/

public section

open Complex Filter Metric Set Topology WithLp
open scoped OnePoint

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-! ### The Siegel domain -/

/-- The height function `ρ(u, v) = Im v - ‖u‖²` of the Siegel domain. -/
def siegelHeight (p : E × ℂ) : ℝ := p.2.im - ‖p.1‖ ^ 2

@[simp]
theorem siegelHeight_mk (u : E) (v : ℂ) : siegelHeight (u, v) = v.im - ‖u‖ ^ 2 := (rfl)

theorem siegelHeight_def (p : E × ℂ) : siegelHeight p = p.2.im - ‖p.1‖ ^ 2 := (rfl)

@[fun_prop]
theorem continuous_siegelHeight : Continuous (siegelHeight : E × ℂ → ℝ) :=
  (continuous_im.comp continuous_snd).sub (continuous_fst.norm.pow 2)

variable (E) in
/-- The Siegel domain `{(u, v) ∈ E × ℂ | Im v > ‖u‖²}`, the unbounded model of the unit ball of
`WithLp 2 (E × ℂ)`. -/
def siegelDomain : Set (E × ℂ) := {p | 0 < siegelHeight p}

@[simp]
theorem mem_siegelDomain {p : E × ℂ} : p ∈ siegelDomain E ↔ 0 < siegelHeight p := Iff.rfl

theorem isOpen_siegelDomain : IsOpen (siegelDomain E) :=
  isOpen_lt continuous_const continuous_siegelHeight

/-- Moving up vertically raises the height: `ρ(u, v + i t) = ρ(u, v) + t`. -/
theorem siegelHeight_add_I_mul (p : E × ℂ) (t : ℝ) :
    siegelHeight (p + (0, I * t)) = siegelHeight p + t := by
  simp only [siegelHeight_def, Prod.fst_add, Prod.snd_add, add_zero, add_im, mul_im, I_re,
    ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
  ring

/-- The closure of the Siegel domain is `{ρ ≥ 0}`. -/
theorem closure_siegelDomain : closure (siegelDomain E) = {p | 0 ≤ siegelHeight p} := by
  refine subset_antisymm (closure_minimal (fun p (hp : 0 < siegelHeight p) ↦ hp.le)
    (isClosed_le continuous_const continuous_siegelHeight)) fun p hp ↦ ?_
  -- `p` is the limit of `p + (0, i t)` as `t → 0⁺`, which lie in the domain.
  have hlim : Tendsto (fun t : ℝ ↦ p + (0, I * t)) (𝓝 0) (𝓝 p) := by
    have : Continuous fun t : ℝ ↦ p + (0, I * t) := by fun_prop
    simpa [Prod.mk_zero_zero] using this.tendsto 0
  replace hlim := hlim.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
  simp only [mem_siegelDomain, siegelHeight_add_I_mul]
  exact add_pos_of_nonneg_of_pos hp ht

private theorem setOf_siegelHeight_nonneg_sdiff_siegelDomain :
    {p : E × ℂ | 0 ≤ siegelHeight p} \ siegelDomain E = {p | siegelHeight p = 0} := by
  ext p
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_siegelDomain, not_lt]
  exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ⟨h.ge, h.le⟩⟩

/-- The boundary of the Siegel domain is `{ρ = 0}`. -/
theorem frontier_siegelDomain : frontier (siegelDomain E) = {p | siegelHeight p = 0} := by
  rw [frontier, closure_siegelDomain, isOpen_siegelDomain.interior_eq,
    setOf_siegelHeight_nonneg_sdiff_siegelDomain]

/-! ### The Cayley transform -/

variable [NormedSpace ℂ E]

/-- The denominator `v + i` of the inverse transform at `v = i (1 + a) / (1 - a)`. -/
private theorem I_mul_one_add_div_one_sub_add_I {a : ℂ} (ha : a ≠ 1) :
    I * (1 + a) / (1 - a) + I = 2 * I / (1 - a) := by
  have : 1 - a ≠ 0 := sub_ne_zero.mpr ha.symm
  field_simp
  ring

/-- The denominator `1 - a` of the transform at `a = (v - i) / (v + i)`. -/
private theorem one_sub_sub_I_div_add_I {v : ℂ} (hv : v ≠ -I) :
    1 - (v - I) / (v + I) = 2 * I / (v + I) := by
  have : v + I ≠ 0 := by rwa [ne_eq, add_eq_zero_iff_eq_neg]
  field_simp
  ring

private theorem two_mul_I_ne_zero : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero

private theorem analyticAt_siegelCayley_toFun {w : WithLp 2 (E × ℂ)} (hw : w.snd ≠ 1) :
    AnalyticAt ℂ (fun w : WithLp 2 (E × ℂ) ↦
      ((1 - w.snd)⁻¹ • w.fst, I * (1 + w.snd) / (1 - w.snd))) w := by
  have hs : AnalyticAt ℂ (fun w : WithLp 2 (E × ℂ) ↦ w.snd) w := (sndL 2 ℂ E ℂ).analyticAt w
  have hf : AnalyticAt ℂ (fun w : WithLp 2 (E × ℂ) ↦ w.fst) w := (fstL 2 ℂ E ℂ).analyticAt w
  have h1 : 1 - w.snd ≠ 0 := sub_ne_zero.mpr hw.symm
  exact (((analyticAt_const.sub hs).inv h1).smul hf).prod
    ((analyticAt_const.mul (analyticAt_const.add hs)).div (analyticAt_const.sub hs) h1)

private theorem analyticAt_siegelCayley_invFun {p : E × ℂ} (hp : p.2 ≠ -I) :
    AnalyticAt ℂ (fun p : E × ℂ ↦
      toLp 2 ((2 * I / (p.2 + I)) • p.1, (p.2 - I) / (p.2 + I))) p := by
  have hs : AnalyticAt ℂ (fun p : E × ℂ ↦ p.2) p := analyticAt_snd
  have hf : AnalyticAt ℂ (fun p : E × ℂ ↦ p.1) p := analyticAt_fst
  have h1 : p.2 + I ≠ 0 := by rwa [ne_eq, add_eq_zero_iff_eq_neg]
  exact (prodContinuousLinearEquiv 2 ℂ E ℂ).symm.analyticAt _ |>.comp
    (((analyticAt_const.div (hs.add analyticAt_const) h1).smul hf).prod
      ((hs.sub analyticAt_const).div (hs.add analyticAt_const) h1))

/-- The Cayley transform `C(w', wₙ) = ((1 - wₙ)⁻¹ • w', i (1 + wₙ) / (1 - wₙ))` from
`WithLp 2 (E × ℂ)` to `E × ℂ`, as an open partial homeomorphism from `{wₙ ≠ 1}` onto
`{v ≠ -i}`, with inverse `C⁻¹(u, v) = ((2 i / (v + i)) • u, (v - i) / (v + i))`. It maps the open
unit ball onto the Siegel domain (`TauCeti.siegelCayley_image_ball`). -/
noncomputable def siegelCayley : OpenPartialHomeomorph (WithLp 2 (E × ℂ)) (E × ℂ) where
  toFun w := ((1 - w.snd)⁻¹ • w.fst, I * (1 + w.snd) / (1 - w.snd))
  invFun p := toLp 2 ((2 * I / (p.2 + I)) • p.1, (p.2 - I) / (p.2 + I))
  source := {w | w.snd ≠ 1}
  target := {p | p.2 ≠ -I}
  map_source' w hw := by
    have h1 : 1 - w.snd ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    rw [mem_ofPred_eq, ne_eq, ← add_eq_zero_iff_eq_neg, I_mul_one_add_div_one_sub_add_I hw]
    exact div_ne_zero two_mul_I_ne_zero h1
  map_target' p hp := by
    simp only [mem_ofPred_eq, toLp_snd]
    rw [ne_comm, ← sub_ne_zero, one_sub_sub_I_div_add_I hp]
    exact div_ne_zero two_mul_I_ne_zero (by rwa [ne_eq, add_eq_zero_iff_eq_neg])
  left_inv' w hw := by
    have h1 : 1 - w.snd ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    have hden := I_mul_one_add_div_one_sub_add_I hw
    refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_)
    · simp only [ofLp_fst, hden, smul_smul]
      rw [show 2 * I / (2 * I / (1 - w.snd)) * (1 - w.snd)⁻¹ = 1 by field_simp, one_smul]
    · simp only [ofLp_snd, hden]
      field_simp
      ring
  right_inv' p hp := by
    have h1 : p.2 + I ≠ 0 := by rwa [ne_eq, add_eq_zero_iff_eq_neg]
    refine Prod.ext ?_ ?_
    · simp only [toLp_fst, toLp_snd, one_sub_sub_I_div_add_I hp, smul_smul]
      rw [inv_mul_cancel₀ (div_ne_zero two_mul_I_ne_zero h1), one_smul]
    · exact I_mul_one_add_sub_I_div_add_I_div_one_sub h1
  open_source := isOpen_ne_fun (WithLp.continuous_snd 2 E ℂ) continuous_const
  open_target := isOpen_ne_fun continuous_snd continuous_const
  continuousOn_toFun := fun _ hw ↦
    (analyticAt_siegelCayley_toFun hw).continuousAt.continuousWithinAt
  continuousOn_invFun := fun _ hp ↦
    (analyticAt_siegelCayley_invFun hp).continuousAt.continuousWithinAt

theorem siegelCayley_apply (w : WithLp 2 (E × ℂ)) :
    siegelCayley w = ((1 - w.snd)⁻¹ • w.fst, I * (1 + w.snd) / (1 - w.snd)) := (rfl)

theorem siegelCayley_symm_apply (p : E × ℂ) :
    siegelCayley.symm p = toLp 2 ((2 * I / (p.2 + I)) • p.1, (p.2 - I) / (p.2 + I)) := (rfl)

@[simp]
theorem siegelCayley_source :
    (siegelCayley : OpenPartialHomeomorph (WithLp 2 (E × ℂ)) (E × ℂ)).source =
      {w | w.snd ≠ 1} := (rfl)

@[simp]
theorem siegelCayley_target :
    (siegelCayley : OpenPartialHomeomorph (WithLp 2 (E × ℂ)) (E × ℂ)).target =
      {p | p.2 ≠ -I} := (rfl)

/-- The centre of the ball goes to the point `(0, i)` of height `1`. -/
@[simp]
theorem siegelCayley_zero : siegelCayley (0 : WithLp 2 (E × ℂ)) = (0, I) := by
  simp [siegelCayley_apply]

/-- **The height of the Cayley transform**: `ρ(C(w)) = (1 - ‖w‖²) / ‖1 - wₙ‖²`. Both sides vanish
when `wₙ = 1`. -/
theorem siegelHeight_siegelCayley (w : WithLp 2 (E × ℂ)) :
    siegelHeight (siegelCayley w) = (1 - ‖w‖ ^ 2) / ‖1 - w.snd‖ ^ 2 := by
  have him : (I * (1 + w.snd) / (1 - w.snd)).im = (1 - ‖w.snd‖ ^ 2) / ‖1 - w.snd‖ ^ 2 := by
    simpa [← sub_eq_add_neg, normSq_eq_norm_sq] using im_I_mul_sub_div_add 1 (-w.snd)
  rw [siegelCayley_apply, siegelHeight_mk, him, norm_smul, norm_inv, prod_norm_sq_eq_of_L2]
  field_simp
  ring

/-- The inverse Cayley transform scales the height: `1 - ‖C⁻¹(u, v)‖² = 4 ρ(u, v) / ‖v + i‖²`. -/
theorem one_sub_norm_sq_siegelCayley_symm {p : E × ℂ} (hp : p.2 ≠ -I) :
    1 - ‖siegelCayley.symm p‖ ^ 2 = 4 * siegelHeight p / ‖p.2 + I‖ ^ 2 := by
  have h1 : p.2 + I ≠ 0 := by rwa [ne_eq, add_eq_zero_iff_eq_neg]
  have hp' : p ∈ siegelCayley.target := hp
  have key := siegelHeight_siegelCayley (siegelCayley.symm p)
  rw [siegelCayley.right_inv hp'] at key
  have hden : 1 - (siegelCayley.symm p).snd = 2 * I / (p.2 + I) := by
    rw [siegelCayley_symm_apply, toLp_snd, one_sub_sub_I_div_add_I hp]
  rw [hden, norm_div, norm_mul, Complex.norm_two, norm_I] at key
  have hn : ‖p.2 + I‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  rw [key]
  field_simp
  ring

/-- The open unit ball lies in the source `{wₙ ≠ 1}` of the Cayley transform. -/
theorem ball_subset_siegelCayley_source :
    ball (0 : WithLp 2 (E × ℂ)) 1 ⊆ siegelCayley.source := fun w hw h ↦ by
  have := (WithLp.norm_snd_le E w).trans_lt (mem_ball_zero_iff.mp hw)
  simp [show w.snd = 1 from h] at this

/-- The closed Siegel domain `{ρ ≥ 0}` lies in the target `{v ≠ -i}` of the Cayley transform. -/
theorem setOf_siegelHeight_nonneg_subset_siegelCayley_target :
    {p : E × ℂ | 0 ≤ siegelHeight p} ⊆ siegelCayley.target := fun p hp h ↦ by
  simp only [mem_ofPred_eq, siegelHeight_def, show p.2 = -I from h, neg_im, I_im] at hp
  nlinarith [sq_nonneg ‖p.1‖]

/-- The Siegel domain lies in the target `{v ≠ -i}` of the Cayley transform. -/
theorem siegelDomain_subset_siegelCayley_target : siegelDomain E ⊆ siegelCayley.target :=
  fun _ hp ↦ setOf_siegelHeight_nonneg_subset_siegelCayley_target (by
    rw [mem_ofPred_eq]
    exact le_of_lt hp)

/-- The Cayley transform maps a point `w` of its source into the closed Siegel domain exactly
when `w` lies in the closed unit ball. -/
theorem siegelCayley_isImage_closedBall :
    siegelCayley.IsImage (closedBall (0 : WithLp 2 (E × ℂ)) 1) {p | 0 ≤ siegelHeight p} :=
  fun w hw ↦ by
    have h1 : 0 < ‖1 - w.snd‖ ^ 2 := by
      have : 1 - w.snd ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
      positivity
    simp only [mem_ofPred_eq, siegelHeight_siegelCayley, mem_closedBall_zero_iff]
    rw [le_div_iff₀ h1, zero_mul, sub_nonneg, sq_le_one_iff₀ (norm_nonneg w)]

/-- The Cayley transform maps a point `w` of its source into the Siegel domain exactly when `w`
lies in the open unit ball. -/
theorem siegelCayley_isImage_ball :
    siegelCayley.IsImage (ball (0 : WithLp 2 (E × ℂ)) 1) (siegelDomain E) :=
  fun w hw ↦ by
    have h1 : 0 < ‖1 - w.snd‖ ^ 2 := by
      have : 1 - w.snd ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
      positivity
    simp only [mem_siegelDomain, siegelHeight_siegelCayley, mem_ball_zero_iff,
      div_pos_iff_of_pos_right h1, sub_pos]
    rw [sq_lt_one_iff₀ (norm_nonneg w)]

/-- The Cayley transform maps a point `w` of its source to the boundary `{ρ = 0}` of the Siegel
domain exactly when `w` lies on the unit sphere. -/
theorem siegelCayley_isImage_sphere :
    siegelCayley.IsImage (sphere (0 : WithLp 2 (E × ℂ)) 1) {p | siegelHeight p = 0} := by
  have := (siegelCayley_isImage_closedBall (E := E)).diff siegelCayley_isImage_ball
  rwa [closedBall_sdiff_ball, setOf_siegelHeight_nonneg_sdiff_siegelDomain] at this

/-- **The Cayley transform maps the open unit ball onto the Siegel domain.** -/
theorem siegelCayley_image_ball :
    siegelCayley '' ball (0 : WithLp 2 (E × ℂ)) 1 = siegelDomain E := by
  have := (siegelCayley_isImage_ball (E := E)).image_eq
  rwa [inter_eq_right.mpr ball_subset_siegelCayley_source,
    inter_eq_right.mpr siegelDomain_subset_siegelCayley_target] at this

/-- The inverse Cayley transform maps the Siegel domain onto the open unit ball. -/
theorem siegelCayley_symm_image_siegelDomain :
    siegelCayley.symm '' siegelDomain E = ball (0 : WithLp 2 (E × ℂ)) 1 := by
  have := (siegelCayley_isImage_ball (E := E)).symm_image_eq
  rwa [inter_eq_right.mpr ball_subset_siegelCayley_source,
    inter_eq_right.mpr siegelDomain_subset_siegelCayley_target] at this

/-- A point of the closed unit ball lies in the source of the Cayley transform exactly when it is
not the boundary point `b₀ = (0, 1)`. -/
theorem mem_siegelCayley_source_iff_ne {w : WithLp 2 (E × ℂ)} (hw : ‖w‖ ≤ 1) :
    w ∈ siegelCayley.source ↔ w ≠ toLp 2 (0, 1) := by
  refine ⟨fun h h' ↦ h (by simp [h']), fun h h' ↦ h ?_⟩
  have hw' := prod_norm_sq_eq_of_L2 w
  rw [show w.snd = 1 from h', norm_one] at hw'
  have : ‖w.fst‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg w]
  have hfst : w.fst = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w.fst])
  exact (WithLp.ext_iff 2).2 (Prod.ext hfst h')

/-- The Cayley transform maps the closed unit ball minus `b₀ = (0, 1)` onto the closed Siegel
domain `{ρ ≥ 0}`. -/
theorem siegelCayley_image_closedBall_diff :
    siegelCayley '' (closedBall (0 : WithLp 2 (E × ℂ)) 1 \ {toLp 2 (0, 1)}) =
      {p | 0 ≤ siegelHeight p} := by
  have := (siegelCayley_isImage_closedBall (E := E)).image_eq
  rwa [inter_eq_right.mpr setOf_siegelHeight_nonneg_subset_siegelCayley_target,
    show siegelCayley.source ∩ closedBall (0 : WithLp 2 (E × ℂ)) 1 =
      closedBall 0 1 \ {toLp 2 (0, 1)} by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_closedBall_zero_iff]
      exact ⟨fun h ↦ ⟨h.2, (mem_siegelCayley_source_iff_ne h.2).1 h.1⟩,
        fun h ↦ ⟨(mem_siegelCayley_source_iff_ne h.1).2 h.2, h.1⟩⟩] at this

/-- The Cayley transform maps the unit sphere minus `b₀ = (0, 1)` onto the boundary `{ρ = 0}` of
the Siegel domain. -/
theorem siegelCayley_image_sphere_diff :
    siegelCayley '' (sphere (0 : WithLp 2 (E × ℂ)) 1 \ {toLp 2 (0, 1)}) =
      {p | siegelHeight p = 0} := by
  have := (siegelCayley_isImage_sphere (E := E)).image_eq
  rwa [inter_eq_right.mpr fun p hp ↦ setOf_siegelHeight_nonneg_subset_siegelCayley_target
      (le_of_eq (Eq.symm hp)),
    show siegelCayley.source ∩ sphere (0 : WithLp 2 (E × ℂ)) 1 =
      sphere 0 1 \ {toLp 2 (0, 1)} by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_sphere_zero_iff_norm]
      exact ⟨fun h ↦ ⟨h.2, (mem_siegelCayley_source_iff_ne h.2.le).1 h.1⟩,
        fun h ↦ ⟨(mem_siegelCayley_source_iff_ne h.1.le).2 h.2, h.1⟩⟩] at this

/-- The Cayley transform restricts to a homeomorphism from the open unit ball onto the Siegel
domain. -/
noncomputable def ballHomeomorphSiegelDomain :
    ball (0 : WithLp 2 (E × ℂ)) 1 ≃ₜ siegelDomain E :=
  siegelCayley.homeomorphOfImageSubsetSource ball_subset_siegelCayley_source
    siegelCayley_image_ball

@[simp]
theorem coe_ballHomeomorphSiegelDomain_apply (w : ball (0 : WithLp 2 (E × ℂ)) 1) :
    (ballHomeomorphSiegelDomain w : E × ℂ) = siegelCayley (w : WithLp 2 (E × ℂ)) := (rfl)

@[simp]
theorem coe_ballHomeomorphSiegelDomain_symm_apply (p : siegelDomain E) :
    (ballHomeomorphSiegelDomain.symm p : WithLp 2 (E × ℂ)) = siegelCayley.symm (p : E × ℂ) := (rfl)

/-! ### Analyticity -/

/-- The Cayley transform is analytic on its source `{wₙ ≠ 1}`. -/
theorem analyticOnNhd_siegelCayley :
    AnalyticOnNhd ℂ (siegelCayley : WithLp 2 (E × ℂ) → E × ℂ) siegelCayley.source :=
  fun _ hw ↦ analyticAt_siegelCayley_toFun hw

/-- The inverse Cayley transform is analytic on its source `{v ≠ -i}`. -/
theorem analyticOnNhd_siegelCayley_symm :
    AnalyticOnNhd ℂ (siegelCayley.symm : E × ℂ → WithLp 2 (E × ℂ)) siegelCayley.target :=
  fun _ hp ↦ analyticAt_siegelCayley_invFun hp

/-! ### Behaviour at the boundary point `b₀ = (0, 1)` -/

/-- The Cayley transform sends the boundary point `b₀ = (0, 1)` to infinity: it tends to infinity
as `w` approaches `b₀` within its source. -/
theorem tendsto_siegelCayley_nhdsWithin_source :
    Tendsto siegelCayley (𝓝[siegelCayley.source] (toLp 2 ((0 : E), (1 : ℂ))))
      (Bornology.cobounded (E × ℂ)) := by
  have hsnd : Tendsto (fun w : WithLp 2 (E × ℂ) ↦ w.snd)
      (𝓝[siegelCayley.source] (toLp 2 ((0 : E), (1 : ℂ)))) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun w hw ↦ hw⟩
    simpa using ((WithLp.continuous_snd 2 E ℂ).tendsto (toLp 2 ((0 : E), (1 : ℂ)))).mono_left
      nhdsWithin_le_nhds
  have h := tendsto_I_mul_one_add_div_one_sub_nhdsNE_one.comp hsnd
  rw [Bornology.cobounded_prod, coprod_eq_prod_top_sup_top_prod]
  exact (tendsto_prod_iff'.mpr ⟨tendsto_top, h⟩).mono_right le_sup_right

/-- The inverse Cayley transform sends infinity in the closed Siegel domain to the boundary
point `b₀ = (0, 1)`. -/
theorem tendsto_siegelCayley_symm_cobounded :
    Tendsto siegelCayley.symm (Bornology.cobounded (E × ℂ) ⊓ 𝓟 {p | 0 ≤ siegelHeight p})
      (𝓝 (toLp 2 ((0 : E), (1 : ℂ)))) := by
  set F := Bornology.cobounded (E × ℂ) ⊓ 𝓟 {p | 0 ≤ siegelHeight p}
  have hF : ∀ᶠ p in F, 0 ≤ siegelHeight p := eventually_inf_principal.mpr (.of_forall fun _ ↦ id)
  -- On `{ρ ≥ 0}` we have `‖u‖² ≤ Im v ≤ ‖v‖`, so `‖(u, v)‖ ≤ ‖v‖ + 1` and `v` tends to infinity.
  have hv : Tendsto (fun p : E × ℂ ↦ p.2) F (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.mp (tendsto_atTop_mono' F ?_
      ((tendsto_atTop_add_const_right _ (-1) tendsto_norm_cobounded_atTop).mono_left inf_le_left))
    filter_upwards [hF] with p hp
    rw [siegelHeight_def, sub_nonneg] at hp
    have hu : ‖p.1‖ ≤ ‖p.2‖ + 1 := by
      nlinarith [im_le_norm p.2, norm_nonneg p.1, norm_nonneg p.2]
    have := max_le hu (le_add_of_nonneg_right zero_le_one : ‖p.2‖ ≤ ‖p.2‖ + 1)
    rw [Prod.norm_def]
    linarith
  -- Hence the second coordinate `(v - i) / (v + i)` of `C⁻¹(u, v)` tends to `1`.
  have hsnd : Tendsto (fun p ↦ (siegelCayley.symm p).snd) F (𝓝 1) :=
    (tendsto_sub_I_div_add_I_cobounded.comp hv).congr fun p ↦ by
      simp [siegelCayley_symm_apply]
  -- Since `C⁻¹(u, v)` lies in the closed ball, `‖C⁻¹(u, v)'‖² ≤ 1 - ‖(v - i) / (v + i)‖² → 0`.
  have hfst : Tendsto (fun p ↦ (siegelCayley.symm p).fst) F (𝓝 0) := by
    have hlim : Tendsto (fun p ↦ 1 - ‖(siegelCayley.symm p).snd‖ ^ 2) F (𝓝 0) := by
      simpa using (hsnd.norm.pow 2).const_sub 1
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (.of_forall fun _ ↦ by positivity)
      ?_ (by simpa using hlim.sqrt))
    filter_upwards [hF] with p hp
    refine Real.le_sqrt_of_sq_le ?_
    have hball := one_sub_norm_sq_siegelCayley_symm
      (setOf_siegelHeight_nonneg_subset_siegelCayley_target hp)
    have hnonneg : 0 ≤ 4 * siegelHeight p / ‖p.2 + I‖ ^ 2 := by positivity
    rw [prod_norm_sq_eq_of_L2] at hball
    linarith
  have := (prod_continuous_toLp 2 E ℂ).tendsto ((0 : E), (1 : ℂ)) |>.comp (hfst.prodMk_nhds hsnd)
  exact this.congr fun p ↦ by rw [Function.comp_apply, ← ofLp_fst, ← ofLp_snd, toLp_ofLp]

/-! ### The extension to the closed ball -/

open scoped Classical in
/-- The Cayley transform extended to all of `WithLp 2 (E × ℂ)` with values in the one-point
compactification of `E × ℂ`, sending the boundary point `b₀ = (0, 1)` to `∞`. On the closed unit
ball it is continuous and injective (`TauCeti.continuousOn_siegelCayleyOnePoint`,
`TauCeti.injOn_siegelCayleyOnePoint`), and for finite-dimensional `E` it is a homeomorphism onto
the closure of the Siegel domain (`TauCeti.closedBallHomeomorphClosureSiegelDomain`). -/
noncomputable def siegelCayleyOnePoint (w : WithLp 2 (E × ℂ)) : OnePoint (E × ℂ) :=
  if w = toLp 2 (0, 1) then ∞ else (siegelCayley w : OnePoint (E × ℂ))

@[simp]
theorem siegelCayleyOnePoint_toLp_zero_one :
    siegelCayleyOnePoint (toLp 2 ((0 : E), (1 : ℂ))) = ∞ := by
  simp [siegelCayleyOnePoint]

/-- Away from `b₀ = (0, 1)`, the extended Cayley transform is the Cayley transform. -/
theorem siegelCayleyOnePoint_of_ne {w : WithLp 2 (E × ℂ)} (hw : w ≠ toLp 2 (0, 1)) :
    siegelCayleyOnePoint w = (siegelCayley w : OnePoint (E × ℂ)) := by
  simp [siegelCayleyOnePoint, hw]

/-- The extended Cayley transform is continuous on the closed unit ball. -/
theorem continuousOn_siegelCayleyOnePoint :
    ContinuousOn siegelCayleyOnePoint (closedBall (0 : WithLp 2 (E × ℂ)) 1) := by
  intro w hw
  rcases eq_or_ne w (toLp 2 (0, 1)) with rfl | hne
  · -- At `b₀`, the transform tends to infinity from within its source.
    rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, siegelCayleyOnePoint_toLp_zero_one]
    have hsub : closedBall (0 : WithLp 2 (E × ℂ)) 1 \ {toLp 2 (0, 1)} ⊆ siegelCayley.source :=
      fun x hx ↦ (mem_siegelCayley_source_iff_ne (mem_closedBall_zero_iff.mp hx.1)).2 hx.2
    have hlim := (tendsto_siegelCayley_nhdsWithin_source (E := E)).mono_left
      (nhdsWithin_mono _ hsub)
    refine (OnePoint.tendsto_coe_infty.comp ((hlim.mono_right cobounded_le_cocompact).mono_right
      cocompact_le_coclosedCompact)).congr' (eventually_nhdsWithin_of_forall fun x hx ↦ ?_)
    exact (siegelCayleyOnePoint_of_ne hx.2).symm
  · -- Away from `b₀`, it agrees near `w` with the continuous map `C`.
    have hsrc := (mem_siegelCayley_source_iff_ne (mem_closedBall_zero_iff.mp hw)).2 hne
    refine ContinuousAt.continuousWithinAt ?_
    refine ((OnePoint.continuous_coe.continuousAt).comp (siegelCayley.continuousAt hsrc)).congr ?_
    filter_upwards [isOpen_ne.mem_nhds hne] with x hx
    exact (siegelCayleyOnePoint_of_ne hx).symm

/-- The extended Cayley transform is injective on the closed unit ball. -/
theorem injOn_siegelCayleyOnePoint :
    InjOn siegelCayleyOnePoint (closedBall (0 : WithLp 2 (E × ℂ)) 1) := by
  intro x hx y hy h
  have hsrc {z : WithLp 2 (E × ℂ)} (hz : z ∈ closedBall 0 1) (hne : z ≠ toLp 2 (0, 1)) :=
    (mem_siegelCayley_source_iff_ne (mem_closedBall_zero_iff.mp hz)).2 hne
  rcases eq_or_ne x (toLp 2 (0, 1)) with rfl | hx'
  · by_contra hne
    rw [siegelCayleyOnePoint_toLp_zero_one, siegelCayleyOnePoint_of_ne (Ne.symm hne)] at h
    exact OnePoint.coe_ne_infty _ h.symm
  rcases eq_or_ne y (toLp 2 (0, 1)) with rfl | hy'
  · rw [siegelCayleyOnePoint_toLp_zero_one, siegelCayleyOnePoint_of_ne hx'] at h
    exact absurd h (OnePoint.coe_ne_infty _)
  rw [siegelCayleyOnePoint_of_ne hx', siegelCayleyOnePoint_of_ne hy'] at h
  exact siegelCayley.injOn (hsrc hx hx') (hsrc hy hy') (OnePoint.coe_injective h)

/-- On the open unit ball, the extended Cayley transform is the Cayley transform, so it maps the
ball onto the Siegel domain. -/
theorem siegelCayleyOnePoint_image_ball :
    siegelCayleyOnePoint '' ball (0 : WithLp 2 (E × ℂ)) 1 =
      ((↑) : E × ℂ → OnePoint (E × ℂ)) '' siegelDomain E := by
  rw [← siegelCayley_image_ball, image_image]
  refine image_congr fun w hw ↦ siegelCayleyOnePoint_of_ne fun h ↦ ?_
  have := mem_ball_zero_iff.mp hw
  simp [h] at this

private theorem isCompact_closedBall_withLp [FiniteDimensional ℂ E] :
    IsCompact (closedBall (0 : WithLp 2 (E × ℂ)) 1) := by
  have : FiniteDimensional ℂ (WithLp 2 (E × ℂ)) :=
    Module.Finite.equiv (WithLp.linearEquiv 2 ℂ (E × ℂ)).symm
  have := FiniteDimensional.proper ℂ (WithLp 2 (E × ℂ))
  exact isCompact_closedBall 0 1

/-- For finite-dimensional `E`, the extended Cayley transform maps the closed unit ball onto the
closure of the Siegel domain in the one-point compactification of `E × ℂ`. -/
theorem siegelCayleyOnePoint_image_closedBall [FiniteDimensional ℂ E] :
    siegelCayleyOnePoint '' closedBall (0 : WithLp 2 (E × ℂ)) 1 =
      closure (((↑) : E × ℂ → OnePoint (E × ℂ)) '' siegelDomain E) := by
  have := FiniteDimensional.proper ℂ E
  have hcl := closure_ball (0 : WithLp 2 (E × ℂ)) one_ne_zero
  refine subset_antisymm ?_ (closure_minimal ?_ ?_)
  · rw [← siegelCayleyOnePoint_image_ball, ← hcl]
    exact (hcl ▸ continuousOn_siegelCayleyOnePoint).image_closure
  · rw [← siegelCayleyOnePoint_image_ball]
    exact image_mono ball_subset_closedBall
  · exact (isCompact_closedBall_withLp.image_of_continuousOn
      continuousOn_siegelCayleyOnePoint).isClosed

/-- **The Cayley transform extends to the closed ball.** For finite-dimensional `E`, the extended
Cayley transform is a homeomorphism from the closed unit ball of `WithLp 2 (E × ℂ)` onto the
closure of the Siegel domain in the one-point compactification of `E × ℂ`, sending `b₀ = (0, 1)`
to `∞`. -/
noncomputable def closedBallHomeomorphClosureSiegelDomain [FiniteDimensional ℂ E] :
    closedBall (0 : WithLp 2 (E × ℂ)) 1 ≃ₜ
      closure (((↑) : E × ℂ → OnePoint (E × ℂ)) '' siegelDomain E) :=
  haveI := FiniteDimensional.proper ℂ E
  haveI : CompactSpace (closedBall (0 : WithLp 2 (E × ℂ)) 1) :=
    isCompact_iff_compactSpace.mp isCompact_closedBall_withLp
  Continuous.homeoOfEquivCompactToT2 (f := BijOn.equiv siegelCayleyOnePoint
    ⟨(mapsTo_image _ _).mono_right siegelCayleyOnePoint_image_closedBall.subset,
      injOn_siegelCayleyOnePoint, siegelCayleyOnePoint_image_closedBall.symm.subset⟩)
    ((continuousOn_iff_continuous_domRestrict.mp continuousOn_siegelCayleyOnePoint).subtype_mk _)

@[simp]
theorem coe_closedBallHomeomorphClosureSiegelDomain_apply [FiniteDimensional ℂ E]
    (w : closedBall (0 : WithLp 2 (E × ℂ)) 1) :
    (closedBallHomeomorphClosureSiegelDomain w : OnePoint (E × ℂ)) =
      siegelCayleyOnePoint (w : WithLp 2 (E × ℂ)) := (rfl)

end TauCeti
