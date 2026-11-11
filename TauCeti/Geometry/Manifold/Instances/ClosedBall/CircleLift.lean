/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.Analysis.Calculus.Deriv.AddCircle
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Topology.Instances.AddCircle.Lift

/-!
# Extending a diffeomorphism of the circle over the disc

An orientation-preserving diffeomorphism `σ` of the unit circle is described by a lift
`F : ℝ → ℝ`, `σ (Circle.exp x) = Circle.exp (F x)`, with `F (x + 2π) = F x + 2π` and `F' > 0`.
This file extends `σ` to a diffeomorphism of the closed unit disc of `ℂ`, in the sense of manifolds
with boundary. This is what lets data bounded by a parametrized circle, such as a slice disc of a
knot, be reparametrized along with the circle.

The extension `TauCeti.circleLiftDiffeomorph` is a diffeomorphism of the whole plane. It turns the
circle of radius `r` by the circle map with lift

`x ↦ x + χ r * (F x - x)`,

where `χ r = smoothTransition (3 r - 1)` is `0` for `r ≤ 1 / 3` and `1` for `r ≥ 2 / 3`
(`TauCeti.circleLiftDiffeomorph_mul_exp`). Since `F x - x` is `2π`-periodic, this is a well defined
map on each circle. It interpolates between the identity near the origin and `σ` on, and outside,
the circle of radius `2 / 3`. Every interpolating lift has positive derivative
`(1 - χ r) + χ r * F' x`, so the map is a bijection of each circle; it is smooth, and its derivative
is invertible everywhere. By the inverse function theorem its inverse is smooth too. It preserves
the norm (`TauCeti.norm_circleLiftDiffeomorph`), so it restricts to a diffeomorphism
`TauCeti.circleLiftDiscDiffeomorph` of the closed unit disc which is `σ` on the boundary circle
(`TauCeti.circleLiftDiscDiffeomorph_inclusion`).

The same radial interpolation through circle diffeomorphisms is
`AddCircle.collarDiffeomorphOfLift`, on the product `ℝ × AddCircle T` of a collar coordinate and
the circle. Here it is carried out directly on the plane, where it is the identity near the origin
and so extends smoothly across the centre of the disc. Both constructions use the interpolating
lift lemmas `AddCircle.add_mul_sub_add_period`, `AddCircle.hasDerivAt_add_mul_sub` and
`AddCircle.one_sub_add_mul_pos`.

## Main definitions

* `TauCeti.circleLiftDiffeomorph`: the diffeomorphism of `ℂ` extending the circle map with lift
  `F`.
* `TauCeti.circleLiftDiscDiffeomorph`: its restriction to the closed unit disc.

## Main results

* `TauCeti.circleLiftDiffeomorph_mul_exp`: the value at `r * exp (x * I)`.
* `TauCeti.norm_circleLiftDiffeomorph`: the diffeomorphism preserves the norm.
* `TauCeti.circleLiftDiffeomorph_of_norm_le`: it is the identity on the disc of radius `1 / 3`.
* `TauCeti.circleLiftDiffeomorph_mul_exp_of_le`: it is the circle map with lift `F` on each circle
  of radius at least `2 / 3`.
* `TauCeti.norm_circleLiftDiffeomorph_symm`, `TauCeti.circleLiftDiffeomorph_symm_of_norm_le`,
  `TauCeti.circleLiftDiffeomorph_symm_mul_exp_of_le`: the same for the inverse.
* `TauCeti.circleLiftDiscDiffeomorph_inclusion`: on the boundary circle of the closed unit disc
  the restriction is the circle map with lift `F`.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 8, §1, for extending a diffeomorphism isotopic to the identity over a collar by a
  radial cutoff of the isotopy.
-/

public section

noncomputable section

open Complex Metric Set Function Real
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {F : ℝ → ℝ}

/-! ### The plane map -/

/-- The weight `χ r = smoothTransition (3 r - 1)` of the interpolation on the circle of radius
`r`: it is `0` for `r ≤ 1 / 3` and `1` for `r ≥ 2 / 3`. -/
private def weight (r : ℝ) : ℝ :=
  smoothTransition (3 * r - 1)

private theorem weight_of_le {r : ℝ} (hr : r ≤ 1 / 3) : weight r = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

private theorem weight_of_ge {r : ℝ} (hr : 2 / 3 ≤ r) : weight r = 1 :=
  smoothTransition.one_of_one_le (by linarith)

private theorem contDiff_weight : ContDiff ℝ ∞ weight :=
  smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The angle by which the plane map turns the point `z`. -/
private def angle (F : ℝ → ℝ) (z : ℂ) : ℝ :=
  weight ‖z‖ * (F (arg z) - arg z)

/-- The plane map: the point `z` is turned by `angle F z`. -/
private def circleLiftMap (F : ℝ → ℝ) (z : ℂ) : ℂ :=
  z * exp (angle F z * I)

variable (hper : ∀ x, F (x + 2 * π) = F x + 2 * π)
include hper

/-- The angle at `r * exp (x * I)`, `r > 0`, is computed from `x` itself, whatever the argument. -/
private theorem angle_mul_exp {r : ℝ} (hr : 0 < r) (x : ℝ) :
    angle F (r * exp (x * I)) = weight r * (F x - x) := by
  have hnorm : ‖(r : ℂ) * exp (x * I)‖ = r := by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hr.le]
  rw [angle, hnorm, arg_real_mul _ hr, arg_exp_mul_I, ← self_sub_toIocDiv_zsmul]
  exact congrArg (weight r * ·) ((AddCircle.periodic_sub_of_lift hper).sub_zsmul_eq _)

/-- The plane map on the circle of radius `r` is the circle map with lift
`x ↦ x + weight r * (F x - x)`. -/
private theorem circleLiftMap_mul_exp {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    circleLiftMap F (r * exp (x * I)) = r * exp ((x + weight r * (F x - x) : ℝ) * I) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [circleLiftMap]
  rw [circleLiftMap, angle_mul_exp hper hr, mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

omit hper in
private theorem norm_circleLiftMap (z : ℂ) : ‖circleLiftMap F z‖ = ‖z‖ := by
  rw [circleLiftMap, norm_mul, norm_exp_ofReal_mul_I, mul_one]

omit hper in
private theorem circleLiftMap_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) : circleLiftMap F z = z := by
  simp [circleLiftMap, angle, weight_of_le hz]

/-! ### Smoothness -/

private theorem contDiff_angle (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (angle F) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  rcases lt_or_ge ‖z‖ (1 / 3) with hz | hz
  · -- Near the origin the weight vanishes, so the angle is zero.
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    simp [angle, weight_of_le (le_of_lt hw)]
  · have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    exact (contDiff_weight.contDiffAt.comp z (contDiffAt_norm ℝ hz0)).mul
      ((hF.sub contDiff_id).contDiffAt_comp_arg (AddCircle.periodic_sub_of_lift hper) hz0)

private theorem contDiff_circleLiftMap (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (circleLiftMap F) :=
  contDiff_id.mul ((Complex.contDiff_exp (𝕜 := ℝ)).comp
    ((ofRealCLM.contDiff.comp (contDiff_angle hper hF)).mul contDiff_const))

/-! ### Bijectivity -/

variable (hF : ContDiff ℝ ∞ F) (hpos : ∀ x, 0 < deriv F x)
include hF hpos

omit hper hpos in
/-- The interpolating lift `x ↦ x + c * (F x - x)` has derivative `1 - c + c * F' x`. -/
private theorem hasDerivAt_lift (c x : ℝ) :
    HasDerivAt (fun y ↦ y + c * (F y - y)) (1 - c + c * deriv F x) x :=
  AddCircle.hasDerivAt_add_mul_sub ((hF.differentiable (by simp)) x).hasDerivAt c

omit hper hF hpos in
private theorem weight_mem (r : ℝ) : 0 ≤ weight r ∧ weight r ≤ 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

omit hper hF in
private theorem deriv_lift_pos (r x : ℝ) : 0 < 1 - weight r + weight r * deriv F x :=
  AddCircle.one_sub_add_mul_pos (weight_mem r).1 (weight_mem r).2 (hpos x)

omit hper in
private theorem strictMono_lift (r : ℝ) : StrictMono fun x ↦ x + weight r * (F x - x) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_lift hF _) (deriv_lift_pos hpos r)

private theorem injective_circleLiftMap : Injective (circleLiftMap F) := by
  intro z w h
  have hnorm : ‖z‖ = ‖w‖ := by
    rw [← norm_circleLiftMap (F := F) z, h, norm_circleLiftMap]
  rw [← norm_mul_exp_arg_mul_I z, ← norm_mul_exp_arg_mul_I w] at h ⊢
  rw [circleLiftMap_mul_exp hper (norm_nonneg _), circleLiftMap_mul_exp hper (norm_nonneg _),
    hnorm] at h
  rcases eq_or_ne ‖w‖ 0 with h0 | h0
  · rw [hnorm, h0]
    simp
  have h' := mul_left_cancel₀ (ofReal_ne_zero.2 h0) h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h'
  -- The two interpolated lifts differ by `2πk`, hence so do the arguments.
  have hk' : arg z + weight ‖w‖ * (F (arg z) - arg z) =
      arg w + k * (2 * π) + weight ‖w‖ * (F (arg w + k * (2 * π)) - (arg w + k * (2 * π))) := by
    rw [AddCircle.lift_add_int_mul (F := fun y ↦ y + weight ‖w‖ * (F y - y))
      (AddCircle.add_mul_sub_add_period hper (weight ‖w‖)) (arg w) k]
    apply ofReal_injective
    have := congrArg (fun u : ℂ ↦ u / I) hk
    simp only [mul_div_assoc, div_self I_ne_zero, mul_one, add_div] at this
    rw [this]
    push_cast
    field_simp
  have harg := (strictMono_lift hF hpos ‖w‖).injective hk'
  rw [hnorm, harg]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨k, by push_cast; ring⟩

private theorem surjective_circleLiftMap : Surjective (circleLiftMap F) := by
  intro w
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  obtain ⟨G, -, hG, -, -⟩ := AddCircle.exists_lift_inverse (hasDerivAt_lift hF (weight ‖w‖))
    (AddCircle.add_mul_sub_add_period hper (weight ‖w‖)) (deriv_lift_pos hpos ‖w‖)
  have hGw : G (arg w) + weight ‖w‖ * (F (G (arg w)) - G (arg w)) = arg w := hG (arg w)
  refine ⟨‖w‖ * exp (G (arg w) * I), ?_⟩
  rw [circleLiftMap_mul_exp hper (norm_nonneg _), hGw, norm_mul_exp_arg_mul_I]

/-! ### The derivative -/

omit hpos in
/-- The derivative of the plane map in the angular direction `z * I` at `z = r * exp (x * I)`: a
positive multiple of the angular direction at the image point. -/
private theorem fderiv_circleLiftMap_mul_I {r : ℝ} (hr : 0 < r) (x : ℝ) :
    fderiv ℝ (circleLiftMap F) (r * exp (x * I)) (r * exp (x * I) * I) =
      r * (exp ((x + weight r * (F x - x) : ℝ) * I) *
        ((1 - weight r + weight r * deriv F x : ℝ) * I)) := by
  have hD : Differentiable ℝ (circleLiftMap F) :=
    (contDiff_circleLiftMap hper hF).differentiable (by simp)
  have hγ : HasDerivAt (fun t : ℝ ↦ (r : ℂ) * exp (t * I)) (r * exp (x * I) * I) x :=
    ((((hasDerivAt_id x).ofReal_comp.mul_const I).cexp).const_mul (r : ℂ)).congr_deriv
      (by simp only [id_eq, ofReal_one, one_mul]; ring)
  have h₂ : HasDerivAt (fun t : ℝ ↦ circleLiftMap F (r * exp (t * I)))
      (r * (exp ((x + weight r * (F x - x) : ℝ) * I) *
        ((1 - weight r + weight r * deriv F x : ℝ) * I))) x := by
    simp only [circleLiftMap_mul_exp hper hr.le]
    exact (((hasDerivAt_lift hF (weight r) x).ofReal_comp.mul_const I).cexp).const_mul (r : ℂ)
  exact ((hD _).hasFDerivAt.comp_hasDerivAt x hγ).unique h₂

omit hpos in
/-- The derivative of the plane map in the radial direction `exp (x * I)` at `r * exp (x * I)`: its
component along the direction `exp ((x + weight r * (F x - x)) * I)` of the image point is `1`. -/
private theorem exists_fderiv_circleLiftMap_exp {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∃ a : ℝ, fderiv ℝ (circleLiftMap F) (r * exp (x * I)) (exp (x * I)) =
      exp ((x + weight r * (F x - x) : ℝ) * I) * (1 + a * I) := by
  have hD : Differentiable ℝ (circleLiftMap F) :=
    (contDiff_circleLiftMap hper hF).differentiable (by simp)
  have hd : HasDerivAt (fun s : ℝ ↦ x + weight s * (F x - x))
      (deriv (fun s : ℝ ↦ x + weight s * (F x - x)) r) r :=
    (((contDiff_weight.differentiable (by simp)).differentiableAt (x := r)).mul_const
      (F x - x)).const_add x |>.hasDerivAt
  refine ⟨r * deriv (fun s : ℝ ↦ x + weight s * (F x - x)) r, ?_⟩
  have hγ : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * exp (x * I)) (exp (x * I)) r := by
    simpa using (hasDerivAt_id r).ofReal_comp.mul_const (exp (x * I))
  have h₂ : HasDerivAt (fun s : ℝ ↦ circleLiftMap F (s * exp (x * I)))
      (exp ((x + weight r * (F x - x) : ℝ) * I) *
        (1 + (r * deriv (fun s : ℝ ↦ x + weight s * (F x - x)) r : ℝ) * I))
      r := by
    have hev : (fun s : ℝ ↦ circleLiftMap F (s * exp (x * I))) =ᶠ[nhds r]
        fun s : ℝ ↦ (s : ℂ) * exp ((x + weight s * (F x - x) : ℝ) * I) := by
      filter_upwards [lt_mem_nhds hr] with s hs
      exact circleLiftMap_mul_exp hper hs.le x
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    convert (hasDerivAt_id r).ofReal_comp.mul (hd.ofReal_comp.mul_const I).cexp using 1
    · rfl
    · simp only [id_eq, ofReal_one, one_mul, ofReal_mul]
      ring
  exact ((hD _).hasFDerivAt.comp_hasDerivAt r hγ).unique h₂

/-- The derivative of the plane map is injective at every point: in the polar coordinates
`r * exp (x * I)`, the radial direction goes to a vector with a nonzero radial component, and the
angular direction goes to a positive multiple of the angular direction at the image point. -/
private theorem injective_fderiv_circleLiftMap (z : ℂ) :
    Injective (fderiv ℝ (circleLiftMap F) z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · -- Near the origin the map is the identity.
    have : circleLiftMap F =ᶠ[nhds 0] id := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
        (show ‖(0 : ℂ)‖ < 1 / 3 by norm_num)] with w hw
      exact circleLiftMap_of_norm_le hw.le
    rw [this.fderiv_eq, fderiv_id]
    exact injective_id
  obtain ⟨r, x, hr, rfl⟩ : ∃ r x : ℝ, 0 < r ∧ z = r * exp (x * I) :=
    ⟨‖z‖, arg z, norm_pos_iff.2 hz, (norm_mul_exp_arg_mul_I z).symm⟩
  set D := fderiv ℝ (circleLiftMap F) (r * exp (x * I))
  have hang := fderiv_circleLiftMap_mul_I hper hF hr x
  obtain ⟨a, ha⟩ := exists_fderiv_circleLiftMap_exp hper hF hr x
  -- A vector `v = s • exp (x * I) + t • (z * I)` goes to
  -- `exp ((x + weight r * (F x - x)) * I) * (s + (s * a + t * r * μ) * I)`, with `μ > 0`; this
  -- vanishes only if `s = 0` and then `t = 0`.
  have hμ := deriv_lift_pos hpos r x
  refine (injective_iff_map_eq_zero D).2 fun v hv ↦ ?_
  obtain ⟨s, t, rfl⟩ : ∃ s t : ℝ, v = s * exp (x * I) + t * (r * exp (x * I) * I) :=
    ⟨_, _, eq_re_mul_add_im_div_mul (exp_ne_zero _) hr.ne' v⟩
  have hsmul (q : ℝ) (w : ℂ) : D (q * w) = q * D w := by
    simpa [Complex.real_smul] using D.map_smul q w
  have hzero : exp ((x + weight r * (F x - x) : ℝ) * I) *
      ((s : ℂ) + ((s * a + t * r * (1 - weight r + weight r * deriv F x) : ℝ) : ℂ) * I) = 0 := by
    rw [← hv, map_add, hsmul, hsmul, ha, hang]
    push_cast
    ring
  have key := (mul_eq_zero.1 hzero).resolve_left (exp_ne_zero _)
  have hs : s = 0 := by simpa using congrArg re key
  have ht : t * r * (1 - weight r + weight r * deriv F x) = 0 := by
    simpa [hs] using congrArg im key
  have ht' : t = 0 := by
    rcases mul_eq_zero.1 ht with h | h
    · exact (mul_eq_zero.1 h).resolve_right hr.ne'
    · exact absurd h hμ.ne'
  simp [hs, ht']

/-! ### The diffeomorphisms -/

/-- The derivative of the plane map at `z`, as a linear automorphism of `ℂ`. -/
private def fderivEquiv (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.ofInjectiveEndo _
    (injective_fderiv_circleLiftMap hper hF hpos z)).toContinuousLinearEquiv

private theorem coe_fderivEquiv (z : ℂ) :
    (fderivEquiv hper hF hpos z : ℂ →L[ℝ] ℂ) = fderiv ℝ (circleLiftMap F) z := by
  ext v
  simp [fderivEquiv]

private theorem hasStrictFDerivAt_circleLiftMap (z : ℂ) :
    HasStrictFDerivAt (circleLiftMap F) (fderivEquiv hper hF hpos z : ℂ →L[ℝ] ℂ) z := by
  rw [coe_fderivEquiv]
  exact (contDiff_circleLiftMap hper hF).contDiffAt.hasStrictFDerivAt_fderiv (by simp)

/-- The plane map as a homeomorphism of `ℂ`: a continuous bijection, open by the inverse function
theorem. -/
private def circleLiftHomeomorph : ℂ ≃ₜ ℂ :=
  (Equiv.ofBijective _ ⟨injective_circleLiftMap hper hF hpos,
    surjective_circleLiftMap hper hF hpos⟩).toHomeomorphOfContinuousOpen
    (contDiff_circleLiftMap hper hF).continuous
    (isOpenMap_of_hasStrictFDerivAt_equiv (hasStrictFDerivAt_circleLiftMap hper hF hpos))

/-- The diffeomorphism of `ℂ` extending the circle map with lift `F`: it turns the circle of
radius `r` by the circle map with lift `x ↦ x + smoothTransition (3 r - 1) * (F x - x)`, so it is
the identity near the origin and the circle map with lift `F` on and outside the circle of radius
`2 / 3`. -/
def circleLiftDiffeomorph : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ where
  toEquiv := (circleLiftHomeomorph hper hF hpos).toEquiv
  contMDiff_toFun := (contDiff_circleLiftMap hper hF).contMDiff
  contMDiff_invFun := ((circleLiftHomeomorph hper hF hpos).contDiff_symm
    (fun z ↦ (hasStrictFDerivAt_circleLiftMap hper hF hpos z).hasFDerivAt)
    (contDiff_circleLiftMap hper hF)).contMDiff

private theorem circleLiftDiffeomorph_apply (z : ℂ) :
    circleLiftDiffeomorph hper hF hpos z = circleLiftMap F z :=
  (rfl)

/-- The diffeomorphism turns the circle of radius `r` by the circle map with lift
`x ↦ x + smoothTransition (3 r - 1) * (F x - x)`. -/
theorem circleLiftDiffeomorph_mul_exp {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    circleLiftDiffeomorph hper hF hpos (r * exp (x * I)) =
      r * exp ((x + smoothTransition (3 * r - 1) * (F x - x) : ℝ) * I) := by
  rw [circleLiftDiffeomorph_apply, circleLiftMap_mul_exp hper hr, weight]

/-- On and outside the circle of radius `2 / 3` the diffeomorphism is the circle map with lift `F`
on each circle about the origin. -/
theorem circleLiftDiffeomorph_mul_exp_of_le {r : ℝ} (hr : 2 / 3 ≤ r) (x : ℝ) :
    circleLiftDiffeomorph hper hF hpos (r * exp (x * I)) = r * exp (F x * I) := by
  rw [circleLiftDiffeomorph_apply, circleLiftMap_mul_exp hper (by linarith),
    weight_of_ge hr, one_mul, add_sub_cancel]

/-- The diffeomorphism preserves the norm. -/
@[simp]
theorem norm_circleLiftDiffeomorph (z : ℂ) : ‖circleLiftDiffeomorph hper hF hpos z‖ = ‖z‖ := by
  rw [circleLiftDiffeomorph_apply, norm_circleLiftMap]

/-- The diffeomorphism is the identity on the closed disc of radius `1 / 3`. -/
theorem circleLiftDiffeomorph_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) :
    circleLiftDiffeomorph hper hF hpos z = z := by
  rw [circleLiftDiffeomorph_apply, circleLiftMap_of_norm_le hz]

/-- The inverse diffeomorphism preserves the norm. -/
@[simp]
theorem norm_circleLiftDiffeomorph_symm (z : ℂ) :
    ‖(circleLiftDiffeomorph hper hF hpos).symm z‖ = ‖z‖ := by
  conv_rhs => rw [← (circleLiftDiffeomorph hper hF hpos).apply_symm_apply z]
  rw [norm_circleLiftDiffeomorph]

/-- The inverse diffeomorphism is the identity on the closed disc of radius `1 / 3`. -/
theorem circleLiftDiffeomorph_symm_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) :
    (circleLiftDiffeomorph hper hF hpos).symm z = z := by
  conv_lhs => rw [← circleLiftDiffeomorph_of_norm_le hper hF hpos hz]
  exact Diffeomorph.symm_apply_apply _ z

/-- On and outside the circle of radius `2 / 3` the inverse diffeomorphism undoes the circle map
with lift `F` on each circle about the origin. -/
theorem circleLiftDiffeomorph_symm_mul_exp_of_le {r : ℝ} (hr : 2 / 3 ≤ r) (x : ℝ) :
    (circleLiftDiffeomorph hper hF hpos).symm (r * exp (F x * I)) = r * exp (x * I) := by
  conv_lhs => rw [← circleLiftDiffeomorph_mul_exp_of_le hper hF hpos hr x]
  exact Diffeomorph.symm_apply_apply _ _

/-- The diffeomorphism of the closed unit disc of `ℂ` extending the circle map with lift `F`. -/
def circleLiftDiscDiffeomorph :
    closedBall (0 : ℂ) 1 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ closedBall (0 : ℂ) 1 :=
  (circleLiftDiffeomorph hper hF hpos).restrictUnitClosedBall (by simp)

@[simp]
theorem coe_circleLiftDiscDiffeomorph_apply (z : closedBall (0 : ℂ) 1) :
    (circleLiftDiscDiffeomorph hper hF hpos z : ℂ) = circleLiftDiffeomorph hper hF hpos z :=
  Diffeomorph.coe_restrictUnitClosedBall_apply _ _ z

@[simp]
theorem coe_circleLiftDiscDiffeomorph_symm_apply (z : closedBall (0 : ℂ) 1) :
    ((circleLiftDiscDiffeomorph hper hF hpos).symm z : ℂ) =
      (circleLiftDiffeomorph hper hF hpos).symm z :=
  Diffeomorph.coe_restrictUnitClosedBall_symm_apply _ _ z

/-- On the boundary circle the diffeomorphism of the closed unit disc is the circle map `σ` with
lift `F`. -/
theorem circleLiftDiscDiffeomorph_inclusion {σ : Circle → Circle}
    (hσ : ∀ x, σ (Circle.exp x) = Circle.exp (F x)) (z : Circle) :
    circleLiftDiscDiffeomorph hper hF hpos (Set.inclusion sphere_subset_closedBall z) =
      Set.inclusion sphere_subset_closedBall (σ z) := by
  apply Subtype.ext
  rw [coe_circleLiftDiscDiffeomorph_apply, ← Circle.exp_arg z, hσ]
  have h := circleLiftDiffeomorph_mul_exp_of_le hper hF hpos (r := 1) (by norm_num) (arg z)
  rw [ofReal_one, one_mul, one_mul] at h
  simpa only [Set.coe_inclusion, Circle.coe_exp] using h

end TauCeti
