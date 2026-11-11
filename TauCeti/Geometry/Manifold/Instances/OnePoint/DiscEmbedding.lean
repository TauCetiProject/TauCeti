/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy

/-!
# The open disc of area `a` is the sphere of area `a` minus a point

For `a > 0`, the open disc `B(√(a / π)) ⊆ ℂ` of area `a`, with the standard area form
`ω₀(v, w) = Im (conj v * w) = dx ∧ dy`, is symplectomorphic to the Riemann sphere minus the point
`∞`, with the Fubini–Study form scaled to total area `a`, `a • ω_FS`. The symplectomorphism is the
radial map

`f(z) = √(π / (a - π |z|²)) z` (`OnePoint.discToSphere`),

whose inverse is `g(w) = √(a / (π (1 + |w|²))) w` (`OnePoint.sphereToDisc`), defined and smooth on
all of `ℂ`, with values in the disc. Both are real-analytic, and together they form the partial
diffeomorphism `OnePoint.discPartialDiffeomorph a ha` from the disc onto `{∞}ᶜ`.

A radial map `u ↦ T(|u|²) u` of the plane multiplies the area form `Im (conj v * w)` by its
Jacobian `T² + 2 T T' |u|²` (`HasDerivAt.im_conj_mul_fderiv_radial_smul`). For `g` this is
`a / (π (1 + |w|²)²) = a ρ(w)`, where `ρ` is the Fubini–Study density, so `g` pulls the area form
back to `a ω_FS` (`OnePoint.im_conj_mul_fderiv_sphereToDisc`). Equivalently `f` pulls `a ω_FS` back
to the area form (`OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_discPartialDiffeomorph`). In terms
of areas: `f` sends the disc of radius `r`, of area `π r²`, onto the disc of radius `R` with
`π r² = a R² / (1 + R²)`, which is the Fubini–Study area of that disc scaled by `a`.

This is the sphere factor of the embedding of a ball of radius `r` into `S²(a) × T²ⁿ⁻²` with
`a > π r²` in Gromov's proof of the nonsqueezing theorem: a ball whose image lies in the cylinder
`{|z₀| < R}` is sent into the product of the sphere of area `a = π R² + ε` with a large torus, by
`f` in the first coordinate.

## Main definitions

* `OnePoint.discToSphere a`: the map `z ↦ √(π / (a - π |z|²)) z` from the disc of area `a` onto `ℂ`.
* `OnePoint.sphereToDisc a`: its inverse `w ↦ √(a / (π (1 + |w|²))) w`.
* `OnePoint.discPartialDiffeomorph a ha`: the partial diffeomorphism from the disc of area `a` onto
  the Riemann sphere minus `∞`.

## Main results

* `HasDerivAt.im_conj_mul_fderiv_radial_smul`: a radial map `u ↦ T(|u|²) u` multiplies the area form
  by `T² + 2 T T' |u|²`.
* `OnePoint.im_conj_mul_fderiv_sphereToDisc`: `g` pulls the area form of the disc back to the
  scaled Fubini–Study form `a ρ(w) Im (conj v * w)`.
* `OnePoint.mul_fubiniStudyDensity_mul_im_conj_fderiv_discToSphere`: `f` pulls the scaled
  Fubini–Study form back to the area form, in the affine coordinate.
* `OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_discPartialDiffeomorph`: the same statement for the
  partial diffeomorphism into the Riemann sphere and the smooth two-form `a • ω_FS`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §0.3.A (the nonsqueezing theorem, proved by compactifying the cylinder to a product of
  a sphere with a torus).
-/

public section

noncomputable section

open Set Metric ComplexConjugate TauCeti Real
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace HasDerivAt

/-- **The derivative of a radial map.** If `T` has derivative `T'` at `‖z‖²`, then the map
`u ↦ T(‖u‖²) u` of a real inner product space has derivative `v ↦ T(‖z‖²) v + 2 T' ⟪z, v⟫ z` at
`z`. -/
theorem hasFDerivAt_radial_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℝ → ℝ} {T' : ℝ} {z : E} (hT : HasDerivAt T T' (‖z‖ ^ 2)) :
    HasFDerivAt (fun u : E ↦ T (‖u‖ ^ 2) • u)
      (T (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ E + (2 * T') • (innerSL ℝ z).smulRight z) z := by
  have h := (hT.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt).smul
    (hasFDerivAt_id z)
  refine h.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Function.comp_apply, id_eq,
    smul_smul]
  ring_nf

/-- **The Jacobian of a radial map of the plane.** If `f u = T(|u|²) u` and `T` has derivative
`T'` at `|z|²`, then the derivative of `f` at `z` multiplies the area form `Im (conj v * w)` by
`T(|z|²)² + 2 T(|z|²) T' |z|²`. -/
theorem im_conj_mul_fderiv_radial_smul {f : ℂ → ℂ} {T : ℝ → ℝ} {T' : ℝ} {z : ℂ}
    (hT : HasDerivAt T T' (‖z‖ ^ 2)) (hf : ∀ u, f u = T (‖u‖ ^ 2) • u) (v w : ℂ) :
    (conj (fderiv ℝ f z v) * fderiv ℝ f z w).im =
      (T (‖z‖ ^ 2) ^ 2 + 2 * T (‖z‖ ^ 2) * T' * ‖z‖ ^ 2) * (conj v * w).im := by
  rw [funext hf, hT.hasFDerivAt_radial_smul.fderiv]
  generalize T (‖z‖ ^ 2) = t
  -- Expand both sides in real and imaginary parts.
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Complex.inner, Complex.sq_norm,
    Complex.normSq_apply, Complex.real_smul, map_add, map_mul, Complex.conj_ofReal,
    Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

end HasDerivAt

namespace OnePoint

variable {a : ℝ} {n : WithTop ℕ∞}

/-- The map `w ↦ √(a / (π (1 + |w|²))) w`, which sends `ℂ`, the Riemann sphere minus `∞`, onto the
open disc of area `a` and pulls its area form back to the Fubini–Study form scaled by `a`. -/
def sphereToDisc (a : ℝ) (w : ℂ) : ℂ :=
  √(a / (π * (1 + ‖w‖ ^ 2))) • w

/-- The map `z ↦ √(π / (a - π |z|²)) z`, which sends the open disc of area `a` onto `ℂ`, the
Riemann sphere minus `∞`, and pulls the Fubini–Study form scaled by `a` back to the area form. It is
the inverse of `OnePoint.sphereToDisc a` on the disc. -/
def discToSphere (a : ℝ) (z : ℂ) : ℂ :=
  √(π / (a - π * ‖z‖ ^ 2)) • z

/-- The open disc of radius `√(a / π)`, the disc of area `a`, is `{z | π |z|² < a}`. -/
private theorem mem_ball_sqrt_div_pi_iff {z : ℂ} : z ∈ ball (0 : ℂ) √(a / π) ↔ π * ‖z‖ ^ 2 < a := by
  rw [mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg z), lt_div_iff₀ pi_pos, mul_comm]

/-- The squared norm of `OnePoint.sphereToDisc a w`. -/
theorem norm_sq_sphereToDisc (ha : 0 ≤ a) (w : ℂ) :
    ‖sphereToDisc a w‖ ^ 2 = a * ‖w‖ ^ 2 / (π * (1 + ‖w‖ ^ 2)) := by
  rw [sphereToDisc, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  ring

/-- The squared norm of `OnePoint.discToSphere a z`, for `z` in the disc of area `a`. -/
theorem norm_sq_discToSphere {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) :
    ‖discToSphere a z‖ ^ 2 = π * ‖z‖ ^ 2 / (a - π * ‖z‖ ^ 2) := by
  rw [mem_ball_sqrt_div_pi_iff] at hz
  rw [discToSphere, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (div_nonneg pi_pos.le (sub_pos.2 hz).le)]
  ring

/-- `OnePoint.sphereToDisc a` takes values in the open disc of area `a`. -/
theorem sphereToDisc_mem_ball (ha : 0 < a) (w : ℂ) : sphereToDisc a w ∈ ball (0 : ℂ) √(a / π) := by
  rw [mem_ball_sqrt_div_pi_iff, norm_sq_sphereToDisc ha.le, mul_div_assoc',
    div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos, mul_pos ha pi_pos]

/-- `OnePoint.discToSphere a` is a left inverse of `OnePoint.sphereToDisc a`. -/
@[simp]
theorem discToSphere_sphereToDisc (ha : 0 < a) (w : ℂ) :
    discToSphere a (sphereToDisc a w) = w := by
  have h : a - π * ‖sphereToDisc a w‖ ^ 2 = a / (1 + ‖w‖ ^ 2) := by
    rw [norm_sq_sphereToDisc ha.le]
    field_simp
    ring
  rw [discToSphere, h, sphereToDisc, smul_smul, ← Real.sqrt_mul (by positivity)]
  convert one_smul ℝ w
  rw [Real.sqrt_eq_one]
  field_simp

/-- `OnePoint.sphereToDisc a` is a left inverse of `OnePoint.discToSphere a` on the disc of
area `a`. -/
theorem sphereToDisc_discToSphere {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) :
    sphereToDisc a (discToSphere a z) = z := by
  have hz' := mem_ball_sqrt_div_pi_iff.1 hz
  have hpos : 0 < a - π * ‖z‖ ^ 2 := sub_pos.2 hz'
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hz'
  have h : 1 + ‖discToSphere a z‖ ^ 2 = a / (a - π * ‖z‖ ^ 2) := by
    rw [norm_sq_discToSphere hz]
    field_simp
    ring
  rw [sphereToDisc, h, discToSphere, smul_smul, ← Real.sqrt_mul (by positivity)]
  convert one_smul ℝ z
  rw [Real.sqrt_eq_one]
  field_simp

/-- `OnePoint.sphereToDisc a` is smooth, indeed real-analytic, on all of `ℂ`. -/
theorem contDiff_sphereToDisc (ha : 0 < a) : ContDiff ℝ n (sphereToDisc a) := by
  refine ContDiff.smul (ContDiff.sqrt ?_ fun w ↦ by positivity) contDiff_id
  exact contDiff_const.div (contDiff_const.mul (contDiff_const.add (contDiff_norm_sq ℝ)))
    fun w ↦ by positivity

/-- `OnePoint.discToSphere a` is smooth, indeed real-analytic, on the disc of area `a`. -/
theorem contDiffOn_discToSphere : ContDiffOn ℝ n (discToSphere a) (ball (0 : ℂ) √(a / π)) := by
  refine ContDiffOn.smul (ContDiffOn.sqrt ?_ fun z hz ↦ ?_) contDiffOn_id
  · exact contDiffOn_const.div
      (contDiffOn_const.sub (contDiffOn_const.mul (contDiff_norm_sq ℝ).contDiffOn))
      fun z hz ↦ (sub_pos.2 (mem_ball_sqrt_div_pi_iff.1 hz)).ne'
  · exact (div_pos pi_pos (sub_pos.2 (mem_ball_sqrt_div_pi_iff.1 hz))).ne'

/-! ### The area forms -/

/-- The derivative of the radial factor `s ↦ √(a / (π (1 + s)))` of `OnePoint.sphereToDisc a`. -/
private theorem hasDerivAt_sqrt_div_pi_mul_one_add (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s : ℝ ↦ √(a / (π * (1 + s))))
      (-(a * π) / (π * (1 + s)) ^ 2 / (2 * √(a / (π * (1 + s))))) s := by
  have hpos : 0 < π * (1 + s) := mul_pos pi_pos (by linarith)
  have h : HasDerivAt (fun s : ℝ ↦ a / (π * (1 + s))) (-(a * π) / (π * (1 + s)) ^ 2) s :=
    ((hasDerivAt_const s a).div (((hasDerivAt_id s).const_add 1).const_mul π)
      hpos.ne').congr_deriv (by simp)
  exact h.sqrt (div_pos ha hpos).ne'

/-- The derivative of the radial factor `s ↦ √(π / (a - π s))` of `OnePoint.discToSphere a`. -/
private theorem hasDerivAt_sqrt_pi_div_sub_pi_mul {s : ℝ} (hs : π * s < a) :
    HasDerivAt (fun s : ℝ ↦ √(π / (a - π * s)))
      (π * π / (a - π * s) ^ 2 / (2 * √(π / (a - π * s)))) s := by
  have hpos : 0 < a - π * s := sub_pos.2 hs
  have h : HasDerivAt (fun s : ℝ ↦ π / (a - π * s)) (π * π / (a - π * s) ^ 2) s :=
    ((hasDerivAt_const s π).div (((hasDerivAt_id s).const_mul π).const_sub a)
      hpos.ne').congr_deriv (by simp)
  exact h.sqrt (div_pos pi_pos hpos).ne'

/-- **`OnePoint.sphereToDisc a` pulls the area form back to `a ω_FS`.** Its derivative at `w`
multiplies the area form `Im (conj v₁ * v₂)` by `a ρ(w) = a / (π (1 + |w|²)²)`, the density of the
Fubini–Study form scaled by `a`. -/
theorem im_conj_mul_fderiv_sphereToDisc (ha : 0 < a) (w v₁ v₂ : ℂ) :
    (conj (fderiv ℝ (sphereToDisc a) w v₁) * fderiv ℝ (sphereToDisc a) w v₂).im =
      a * fubiniStudyDensity w * (conj v₁ * v₂).im := by
  rw [(hasDerivAt_sqrt_div_pi_mul_one_add ha (sq_nonneg ‖w‖)).im_conj_mul_fderiv_radial_smul
    (f := sphereToDisc a) fun _ ↦ rfl]
  congr 1
  have hpos : 0 < π * (1 + ‖w‖ ^ 2) := by positivity
  have hq : 0 < √(a / (π * (1 + ‖w‖ ^ 2))) := Real.sqrt_pos.2 (div_pos ha hpos)
  rw [fubiniStudyDensity_def]
  field_simp
  rw [Real.sq_sqrt (div_pos ha hpos).le]
  field_simp
  ring

/-- **`OnePoint.discToSphere a` pulls `a ω_FS` back to the area form**, in the affine coordinate:
at a point `z` of the disc of area `a`, `a ρ(f z) Im (conj (Df v₁) * Df v₂) = Im (conj v₁ * v₂)`. -/
theorem mul_fubiniStudyDensity_mul_im_conj_fderiv_discToSphere {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) √(a / π)) (v₁ v₂ : ℂ) :
    a * fubiniStudyDensity (discToSphere a z) *
        (conj (fderiv ℝ (discToSphere a) z v₁) * fderiv ℝ (discToSphere a) z v₂).im =
      (conj v₁ * v₂).im := by
  have hz' := mem_ball_sqrt_div_pi_iff.1 hz
  have hpos : 0 < a - π * ‖z‖ ^ 2 := sub_pos.2 hz'
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hz'
  have hq : 0 < √(π / (a - π * ‖z‖ ^ 2)) := Real.sqrt_pos.2 (div_pos pi_pos hpos)
  rw [fubiniStudyDensity_def, norm_sq_discToSphere hz,
    (hasDerivAt_sqrt_pi_div_sub_pi_mul hz').im_conj_mul_fderiv_radial_smul
      (f := discToSphere a) fun _ ↦ rfl,
    ← mul_assoc]
  conv_rhs => rw [← one_mul (conj v₁ * v₂).im]
  congr 1
  field_simp
  rw [Real.sq_sqrt (div_pos pi_pos hpos).le]
  field_simp
  ring

/-! ### The partial diffeomorphism onto the sphere minus a point -/

/-- **The open disc of area `a` is the Riemann sphere minus `∞`.** The map
`OnePoint.discToSphere a`, from the open disc of radius `√(a / π)` onto `{∞}ᶜ`, with inverse
`OnePoint.sphereToDisc a` read in the affine chart, as a partial diffeomorphism of every order. It
pulls the Fubini–Study form scaled by `a` back to the area form
(`OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_discPartialDiffeomorph`). -/
def discPartialDiffeomorph (a : ℝ) (ha : 0 < a) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ (OnePoint ℂ) n where
  toFun z := discToSphere a z
  invFun x := sphereToDisc a (affineChart x)
  source := ball (0 : ℂ) √(a / π)
  target := {(∞ : OnePoint ℂ)}ᶜ
  map_source' _ _ := coe_ne_infty _
  map_target' _ _ := sphereToDisc_mem_ball ha _
  left_inv' z hz := by rw [affineChart_coe, sphereToDisc_discToSphere hz]
  right_inv' x hx := by
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe w => rw [affineChart_coe, discToSphere_sphereToDisc ha]
  open_source := isOpen_ball
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun :=
    (contMDiff_coe_real.of_le le_top).comp_contMDiffOn contDiffOn_discToSphere.contMDiffOn
  contMDiffOn_invFun := by
    have h := contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ω) (x := ((0 : ℂ) : OnePoint ℂ))
    rw [chartAt_coe, affineChart_source] at h
    exact (contDiff_sphereToDisc ha).contMDiff.comp_contMDiffOn (h.of_le le_top)

theorem coe_discPartialDiffeomorph (ha : 0 < a) :
    ⇑(discPartialDiffeomorph a ha (n := n)) = (↑) ∘ discToSphere a :=
  (rfl)

@[simp]
theorem discPartialDiffeomorph_apply (ha : 0 < a) (z : ℂ) :
    discPartialDiffeomorph a ha (n := n) z = discToSphere a z :=
  (rfl)

/-- The inverse of `OnePoint.discPartialDiffeomorph a ha` at a finite point `w` is
`OnePoint.sphereToDisc a w`. -/
theorem discPartialDiffeomorph_symm_apply_coe (ha : 0 < a) (w : ℂ) :
    (discPartialDiffeomorph a ha (n := n)).symm w = sphereToDisc a w :=
  congrArg (sphereToDisc a) (affineChart_coe w)

@[simp]
theorem discPartialDiffeomorph_source (ha : 0 < a) :
    (discPartialDiffeomorph a ha (n := n)).source = ball (0 : ℂ) √(a / π) :=
  (rfl)

@[simp]
theorem discPartialDiffeomorph_target (ha : 0 < a) :
    (discPartialDiffeomorph a ha (n := n)).target = {(∞ : OnePoint ℂ)}ᶜ :=
  (rfl)

/-- The derivative of `OnePoint.discPartialDiffeomorph a ha` at a point of the disc, read in the
affine chart, is the derivative of `OnePoint.discToSphere a`. -/
theorem mfderiv_discPartialDiffeomorph (ha : 0 < a) {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discPartialDiffeomorph a ha (n := n)) z =
      fderiv ℝ (discToSphere a) z := by
  have hd : DifferentiableAt ℝ (discToSphere a) z :=
    (contDiffOn_discToSphere.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt
      (n := 1) one_ne_zero
  rw [coe_discPartialDiffeomorph,
    mfderiv_comp z ((contMDiff_coe_real _).mdifferentiableAt (by simp)) hd.mdifferentiableAt,
    mfderiv_coe_real, mfderiv_eq_fderiv]
  exact ContinuousLinearMap.id_comp _

/-- **The disc of area `a` embeds symplectically into the sphere of area `a`.** The partial
diffeomorphism `OnePoint.discPartialDiffeomorph a ha` from the open disc of area `a` onto the
Riemann sphere minus `∞` pulls the Fubini–Study form scaled by `a`, of total area `a`, back to the
area form `Im (conj v * w) = dx ∧ dy` of the disc. -/
theorem eval₂_smul_fubiniStudyForm_mfderiv_discPartialDiffeomorph (ha : 0 < a) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) √(a / π)) (v w : ℂ) :
    SmoothBundleForm.eval₂ (a • fubiniStudyForm) (discPartialDiffeomorph a ha (n := n) z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discPartialDiffeomorph a ha (n := n)) z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discPartialDiffeomorph a ha (n := n)) z w) =
      (conj v * w).im := by
  rw [SmoothForm.eval₂_smul]
  -- Read the Fubini–Study form in the affine coordinate of the finite point `f z`.
  refine (congrArg (a • ·) (eval₂_fubiniStudyForm_coe (discToSphere a z) _ _)).trans ?_
  rw [mfderiv_discPartialDiffeomorph ha hz, smul_eq_mul, ← mul_assoc]
  exact mul_fubiniStudyDensity_mul_im_conj_fderiv_discToSphere hz v w

end OnePoint
