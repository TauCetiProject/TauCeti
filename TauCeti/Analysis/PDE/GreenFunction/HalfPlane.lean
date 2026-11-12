/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Gradient
public import TauCeti.Analysis.PDE.GreenFunction.HalfSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian

/-!
# The Green kernel of a half-plane

Let `v` be a unit vector of the plane `ℂ` and let `H = {z | 0 < ⟪v, z⟫}` be the open half-plane
with inward unit normal `v`, bounded by the line `⟪v, z⟫ = 0`. Write `a* = (ℝ ∙ v)ᗮ.reflection a`
for the mirror image of a point `a` in that line. The method of images gives the Dirichlet Green
kernel of `H` from the logarithmic kernel `Φ = TauCeti.planarNewtonianKernel`,
`Φ z = -(2π)⁻¹ log ‖z‖`:

`G(a, z) = Φ(z - a) - Φ(z - a*)`

(`TauCeti.planarGreenKernelHalfPlane`). This is the case `n = 2` that the Newtonian
normalization of `TauCeti.halfSpaceGreenKernel` does not cover. The kernel

* is symmetric in its two arguments and odd under reflection in the boundary line, in either
  argument;
* vanishes when either argument lies on the boundary line, is positive at distinct points of
  `H` and nonnegative on its closure away from the pole;
* is harmonic away from the pole and its image, and its regular part `G(a, ·) - Φ(· - a)` is
  harmonic throughout `H`;
* tends to `0` at infinity;
* has distributional Laplacian `-Δ G(a, ·) = δₐ - δ_{a*}` on the whole plane, hence
  `-Δ G(a, ·) = δₐ` against `C²` functions with compact support in the closed half-plane;
* has outward normal derivative on the boundary line equal to minus the half-space Poisson
  kernel of dimension two, `⟪v, a⟫ / (π ‖z - a‖²)`, in the coordinates
  `Complex.orthonormalBasisOneI` of `EuclideanSpace ℝ (Fin 2)`, which is the kernel of the
  half-space Poisson integral `TauCeti.halfSpacePoissonIntegral` in dimension two.

The kernel serves the representation of solutions near a flat boundary in dimension two, where
the image construction with the logarithmic kernel replaces the power-law kernel of the
higher-dimensional half-space.

## Main declarations

* `TauCeti.planarGreenKernelHalfPlane`: the Green kernel of the half-plane.
* `TauCeti.planarGreenKernelHalfPlane_pos`: positivity in the open half-plane.
* `TauCeti.harmonicOnNhd_planarGreenKernelHalfPlane`: harmonicity away from the pole.
* `TauCeti.tendsto_planarGreenKernelHalfPlane_cocompact`: decay at infinity.
* `TauCeti.integral_laplacian_mul_planarGreenKernelHalfPlane_of_inner_neg`: `-Δ G(a, ·) = δₐ`.
* `TauCeti.fderiv_planarGreenKernelHalfPlane_normal`: the outward normal derivative on the
  boundary is minus the Poisson kernel.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.4 (Green's function for a
  half-space by reflection).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.5.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Topology
open scoped RealInnerProductSpace

local notation "U" => {w : ℂ // ‖w‖ = 1}

/-- The Dirichlet Green kernel of the half-plane `0 < ⟪v, z⟫` with inward unit normal `v`,
evaluated at the pole `a` and the variable `z`: the logarithmic kernel with pole `a` minus the
logarithmic kernel with pole at the mirror image of `a` in the boundary line. -/
def planarGreenKernelHalfPlane (v : {w : ℂ // ‖w‖ = 1}) (a z : ℂ) : ℝ :=
  planarNewtonianKernel (z - a) - planarNewtonianKernel (z - (ℝ ∙ (v : ℂ))ᗮ.reflection a)

/-- The method-of-images formula for the half-plane Green kernel. -/
theorem planarGreenKernelHalfPlane_def (v : U) (a z : ℂ) :
    planarGreenKernelHalfPlane v a z =
      planarNewtonianKernel (z - a) - planarNewtonianKernel (z - (ℝ ∙ (v : ℂ))ᗮ.reflection a) := by
  rw [planarGreenKernelHalfPlane]

/-- The half-plane Green kernel is symmetric in its pole and variable. -/
theorem planarGreenKernelHalfPlane_comm (v : U) (a z : ℂ) :
    planarGreenKernelHalfPlane v a z = planarGreenKernelHalfPlane v z a := by
  rw [planarGreenKernelHalfPlane_def, planarGreenKernelHalfPlane_def,
    planarNewtonianKernel_sub_comm z a]
  congr 1
  exact planarNewtonianKernel_eq_of_norm_eq (by
    rw [norm_sub_reflection_orthogonal_singleton, norm_sub_rev])

/-- The half-plane Green kernel is odd under reflection of its variable in the boundary line. -/
@[simp] theorem planarGreenKernelHalfPlane_reflection_right (v : U) (a z : ℂ) :
    planarGreenKernelHalfPlane v a ((ℝ ∙ (v : ℂ))ᗮ.reflection z) =
      -planarGreenKernelHalfPlane v a z := by
  rw [planarGreenKernelHalfPlane_def, planarGreenKernelHalfPlane_def, neg_sub]
  congr 1
  · exact planarNewtonianKernel_eq_of_norm_eq
      (norm_sub_reflection_orthogonal_singleton (v : ℂ) a z).symm
  · exact planarNewtonianKernel_eq_of_norm_eq (by rw [← map_sub, LinearIsometryEquiv.norm_map])

/-- The half-plane Green kernel is odd under reflection of its pole in the boundary line. -/
@[simp] theorem planarGreenKernelHalfPlane_reflection_left (v : U) (a z : ℂ) :
    planarGreenKernelHalfPlane v ((ℝ ∙ (v : ℂ))ᗮ.reflection a) z =
      -planarGreenKernelHalfPlane v a z := by
  rw [planarGreenKernelHalfPlane_comm, planarGreenKernelHalfPlane_reflection_right,
    planarGreenKernelHalfPlane_comm]

/-- The half-plane Green kernel vanishes when its variable lies on the boundary line. -/
@[simp] theorem planarGreenKernelHalfPlane_eq_zero_of_inner_eq_zero_right {v : U} (a : ℂ)
    {z : ℂ} (hz : ⟪(v : ℂ), z⟫_ℝ = 0) : planarGreenKernelHalfPlane v a z = 0 := by
  rw [planarGreenKernelHalfPlane_def, sub_eq_zero]
  exact planarNewtonianKernel_eq_of_norm_eq
    (norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero a hz).symm

/-- The half-plane Green kernel vanishes when its pole lies on the boundary line. -/
@[simp] theorem planarGreenKernelHalfPlane_eq_zero_of_inner_eq_zero_left {v : U} {a : ℂ}
    (ha : ⟪(v : ℂ), a⟫_ℝ = 0) (z : ℂ) : planarGreenKernelHalfPlane v a z = 0 := by
  rw [planarGreenKernelHalfPlane_def, reflection_orthogonal_singleton_eq_self_of_inner_eq_zero ha,
    sub_self]

/-- The half-plane Green kernel is `(2π)⁻¹ (log ‖z - a*‖ - log ‖z - a‖)`. -/
private theorem planarGreenKernelHalfPlane_eq_mul_log_sub (v : U) (a z : ℂ) :
    planarGreenKernelHalfPlane v a z =
      (2 * Real.pi)⁻¹ * (Real.log ‖z - (ℝ ∙ (v : ℂ))ᗮ.reflection a‖ - Real.log ‖z - a‖) := by
  rw [planarGreenKernelHalfPlane_def, planarNewtonianKernel_def, planarNewtonianKernel_def]
  ring

/-- The half-plane Green kernel is positive at distinct points of the open half-plane. -/
theorem planarGreenKernelHalfPlane_pos {v : U} {a z : ℂ} (ha : 0 < ⟪(v : ℂ), a⟫_ℝ)
    (hz : 0 < ⟪(v : ℂ), z⟫_ℝ) (hza : z ≠ a) : 0 < planarGreenKernelHalfPlane v a z := by
  rw [planarGreenKernelHalfPlane_eq_mul_log_sub]
  have hlt := norm_sub_lt_norm_sub_reflection_orthogonal_singleton ha hz
  exact mul_pos (by positivity) (sub_pos.2 (Real.log_lt_log (norm_pos_iff.2 (sub_ne_zero.2 hza))
    hlt))

/-- The half-plane Green kernel is nonnegative on the closed half-plane away from its pole. -/
theorem planarGreenKernelHalfPlane_nonneg {v : U} {a z : ℂ} (ha : 0 ≤ ⟪(v : ℂ), a⟫_ℝ)
    (hz : 0 ≤ ⟪(v : ℂ), z⟫_ℝ) (hza : z ≠ a) : 0 ≤ planarGreenKernelHalfPlane v a z := by
  rw [planarGreenKernelHalfPlane_eq_mul_log_sub]
  have hsq := norm_sub_reflection_orthogonal_singleton_sq v.2 a z
  have hle : ‖z - a‖ ≤ ‖z - (ℝ ∙ (v : ℂ))ᗮ.reflection a‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
      rw [hsq]; nlinarith [mul_nonneg ha hz])
  exact mul_nonneg (by positivity)
    (sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hza)) hle))

/-- The half-plane Green kernel is harmonic away from its pole and the image of the pole. -/
theorem harmonicAt_planarGreenKernelHalfPlane {v : U} {a z : ℂ} (hza : z ≠ a)
    (hza' : z ≠ (ℝ ∙ (v : ℂ))ᗮ.reflection a) : HarmonicAt (planarGreenKernelHalfPlane v a) z :=
  (harmonicAt_planarNewtonianKernel_sub hza).sub (harmonicAt_planarNewtonianKernel_sub hza')

/-- For a pole in the closed half-plane, the half-plane Green kernel is harmonic on the open
half-plane punctured at the pole. -/
theorem harmonicOnNhd_planarGreenKernelHalfPlane {v : U} {a : ℂ} (ha : 0 ≤ ⟪(v : ℂ), a⟫_ℝ) :
    HarmonicOnNhd (planarGreenKernelHalfPlane v a) ({z : ℂ | 0 < ⟪(v : ℂ), z⟫_ℝ} \ {a}) :=
  fun _ hz ↦ harmonicAt_planarGreenKernelHalfPlane hz.2
    (ne_reflection_orthogonal_singleton_of_inner_ne_neg (by linarith [hz.1.out]))

/-- The half-plane Green kernel is harmonic in its pole away from the variable and its image. -/
theorem harmonicAt_planarGreenKernelHalfPlane_left {v : U} {a z : ℂ} (haz : a ≠ z)
    (haz' : a ≠ (ℝ ∙ (v : ℂ))ᗮ.reflection z) :
    HarmonicAt (fun b ↦ planarGreenKernelHalfPlane v b z) a := by
  simp_rw [planarGreenKernelHalfPlane_comm v _ z]
  exact harmonicAt_planarGreenKernelHalfPlane haz haz'

/-- For a pole in the closed half-plane, the regular part `G(a, ·) - Φ(· - a)` of the half-plane
Green kernel is harmonic on the whole open half-plane, including at the pole. -/
theorem harmonicOnNhd_planarGreenKernelHalfPlane_sub_planarNewtonianKernel {v : U} {a : ℂ}
    (ha : 0 ≤ ⟪(v : ℂ), a⟫_ℝ) :
    HarmonicOnNhd (fun z ↦ planarGreenKernelHalfPlane v a z - planarNewtonianKernel (z - a))
      {z : ℂ | 0 < ⟪(v : ℂ), z⟫_ℝ} := by
  intro z hz
  simp_rw [planarGreenKernelHalfPlane_def, sub_sub_cancel_left]
  exact (harmonicAt_planarNewtonianKernel_sub
    (ne_reflection_orthogonal_singleton_of_inner_ne_neg (by linarith [hz.out]))).neg

/-- **The half-plane Green kernel vanishes at infinity.** -/
theorem tendsto_planarGreenKernelHalfPlane_cocompact (v : U) (a : ℂ) :
    Tendsto (planarGreenKernelHalfPlane v a) (cocompact ℂ) (𝓝 0) := by
  have h := (tendsto_planarNewtonianKernel_sub_sub_cocompact a).sub
    (tendsto_planarNewtonianKernel_sub_sub_cocompact ((ℝ ∙ (v : ℂ))ᗮ.reflection a))
  rw [sub_zero] at h
  refine h.congr fun z ↦ ?_
  rw [planarGreenKernelHalfPlane_def]
  ring

/-- **The distributional Laplacian of the half-plane Green kernel on the plane.** For every
`C²` function `f` with compact support on `ℂ`, `∫ Δ f · G(a, ·) = -f a + f a*`: that is,
`-Δ G(a, ·) = δₐ - δ_{a*}` in the sense of distributions. -/
theorem integral_laplacian_mul_planarGreenKernelHalfPlane {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (v : U) (a : ℂ) :
    ∫ z, Δ f z * planarGreenKernelHalfPlane v a z =
      -f a + f ((ℝ ∙ (v : ℂ))ᗮ.reflection a) := by
  simp_rw [planarGreenKernelHalfPlane_def, mul_sub]
  rw [integral_sub (integrable_laplacian_mul_planarNewtonianKernel_sub hf hc a)
      (integrable_laplacian_mul_planarNewtonianKernel_sub hf hc _),
    integral_laplacian_mul_planarNewtonianKernel_sub hf hc,
    integral_laplacian_mul_planarNewtonianKernel_sub hf hc]
  ring

/-- **The half-plane Green kernel is a fundamental solution of `-Δ` in the half-plane.** For a
pole `a` in the open half-plane and every `C²` function `f` with compact support that vanishes
on the open complementary half-plane, `∫ Δ f · G(a, ·) = -f a`. -/
theorem integral_laplacian_mul_planarGreenKernelHalfPlane_of_inner_neg {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {v : U} {a : ℂ} (ha : 0 < ⟪(v : ℂ), a⟫_ℝ)
    (hf₀ : ∀ z, ⟪(v : ℂ), z⟫_ℝ < 0 → f z = 0) :
    ∫ z, Δ f z * planarGreenKernelHalfPlane v a z = -f a := by
  rw [integral_laplacian_mul_planarGreenKernelHalfPlane hf hc,
    hf₀ ((ℝ ∙ (v : ℂ))ᗮ.reflection a) (by rw [inner_reflection_orthogonal_singleton]; linarith),
    add_zero]

/-- The Fréchet derivative of the half-plane Green kernel away from its pole and the image of
the pole. -/
theorem hasFDerivAt_planarGreenKernelHalfPlane {v : U} {a z : ℂ} (hza : z ≠ a)
    (hza' : z ≠ (ℝ ∙ (v : ℂ))ᗮ.reflection a) :
    HasFDerivAt (planarGreenKernelHalfPlane v a)
      ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a) -
        (-(2 * Real.pi)⁻¹ * (‖z - (ℝ ∙ (v : ℂ))ᗮ.reflection a‖ ^ 2)⁻¹) •
          innerSL ℝ (z - (ℝ ∙ (v : ℂ))ᗮ.reflection a)) z :=
  (hasFDerivAt_planarNewtonianKernel_sub hza).sub (hasFDerivAt_planarNewtonianKernel_sub hza')

/-- On the boundary line, the derivative of the half-plane Green kernel in the outward normal
direction `-v` is `-⟪v, a⟫ / (π ‖z - a‖²)`. -/
theorem fderiv_planarGreenKernelHalfPlane_normal_eq_neg_div {v : U} {a z : ℂ}
    (hz : ⟪(v : ℂ), z⟫_ℝ = 0) (hza : z ≠ a) :
    fderiv ℝ (planarGreenKernelHalfPlane v a) z (-(v : ℂ)) =
      -(⟪(v : ℂ), a⟫_ℝ / (Real.pi * ‖z - a‖ ^ 2)) := by
  have hza' : z ≠ (ℝ ∙ (v : ℂ))ᗮ.reflection a := by
    by_cases ha : ⟪(v : ℂ), a⟫_ℝ = 0
    · rwa [reflection_orthogonal_singleton_eq_self_of_inner_eq_zero ha]
    · exact ne_reflection_orthogonal_singleton_of_inner_ne_neg fun h ↦ ha (by linarith)
  have hnorm := norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero a hz
  rw [(hasFDerivAt_planarGreenKernelHalfPlane hza hza').fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, hnorm, inner_sub_left,
    inner_neg_right]
  rw [real_inner_comm (v : ℂ) z, real_inner_comm (v : ℂ) a,
    real_inner_comm (v : ℂ) ((ℝ ∙ (v : ℂ))ᗮ.reflection a), inner_reflection_orthogonal_singleton,
    hz]
  have hpos : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
  field_simp
  ring

/-- **The outward normal derivative of the half-plane Green kernel is minus the Poisson kernel.**
On the boundary line, the derivative of `G(a, ·)` in the outward normal direction `-v` is minus
the half-space Poisson kernel of dimension two, read in the coordinates
`Complex.orthonormalBasisOneI` of `EuclideanSpace ℝ (Fin 2)`. -/
theorem fderiv_planarGreenKernelHalfPlane_normal {v : U} {a z : ℂ}
    (hz : ⟪(v : ℂ), z⟫_ℝ = 0) (hza : z ≠ a) :
    fderiv ℝ (planarGreenKernelHalfPlane v a) z (-(v : ℂ)) =
      -halfSpacePoissonKernel 2
        ⟨Complex.orthonormalBasisOneI.repr v, by simpa using v.2⟩
        (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr z) := by
  rw [fderiv_planarGreenKernelHalfPlane_normal_eq_neg_div hz hza,
    halfSpacePoissonKernel_eq_div,
    LinearIsometryEquiv.inner_map_map, ← map_sub, LinearIsometryEquiv.norm_map]
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = Real.pi := by
    simp [Measure.real, Real.pi_pos.le]
  rw [hvol]
  have hpos : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
  field_simp
  norm_num

end TauCeti

end
