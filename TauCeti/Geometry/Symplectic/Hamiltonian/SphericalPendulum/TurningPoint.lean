/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The turning points of the spherical pendulum

On the fibre `F⁻¹(h, j)` of the energy–momentum map `F = (H, J)` of the spherical pendulum the
height `z = q₃` and the vertical momentum satisfy `p₃² = 2 (h - z) (1 - z²) - j²`
(`TauCeti.sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace`). The heights occurring in the fibre
are therefore those `z ∈ [-1, 1]` with `z ≤ h` where this cubic radicand is nonnegative
(`TauCeti.image_apply_two_preimage_sphericalPendulumEnergyMomentum`), and the motion of the height
turns around at its lowest and highest values `z₋` and `z₊`, the **turning points**
(`TauCeti.sphericalPendulumLowerTurningPoint`, `TauCeti.sphericalPendulumUpperTurningPoint`),
defined as the infimum and the supremum of the heights of the fibre.

This file studies them at the values `(h, j)` with `j ≠ 0` lying strictly above the curve of
relative equilibria, that is, with `V_j(z) < h` for some height `z ∈ (-1, 1)`, where `V_j` is the
effective potential (`TauCeti.sphericalPendulumEffectivePotential`). There the turning points
satisfy `-1 < z₋ < z₊ < 1`, the heights of the fibre form the interval `[z₋, z₊]`, and the
radicand factors as

`2 (h - z) (1 - z²) - j² = 2 (z - z₋) (z₊ - z) (z₃ - z)`,  `z₃ = h - z₋ - z₊ > 1`.

So `z₋` and `z₊` are simple roots of the radicand, and its third root `z₃` lies above the north
pole. Simple roots move continuously with the coefficients: both turning points are continuous
functions of `(h, j)` on this set of values. These are the inputs for writing the quadratures of
the pendulum, such as its rotation angle, as integrals with continuous integrands in the angle
`θ` of the substitution `z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ`.

On the axis `j = 0`, for `h > -1`, the fibre heights form `[-1, min h 1]`, so `z₋ = -1` and
`z₊ = min h 1`, and both turning points are continuous at `(h, 0)`. For `h ≠ 1` the radicand
`2 (h - z) (1 - z²)` again factors with the third root `max h 1 > z₊`, and the same substitution
shows that height quadratures with weights continuous up to the poles are continuous across the
axis. This is what makes the period continuous along loops crossing the axis away from the
focus–focus value `(1, 0)`.

## Main declarations

* `TauCeti.sphericalPendulumLowerTurningPoint`, `TauCeti.sphericalPendulumUpperTurningPoint`: the
  lowest and the highest height on the fibre `F⁻¹(h, j)`.
* `TauCeti.image_apply_two_preimage_sphericalPendulumEnergyMomentum_eq_Icc`: the heights of the
  fibre form the interval `[z₋, z₊]`.
* `TauCeti.two_mul_sub_mul_one_sub_sq_sub_sq_eq`: the factorization of the radicand.
* `TauCeti.two_mul_sub_mul_one_sub_sq_sub_sq_pos`,
  `TauCeti.two_mul_sub_mul_one_sub_sq_sub_sq_nonpos`: the radicand is positive strictly between the
  turning points and nonpositive elsewhere below the north pole.
* `TauCeti.three_mul_sphericalPendulumLowerTurningPoint_sq_sub_pos`,
  `TauCeti.three_mul_sphericalPendulumUpperTurningPoint_sq_sub_neg`: the radicand increases through
  `z₋` and decreases through `z₊`.
* `TauCeti.snd_two_ne_zero_iff_apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace`: on the
  fibre, the vertical momentum vanishes exactly at the turning points.
* `TauCeti.integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq`: integrals over `(-1, 1)`
  against the inverse square root of the radicand run between the turning points.
* `TauCeti.integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq_integral_sin`: the sine
  substitution turns such an integral into one over `[-π/2, π/2]` with a regular denominator,
  positive by `TauCeti.two_mul_sub_sub_sub_add_mul_sin_pos`.
* `TauCeti.continuousOn_sphericalPendulumLowerTurningPoint`,
  `TauCeti.continuousOn_sphericalPendulumUpperTurningPoint`: continuity of the turning points.
* `TauCeti.continuousOn_integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq`: such integrals are
  continuous in `(h, j)` for continuous weights.
* `TauCeti.mem_sphericalPendulumTurningPointDomain_of_le_one`: the circles of radius `r ≤ 1` about
  the focus–focus value `(1, 0)` run above the curve of relative equilibria off the axis `j = 0`.
* `TauCeti.isOpen_sphericalPendulumTurningPointDomain`: these values form an open set.
* `TauCeti.sphericalPendulumLowerTurningPoint_zero_right`,
  `TauCeti.sphericalPendulumUpperTurningPoint_zero_right`,
  `TauCeti.continuousAt_sphericalPendulumLowerTurningPoint_zero_right`,
  `TauCeti.continuousAt_sphericalPendulumUpperTurningPoint_zero_right`: the turning points on the
  axis `j = 0` and their continuity there.
* `TauCeti.continuousAt_integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq`: height quadratures are
  continuous across the axis away from the poles and from the focus–focus value.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

/-- The energy–momentum values with nonzero vertical angular momentum strictly above the curve of
relative equilibria: the domain where the two turning points are distinct and avoid the poles. -/
def sphericalPendulumTurningPointDomain : Set (ℝ × ℝ) :=
  {c | c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1, sphericalPendulumEffectivePotential c.2 z < c.1}

/-- Membership in the domain of distinct nonpolar turning points. -/
@[simp]
theorem mem_sphericalPendulumTurningPointDomain_iff {c : ℝ × ℝ} :
    c ∈ sphericalPendulumTurningPointDomain ↔
      c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1, sphericalPendulumEffectivePotential c.2 z < c.1 := (Iff.rfl)

/-- A value `(h, j)` with `j ≠ 0` and `j² < 2 h` lies strictly above the curve of relative
equilibria, since the effective potential at the equator is `V_j(0) = j² / 2 < h`. -/
theorem mem_sphericalPendulumTurningPointDomain_of_sq_lt {h j : ℝ} (hj : j ≠ 0)
    (hjh : j ^ 2 < 2 * h) : (h, j) ∈ sphericalPendulumTurningPointDomain :=
  ⟨hj, 0, ⟨by norm_num, by norm_num⟩, by
    rw [sphericalPendulumEffectivePotential_def,
      show j ^ 2 / (2 * (1 - (0 : ℝ) ^ 2)) + 0 = j ^ 2 / 2 by ring]
    linarith⟩

open Real in
/-- The counterclockwise circles of radius `0 < r ≤ 1` about the focus–focus value `(1, 0)` run
above the curve of relative equilibria off the axis `j = 0`. -/
theorem mem_sphericalPendulumTurningPointDomain_of_le_one {r t : ℝ} (hr : 0 < r) (hr₂ : r ≤ 1)
    (ht : sin t ≠ 0) : (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain := by
  refine mem_sphericalPendulumTurningPointDomain_of_sq_lt (mul_ne_zero hr.ne' ht) ?_
  -- `2 (1 + r cos t) - r² sin² t = (1 + r cos t)² + 1 - r²`, and `cos t > -1` off the axis.
  have hc : 0 < 1 + cos t := by
    rcases (neg_one_le_cos t).lt_or_eq with hc | hc
    · linarith
    · exact absurd (by linear_combination sin_sq_add_cos_sq t + (cos t - 1) * hc)
        (pow_ne_zero 2 ht)
  have hrc : 0 < r * (1 + cos t) := mul_pos hr hc
  have key : 2 * (1 + r * cos t) - (r * sin t) ^ 2 = (1 + r * cos t) ^ 2 + (1 - r ^ 2) := by
    linear_combination -r ^ 2 * sin_sq_add_cos_sq t
  nlinarith [mul_pos hrc (by linarith : 0 < 2 - r + r * cos t)]

/-- The values with nonzero vertical angular momentum strictly above the curve of relative
equilibria form an open set. -/
theorem isOpen_sphericalPendulumTurningPointDomain :
    IsOpen sphericalPendulumTurningPointDomain := by
  have : sphericalPendulumTurningPointDomain = {c : ℝ × ℝ | c.2 ≠ 0} ∩
      ⋃ z ∈ Ioo (-1 : ℝ) 1, {c | sphericalPendulumEffectivePotential c.2 z < c.1} := by
    ext c
    simp [sphericalPendulumTurningPointDomain]
  rw [this]
  refine (isOpen_ne_fun continuous_snd continuous_const).inter
    (isOpen_biUnion fun z _ ↦ isOpen_lt ?_ continuous_fst)
  simp only [sphericalPendulumEffectivePotential_def]
  fun_prop

/-- The **lower turning point** `z₋` of the spherical pendulum at energy `h` and vertical angular
momentum `j`: the infimum of the heights `q₃` of the points of the fibre `F⁻¹(h, j)` of the
energy–momentum map. -/
noncomputable def sphericalPendulumLowerTurningPoint (h j : ℝ) : ℝ :=
  sInf ((fun x ↦ x.1 2) ''
    (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}))

/-- The **upper turning point** `z₊` of the spherical pendulum at energy `h` and vertical angular
momentum `j`: the supremum of the heights `q₃` of the points of the fibre `F⁻¹(h, j)` of the
energy–momentum map. -/
noncomputable def sphericalPendulumUpperTurningPoint (h j : ℝ) : ℝ :=
  sSup ((fun x ↦ x.1 2) ''
    (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}))

/-- The heights `z ∈ [-1, 1]` with `z ≤ h` and `j² ≤ 2 (h - z) (1 - z²)`, which are the heights
of the fibre over `(h, j)`. -/
private def fibreHeights (h j : ℝ) : Set ℝ :=
  {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)}

/-- The lower turning point is the infimum of the heights `z ∈ [-1, 1]` with `z ≤ h` and
`j² ≤ 2 (h - z) (1 - z²)`. -/
theorem sphericalPendulumLowerTurningPoint_eq_sInf (h j : ℝ) :
    sphericalPendulumLowerTurningPoint h j =
      sInf {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} := by
  rw [sphericalPendulumLowerTurningPoint, image_apply_two_preimage_sphericalPendulumEnergyMomentum]

/-- The upper turning point is the supremum of the heights `z ∈ [-1, 1]` with `z ≤ h` and
`j² ≤ 2 (h - z) (1 - z²)`. -/
theorem sphericalPendulumUpperTurningPoint_eq_sSup (h j : ℝ) :
    sphericalPendulumUpperTurningPoint h j =
      sSup {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} := by
  rw [sphericalPendulumUpperTurningPoint, image_apply_two_preimage_sphericalPendulumEnergyMomentum]

/-! ### The heights of a fibre -/

private theorem isClosed_fibreHeights (h j : ℝ) : IsClosed (fibreHeights h j) := by
  simp only [fibreHeights, ofPred_and, ofPred_mem_eq]
  exact isClosed_Icc.inter ((isClosed_le continuous_id continuous_const).inter
    (isClosed_le continuous_const (by fun_prop)))

private theorem bddBelow_fibreHeights (h j : ℝ) : BddBelow (fibreHeights h j) :=
  ⟨-1, fun _ hz ↦ hz.1.1⟩

private theorem bddAbove_fibreHeights (h j : ℝ) : BddAbove (fibreHeights h j) :=
  ⟨1, fun _ hz ↦ hz.1.2⟩

/-- A height `z ∈ (-1, 1)` where the radicand is positive belongs to the fibre. -/
private theorem mem_fibreHeights_of_lt {h j z : ℝ} (hz : z ∈ Ioo (-1) 1)
    (hlt : j ^ 2 < 2 * (h - z) * (1 - z ^ 2)) : z ∈ fibreHeights h j := by
  have h₁ : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  refine ⟨Ioo_subset_Icc_self hz, ?_, hlt.le⟩
  by_contra hzh
  nlinarith [mul_pos (sub_pos.2 (not_le.1 hzh)) h₁, sq_nonneg j]

/-- For `j ≠ 0` the fibre contains neither pole. -/
private theorem mem_Ioo_of_mem_fibreHeights {h j z : ℝ} (hj : j ≠ 0)
    (hz : z ∈ fibreHeights h j) : z ∈ Ioo (-1) 1 := by
  obtain ⟨⟨h₁, h₂⟩, -, hjz⟩ := hz
  have hj2 : 0 < j ^ 2 := by positivity
  refine ⟨lt_of_le_of_ne h₁ ?_, lt_of_le_of_ne h₂ ?_⟩ <;> rintro rfl <;> nlinarith

/-- Above the curve of relative equilibria the fibre contains a height of positive radicand. -/
private theorem exists_mem_fibreHeights {h j z₀ : ℝ} (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    z₀ ∈ fibreHeights h j ∧ j ^ 2 < 2 * (h - z₀) * (1 - z₀ ^ 2) := by
  have hlt := (sphericalPendulumEffectivePotential_lt_iff
    ((sq_lt_one_iff_abs_lt_one _).2 (abs_lt.2 hz₀))).1 hV
  exact ⟨mem_fibreHeights_of_lt hz₀ hlt, hlt⟩

/-- Strict positivity of the radicand away from the poles gives an interior fibre height. -/
private theorem mem_interior_fibreHeights_of_lt {h j z : ℝ} (hz : z ∈ Ioo (-1) 1)
    (hlt : j ^ 2 < 2 * (h - z) * (1 - z ^ 2)) : z ∈ interior (fibreHeights h j) := by
  have hcont : Continuous fun z : ℝ ↦ 2 * (h - z) * (1 - z ^ 2) := by fun_prop
  exact mem_interior_iff_mem_nhds.2
    ((((hcont.tendsto z).eventually_const_lt hlt).and (isOpen_Ioo.mem_nhds hz)).mono
      fun _ hx ↦ mem_fibreHeights_of_lt hx.2 hx.1)

/-- At the infimum of the heights of a nonempty fibre with `j ≠ 0` the radicand vanishes: a
height of positive radicand has lower heights of the fibre next to it. -/
private theorem radicand_sInf_eq_zero {h j : ℝ} (hj : j ≠ 0) (hne : (fibreHeights h j).Nonempty) :
    2 * (h - sInf (fibreHeights h j)) * (1 - sInf (fibreHeights h j) ^ 2) - j ^ 2 = 0 := by
  set a := sInf (fibreHeights h j)
  have ha : a ∈ fibreHeights h j :=
    (isClosed_fibreHeights h j).csInf_mem hne (bddBelow_fibreHeights h j)
  refine le_antisymm ?_ (sub_nonneg.2 ha.2.2)
  by_contra hpos
  have hmem := mem_interior_fibreHeights_of_lt (mem_Ioo_of_mem_fibreHeights hj ha)
    (by linarith : j ^ 2 < 2 * (h - a) * (1 - a ^ 2))
  have hsub : fibreHeights h j ⊆ Ici a := fun _ hz ↦ csInf_le (bddBelow_fibreHeights h j) hz
  have := interior_mono hsub hmem
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at this

/-- At the supremum of the heights of a nonempty fibre with `j ≠ 0` the radicand vanishes. -/
private theorem radicand_sSup_eq_zero {h j : ℝ} (hj : j ≠ 0) (hne : (fibreHeights h j).Nonempty) :
    2 * (h - sSup (fibreHeights h j)) * (1 - sSup (fibreHeights h j) ^ 2) - j ^ 2 = 0 := by
  set b := sSup (fibreHeights h j)
  have hb : b ∈ fibreHeights h j :=
    (isClosed_fibreHeights h j).csSup_mem hne (bddAbove_fibreHeights h j)
  refine le_antisymm ?_ (sub_nonneg.2 hb.2.2)
  by_contra hpos
  have hmem := mem_interior_fibreHeights_of_lt (mem_Ioo_of_mem_fibreHeights hj hb)
    (by linarith : j ^ 2 < 2 * (h - b) * (1 - b ^ 2))
  have hsub : fibreHeights h j ⊆ Iic b := fun _ hz ↦ le_csSup (bddAbove_fibreHeights h j) hz
  have := interior_mono hsub hmem
  simp only [interior_Iic, mem_Iio, lt_self_iff_false] at this

/-- **Vieta.** If the radicand `2 (h - z) (1 - z²) - j²`, a cubic in `z` with leading coefficient
`2` and sum of roots `h`, vanishes at two distinct heights `a` and `b`, then its third root is
`h - a - b`. -/
private theorem radicand_eq_of_ne {h j a b : ℝ} (hab : a ≠ b)
    (ha : 2 * (h - a) * (1 - a ^ 2) - j ^ 2 = 0) (hb : 2 * (h - b) * (1 - b ^ 2) - j ^ 2 = 0)
    (z : ℝ) :
    2 * (h - z) * (1 - z ^ 2) - j ^ 2 = 2 * (z - a) * (b - z) * (h - a - b - z) := by
  have hK : a ^ 2 + a * b + b ^ 2 - h * (a + b) - 1 = 0 := by
    have : (a - b) * (a ^ 2 + a * b + b ^ 2 - h * (a + b) - 1) = 0 := by
      linear_combination (ha - hb) / 2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab)
  linear_combination ha + 2 * (z - a) * hK

/-! ### The turning points above the curve of relative equilibria -/

section Regular

variable {h j z₀ : ℝ}

/-- The turning points lie in the fibre, the radicand vanishes there, and they are distinct. -/
private theorem turningPoint_spec (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumLowerTurningPoint h j ∈ fibreHeights h j ∧
      sphericalPendulumUpperTurningPoint h j ∈ fibreHeights h j ∧
      sphericalPendulumLowerTurningPoint h j < sphericalPendulumUpperTurningPoint h j ∧
      ∀ z, 2 * (h - z) * (1 - z ^ 2) - j ^ 2 =
        2 * (z - sphericalPendulumLowerTurningPoint h j) *
          (sphericalPendulumUpperTurningPoint h j - z) *
          (h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j -
            z) := by
  obtain ⟨hmem₀, hlt₀⟩ := exists_mem_fibreHeights hz₀ hV
  rw [sphericalPendulumLowerTurningPoint_eq_sInf, sphericalPendulumUpperTurningPoint_eq_sSup]
  have ha := (isClosed_fibreHeights h j).csInf_mem ⟨z₀, hmem₀⟩ (bddBelow_fibreHeights h j)
  have hb := (isClosed_fibreHeights h j).csSup_mem ⟨z₀, hmem₀⟩ (bddAbove_fibreHeights h j)
  have ha₀ := radicand_sInf_eq_zero hj ⟨z₀, hmem₀⟩
  have hb₀ := radicand_sSup_eq_zero hj ⟨z₀, hmem₀⟩
  have hlt : sInf (fibreHeights h j) < sSup (fibreHeights h j) := by
    refine (csInf_le (bddBelow_fibreHeights h j) hmem₀).lt_of_ne ?_ |>.trans_le
      (le_csSup (bddAbove_fibreHeights h j) hmem₀)
    rintro hEq
    rw [hEq] at ha₀
    linarith
  exact ⟨ha, hb, hlt, radicand_eq_of_ne hlt.ne ha₀ hb₀⟩

/-- Above the curve of relative equilibria, the lower turning point lies above the south pole. -/
theorem neg_one_lt_sphericalPendulumLowerTurningPoint (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    -1 < sphericalPendulumLowerTurningPoint h j :=
  (mem_Ioo_of_mem_fibreHeights hj (turningPoint_spec hj hz₀ hV).1).1

/-- Above the curve of relative equilibria, the upper turning point lies below the north pole. -/
theorem sphericalPendulumUpperTurningPoint_lt_one (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumUpperTurningPoint h j < 1 :=
  (mem_Ioo_of_mem_fibreHeights hj (turningPoint_spec hj hz₀ hV).2.1).2

/-- Above the curve of relative equilibria, the two turning points are distinct. -/
theorem sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumLowerTurningPoint h j < sphericalPendulumUpperTurningPoint h j :=
  (turningPoint_spec hj hz₀ hV).2.2.1

/-- **The factorization of the radicand.** Above the curve of relative equilibria, the radicand
`p₃² = 2 (h - z) (1 - z²) - j²` of the fibre over `(h, j)` has the turning points `z₋`, `z₊` as
roots, and its third root is `z₃ = h - z₋ - z₊`:
`2 (h - z) (1 - z²) - j² = 2 (z - z₋) (z₊ - z) (z₃ - z)`. -/
theorem two_mul_sub_mul_one_sub_sq_sub_sq_eq (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) (z : ℝ) :
    2 * (h - z) * (1 - z ^ 2) - j ^ 2 =
      2 * (z - sphericalPendulumLowerTurningPoint h j) *
        (sphericalPendulumUpperTurningPoint h j - z) *
        (h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j - z) :=
  (turningPoint_spec hj hz₀ hV).2.2.2 z

/-- Above the curve of relative equilibria, the third root `h - z₋ - z₊` of the radicand lies
above the north pole: at `z = 1` the radicand is `-j² < 0`. -/
theorem one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    1 < h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j := by
  have h₁ := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV 1
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hj2 : 0 < j ^ 2 := by positivity
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  by_contra hc
  have : 0 ≤ (1 - a) * (1 - b) * (1 - (h - a - b)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

/-- Above the curve of relative equilibria, the radicand `2 (h - z) (1 - z²) - j²` is positive
strictly between the turning points. -/
theorem two_mul_sub_mul_one_sub_sq_sub_sq_pos (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) {z : ℝ}
    (hz : z ∈ Ioo (sphericalPendulumLowerTurningPoint h j)
      (sphericalPendulumUpperTurningPoint h j)) :
    0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2 := by
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  rw [two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV z]
  have := mul_pos (mul_pos (sub_pos.2 hz.1) (sub_pos.2 hz.2))
    (by linarith [hz.2] : (0 : ℝ) < h - sphericalPendulumLowerTurningPoint h j -
      sphericalPendulumUpperTurningPoint h j - z)
  linarith

/-- Above the curve of relative equilibria, the radicand `2 (h - z) (1 - z²) - j²` is nonpositive
at every height `z ≤ 1` outside the open interval between the turning points, since its third root
`h - z₋ - z₊` lies above the north pole. -/
theorem two_mul_sub_mul_one_sub_sq_sub_sq_nonpos (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) {z : ℝ} (hz : z ≤ 1)
    (hzab : z ∉ Ioo (sphericalPendulumLowerTurningPoint h j)
      (sphericalPendulumUpperTurningPoint h j)) :
    2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0 := by
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  rw [two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV z]
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  have hz3 : 0 < h - a - b - z := by linarith
  rcases le_or_gt z a with hza | hza
  · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hza) (by linarith : (0 : ℝ) ≤ b - z)) hz3.le]
  · have hbz : b ≤ z := not_lt.1 fun hzb ↦ hzab ⟨hza, hzb⟩
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hbz) (by linarith : (0 : ℝ) ≤ z - a)) hz3.le]

/-- At the lower turning point `z₋`, half the derivative `3 z² - 2 h z - 1` of the radicand
`2 (h - z) (1 - z²) - j²` is positive: `3 z₋² - 2 h z₋ - 1 = (z₊ - z₋) (z₃ - z₋)`, where
`z₃ = h - z₋ - z₊` is the third root. -/
theorem three_mul_sphericalPendulumLowerTurningPoint_sq_sub_pos (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    0 < 3 * sphericalPendulumLowerTurningPoint h j ^ 2 -
      2 * h * sphericalPendulumLowerTurningPoint h j - 1 := by
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  -- Comparing coefficients in the factorization.
  have : 3 * a ^ 2 - 2 * h * a - 1 = (b - a) * (h - a - b - a) := by
    linear_combination (hfac 1 - hfac (-1)) / 4
  rw [this]
  exact mul_pos (by linarith) (by linarith)

/-- At the upper turning point `z₊`, half the derivative `3 z² - 2 h z - 1` of the radicand
`2 (h - z) (1 - z²) - j²` is negative: `3 z₊² - 2 h z₊ - 1 = -(z₊ - z₋) (z₃ - z₊)`, where
`z₃ = h - z₋ - z₊` is the third root. -/
theorem three_mul_sphericalPendulumUpperTurningPoint_sq_sub_neg (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    3 * sphericalPendulumUpperTurningPoint h j ^ 2 -
      2 * h * sphericalPendulumUpperTurningPoint h j - 1 < 0 := by
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  -- Comparing coefficients in the factorization.
  have : 3 * b ^ 2 - 2 * h * b - 1 = -((b - a) * (h - a - b - b)) := by
    linear_combination (hfac 1 - hfac (-1)) / 4
  rw [this, neg_lt_zero]
  exact mul_pos (by linarith) (by linarith)

/-- If the radicand `2 (h - z) (1 - z²) - j²` factors as `2 (z - a) (b - z) (c - z)` with
`c = h - a - b`, where `-1 ≤ a < b ≤ 1 ≤ c`, then it is nonpositive on `[-1, 1]` outside `(a, b)`,
so a height quadrature over `(-1, 1)` is the integral from `a` to `b`. -/
private theorem integral_div_sqrt_eq_integral_of_factor {h j a b : ℝ} (ha : -1 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (hc : 1 ≤ h - a - b)
    (hfac : ∀ z, 2 * (h - z) * (1 - z ^ 2) - j ^ 2 = 2 * (z - a) * (b - z) * (h - a - b - z))
    (g : ℝ → ℝ) :
    ∫ z in (-1)..1, g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) =
      ∫ z in a..b, g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le hab.le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (s := Ioo _ _) fun z hz ↦ ⟨ha.trans hz.1.le, hz.2.le.trans hb⟩]
  rintro z ⟨hz, hzab⟩
  -- Outside `(a, b)` one of the first two factors is nonpositive and the other nonnegative.
  have hcz : 0 ≤ h - a - b - z := by linarith [hz.2]
  have hnonpos : (z - a) * (b - z) ≤ 0 := by
    rcases le_or_gt z a with hza | hza
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (by linarith [not_lt.1 fun h' ↦ hzab ⟨hza, h'⟩])
  rw [Real.sqrt_eq_zero'.2 (by rw [hfac z]; nlinarith [mul_nonpos_of_nonpos_of_nonneg hnonpos hcz]),
    div_zero]

/-- **Height quadratures run between the turning points.** Above the curve of relative equilibria,
the square root of the radicand `2 (h - z) (1 - z²) - j²` vanishes at every height of `[-1, 1]`
outside the open interval between the turning points. So the integral over `(-1, 1)` of any
function divided by it is the integral from `z₋` to `z₊`. -/
theorem integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) (g : ℝ → ℝ) :
    ∫ z in (-1)..1, g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) =
      ∫ z in (sphericalPendulumLowerTurningPoint h j)..(sphericalPendulumUpperTurningPoint h j),
        g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) :=
  integral_div_sqrt_eq_integral_of_factor
    (neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV).le
    (sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV)
    (sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV).le
    (one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
      hj hz₀ hV).le
    (two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV) g

/-- Above the curve of relative equilibria, the factor `2 (z₃ - z)` of the radicand stays positive
along the sine substitution `z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ`, where
`z₃ = h - z₋ - z₊` is the third root: `z ≤ z₊ < 1 < z₃`. -/
theorem two_mul_sub_sub_sub_add_mul_sin_pos (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) (θ : ℝ) :
    0 < 2 * (h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j -
      ((sphericalPendulumLowerTurningPoint h j + sphericalPendulumUpperTurningPoint h j) / 2 +
        (sphericalPendulumUpperTurningPoint h j - sphericalPendulumLowerTurningPoint h j) / 2 *
          Real.sin θ)) := by
  have hu := mem_Icc_add_mul_sin
    (sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV).le θ
  linarith [hu.2, sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV,
    one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint hj hz₀ hV]

/-- **The sine substitution for a factored radicand.** If the radicand `2 (h - z) (1 - z²) - j²`
factors as `2 (z - a) (b - z) (c - z)` with `c = h - a - b`, where `-1 ≤ a < b ≤ 1 ≤ c` and
`b < c`, then the substitution `z = (a + b) / 2 + (b - a) / 2 · sin θ` turns a height
quadrature into an integral over `[-π/2, π/2]` with the positive denominator `√(2 (c - z))`. This
covers both the values above the curve of relative equilibria and the values on the axis
`j = 0`. -/
private theorem integral_div_sqrt_eq_integral_sin_of_factor {h j a b : ℝ} (ha : -1 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (hc : 1 ≤ h - a - b) (hbc : b < h - a - b)
    (hfac : ∀ z, 2 * (h - z) * (1 - z ^ 2) - j ^ 2 = 2 * (z - a) * (b - z) * (h - a - b - z))
    (g : ℝ → ℝ) :
    ∫ z in (-1)..1, g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) =
      ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        g ((a + b) / 2 + (b - a) / 2 * Real.sin θ) /
          √(2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 * Real.sin θ))) := by
  rw [integral_div_sqrt_eq_integral_of_factor ha hab hb hc hfac]
  have hsin (θ : ℝ) : 0 < 2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 * Real.sin θ)) := by
    linarith [(mem_Icc_add_mul_sin hab.le θ).2]
  set u : ℝ → ℝ := fun θ ↦ (a + b) / 2 + (b - a) / 2 * Real.sin θ with hu
  have hr : 0 < (b - a) / 2 := by linarith
  -- The substitution maps `[-π/2, π/2]` injectively onto `[a, b]`.
  have hu_image : u '' Icc (-(Real.pi / 2)) (Real.pi / 2) = Icc a b := by
    have : u = (fun s ↦ (b - a) / 2 * s + (a + b) / 2) ∘ Real.sin := by
      funext θ
      simp only [hu, Function.comp]
      ring
    rw [this, image_comp, Real.bijOn_sin.image_eq, image_affine_Icc' hr]
    congr 1 <;> ring
  have hu_inj : InjOn u (Icc (-(Real.pi / 2)) (Real.pi / 2)) := fun x hx y hy hxy ↦
    Real.injOn_sin hx hy (by simpa [hu, hr.ne'] using hxy)
  have hu_deriv : ∀ θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivWithinAt u ((b - a) / 2 * Real.cos θ) (Icc (-(Real.pi / 2)) (Real.pi / 2)) θ :=
    fun θ _ ↦ (((Real.hasDerivAt_sin θ).const_mul _).const_add _).hasDerivWithinAt
  rw [intervalIntegral.integral_of_le hab.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← hu_image,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hu_deriv hu_inj,
    MeasureTheory.integral_Icc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  -- On `(-π/2, π/2)`, the Jacobian `(b - a) / 2 · cos θ` cancels the vanishing factor
  -- `√((z - a) (b - z))` of the square root of the radicand.
  have hrc : 0 < (b - a) / 2 * Real.cos θ := mul_pos hr (Real.cos_pos_of_mem_Ioo hθ)
  have hpos : 0 < √(2 * (h - a - b - u θ)) := Real.sqrt_pos.2 (hsin θ)
  have hrad : 2 * (h - u θ) * (1 - u θ ^ 2) - j ^ 2 =
      ((b - a) / 2 * Real.cos θ) ^ 2 * (2 * (h - a - b - u θ)) := by
    rw [hfac]
    simp only [hu]
    linear_combination
      (-2 * ((b - a) / 2) ^ 2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 * Real.sin θ))) *
        Real.sin_sq_add_cos_sq θ
  have hux : u θ = (a + b) / 2 + (b - a) / 2 * Real.sin θ := rfl
  rw [← hux, hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hrc.le, abs_of_pos hrc, smul_eq_mul]
  generalize √(2 * (h - a - b - u θ)) = k at hpos ⊢
  generalize (b - a) / 2 * Real.cos θ = c at hrc ⊢
  field_simp

/-- **The sine substitution between the turning points.** Above the curve of relative equilibria,
the substitution `z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ` between the turning points `z₋ < z₊`
absorbs both inverse square root singularities of a height quadrature: for every function `g`,

`∫_{-1}^{1} g(z) dz / √(2 (h - z) (1 - z²) - j²) = ∫_{-π/2}^{π/2} g(z) dθ / √(2 (z₃ - z))`,

where `z₃ = h - z₋ - z₊ > 1` is the third root of the radicand. The new denominator is positive
for every `θ`. -/
theorem integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq_integral_sin (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) (g : ℝ → ℝ) :
    ∫ z in (-1)..1, g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) =
      ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        g ((sphericalPendulumLowerTurningPoint h j + sphericalPendulumUpperTurningPoint h j) / 2 +
            (sphericalPendulumUpperTurningPoint h j - sphericalPendulumLowerTurningPoint h j) / 2 *
              Real.sin θ) /
          √(2 * (h - sphericalPendulumLowerTurningPoint h j -
            sphericalPendulumUpperTurningPoint h j -
            ((sphericalPendulumLowerTurningPoint h j + sphericalPendulumUpperTurningPoint h j) / 2 +
              (sphericalPendulumUpperTurningPoint h j - sphericalPendulumLowerTurningPoint h j) /
                2 * Real.sin θ))) :=
  integral_div_sqrt_eq_integral_sin_of_factor
    (neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV).le
    (sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV)
    (sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV).le
    (one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
      hj hz₀ hV).le
    ((sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV).trans
      (one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
        hj hz₀ hV))
    (two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV) g

/-- **The heights of a fibre.** Above the curve of relative equilibria, the heights `q₃` of the
points of the fibre `F⁻¹(h, j)` of the energy–momentum map form the interval `[z₋, z₊]` between
the turning points. -/
theorem image_apply_two_preimage_sphericalPendulumEnergyMomentum_eq_Icc (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    (fun x ↦ x.1 2) ''
        (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}) =
      Icc (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j) := by
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  have ha := neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  rw [image_apply_two_preimage_sphericalPendulumEnergyMomentum (h, j)]
  refine Subset.antisymm (fun z hz ↦ ⟨?_, ?_⟩) fun z hz ↦ ?_
  · rw [sphericalPendulumLowerTurningPoint_eq_sInf]
    exact csInf_le (bddBelow_fibreHeights h j) hz
  · rw [sphericalPendulumUpperTurningPoint_eq_sSup]
    exact le_csSup (bddAbove_fibreHeights h j) hz
  · set a := sphericalPendulumLowerTurningPoint h j
    set b := sphericalPendulumUpperTurningPoint h j
    have hzI : z ∈ Ioo (-1) 1 := ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
    have hnn : 0 ≤ 2 * (h - z) * (1 - z ^ 2) - j ^ 2 := by
      rw [hfac z]
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hz.1) (sub_nonneg.2 hz.2))
        (by linarith [hz.2, hzI.2] : (0 : ℝ) ≤ h - a - b - z)
      linarith
    have h₁ : 0 < 1 - z ^ 2 := by nlinarith [hzI.1, hzI.2]
    refine ⟨Ioo_subset_Icc_self hzI, ?_, by linarith⟩
    by_contra hzh
    nlinarith [mul_pos (sub_pos.2 (not_le.1 hzh)) h₁, sq_pos_of_ne_zero hj]

/-- **The vertical momentum vanishes exactly at the turning points.** Above the curve of relative
equilibria, a point of the fibre `F⁻¹(h, j)` has nonzero vertical momentum `p₃` if and only if its
height lies strictly between the turning points. -/
theorem snd_two_ne_zero_iff_apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h)
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} (hx : x ∈ sphericalPendulumPhaseSpace)
    (hF : sphericalPendulumEnergyMomentum x = (h, j)) :
    x.2 2 ≠ 0 ↔ x.1 2 ∈ Ioo (sphericalPendulumLowerTurningPoint h j)
      (sphericalPendulumUpperTurningPoint h j) := by
  have hsq := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
  rw [hF] at hsq
  have hz : x.1 2 ∈ Icc (sphericalPendulumLowerTurningPoint h j)
      (sphericalPendulumUpperTurningPoint h j) := by
    rw [← image_apply_two_preimage_sphericalPendulumEnergyMomentum_eq_Icc hj hz₀ hV]
    exact ⟨x, ⟨hx, hF⟩, rfl⟩
  refine ⟨fun hp ↦ ?_, fun hz hp ↦ ?_⟩
  · by_contra hz'
    have := two_mul_sub_mul_one_sub_sq_sub_sq_nonpos hj hz₀ hV
      (hz.2.trans (sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV).le) hz'
    exact hp (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (hsq ▸ this) (sq_nonneg _)))
  · have := two_mul_sub_mul_one_sub_sq_sub_sq_pos hj hz₀ hV hz
    rw [← hsq, hp] at this
    simp at this

end Regular

/-! ### Continuity of the turning points -/

/-- If the radicand is positive at a height `y` for the value `(h₀, j₀)`, it stays positive there
for all nearby values. -/
private theorem eventually_radicand_pos {h₀ j₀ y : ℝ}
    (hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - j₀ ^ 2) :
    ∀ᶠ c : ℝ × ℝ in 𝓝 (h₀, j₀), 0 < 2 * (c.1 - y) * (1 - y ^ 2) - c.2 ^ 2 :=
  ((by fun_prop : Continuous fun c : ℝ × ℝ ↦ 2 * (c.1 - y) * (1 - y ^ 2) - c.2 ^ 2).tendsto
    (h₀, j₀)).eventually_const_lt hpos

/-- If the radicand is negative on a compact set of heights for the value `(h₀, j₀)`, it stays
negative there for all nearby values. -/
private theorem eventually_forall_radicand_neg {h₀ j₀ : ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hneg : ∀ z ∈ K, 2 * (h₀ - z) * (1 - z ^ 2) - j₀ ^ 2 < 0) :
    ∀ᶠ c : ℝ × ℝ in 𝓝 (h₀, j₀), ∀ z ∈ K, 2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2 < 0 :=
  hK.eventually_forall_of_forall_eventually fun z hz ↦
    ((by fun_prop : Continuous fun p : (ℝ × ℝ) × ℝ ↦
      2 * (p.1.1 - p.2) * (1 - p.2 ^ 2) - p.1.2 ^ 2).tendsto ((h₀, j₀), z)).eventually_lt_const
      (hneg z hz)

/-- **Continuity of the lower turning point** on the values `(h, j)` with `j ≠ 0` lying strictly
above the curve of relative equilibria. -/
theorem continuousOn_sphericalPendulumLowerTurningPoint :
    ContinuousOn (fun c : ℝ × ℝ ↦ sphericalPendulumLowerTurningPoint c.1 c.2)
      sphericalPendulumTurningPointDomain := by
  rintro ⟨h₀, j₀⟩ ⟨hj₀, z₀, hz₀, hV₀⟩
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj₀ hz₀ hV₀
  have ha₀ := neg_one_lt_sphericalPendulumLowerTurningPoint hj₀ hz₀ hV₀
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj₀ hz₀ hV₀
  have hb₀ := sphericalPendulumUpperTurningPoint_lt_one hj₀ hz₀ hV₀
  have hc₀ := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj₀ hz₀ hV₀
  set a := sphericalPendulumLowerTurningPoint h₀ j₀
  set b := sphericalPendulumUpperTurningPoint h₀ j₀
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · -- Below `l < z₋` the radicand stays negative, so the fibre has no heights there.
    have hK := eventually_forall_radicand_neg (h₀ := h₀) (j₀ := j₀)
      (isCompact_Icc (a := -1) (b := l))
      fun z hz ↦ by
        rw [hfac z]
        have : 0 < (a - z) * (b - z) * (h₀ - a - b - z) :=
          mul_pos (mul_pos (by linarith [hz.2]) (by linarith [hz.2])) (by linarith [hz.2])
        nlinarith
    filter_upwards [nhdsWithin_le_nhds hK, self_mem_nhdsWithin] with c hc ⟨hj, z, hz, hV⟩
    have hmem := (turningPoint_spec hj hz hV).1
    by_contra hle
    exact (hc _ ⟨hmem.1.1, not_lt.1 hle⟩).not_ge (sub_nonneg.2 hmem.2.2)
  · -- Just above `z₋` the radicand stays positive, so this height stays in the fibre.
    set y := (a + min u b) / 2
    have hy₁ : a < y := by simp only [y]; linarith [lt_min hu hab]
    have hy₂ : y < min u b := by simp only [y]; linarith [lt_min hu hab]
    have hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - j₀ ^ 2 := by
      rw [hfac y]
      have := min_le_right u b
      have : 0 < (y - a) * (b - y) * (h₀ - a - b - y) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      linarith
    filter_upwards [nhdsWithin_le_nhds (eventually_radicand_pos hpos)] with c hc
    rw [sphericalPendulumLowerTurningPoint_eq_sInf]
    have hyI : y ∈ Ioo (-1) 1 := ⟨by linarith, by linarith [min_le_right u b]⟩
    exact (csInf_le (bddBelow_fibreHeights c.1 c.2)
      (mem_fibreHeights_of_lt hyI (by linarith))).trans_lt (hy₂.trans_le (min_le_left u b))

/-- **Continuity of the upper turning point** on the values `(h, j)` with `j ≠ 0` lying strictly
above the curve of relative equilibria. -/
theorem continuousOn_sphericalPendulumUpperTurningPoint :
    ContinuousOn (fun c : ℝ × ℝ ↦ sphericalPendulumUpperTurningPoint c.1 c.2)
      sphericalPendulumTurningPointDomain := by
  rintro ⟨h₀, j₀⟩ ⟨hj₀, z₀, hz₀, hV₀⟩
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj₀ hz₀ hV₀
  have ha₀ := neg_one_lt_sphericalPendulumLowerTurningPoint hj₀ hz₀ hV₀
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj₀ hz₀ hV₀
  have hb₀ := sphericalPendulumUpperTurningPoint_lt_one hj₀ hz₀ hV₀
  have hc₀ := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj₀ hz₀ hV₀
  set a := sphericalPendulumLowerTurningPoint h₀ j₀
  set b := sphericalPendulumUpperTurningPoint h₀ j₀
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · -- Just below `z₊` the radicand stays positive, so this height stays in the fibre.
    set y := (max l a + b) / 2
    have hy₁ : max l a < y := by simp only [y]; linarith [max_lt hl hab]
    have hy₂ : y < b := by simp only [y]; linarith [max_lt hl hab]
    have hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - j₀ ^ 2 := by
      rw [hfac y]
      have := le_max_right l a
      have : 0 < (y - a) * (b - y) * (h₀ - a - b - y) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      linarith
    filter_upwards [nhdsWithin_le_nhds (eventually_radicand_pos hpos)] with c hc
    rw [sphericalPendulumUpperTurningPoint_eq_sSup]
    have hyI : y ∈ Ioo (-1) 1 := ⟨by linarith [le_max_right l a], by linarith⟩
    exact ((le_max_left l a).trans_lt hy₁).trans_le (le_csSup (bddAbove_fibreHeights c.1 c.2)
      (mem_fibreHeights_of_lt hyI (by linarith)))
  · -- Above `u > z₊` the radicand stays negative, so the fibre has no heights there.
    have hK := eventually_forall_radicand_neg (h₀ := h₀) (j₀ := j₀)
      (isCompact_Icc (a := u) (b := 1))
      fun z hz ↦ by
        rw [hfac z]
        have : 0 < (z - a) * (z - b) * (h₀ - a - b - z) :=
          mul_pos (mul_pos (by linarith [hz.1]) (by linarith [hz.1])) (by linarith [hz.2])
        nlinarith
    filter_upwards [nhdsWithin_le_nhds hK, self_mem_nhdsWithin] with c hc ⟨hj, z, hz, hV⟩
    have hmem := (turningPoint_spec hj hz hV).2.1
    by_contra hle
    exact (hc _ ⟨not_lt.1 hle, hmem.1.2⟩).not_ge (sub_nonneg.2 hmem.2.2)

/-! ### The turning points on the axis `j = 0` -/

/-- On the axis `j = 0`, the heights of the fibre over `(h, 0)` form the interval `[-1, min h 1]`:
the radicand `2 (h - z) (1 - z²)` is nonnegative at every height `z ∈ [-1, 1]` with `z ≤ h`. -/
private theorem fibreHeights_zero_right (h : ℝ) :
    fibreHeights h 0 = Icc (-1) (min h 1) := by
  ext z
  simp only [fibreHeights, mem_ofPred_eq, mem_Icc, le_min_iff]
  refine ⟨fun ⟨⟨h₁, h₂⟩, h₃, _⟩ ↦ ⟨h₁, h₃, h₂⟩, fun ⟨h₁, h₃, h₂⟩ ↦ ⟨⟨h₁, h₂⟩, h₃, ?_⟩⟩
  have h₄ : 0 ≤ 1 - z ^ 2 := by nlinarith
  simpa using mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 h₃)) h₄

/-- On the axis `j = 0`, for `h ≥ -1`, the lower turning point is the south pole. -/
theorem sphericalPendulumLowerTurningPoint_zero_right {h : ℝ} (hh : -1 ≤ h) :
    sphericalPendulumLowerTurningPoint h 0 = -1 := by
  rw [sphericalPendulumLowerTurningPoint_eq_sInf]
  exact (congrArg sInf (fibreHeights_zero_right h)).trans (csInf_Icc (le_min hh (by norm_num)))

/-- On the axis `j = 0`, for `h ≥ -1`, the upper turning point is `min h 1`: the height `h` for
`h ≤ 1`, and the north pole for `h ≥ 1`. -/
theorem sphericalPendulumUpperTurningPoint_zero_right {h : ℝ} (hh : -1 ≤ h) :
    sphericalPendulumUpperTurningPoint h 0 = min h 1 := by
  rw [sphericalPendulumUpperTurningPoint_eq_sSup]
  exact (congrArg sSup (fibreHeights_zero_right h)).trans (csSup_Icc (le_min hh (by norm_num)))

/-- For every height `y ∈ (-1, 1)` below `h₀`, the radicand `2 (h - y) (1 - y²) - j²` stays
positive for all values `(h, j)` near `(h₀, 0)`, so `y` lies in those fibres
(`mem_fibreHeights_of_lt`). -/
private theorem eventually_sq_lt_radicand_of_lt {h₀ y : ℝ} (hy : y ∈ Ioo (-1) 1) (hyh : y < h₀) :
    ∀ᶠ c : ℝ × ℝ in 𝓝 (h₀, 0), c.2 ^ 2 < 2 * (c.1 - y) * (1 - y ^ 2) := by
  have h₁ : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - (0 : ℝ) ^ 2 := by
    simpa using mul_pos (mul_pos two_pos (sub_pos.2 hyh)) h₁
  filter_upwards [eventually_radicand_pos hpos] with c hc
  linarith

/-- For `h₀ > -1`, the height `(-1 + min h₀ 1) / 2` lies in `(-1, 1)`, and the radicand at this
height stays positive for all values near `(h₀, 0)`; in particular those fibres are nonempty. -/
private theorem eventually_radicand_pos_zero_right {h₀ : ℝ} (hh : -1 < h₀) :
    (-1 + min h₀ 1) / 2 ∈ Ioo (-1) 1 ∧ ∀ᶠ c : ℝ × ℝ in 𝓝 (h₀, 0),
      c.2 ^ 2 < 2 * (c.1 - (-1 + min h₀ 1) / 2) * (1 - ((-1 + min h₀ 1) / 2) ^ 2) := by
  have hy : (-1 + min h₀ 1) / 2 ∈ Ioo (-1) 1 :=
    ⟨by linarith [lt_min hh (by norm_num : (-1 : ℝ) < 1)], by linarith [min_le_right h₀ 1]⟩
  exact ⟨hy, eventually_sq_lt_radicand_of_lt hy (by linarith [min_le_left h₀ 1])⟩

/-- **Continuity of the lower turning point on the axis.** For `h > -1` the lower turning point
`z₋` is continuous at `(h, 0)`, where it is the south pole. -/
theorem continuousAt_sphericalPendulumLowerTurningPoint_zero_right {h : ℝ} (hh : -1 < h) :
    ContinuousAt (fun c : ℝ × ℝ ↦ sphericalPendulumLowerTurningPoint c.1 c.2) (h, 0) := by
  have hm : -1 < min h 1 := lt_min hh (by norm_num)
  rw [ContinuousAt, sphericalPendulumLowerTurningPoint_zero_right hh.le]
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · -- The fibre is nonempty and its heights are at least `-1`.
    obtain ⟨hy, hev⟩ := eventually_radicand_pos_zero_right hh
    filter_upwards [hev] with c hc
    rw [sphericalPendulumLowerTurningPoint_eq_sInf]
    exact hl.trans_le (le_csInf ⟨_, mem_fibreHeights_of_lt hy hc⟩ fun z hz ↦ hz.1.1)
  · -- A height just above the south pole stays in the fibre.
    have hm' : -1 < min u (min h 1) := lt_min hu hm
    have hy : (-1 + min u (min h 1)) / 2 ∈ Ioo (-1) 1 :=
      ⟨by linarith, by linarith [min_le_right u (min h 1), min_le_right h 1]⟩
    filter_upwards [eventually_sq_lt_radicand_of_lt hy
      (by linarith [min_le_right u (min h 1), min_le_left h 1])] with c hc
    rw [sphericalPendulumLowerTurningPoint_eq_sInf]
    exact (csInf_le (bddBelow_fibreHeights c.1 c.2) (mem_fibreHeights_of_lt hy hc)).trans_lt
      (by linarith [min_le_left u (min h 1)])

/-- **Continuity of the upper turning point on the axis.** For `h > -1` the upper turning point
`z₊` is continuous at `(h, 0)`, where it is `min h 1`. -/
theorem continuousAt_sphericalPendulumUpperTurningPoint_zero_right {h : ℝ} (hh : -1 < h) :
    ContinuousAt (fun c : ℝ × ℝ ↦ sphericalPendulumUpperTurningPoint c.1 c.2) (h, 0) := by
  have hm : -1 < min h 1 := lt_min hh (by norm_num)
  rw [ContinuousAt, sphericalPendulumUpperTurningPoint_zero_right hh.le]
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · -- A height just below `min h 1` stays in the fibre.
    have hl' : max l (-1) < min h 1 := max_lt hl hm
    have hy : (max l (-1) + min h 1) / 2 ∈ Ioo (-1) 1 :=
      ⟨by linarith [le_max_right l (-1)], by linarith [min_le_right h 1]⟩
    filter_upwards [eventually_sq_lt_radicand_of_lt hy (by linarith [min_le_left h 1])]
      with c hc
    rw [sphericalPendulumUpperTurningPoint_eq_sSup]
    exact (by linarith [le_max_left l (-1)] : l < _).trans_le
      (le_csSup (bddAbove_fibreHeights c.1 c.2) (mem_fibreHeights_of_lt hy hc))
  · -- The fibre is nonempty and its heights are at most `min c.1 1`, which tends to `min h 1`.
    obtain ⟨hy, hev⟩ := eventually_radicand_pos_zero_right hh
    have hlim : Tendsto (fun c : ℝ × ℝ ↦ min c.1 1) (𝓝 (h, 0)) (𝓝 (min h 1)) :=
      (continuous_fst.min continuous_const).tendsto (h, (0 : ℝ))
    filter_upwards [hlim.eventually_lt_const hu, hev] with c hcu hc
    rw [sphericalPendulumUpperTurningPoint_eq_sSup]
    exact (csSup_le ⟨_, mem_fibreHeights_of_lt hy hc⟩ fun z hz ↦ le_min hz.2.1 hz.1.2).trans_lt
      hcu

/-! ### Continuity of height quadratures -/

/-- The turning points at a value above the curve of relative equilibria, or on the axis `j = 0`
away from the poles, are roots `-1 ≤ z₋ < z₊ ≤ 1` of the radicand, whose third root
`z₃ = h - z₋ - z₊` satisfies `z₃ ≥ 1` and `z₃ > z₊`. On the axis, `z₋ = -1`, `z₊ = min h 1` and
`z₃ = max h 1`. -/
private theorem turningPoint_spec_of_mem {c : ℝ × ℝ}
    (hc : c ∈ sphericalPendulumTurningPointDomain ∨ (c.2 = 0 ∧ -1 < c.1 ∧ c.1 ≠ 1)) :
    -1 ≤ sphericalPendulumLowerTurningPoint c.1 c.2 ∧
      sphericalPendulumLowerTurningPoint c.1 c.2 < sphericalPendulumUpperTurningPoint c.1 c.2 ∧
      sphericalPendulumUpperTurningPoint c.1 c.2 ≤ 1 ∧
      1 ≤ c.1 - sphericalPendulumLowerTurningPoint c.1 c.2 -
        sphericalPendulumUpperTurningPoint c.1 c.2 ∧
      sphericalPendulumUpperTurningPoint c.1 c.2 <
        c.1 - sphericalPendulumLowerTurningPoint c.1 c.2 -
          sphericalPendulumUpperTurningPoint c.1 c.2 ∧
      ∀ z, 2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2 =
        2 * (z - sphericalPendulumLowerTurningPoint c.1 c.2) *
          (sphericalPendulumUpperTurningPoint c.1 c.2 - z) *
          (c.1 - sphericalPendulumLowerTurningPoint c.1 c.2 -
            sphericalPendulumUpperTurningPoint c.1 c.2 - z) := by
  obtain ⟨h, j⟩ := c
  rcases hc with ⟨hj, z₀, hz₀, hV⟩ | ⟨hj, hh, h1⟩
  · have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
    have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
      hj hz₀ hV
    exact ⟨(neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV).le,
      sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV, hb.le,
      hc.le, hb.trans hc, two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV⟩
  · dsimp only at hj hh h1 ⊢
    subst hj
    rw [sphericalPendulumLowerTurningPoint_zero_right hh.le,
      sphericalPendulumUpperTurningPoint_zero_right hh.le]
    rcases h1.lt_or_gt with h1 | h1
    · rw [min_eq_left h1.le]
      exact ⟨le_rfl, hh, h1.le, by linarith, by linarith, fun z ↦ by ring⟩
    · rw [min_eq_right h1.le]
      exact ⟨le_rfl, by norm_num, le_rfl, by linarith, by linarith, fun z ↦ by ring⟩

/-- Height quadratures are continuous on any set `S` of values above the curve of relative
equilibria or on the axis `j = 0` away from the poles, for weights `g` continuous on `S ×ˢ K`,
where `K` contains the heights between the turning points: after the sine substitution the
integrand is jointly continuous. -/
private theorem continuousOn_integral_div_sqrt_of_forall_mem {g : ℝ × ℝ → ℝ → ℝ}
    {S : Set (ℝ × ℝ)} {K : Set ℝ}
    (hS : ∀ c ∈ S, c ∈ sphericalPendulumTurningPointDomain ∨ (c.2 = 0 ∧ -1 < c.1 ∧ c.1 ≠ 1))
    (hK : ∀ c ∈ S, Icc (sphericalPendulumLowerTurningPoint c.1 c.2)
      (sphericalPendulumUpperTurningPoint c.1 c.2) ⊆ K)
    (hg : ContinuousOn (Function.uncurry g) (S ×ˢ K)) :
    ContinuousOn (fun c : ℝ × ℝ ↦ ∫ z in (-1)..1, g c z / √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2))
      S := by
  -- Both turning points are continuous on `S`: inside the open domain by their continuity there,
  -- and on the axis by their continuity at `(h, 0)`.
  have hcont {f : ℝ → ℝ → ℝ}
      (hdom : ContinuousOn (fun c : ℝ × ℝ ↦ f c.1 c.2) sphericalPendulumTurningPointDomain)
      (haxis : ∀ {h : ℝ}, -1 < h → ContinuousAt (fun c : ℝ × ℝ ↦ f c.1 c.2) (h, 0)) :
      Continuous fun c : S ↦ f (c : ℝ × ℝ).1 (c : ℝ × ℝ).2 := by
    refine (continuousOn_iff_continuous_domRestrict (f := fun c : ℝ × ℝ ↦ f c.1 c.2) (s := S)).1
      fun c hc ↦ ContinuousAt.continuousWithinAt ?_
    rcases hS c hc with hc | ⟨hj, hh, -⟩
    · exact hdom.continuousAt (isOpen_sphericalPendulumTurningPointDomain.mem_nhds hc)
    · obtain ⟨h, j⟩ := c
      dsimp only at hj hh
      subst hj
      exact haxis hh
  have ha := hcont continuousOn_sphericalPendulumLowerTurningPoint
    continuousAt_sphericalPendulumLowerTurningPoint_zero_right
  have hb := hcont continuousOn_sphericalPendulumUpperTurningPoint
    continuousAt_sphericalPendulumUpperTurningPoint_zero_right
  -- The substituted height `u(c, θ)`, jointly continuous with values in `[z₋, z₊] ⊆ K`.
  let u : S × ℝ → ℝ := fun p ↦
    (sphericalPendulumLowerTurningPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2 +
        sphericalPendulumUpperTurningPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2) / 2 +
      (sphericalPendulumUpperTurningPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2 -
        sphericalPendulumLowerTurningPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2) / 2 * Real.sin p.2
  have ha' := ha.comp (continuous_fst (X := S) (Y := ℝ))
  have hb' := hb.comp (continuous_fst (X := S) (Y := ℝ))
  simp only [Function.comp_def] at ha' hb'
  have hu : Continuous u := by fun_prop
  have hgu : Continuous fun p : S × ℝ ↦ g p.1 (u p) :=
    hg.comp_continuous (by fun_prop : Continuous fun p : S × ℝ ↦ ((p.1 : ℝ × ℝ), u p)) fun p ↦ by
      obtain ⟨-, h₂, -⟩ := turningPoint_spec_of_mem (hS _ p.1.property)
      exact ⟨p.1.property, hK _ p.1.property (mem_Icc_add_mul_sin h₂.le p.2)⟩
  let G : S → ℝ → ℝ := fun c θ ↦ g c (u (c, θ)) /
    √(2 * ((c : ℝ × ℝ).1 - sphericalPendulumLowerTurningPoint (c : ℝ × ℝ).1 (c : ℝ × ℝ).2 -
      sphericalPendulumUpperTurningPoint (c : ℝ × ℝ).1 (c : ℝ × ℝ).2 - u (c, θ)))
  have hG : Continuous (Function.uncurry G) :=
    hgu.div (by fun_prop) fun p ↦ by
      obtain ⟨-, h₂, -, -, h₅, -⟩ := turningPoint_spec_of_mem (hS _ p.1.property)
      have := (mem_Icc_add_mul_sin h₂.le p.2).2
      exact (Real.sqrt_pos.2 (by dsimp only [u]; linarith)).ne'
  rw [continuousOn_iff_continuous_domRestrict]
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hG (-(Real.pi / 2)) (Real.pi / 2)).congr fun c ↦ ?_
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := turningPoint_spec_of_mem (hS _ c.property)
  exact (integral_div_sqrt_eq_integral_sin_of_factor h₁ h₂ h₃ h₄ h₅ h₆ (g c)).symm

/-- **Continuity of height quadratures.** If `g` is continuous in `((h, j), z)` for `(h, j)` in
`sphericalPendulumTurningPointDomain` and heights `z ∈ (-1, 1)`, then
`∫_{-1}^{1} g(h, j, z) dz / √(2 (h - z) (1 - z²) - j²)` is continuous in `(h, j)` there. After the
sine substitution its integrand is jointly continuous, since the turning points are continuous and
the substituted height stays in `[z₋, z₊] ⊆ (-1, 1)`. -/
theorem continuousOn_integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq {g : ℝ × ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (sphericalPendulumTurningPointDomain ×ˢ Ioo (-1) 1)) :
    ContinuousOn (fun c : ℝ × ℝ ↦ ∫ z in (-1)..1, g c z / √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2))
      sphericalPendulumTurningPointDomain :=
  continuousOn_integral_div_sqrt_of_forall_mem (fun _ hc ↦ .inl hc)
    (fun _ ⟨hj, _, hz, hV⟩ ↦ Icc_subset_Ioo (neg_one_lt_sphericalPendulumLowerTurningPoint hj hz hV)
      (sphericalPendulumUpperTurningPoint_lt_one hj hz hV)) hg

/-- **Continuity of height quadratures across the axis.** Let `h > -1` with `h ≠ 1`, and let `g`
be continuous in `((h', j), z)` for `(h', j)` in a neighborhood of `(h, 0)` and heights
`z ∈ [-1, 1]`. Then `∫_{-1}^{1} g(h', j, z) dz / √(2 (h' - z) (1 - z²) - j²)` is continuous in
`(h', j)` at `(h, 0)`. Near the axis the turning points tend to `-1` and `min h 1`, while the third
root of the radicand stays above `min h 1`; the sine substitution keeps the integrand regular. -/
theorem continuousAt_integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq {g : ℝ × ℝ → ℝ → ℝ}
    {h : ℝ} (hh : -1 < h) (h1 : h ≠ 1) {s : Set (ℝ × ℝ)} (hs : s ∈ 𝓝 (h, 0))
    (hg : ContinuousOn (Function.uncurry g) (s ×ˢ Icc (-1) 1)) :
    ContinuousAt (fun c : ℝ × ℝ ↦ ∫ z in (-1)..1, g c z / √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2))
      (h, 0) := by
  -- Near `(h, 0)`, every value off the axis lies above the curve of relative equilibria: the
  -- radicand stays positive at a fixed height `z₀ ∈ (-1, min h 1)`.
  obtain ⟨hz₀, hev⟩ := eventually_radicand_pos_zero_right hh
  have hS : {c : ℝ × ℝ | c ∈ sphericalPendulumTurningPointDomain ∨
      (c.2 = 0 ∧ -1 < c.1 ∧ c.1 ≠ 1)} ∈ 𝓝 (h, 0) := by
    filter_upwards [hev,
      continuous_fst.continuousAt.eventually (lt_mem_nhds hh),
      continuous_fst.continuousAt.eventually (isOpen_ne.mem_nhds h1)] with c hc hc₁ hc₂
    by_cases hj : c.2 = 0
    · exact Or.inr ⟨hj, hc₁, hc₂⟩
    · refine Or.inl ⟨hj, _, hz₀, (sphericalPendulumEffectivePotential_lt_iff ?_).2 (by linarith)⟩
      nlinarith [hz₀.1, hz₀.2]
  exact (continuousOn_integral_div_sqrt_of_forall_mem (S := s ∩ {c : ℝ × ℝ |
    c ∈ sphericalPendulumTurningPointDomain ∨ (c.2 = 0 ∧ -1 < c.1 ∧ c.1 ≠ 1)}) (fun c hc ↦ hc.2)
    (fun c hc ↦ have h := turningPoint_spec_of_mem hc.2; Icc_subset_Icc h.1 h.2.2.1)
    (hg.mono (prod_mono inter_subset_left subset_rfl))).continuousAt (inter_mem hs hS)

end TauCeti
