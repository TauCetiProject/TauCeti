/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Topology.Circle.Metric

/-!
# Distance of the boundary contour from `ρ`

The geometry of the shifted contour `t ↦ fdBoundary H t - ρ` about the corner `ρ` at
parameter `t = 3`: the chord distance along the arc, the purely imaginary linear form
along the left vertical, the norm lower bounds on the far pieces, the slit-plane
confinement of every piece, and the exact polar forms and principal logarithms of the
shifted contour beside the corner. The corner joins the arc to the vertical at the
interior angle `π/3`, which is exactly the gap between the two one-sided argument limits
`π/6` and `π/2` — the source of the winding value `-1/6` at `ρ`.

## Main declarations

* `TauCeti.ModularForm.norm_fdBoundary_sub_rho_arc` (the chord distance).
* `TauCeti.ModularForm.fdBoundary_sub_rho_of_mem_Icc_three_four` (the linear form).
* `TauCeti.ModularForm.log_fdBoundary_three_sub_sub_rho`,
  `TauCeti.ModularForm.log_fdBoundary_three_add_sub_rho` (the endpoint logarithms).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Rho.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex Set

namespace TauCeti

namespace ModularForm

variable {H δ t : ℝ}

/-- The corner `ρ` is the unit-circle point of angle `2π/3`. -/
private lemma rho_eq_exp :
    (UpperHalfPlane.ρ : ℂ) = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  refine Complex.ext ?_ ?_
  · rw [Complex.exp_ofReal_mul_I_re, h23, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num [UpperHalfPlane.ρ]
  · rw [Complex.exp_ofReal_mul_I_im, h23, Real.sin_pi_sub, Real.sin_pi_div_three]
    exact rho_im

/-- On the arc the distance from `ρ` is the chord distance: `2·sin(|t - 3|·π/12)` up to
the absolute value inside the sine. -/
theorem norm_fdBoundary_sub_rho_arc (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ = 2 * |Real.sin ((t - 3) * (Real.pi / 12))| := by
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ht
  have hρ : (UpperHalfPlane.ρ : ℂ) = circleMap 0 1 (2 * Real.pi / 3) := by
    rw [circleMap_zero, Complex.ofReal_one, one_mul]
    exact rho_eq_exp
  rw [← Complex.dist_eq, hcurve, hρ, dist_circleMap_eq_two_mul_abs_sin,
    (by ring : ((t + 1) * (Real.pi / 6) - 2 * Real.pi / 3) / 2 = (t - 3) * (Real.pi / 12))]
  norm_num

/-- On the left vertical the shifted contour is the purely imaginary linear form
`(t - 3)·(H - √3/2)·i`. -/
theorem fdBoundary_sub_rho_of_mem_Icc_three_four (H : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) =
      (((t - 3) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  rw [eqOn_fdBoundarySegment4 H ht, fdBoundarySegment4_apply, AffineMap.lineMap_apply]
  refine Complex.ext ?_ ?_
  · simp [UpperHalfPlane.ρ, Complex.real_smul]
  · simp [UpperHalfPlane.ρ, Complex.real_smul]

/-- On the right vertical the contour keeps distance at least `1` from `ρ`: the real parts differ
by exactly `1`. -/
theorem norm_fdBoundary_sub_rho_segment1 (H : ℝ) (ht : t ≤ 1) :
    1 ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  have hre : (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).re = 1 := by
    rw [Complex.sub_re, re_fdBoundary_of_le_one ht]
    norm_num [UpperHalfPlane.ρ]
  have h1 : |(fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).re| ≤
      ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := Complex.abs_re_le_norm _
  rw [hre] at h1
  simpa using h1

/-- On the ceiling the contour keeps distance at least `|H - √3/2|` from `ρ`: the heights
differ by exactly `H - √3/2`. The absolute value is what the height difference actually
gives, and it is the only form with content below the corner row, where `H - √3/2 < 0`
makes the signed bound vacuous. -/
theorem norm_fdBoundary_sub_rho_segment5 (ht : 4 ≤ t) :
    |H - Real.sqrt 3 / 2| ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  have him : (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases ht.eq_or_lt with rfl | h4
    · rw [Complex.sub_im, fdBoundary_apply_four, rho_im]
      simp
    · rw [Complex.sub_im, im_fdBoundary_of_gt_four h4, rho_im]
  have h1 : |(fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).im| ≤
      ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := Complex.abs_im_le_norm _
  exact him ▸ h1

/-- Before the corner the contour stays right of the corner column: on the arc the real part of
the shifted contour is `cos((t+1)·π/6) + 1/2 > 0`, and on the right vertical it is `1`, so it lies
in the slit plane. -/
theorem fdBoundary_sub_rho_mem_slitPlane_of_lt_three (H : ℝ) (ht3 : t < 3) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [Complex.sub_re, re_fdBoundary_of_le_one ht1]
    norm_num [UpperHalfPlane.ρ]
  replace ht1 : 1 ≤ t := ht1.le
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨ht1, ht3.le⟩
  rw [Complex.sub_re, hcurve, circleMap_zero_re, one_mul]
  have hcos : Real.cos (2 * Real.pi / 3) < Real.cos ((t + 1) * (Real.pi / 6)) := by
    refine Real.strictAntiOn_cos ⟨by positivity, by nlinarith [Real.pi_pos]⟩
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three] at hcos
  have hrho : ((UpperHalfPlane.ρ : ℂ)).re = -(1 / 2) := by
    norm_num [UpperHalfPlane.ρ]
  rw [hrho]
  linarith

/-- After the corner the shifted contour has nonzero imaginary part, `(t - 3) * (H - √3/2)` on the
left vertical and `H - √3/2` on the ceiling, so it lies in the slit plane. -/
theorem fdBoundary_sub_rho_mem_slitPlane_of_three_lt (hH : H ≠ Real.sqrt 3 / 2)
    (ht3 : 3 < t) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
  rcases le_or_gt t 4 with ht4 | ht4
  swap
  · rw [Complex.sub_im, im_fdBoundary_of_gt_four ht4, rho_im]
    exact sub_ne_zero.mpr hH
  rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨ht3.le, ht4⟩]
  have him : ((((t - 3) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I).im =
      (t - 3) * (H - Real.sqrt 3 / 2) := by
    simp
  rw [him]
  exact mul_ne_zero (sub_ne_zero.mpr ht3.ne') (sub_ne_zero.mpr hH)

/-- The polar form of the shifted contour just before the corner. -/
private lemma fdBoundary_three_sub_sub_rho_eq (H : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    fdBoundary H (3 - δ) - (UpperHalfPlane.ρ : ℂ) =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((Real.pi / 6 - δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  have hI : Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    exact Complex.exp_pi_div_two_mul_I.symm
  have hcurve : fdBoundary H (3 - δ) = circleMap 0 1 ((3 - δ + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨by linarith, by linarith⟩
  rw [hcurve, circleMap_zero, Complex.ofReal_one, one_mul, rho_eq_exp,
    exp_mul_I_sub_exp_mul_I,
    (by ring : ((3 - δ + 1) * (Real.pi / 6) - 2 * Real.pi / 3) / 2 = -(δ * (Real.pi / 12))),
    (by ring : ((3 - δ + 1) * (Real.pi / 6) + 2 * Real.pi / 3) / 2 =
      Real.pi / 2 + (Real.pi / 6 - δ * (Real.pi / 12))),
    Real.sin_neg]
  have hsplit : ((Real.pi / 2 + (Real.pi / 6 - δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I +
        ((Real.pi / 6 - δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← hI]
  push_cast
  -- The two factors of `I` are separated by the exponential, so `Complex.I_mul_I` has no
  -- `I * I` to match; `ring_nf` collects them into `I ^ 2` first, and the squaring lemma
  -- supplies the value `ring` cannot know.
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The principal logarithm of the shifted contour just before the corner. -/
theorem log_fdBoundary_three_sub_sub_rho (H : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    Complex.log (fdBoundary H (3 - δ) - (UpperHalfPlane.ρ : ℂ)) =
      ((Real.log (2 * Real.sin (δ * (Real.pi / 12))) : ℝ) : ℂ) +
        ((Real.pi / 6 - δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
  have hsin_pos : 0 < Real.sin (δ * (Real.pi / 12)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [fdBoundary_three_sub_sub_rho_eq H hδ hδ2,
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith [Real.pi_pos]) (by simp; nlinarith [Real.pi_pos])]

/-- The principal logarithm of the shifted contour just after the corner. -/
theorem log_fdBoundary_three_add_sub_rho (hH : Real.sqrt 3 / 2 < H) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1) :
    Complex.log (fdBoundary H (3 + δ) - (UpperHalfPlane.ρ : ℂ)) =
      ((Real.log (δ * (H - Real.sqrt 3 / 2)) : ℝ) : ℂ) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have heval : fdBoundary H (3 + δ) - (UpperHalfPlane.ρ : ℂ) =
      ((δ * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
    rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨by linarith, by linarith⟩]
    norm_num
  rw [heval, Complex.log_ofReal_mul (by positivity) Complex.I_ne_zero, Complex.log_I,
    Complex.ofReal_div, Complex.ofReal_ofNat]


/-- The contour passes through `ρ` only at the corner `t = 3`. -/
theorem eq_three_of_fdBoundary_eq_rho (hH : H ≠ Real.sqrt 3 / 2)
    (heq : fdBoundary H t = (UpperHalfPlane.ρ : ℂ)) : t = 3 := by
  rcases lt_trichotomy t 3 with h3 | h3 | h3
  · exact absurd (sub_eq_zero.mpr heq)
      (Complex.slitPlane_ne_zero (fdBoundary_sub_rho_mem_slitPlane_of_lt_three H h3))
  · exact h3
  · exact absurd (sub_eq_zero.mpr heq)
      (Complex.slitPlane_ne_zero (fdBoundary_sub_rho_mem_slitPlane_of_three_lt hH h3))

end ModularForm

end TauCeti

end
