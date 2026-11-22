/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.Winding.Number.Circle.Basic

/-!
# Cauchy integral lemmas on circles and concentric annuli

This file collects general circle-integral Cauchy lemmas that do not depend on Laurent series or
rectangles:

* the divided-difference identity `TauCeti.circleIntegral_dslope_eq` and the two-circle Cauchy
  formula on a closed annulus off a countable exceptional set
  (`two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus_off_countable`);
* the signed-kernel conversions `TauCeti.Contour.circleIntegral_sub_inv_smul_eq_neg` and
  `TauCeti.Contour.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq_neg`;
* off-circle complex differentiability of `s ↦ ∮ w in C(c, r), (s - w)⁻¹ • f w`
  (`TauCeti.Contour.hasDerivAt_circleIntegral_sub_inv_smul_left`,
  `TauCeti.Contour.differentiableAt_circleIntegral_sub_inv_smul_left`, and
  `TauCeti.Contour.differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left`);
* the annulus subtraction formula
  (`TauCeti.Contour.sub_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq`) expressing
  `f w - (2πi)⁻¹ • ∮ z in C(c, r), (w - z)⁻¹ • f z` as the interior Cauchy integral over
  `C(c, R)`.

## Main results

* `TauCeti.circleIntegral_dslope_eq`
* `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus_off_countable`
* `TauCeti.Contour.circleIntegral_sub_inv_smul_eq_neg`
* `TauCeti.Contour.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq_neg`
* `TauCeti.Contour.hasDerivAt_circleIntegral_sub_inv_smul_left`
* `TauCeti.Contour.differentiableAt_circleIntegral_sub_inv_smul_left`
* `TauCeti.Contour.differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left`
* `TauCeti.Contour.sub_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq`

## Provenance

The divided-difference proof of the two-circle annulus Cauchy formula is adapted from Mathlib's
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux`, by Yury Kudryashov,
from a disc to an annulus.
-/

public section

open Complex Set Metric Filter
open scoped Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The circle integral of the divided difference `dslope f w` around a circle avoiding `w` is
the difference of the Cauchy integral of `f` and the circle integral of `(z - w)⁻¹` times `f w`.
Only integrability of `f` on the circle is needed. -/
theorem circleIntegral_dslope_eq {f : ℂ → E} {c w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : CircleIntegrable f c ρ) (hw : w ∉ sphere c ρ) :
    (∮ z in C(c, ρ), dslope f w z) =
      (∮ z in C(c, ρ), (z - w)⁻¹ • f z) - (∮ z in C(c, ρ), (z - w)⁻¹) • f w := by
  have hne : ∀ z ∈ sphere c ρ, z ≠ w := fun _ hz => ne_of_mem_of_not_mem hz hw
  have hw' : w ∉ sphere c |ρ| := by rwa [abs_of_nonneg hρ]
  have hi₁ : CircleIntegrable (fun z => (z - w)⁻¹ • f z) c ρ := by
    simpa only [zpow_neg_one] using hf.sub_zpow_smul (-1) hw'
  have hi₂ : CircleIntegrable (fun z => (z - w)⁻¹ • f w) c ρ := by
    simpa only [zpow_neg_one] using (circleIntegrable_const (f w) c ρ).sub_zpow_smul (-1) hw'
  rw [← circleIntegral.integral_smul_const, ← circleIntegral.integral_sub hi₁ hi₂]
  apply circleIntegral.integral_congr hρ
  intro z hz
  simp only [dslope_of_ne _ (hne z hz), slope, vsub_eq_sub, smul_sub]

/-- The two-circle Cauchy formula on an annulus. The function is continuous on the closed
annulus and complex differentiable outside a countable exceptional set in the open annulus.
The evaluation point may belong to the exceptional set. -/
theorem
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus_off_countable
    {f : ℂ → E} {c w : ℂ} {r R : ℝ} (hr : 0 < r)
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R \ closedBall c r)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (2 * π * I : ℂ)⁻¹ •
        ((∮ z in C(c, R), (z - w)⁻¹ • f z) -
          ∮ z in C(c, r), (z - w)⁻¹ • f z) = f w := by
  have hrw : r < dist w c := lt_of_not_ge hw.2
  have hrR : r ≤ R := (hrw.trans hw.1).le
  have hR : 0 < R := hr.trans_le hrR
  have hU : IsOpen (ball c R \ closedBall c r) := isOpen_ball.sdiff isClosed_closedBall
  have hUA : ball c R \ closedBall c r ⊆ closedBall c R \ ball c r :=
    fun _ hz => ⟨ball_subset_closedBall hz.1, fun h => hz.2 (ball_subset_closedBall h)⟩
  have hA : closedBall c R \ ball c r ∈ 𝓝 w := mem_of_superset (hU.mem_nhds hw) hUA
  -- Mathlib's local Cauchy formula removes countable exceptions by continuity and closure.
  have hdf : DifferentiableAt ℂ f w := by
    obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hw)
    have hf := Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
      (R := ⟨ε, hε.le⟩) hs (hc.mono (hεU.trans hUA))
      (fun z hz => hd z ⟨hεU (ball_subset_closedBall hz.1), hz.2⟩) hε
    exact hf.analyticAt.differentiableAt
  -- Fill the divided difference at w; Cauchy-Goursat permits the enlarged exceptional set.
  have hcd : ContinuousOn (dslope f w) (closedBall c R \ ball c r) :=
    (continuousOn_dslope hA).2 ⟨hc, hdf⟩
  have hid := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (hs.insert w) hcd (fun z hz =>
      (differentiableAt_dslope_of_ne
        (ne_of_mem_of_not_mem (mem_insert w s) hz.2).symm).2
          (hd z (sdiff_subset_sdiff_right (subset_insert w s) hz)))
  have hRA : sphere c R ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨sphere_subset_closedBall hz, fun hzr =>
      (not_lt_of_ge hrR) ((mem_sphere.mp hz) ▸ hzr)⟩
  have hrA : sphere c r ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨closedBall_subset_closedBall hrR (sphere_subset_closedBall hz),
      fun h => (ne_of_lt h) (mem_sphere.mp hz)⟩
  have hwR : w ∉ sphere c R := fun h => (ne_of_lt hw.1) (mem_sphere.mp h)
  have hwr : w ∉ sphere c r := fun h => hw.2 (sphere_subset_closedBall h)
  rw [circleIntegral_dslope_eq hR.le ((hc.mono hRA).circleIntegrable hR.le) hwR,
    circleIntegral_dslope_eq hr.le ((hc.mono hrA).circleIntegrable hr.le) hwr,
    circleIntegral.integral_sub_inv_of_mem_ball hw.1,
    Contour.circleIntegral_sub_inv_eq_zero_of_lt_dist hr.le hrw, zero_smul, sub_zero] at hid
  have hdiff : (∮ z in C(c, R), (z - w)⁻¹ • f z) -
      (∮ z in C(c, r), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hid).trans (add_comm _ _))
  rw [hdiff, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]

namespace Contour

omit [CompleteSpace E] in
/-- Reversing the sign in the Cauchy kernel negates the circle integral:
`∮ w in C(c, r), (z - w)⁻¹ • f w = -(∮ w in C(c, r), (w - z)⁻¹ • f w)`. -/
theorem circleIntegral_sub_inv_smul_eq_neg (f : ℂ → E) (c z : ℂ) (r : ℝ) :
    (∮ w in C(c, r), (z - w)⁻¹ • f w) = -(∮ w in C(c, r), (w - z)⁻¹ • f w) := by
  calc ∮ w in C(c, r), (z - w)⁻¹ • f w
      = ∮ w in C(c, r), (-1 : ℂ) • ((w - z)⁻¹ • f w) := by
        simp only [circleIntegral]
        refine intervalIntegral.integral_congr fun θ _ ↦ ?_
        congr 1
        rw [neg_one_smul, ← neg_smul, ← inv_neg, neg_sub]
    _ = (-1 : ℂ) • ∮ w in C(c, r), (w - z)⁻¹ • f w :=
        circleIntegral.integral_smul _ _ _ _
    _ = -(∮ w in C(c, r), (w - z)⁻¹ • f w) := neg_one_smul _ _

omit [CompleteSpace E] in
/-- Reversing the sign in the Cauchy kernel negates the `(2πi)⁻¹`-normalized circle integral. -/
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq_neg (f : ℂ → E) (c z : ℂ) (r : ℝ) :
    (2 * π * I : ℂ)⁻¹ • (∮ w in C(c, r), (z - w)⁻¹ • f w) =
      -((2 * π * I : ℂ)⁻¹ • ∮ w in C(c, r), (w - z)⁻¹ • f w) := by
  rw [circleIntegral_sub_inv_smul_eq_neg, smul_neg]

omit [CompleteSpace E] in
/-- Away from `sphere c |r|`, `s ↦ ∮ w in C(c, r), (s - w)⁻¹ • f w` has derivative
`-(∮ w in C(c, r), (z - w) ^ (-2 : ℤ) • f w)` at `z`. -/
theorem hasDerivAt_circleIntegral_sub_inv_smul_left {f : ℂ → E} {c z : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (hz : z ∉ sphere c |r|) :
    HasDerivAt (fun s ↦ ∮ w in C(c, r), (s - w)⁻¹ • f w)
      (-(∮ w in C(c, r), (z - w) ^ (-2 : ℤ) • f w)) z := by
  have heq : (fun s ↦ ∮ w in C(c, r), (s - w)⁻¹ • f w) =
      fun s ↦ -(∮ w in C(c, r), (w - s)⁻¹ • f w) :=
    funext fun s ↦ circleIntegral_sub_inv_smul_eq_neg f c s r
  rw [heq]
  refine (hasDerivAt_circleIntegral_sub_inv_smul hf hz).neg.congr_deriv ?_
  congr 1
  simp only [circleIntegral]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  congr 2
  rw [← neg_sub z (circleMap c r θ), show (-2 : ℤ) = -(2 : ℕ) by rfl, zpow_neg, zpow_neg,
    zpow_natCast, neg_sq]
  norm_cast

omit [CompleteSpace E] in
/-- The exterior Cauchy integral `s ↦ ∮ w in C(c, r), (s - w)⁻¹ • f w` is complex
differentiable at every point off `sphere c |r|`. -/
theorem differentiableAt_circleIntegral_sub_inv_smul_left {f : ℂ → E} {c z : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (hz : z ∉ sphere c |r|) :
    DifferentiableAt ℂ (fun s ↦ ∮ w in C(c, r), (s - w)⁻¹ • f w) z :=
  (hasDerivAt_circleIntegral_sub_inv_smul_left hf hz).differentiableAt

omit [CompleteSpace E] in
/-- The normalized exterior Cauchy integral `s ↦ (2πi)⁻¹ • ∮ w in C(c, r), (s - w)⁻¹ • f w`
is complex differentiable at every point off `sphere c |r|`. -/
theorem differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left
    {f : ℂ → E} {c z : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) (hz : z ∉ sphere c |r|) :
    DifferentiableAt ℂ
      (fun s ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(c, r), (s - w)⁻¹ • f w) z :=
  (differentiableAt_circleIntegral_sub_inv_smul_left hf hz).const_smul _

/-- **Annulus subtraction formula.** On the open annulus `ball c R \ closedBall c r` (`0 < r`), if
`f` is continuous on `closedBall c R \ ball c r` and complex differentiable outside a countable
set `s` in `ball c R \ closedBall c r`, then subtracting the exterior Cauchy integral over `C(c, r)`
leaves the interior Cauchy integral over `C(c, R)`, even at points of `s`. -/
theorem sub_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq
    {f : ℂ → E} {c w : ℂ} {r R : ℝ} (hr : 0 < r)
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R \ closedBall c r)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    f w - (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (w - z)⁻¹ • f z =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z := by
  have hann :=
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus_off_countable
      hr hs hw hc hd
  rw [← hann, smul_sub, two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq_neg]
  abel

end Contour

end TauCeti
