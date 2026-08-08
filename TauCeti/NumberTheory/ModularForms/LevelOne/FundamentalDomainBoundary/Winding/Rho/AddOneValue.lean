/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Rho.AddOneGeometry

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The winding number of the boundary contour at `ρ + 1`

The generalized winding number of the truncated-fundamental-domain boundary about the
corner `ρ + 1` is `-1/6`. Over the corner-excised parameter ranges the logarithmic integral
of the shifted contour `t ↦ fdBoundary H t - (ρ + 1)` telescopes piece by piece through the
boundary-tolerant logarithmic fundamental theorem, and the `ε`-excision of the principal
value collapses to exactly those ranges with asymmetric half-widths — linear
`δ_L(ε) = ε/(H - √3/2)` on the vertical side and chord-matched
`δ_R(ε) = 12/π·arcsin(ε/2)` on the arc side. Both endpoint distances are then exactly `ε`,
the log-norm parts cancel, and only the corner angle defect `π/3` survives the limit.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_rho_add_one` (the principal value `-πi/3`).
* `TauCeti.ModularForm.windingNumber_fdBoundary_rho_add_one` (the winding number `-1/6`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean`) this file ports
  onto the current Mathlib pin.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

namespace ModularForm


variable {H δL δR : ℝ}

/-- The ordered slit-plane comparison step of the telescope: the canonical logarithmic FTC
`TauCeti.Contour.integral_deriv_div_eq_log_sub_log` applied to the comparison function, its
integrability from the continuous derivative, both transported to the contour across the
interior agreement. -/
private lemma slit_comparison {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Ioo a b)) (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hne : ∀ t ∈ Icc a b, h t ≠ 0 := fun t ht ↦ Complex.slitPlane_ne_zero (hh_slit t ht)
  have heq' : Set.EqOn (fun t ↦ deriv g t / g t) (fun t ↦ deriv h t / h t) (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    simp only [heq ht, heq.deriv isOpen_Ioo ht]
  have hint : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hne).mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  refine ⟨hint.congr_uIoo fun t ht ↦ (heq' ht).symm, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_uIoo heq'
    _ = Complex.log (h b) - Complex.log (h a) :=
        Contour.integral_deriv_div_eq_log_sub_log countable_empty (hu ▸ hh_cont)
          (fun t ht ↦ (hh_diff t (by
            rw [min_eq_left hab, max_eq_right hab] at ht
            exact ht.1)).hasDerivAt)
          (fun t ht ↦ hh_slit t (hu ▸ ht)) hint
    _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]


/-- The right-vertical piece `[0, 1-δ_L]` of the telescope at `ρ + 1`, stopping short of
the corner. -/
private lemma telescope_rho_add_one_piece_right_vertical (hH : Real.sqrt 3 / 2 < H)
    (hδL : 0 < δL) (hδL1 : δL ≤ 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 0 (1 - δL) ∧
    ∫ t in (0 : ℝ)..(1 - δL),
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H (1 - δL) - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 0 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have hab : (0 : ℝ) ≤ 1 - δL := by linarith
  have heval : ∀ s ∈ Icc (0 : ℝ) (1 - δL), fdBoundary H s = fdBoundary_segment1 H s :=
    fun s hs ↦ fdBoundary_of_le_one (by linarith [hs.2])
  have hd : deriv (fun s ↦ fdBoundary_segment1 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      fun _ ↦ (UpperHalfPlane.ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment1]
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment1 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment1 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment1 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ (by
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one H ⟨ht.1, by linarith [ht.2]⟩]
      have him : ((((1 - t) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I).im =
          (1 - t) * (H - Real.sqrt 3 / 2) := by simp
      rw [him]
      have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
      positivity))
    (fun t ht ↦ congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 0 (left_mem_Icc.mpr hab)))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval (1 - δL) (right_mem_Icc.mpr hab)))

/-- The first arc piece `[1+δ_R, 2]` of the telescope at `ρ + 1`, starting past the
corner. -/
private lemma telescope_rho_add_one_piece_arc_first (H : ℝ) (hδR : 0 < δR) (hδR1 : δR < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume (1 + δR) 2 ∧
    ∫ t in (1 + δR : ℝ)..2,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 2 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H (1 + δR) - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have hab : (1 + δR : ℝ) ≤ 2 := by linarith
  have heval : ∀ s ∈ Icc (1 + δR : ℝ) 2, fdBoundary H s = fdBoundary_segment2 s :=
    fun s hs ↦ fdBoundary_of_le_two (by linarith [hs.1]) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment2 s - ((UpperHalfPlane.ρ : ℂ) + 1)) = fun s ↦
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment2]
  have hθc : Continuous fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3) := by
    fun_prop
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment2 s - ((UpperHalfPlane.ρ : ℂ) + 1)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment2 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment2 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (Real.pi / 2 - Real.pi / 3)).continuousOn)
    (fun t ht ↦ heval t ht ▸ Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt
      (im_fdBoundary_sub_rho_add_one_arc_pos H (by linarith [ht.1]) (by linarith [ht.2])))))
    (fun t ht ↦ congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval (1 + δR) (left_mem_Icc.mpr hab)))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 2 (right_mem_Icc.mpr hab)))

/-- The second arc piece `[2, 3]` of the telescope at `ρ + 1`: the shifted contour meets
the branch cut at the right endpoint, so the boundary-tolerant upper form applies. -/
private lemma telescope_rho_add_one_piece_arc_second (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 2 3 ∧
    ∫ t in (2 : ℝ)..3,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 3 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 2 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have heval : ∀ s ∈ Icc (2 : ℝ) 3, fdBoundary H s = fdBoundary_segment3 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h2 | h2
    · rw [← h2, fdBoundary_apply_two, fdBoundary_segment3_apply_two]
    · exact fdBoundary_of_le_three h2 hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1)) = fun s ↦
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment3]
  have hθc : Continuous fun s : ℝ ↦
      Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
    fun_prop
  have hne : ∀ t ∈ Icc (2 : ℝ) 3, fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h3 | h3
    · rw [h3, fdBoundary_apply_three_sub_rho_add_one]
      norm_num
    · have him := im_fdBoundary_sub_rho_add_one_arc_pos H (by linarith [ht.1]) h3
      exact fun h0 ↦ by rw [h0] at him; simp at him
  have hu : uIcc (2 : ℝ) 3 = Icc 2 3 := uIcc_of_le (by norm_num)
  have ho : Ioo (min (2 : ℝ) 3) (max (2 : ℝ) 3) = Ioo 2 3 := by
    rw [min_eq_left (by norm_num : (2 : ℝ) ≤ 3), max_eq_right (by norm_num : (2 : ℝ) ≤ 3)]
  have hcont : ContinuousOn (fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1))
      (Icc (2 : ℝ) 3) :=
    Continuous.continuousOn (Differentiable.continuous fun s ↦
      (hasDerivAt_fdBoundary_segment3 s).differentiableAt.sub_const _)
  have hne' : ∀ t ∈ Icc (2 : ℝ) 3,
      fdBoundary_segment3 t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := fun t ht ↦
    heval t ht ▸ hne t ht
  have hint : IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary_segment3 t - ((UpperHalfPlane.ρ : ℂ) + 1))) volume 2 3 :=
    ((((by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (2 * Real.pi / 3 - Real.pi / 2)).continuousOn :
        ContinuousOn (deriv fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1))
          (Icc (2 : ℝ) 3))).div hcont hne').mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  exact Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1)) countable_empty
    (hu ▸ hcont)
    (fun t ht ↦ (hasDerivAt_fdBoundary_segment3 t).differentiableAt.sub_const _)
    hint
    (fun t ht ↦ by
      rw [hu] at ht
      exact heval t ht ▸ im_fdBoundary_sub_rho_add_one_arc_nonneg H ⟨by linarith [ht.1], ht.2⟩)
    (hne' 2 (left_mem_Icc.mpr (by norm_num)))
    (hne' 3 (right_mem_Icc.mpr (by norm_num)))
    (fun t ht ↦ by
      rw [ho] at ht
      exact heval t ⟨ht.1.le, ht.2.le⟩ ▸ Complex.mem_slitPlane_iff.mpr (Or.inr
        (ne_of_gt (im_fdBoundary_sub_rho_add_one_arc_pos H (by linarith [ht.1]) ht.2))))
    (fun t ht ↦ by
      rw [ho] at ht
      exact congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 2 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 3 (right_mem_Icc.mpr (by norm_num))))

/-- The left-vertical piece `[3, 4]` of the telescope at `ρ + 1`: the shifted contour
leaves the branch cut at the left endpoint, so the boundary-tolerant upper form
applies. -/
private lemma telescope_rho_add_one_piece_left_vertical (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 3 4 ∧
    ∫ t in (3 : ℝ)..4,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 4 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 3 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have heval : ∀ s ∈ Icc (3 : ℝ) 4, fdBoundary H s = fdBoundary_segment4 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h3 | h3
    · rw [← h3, fdBoundary_apply_three, fdBoundary_segment4_apply_three]
    · exact fdBoundary_of_le_four h3 hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  have him : ∀ t ∈ Icc (3 : ℝ) 4,
      (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im =
        (t - 3) * (H - Real.sqrt 3 / 2) := fun t ht ↦ by
    rw [fdBoundary_sub_rho_add_one_of_mem_Icc_three_four H ht]
    simp
  have hne : ∀ t ∈ Icc (3 : ℝ) 4, fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := by
    intro t ht h0
    have hre : (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).re = -1 := by
      rw [fdBoundary_sub_rho_add_one_of_mem_Icc_three_four H ht]
      simp
    rw [h0] at hre
    norm_num at hre
  have hu : uIcc (3 : ℝ) 4 = Icc 3 4 := uIcc_of_le (by norm_num)
  have ho : Ioo (min (3 : ℝ) 4) (max (3 : ℝ) 4) = Ioo 3 4 := by
    rw [min_eq_left (by norm_num : (3 : ℝ) ≤ 4), max_eq_right (by norm_num : (3 : ℝ) ≤ 4)]
  have hcont : ContinuousOn (fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1))
      (Icc (3 : ℝ) 4) :=
    Continuous.continuousOn (Differentiable.continuous fun s ↦
      (hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)
  have hne' : ∀ t ∈ Icc (3 : ℝ) 4,
      fdBoundary_segment4 H t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := fun t ht ↦
    heval t ht ▸ hne t ht
  have hint : IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary_segment4 H t - ((UpperHalfPlane.ρ : ℂ) + 1))) volume 3 4 :=
    ((((by rw [hd]; exact continuousOn_const :
        ContinuousOn (deriv fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1))
          (Icc (3 : ℝ) 4))).div hcont hne').mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  exact Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) countable_empty
    (hu ▸ hcont)
    (fun t ht ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    hint
    (fun t ht ↦ by
      rw [hu] at ht
      exact heval t ht ▸ (by
        rw [him t ht]
        exact mul_nonneg (by linarith [ht.1]) (by linarith)))
    (hne' 3 (left_mem_Icc.mpr (by norm_num)))
    (hne' 4 (right_mem_Icc.mpr (by norm_num)))
    (fun t ht ↦ by
      rw [ho] at ht
      exact heval t ⟨ht.1.le, ht.2.le⟩ ▸ Complex.mem_slitPlane_iff.mpr (Or.inr (by
        rw [him t ⟨ht.1.le, ht.2.le⟩]
        have := mul_pos (by linarith [ht.1] : (0 : ℝ) < t - 3) (by linarith :
          (0 : ℝ) < H - Real.sqrt 3 / 2)
        linarith)))
    (fun t ht ↦ by
      rw [ho] at ht
      exact congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 3 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 4 (right_mem_Icc.mpr (by norm_num))))

/-- The ceiling piece `[4, 5]` of the telescope at `ρ + 1`. -/
private lemma telescope_rho_add_one_piece_ceiling (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 4 5 ∧
    ∫ t in (4 : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 5 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 4 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have heval : ∀ s ∈ Icc (4 : ℝ) 5, fdBoundary H s = fdBoundary_segment5 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h4 | h4
    · rw [← h4, fdBoundary_apply_four, fdBoundary_segment5_apply_four]
    · exact fdBoundary_of_gt_four h4
  have hd : deriv (fun s ↦ fdBoundary_segment5 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      fun _ ↦ (1 : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment5]
  have hslit : ∀ t ∈ Icc (4 : ℝ) 5,
      fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) ∈ Complex.slitPlane := by
    intro t ht
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im =
        H - Real.sqrt 3 / 2 := by
      rw [Complex.sub_im, im_fdBoundary_segment5 H ht]
      norm_num [UpperHalfPlane.ρ]
    rw [him]
    linarith
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment5 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment5 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment5 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ hslit t ht)
    (fun t ht ↦ congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 4 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 5 (right_mem_Icc.mpr (by norm_num))))

/-- **The logarithmic telescope at `ρ + 1`**: over the corner-excluded ranges the
logarithmic integral of the shifted contour is integrable and evaluates to the
difference of the endpoint logarithms beside the corner — the branch-cut touch at
`t = 3` passes through the principal logarithm without a jump. -/
private theorem ftc_logDeriv_telescope_rho_add_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL1 : δL ≤ 1) (hδR : 0 < δR) (hδR1 : δR < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 0 (1 - δL) ∧
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume (1 + δR) 5 ∧
    (∫ t in (0 : ℝ)..(1 - δL),
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))) +
      (∫ t in (1 + δR : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))) =
      Complex.log (fdBoundary H (1 - δL) - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H (1 + δR) - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  obtain ⟨hi01, he01⟩ := telescope_rho_add_one_piece_right_vertical hH hδL hδL1
  obtain ⟨hi12, he12⟩ := telescope_rho_add_one_piece_arc_first H hδR hδR1
  obtain ⟨hi23, he23⟩ := telescope_rho_add_one_piece_arc_second H
  obtain ⟨hi34, he34⟩ := telescope_rho_add_one_piece_left_vertical hH
  obtain ⟨hi45, he45⟩ := telescope_rho_add_one_piece_ceiling hH
  have hint13 := hi12.trans hi23
  have hint34 := hi34.trans hi45
  refine ⟨hi01, hint13.trans hint34, ?_⟩
  have hlog50 : Complex.log (fdBoundary H 5 - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 0 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
    rw [fdBoundary_apply_five, fdBoundary_apply_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint13 hint34,
    ← intervalIntegral.integral_add_adjacent_intervals hi12 hi23,
    ← intervalIntegral.integral_add_adjacent_intervals hi34 hi45,
    he01, he12, he23, he34, he45, hlog50]
  ring


variable {H ε δ t : ℝ}

/-- Far from the corner along the arc, the chord distance strictly exceeds the excision
chord. -/
private lemma lt_norm_fdBoundary_sub_rho_add_one_arc_of_far (harc : t ∈ Icc (1 : ℝ) 3)
    (hd : 0 < δ) (hd1 : δ < 1) (hfar : δ < t - 1) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := by
  rw [norm_fdBoundary_sub_rho_add_one_arc H harc,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos, harc.1]) (by nlinarith [Real.pi_pos, harc.2]))]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin ((t - 1) * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, harc.1], by nlinarith [Real.pi_pos, harc.2]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the corner along the arc, the chord distance is at most the excision chord. -/
private lemma norm_fdBoundary_sub_rho_add_one_arc_le_of_near (harc : t ∈ Icc (1 : ℝ) 3)
    (hd1 : δ < 1) (hnear : t - 1 ≤ δ) :
    ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ ≤
      2 * Real.sin (δ * (Real.pi / 12)) := by
  have hd0 : 0 ≤ δ := le_trans (by linarith [harc.1]) hnear
  rw [norm_fdBoundary_sub_rho_add_one_arc H harc,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos, harc.1]) (by nlinarith [Real.pi_pos, harc.2]))]
  have hmono : Real.sin ((t - 1) * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin.monotoneOn
      ⟨by nlinarith [Real.pi_pos, harc.1], by nlinarith [Real.pi_pos, harc.2]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- Left of the excised corner, the contour keeps distance more than `ε` from `ρ + 1`. -/
private lemma lt_norm_of_far_left_rho_add_one (hH : Real.sqrt 3 / 2 < H) (hd : 0 < δ)
    (hlin : δ * (H - Real.sqrt 3 / 2) = ε) (ht : t ∈ Ico (0 : ℝ) (1 - δ)) :
    ε < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := by
  rw [fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one H ⟨ht.1, by linarith [ht.2]⟩, ← hlin,
    norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by linarith [ht.2]) (by linarith))]
  exact mul_lt_mul_of_pos_right (by linarith [ht.2]) (by linarith)

/-- Right of the excised corner, the contour keeps distance more than `ε` from
`ρ + 1`. -/
private lemma lt_norm_of_far_right_rho_add_one (hε₁ : ε < 1)
    (hεH : ε < H - Real.sqrt 3 / 2) (hd : 0 < δ) (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Ioc (1 + δ : ℝ) 5) :
    ε < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := by
  rcases le_or_gt t 3 with ht3 | ht3
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_rho_add_one_arc_of_far ⟨by linarith [ht.1], ht3⟩ hd hd1 ?_
    linarith [ht.1]
  · rcases le_or_gt t 4 with ht4 | ht4
    · calc ε < 1 := hε₁
        _ ≤ ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ :=
          norm_fdBoundary_sub_rho_add_one_segment4 H ⟨ht3.le, ht4⟩
    · calc ε < H - Real.sqrt 3 / 2 := hεH
        _ ≤ ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ :=
          norm_fdBoundary_sub_rho_add_one_segment5 (H := H) ⟨ht4.le, ht.2⟩

/-- Over the excised corner, the contour stays within distance `ε` of `ρ + 1`. -/
private lemma norm_le_of_near_rho_add_one {δL δR : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hδL1 : δL ≤ 1) (hlin : δL * (H - Real.sqrt 3 / 2) = ε)
    (hδR1 : δR < 1) (h2sin : 2 * Real.sin (δR * (Real.pi / 12)) = ε)
    (ht : t ∈ Icc (1 - δL : ℝ) (1 + δR)) :
    ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ ≤ ε := by
  rcases le_or_gt t 1 with h1 | h1
  · rw [fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one H ⟨by linarith [ht.1], h1⟩,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith) (by linarith)), ← hlin]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (by linarith)
  · rw [← h2sin]
    refine norm_fdBoundary_sub_rho_add_one_arc_le_of_near
      ⟨h1.le, by linarith [ht.2]⟩ hδR1 (by linarith [ht.2])

/-- The arc-side excision half-width `δ_R(ε) = 12/π · arcsin(ε/2)` is positive, below
`1`, and turns the chord identity into the exact excision radius `ε`. -/
private lemma delta_right_spec_rho_add_one (hε : 0 < ε)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    0 < 12 / Real.pi * Real.arcsin (ε / 2) ∧ 12 / Real.pi * Real.arcsin (ε / 2) < 1 ∧
      2 * Real.sin (12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12)) = ε := by
  have hπ := Real.pi_pos
  have hsin1 : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _
  have harc_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr (by linarith)
  have harc_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
    have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
      Real.arcsin_lt_arcsin (by linarith) (by linarith) hsin1
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at h1
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_one hπ]
    linarith
  · have hδπ : 12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12) = Real.arcsin (ε / 2) := by
      field_simp
    rw [hδπ, Real.sin_arcsin (by linarith) (by linarith)]
    ring

/-- **The excision collapse at `ρ + 1`**: for small `ε`, the `ε`-excised index integrand
of the boundary contour about `ρ + 1` is interval integrable, and its integral is
exactly `-πi/3 - arcsin(ε/2)·i`. -/
private lemma truncated_integral_spec_rho_add_one (hH : Real.sqrt 3 / 2 < H) (hε : 0 < ε)
    (hε₁ : ε < 1) (hεH : ε < H - Real.sqrt 3 / 2)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖
        then (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) t
        else 0)
      volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖
        then (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) t
        else 0) =
      -((Real.pi : ℂ) / 3) * Complex.I - ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδR_pos, hδR_lt, h2sin⟩ := delta_right_spec_rho_add_one hε hε₃
  set δR := 12 / Real.pi * Real.arcsin (ε / 2) with hδR_def
  have hHpos : (0 : ℝ) < H - Real.sqrt 3 / 2 := by linarith
  set δL := ε / (H - Real.sqrt 3 / 2) with hδL_def
  have hδL_pos : 0 < δL := by rw [hδL_def]; positivity
  have hδL_le : δL ≤ 1 := by
    rw [hδL_def, div_le_one hHpos]
    linarith
  have hlin : δL * (H - Real.sqrt 3 / 2) = ε := by
    rw [hδL_def]
    exact div_mul_cancel₀ ε hHpos.ne'
  obtain ⟨hi_left, hi_right, hval⟩ :=
    ftc_logDeriv_telescope_rho_add_one H hH hδL_pos hδL_le hδR_pos hδR_lt
  have hconv : ∀ s : ℝ,
      (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) s =
      deriv (fun r ↦ fdBoundary H r - ((UpperHalfPlane.ρ : ℂ) + 1)) s /
        (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) :=
    fun s ↦ by rw [deriv_sub_const, inv_mul_eq_div]
  have hae_left : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) (1 - δL) →
      deriv (fun r ↦ fdBoundary H r - ((UpperHalfPlane.ρ : ℂ) + 1)) s /
        (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
        (if ε < ‖fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)‖
          then (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) s
          else 0) := by
    have hb_ae : ({1 - δL} : Set ℝ)ᶜ ∈ ae volume := by
      simp [MeasureTheory.mem_ae_iff]
    filter_upwards [hb_ae] with s hs_ne hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hsIco : s ∈ Ico (0 : ℝ) (1 - δL) := ⟨hmem.1.le,
      lt_of_le_of_ne hmem.2 fun h ↦ hs_ne (mem_singleton_iff.mpr h)⟩
    rw [if_pos (lt_norm_of_far_left_rho_add_one hH hδL_pos hlin hsIco), hconv s]
  have hae_right : ∀ᵐ s ∂volume, s ∈ uIoc (1 + δR : ℝ) 5 →
      deriv (fun r ↦ fdBoundary H r - ((UpperHalfPlane.ρ : ℂ) + 1)) s /
        (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
        (if ε < ‖fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)‖
          then (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) s
          else 0) := by
    refine Eventually.of_forall fun s hmem ↦ ?_
    rw [uIoc_of_le (by linarith)] at hmem
    rw [if_pos (lt_norm_of_far_right_rho_add_one hε₁ hεH hδR_pos hδR_lt h2sin hmem), hconv s]
  have hmid : EqOn (fun s ↦ if ε < ‖fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)‖
      then (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) s
      else 0)
      (fun _ ↦ (0 : ℂ)) (uIcc (1 - δL : ℝ) (1 + δR)) := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    exact if_neg (not_lt.mpr (norm_le_of_near_rho_add_one hH hδL_le hlin hδR_lt h2sin hs))
  have hi02 := hi_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_left)
  have hi25 := hi_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_right)
  have himid : IntervalIntegrable (fun s ↦
      if ε < ‖fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)‖
        then (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) s
        else 0)
      volume (1 - δL) (1 + δR) := by
    refine (intervalIntegrable_const (c := (0 : ℂ))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun s hs ↦ ?_))
    rw [uIoc_of_le (by linarith)] at hs
    have hsub : s ∈ uIcc (1 - δL : ℝ) (1 + δR) := by
      rw [uIcc_of_le (by linarith : (1 - δL : ℝ) ≤ 1 + δR)]
      exact Ioc_subset_Icc_self hs
    exact (hmid hsub).symm
  refine ⟨(hi02.trans himid).trans hi25, ?_⟩
  have hδ12 : δR * (Real.pi / 12) = Real.arcsin (ε / 2) := by
    rw [hδR_def]
    field_simp
  have hmid0 : ∫ s in (1 - δL : ℝ)..(1 + δR),
      (if ε < ‖fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)‖
        then (fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) s
        else 0) = 0 := by
    rw [intervalIntegral.integral_congr hmid]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi02.trans himid) hi25,
    ← intervalIntegral.integral_add_adjacent_intervals hi02 himid,
    hmid0, add_zero,
    ← intervalIntegral.integral_congr_ae hae_left,
    ← intervalIntegral.integral_congr_ae hae_right,
    hval, log_fdBoundary_one_sub_sub_rho_add_one hH hδL_pos hδL_le,
    log_fdBoundary_one_add_sub_rho_add_one H hδR_pos (hδR_lt.le.trans one_le_two), hlin,
    h2sin, hδ12]
  push_cast
  ring

/-- **The principal value at `ρ + 1`**: the Cauchy principal value of the index
integrand of the boundary contour about the corner `ρ + 1` is `-πi/3` — the corner's
angle defect. -/
theorem hasCauchyPVAt_fdBoundary_rho_add_one (hH : Real.sqrt 3 / 2 < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5
      (fun z ↦ (z - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹) ((UpperHalfPlane.ρ : ℂ) + 1)
      (-((Real.pi : ℂ) / 3) * Complex.I) := by
  have hsin12 : 0 < 2 * Real.sin (Real.pi / 12) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 12) (by positivity)
      (by linarith [Real.pi_pos])
    linarith
  have hε₀ : 0 < min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12)) :=
    lt_min (lt_min (by norm_num) (by linarith)) hsin12
  have hIoo : Ioo (0 : ℝ)
      (min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12))) ∈
      𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12))),
      IntervalIntegrable (fun t ↦
          if ε < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖
            then (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) t
            else 0)
        volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖
          then (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))⁻¹ * deriv (fdBoundary H) t
          else 0) =
        -((Real.pi : ℂ) / 3) * Complex.I - ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec_rho_add_one hH hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le (min_le_right _ _))
  have hcont : Tendsto (fun ε : ℝ ↦ -((Real.pi : ℂ) / 3) * Complex.I -
      ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-((Real.pi : ℂ) / 3) * Complex.I)) := by
    have hc : Continuous fun ε : ℝ ↦ -((Real.pi : ℂ) / 3) * Complex.I -
        ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
      refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      exact Real.continuous_arcsin.comp (continuous_id.div_const 2)
    simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ hcont
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at `ρ + 1` is `-1/6`**: the corner
`ρ + 1` sits on the contour with interior angle `2π/3`, and the principal-value
normalization sees exactly the angle defect `π/3` of a clockwise turn. -/
theorem windingNumber_fdBoundary_rho_add_one (hH : Real.sqrt 3 / 2 < H) :
    Contour.windingNumber (fdBoundary H) 0 5 ((UpperHalfPlane.ρ : ℂ) + 1) =
      -(1 / 6 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_fdBoundary_rho_add_one hH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

end ModularForm

end TauCeti

end
