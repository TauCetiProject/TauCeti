/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.CutoffKernel
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Decay
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The dual Mellin cutoff kernel of an approximate functional equation

A smoothed approximate functional equation weights the terms of a Dirichlet series with the Mellin
cutoff kernel `F₁(φ, x) = ∫_{(x,∞)} φ(y) dy/y` (`TauCeti.mellinCutoffKernel`) of a cutoff
`φ : ℝ → ℂ`, and the terms of its dual series with the *dual Mellin cutoff kernel*
`F₂(φ, G, β, x) = (2π)⁻¹ ∫_ℝ x^{-s} mellin φ (-s) G(β - s) / s dt` along the line `s = 2 + it`,
for a function `G` (in applications a ratio of gamma factors) and a parameter `β`. For `G = 1`
the dual kernel is the cutoff kernel of the reflected cutoff `y ↦ φ (1 / y)`, by
`mellin_comp_inv`.

## Main definitions

* `TauCeti.dualMellinCutoffKernel φ G β x`: the kernel `F₂(φ, G, β, x)`.

## Main results

* `TauCeti.dualMellinCutoffKernel_zero_right`, `TauCeti.dualMellinCutoffKernel_zero_left`: the
  dual kernel vanishes for `G = 0` and for `φ = 0`.
* `MellinConvergent.dualMellinCutoffKernel_one_right`,
  `ContDiffOn.dualMellinCutoffKernel_one_right`: for `G = 1` the dual kernel is the cutoff kernel
  of `y ↦ φ (1 / y)`.

## References

* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equation (3.7) and Lemma 3.1.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti

variable {φ : ℝ → ℂ} {x : ℝ}

/-- The *dual Mellin cutoff kernel*
`F₂(φ, G, β, x) = (2π)⁻¹ ∫_ℝ x^{-s} mellin φ (-s) G(β - s) / s dt`, `s = 2 + it`, of a cutoff
`φ`, a function `G` and a parameter `β`. No growth condition on `G` is imposed: when the integrand
is not integrable the Bochner integral is `0`. -/
noncomputable def dualMellinCutoffKernel (φ : ℝ → ℂ) (G : ℂ → ℂ) (β : ℂ) (x : ℝ) : ℂ :=
  mellinInv 2 (fun s ↦ mellin φ (-s) * G (β - s) / s) x

theorem dualMellinCutoffKernel_def (φ : ℝ → ℂ) (G : ℂ → ℂ) (β : ℂ) (x : ℝ) :
    dualMellinCutoffKernel φ G β x = mellinInv 2 (fun s ↦ mellin φ (-s) * G (β - s) / s) x :=
  (rfl)

/-- The dual kernel of the zero function `G = 0` vanishes. -/
@[simp]
theorem dualMellinCutoffKernel_zero_right (φ : ℝ → ℂ) (β : ℂ) (x : ℝ) :
    dualMellinCutoffKernel φ 0 β x = 0 := by
  simp [dualMellinCutoffKernel_def, mellinInv]

/-- The dual kernel of the zero cutoff `φ = 0` vanishes. -/
@[simp]
theorem dualMellinCutoffKernel_zero_left (G : ℂ → ℂ) (β : ℂ) (x : ℝ) :
    dualMellinCutoffKernel 0 G β x = 0 := by
  simp [dualMellinCutoffKernel_def, mellinInv, mellin]

/-- For `G = 1` the dual kernel is the cutoff kernel of the reflected cutoff `y ↦ φ (1 / y)`:
`F₂(φ, 1, β, x) = F₁(φ ∘ inv, x)` for `x > 0`, if `φ` is Mellin convergent at `-2` and
`s ↦ mellin φ (-s) / s` is integrable on the line `Re s = 2`. -/
theorem _root_.MellinConvergent.dualMellinCutoffKernel_one_right (hφ : MellinConvergent φ (-2))
    (hV : VerticalIntegrable (fun s ↦ mellin φ (-s) / s) 2) (β : ℂ) (hx : 0 < x) :
    dualMellinCutoffKernel φ 1 β x = mellinCutoffKernel (fun y ↦ φ y⁻¹) x := by
  have hφ' : MellinConvergent (fun y ↦ φ y⁻¹) (2 : ℝ) := by
    have h := (MellinConvergent.comp_rpow (f := φ) (s := 2) (a := -1) (by norm_num)).mpr
      (by convert hφ using 1; norm_num)
    simpa only [Real.rpow_neg_one, ofReal_ofNat] using h
  have hV' : VerticalIntegrable (fun s ↦ mellin (fun y ↦ φ y⁻¹) s / s) 2 := by
    simpa only [mellin_comp_inv] using hV
  rw [hφ'.mellinCutoffKernel_eq_mellinInv hV' two_pos hx, dualMellinCutoffKernel_def]
  simp only [Pi.one_apply, mul_one, mellin_comp_inv]

/-- For `G = 1` the dual kernel is the cutoff kernel of the reflected cutoff `y ↦ φ (1 / y)`:
`F₂(φ, 1, β, x) = F₁(φ ∘ inv, x)` for `φ` of class `C¹` on `(0, ∞)` with compact positive
closed support and `x > 0`. -/
theorem _root_.ContDiffOn.dualMellinCutoffKernel_one_right (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : IsCompact (tsupport φ ∩ Ioi 0)) (β : ℂ) (hx : 0 < x) :
    dualMellinCutoffKernel φ 1 β x = mellinCutoffKernel (fun y ↦ φ y⁻¹) x := by
  have hφ' : ContDiffOn ℝ 1 (fun y ↦ φ y⁻¹) (Ioi 0) :=
    hφ.comp ((contDiffOn_inv ℝ).mono fun y hy ↦ ne_of_gt hy) fun y hy ↦ inv_pos.mpr hy
  have hm := (hφ.continuousOn.locallyIntegrableOn
    measurableSet_Ioi).mellinConvergent_of_isCompact_tsupport_inter_Ioi hc (-2)
  exact hm.dualMellinCutoffKernel_one_right
    (by simpa only [mellin_comp_inv] using
      hφ'.verticalIntegrable_mellin_div hc.tsupport_comp_inv_inter_Ioi two_ne_zero) β hx

end TauCeti
