/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
public import TauCeti.Analysis.Sobolev.BesselPotential.Exp

/-!
# The Sobolev framed gauge group is a Lie group

For a real order `s > 1`, the Sobolev framed gauge group `G_s` of plane vortices
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) is a manifold modelled on the real `H^s` phases,
with the exponential charts `F ↦ u exp (i F)` (`TauCeti.Vortex.gaugeChart`). This file shows that
`G_s` is a Lie group in these charts, and that the embedding `u ↦ u - 1` of `G_s` into `H^s(ℂ)`,
which defines its topology, is smooth for this manifold structure.

**Group operations.** The group `G_s` is commutative, so in the charts at `u` and `v` the product
is `(F, G) ↦ F + G` in the chart at `u v`, and in the charts at `u` and `u⁻¹` inversion is
`F ↦ -F`. Hence multiplication and inversion are smooth of every order, analytic included
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.instLieGroup`), and the exponential, which is the
inverse of the chart at `1`, is smooth (`TauCeti.Vortex.contMDiff_expGauge`).

**The ambient coordinate `u - 1`.** Since `H^s(ℂ)`, `s > 1`, is an algebra
(`BesselPotentialSpace.mulCLM`), the exponential acts on it, and for a real phase `F` the
coordinate `exp (i F) - 1` is the smooth map `BesselPotentialSpace.expSubOne` at `i F`
(`TauCeti.Vortex.subOne_expGauge_eq_expSubOne`). Composing with the real-linear map `F ↦ i F`,
`F ↦ exp (i F) - 1` has derivative `G ↦ i (1 + (exp (i F) - 1)) G` at `F`
(`TauCeti.Vortex.hasFDerivAt_subOne_expGauge`) and is smooth
(`TauCeti.Vortex.contDiff_subOne_expGauge`), so the embedding `u ↦ u - 1`
of `G_s` into `H^s(ℂ)` is smooth (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_subOne`).
So are the real coordinates `Re u - 1 = ((u - 1) + (u⁻¹ - 1)) / 2` and
`Im u = -i ((u - 1) - (u⁻¹ - 1)) / 2`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_reSubOne`,
`TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_imPart`), through which `G_s` acts on the
framed vortex fields. At the identity, in the exponential chart, their derivatives are `0` and
`G ↦ G` (`TauCeti.Vortex.hasFDerivAt_reSubOne_expGauge_zero`,
`TauCeti.Vortex.hasFDerivAt_imPart_expGauge_zero`): `cos F - 1` is quadratic in `F`, and the
linear part of `sin F` is `F`.

## Main results

* `TauCeti.Vortex.subOne_expGauge_eq_expSubOne`: `exp (i F) - 1` is `expSubOne` at `i F`.
* `TauCeti.Vortex.hasFDerivAt_subOne_expGauge`, `TauCeti.Vortex.hasFDerivAt_subOne_expGauge_zero`:
  the derivative of `F ↦ exp (i F) - 1`, which is `G ↦ i G` at `F = 0`.
* `TauCeti.Vortex.contDiff_subOne_expGauge`: `F ↦ exp (i F) - 1` is smooth.
* `TauCeti.Vortex.hasFDerivAt_subOne_inv_expGauge_zero`: the derivative of
  `F ↦ exp (i F)⁻¹ - 1` at `F = 0`, which is `G ↦ -i G`.
* `TauCeti.Vortex.hasFDerivAt_reSubOne_expGauge_zero`,
  `TauCeti.Vortex.hasFDerivAt_imPart_expGauge_zero`: the derivatives of `F ↦ cos F - 1` and
  `F ↦ sin F` at `F = 0`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instLieGroup`: `G_s` is a Lie group.
* `TauCeti.Vortex.contMDiff_gaugeChart_symm`, `TauCeti.Vortex.contMDiff_expGauge`: the inverse
  charts `F ↦ u exp (i F)`, and in particular the exponential, are smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_subOne`: `u ↦ u - 1` is smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_reSubOne`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_imPart`: `u ↦ Re u - 1` and `u ↦ Im u`
  are smooth.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module Set TemperedDistribution BesselPotentialSpace Topology
  Asymptotics
open scoped SchwartzMap BesselPotentialSpace Manifold ContDiff Nat

variable {s : ℝ}

open SobolevTopologicalGaugeGroup

/-- **The exponential coordinate is the exponential of `H^s(ℂ)`**: `exp (i F) - 1` is
`BesselPotentialSpace.expSubOne` at `i F`. -/
theorem subOne_expGauge_eq_expSubOne (hs : 1 < s) (F : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    subOne (expGauge hs F) =
      expSubOne (finrank_real_complex_lt_two_mul hs) (I • (F : H^{s}(ℂ))) := by
  have h : 0 ≤ s := zero_le_one.trans hs.le
  have hd := finrank_real_complex_lt_two_mul hs
  refine eq_expSubOne_of_ae hd h ?_
  have hF : (inclusion h (F : H^{s}(ℂ))).toLp =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
    rw [toLp_inclusion]
    exact coeFn_inclusionLp_ae_eq_continuousRep hd F
  filter_upwards [coeFn_toLp_inclusion_subOne_expGauge hs h F,
    coeFn_toLp_inclusion_smul h I (F : H^{s}(ℂ)), hF] with z h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃, smul_eq_mul, Circle.coe_exp, mul_comm]

/-! ### Smoothness of the exponential coordinate -/

variable {hs : 1 < s}

/-- **The derivative of the exponential coordinate.** The map `F ↦ exp (i F) - 1` from the real
phases to `H^s(ℂ)` has derivative `G ↦ i (1 + (exp (i F) - 1)) G` at `F`, the product being that
of `H^s(ℂ)`. It is `BesselPotentialSpace.expSubOne` composed with `F ↦ i F`. -/
theorem hasFDerivAt_subOne_expGauge (F : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    HasFDerivAt (fun F ↦ subOne (expGauge hs F))
      (((mulCLM (finrank_real_complex_lt_two_mul hs) (subOne (expGauge hs F))).restrictScalars ℝ +
          .id ℝ H^{s}(ℂ)) ∘L (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL)) F := by
  set ι := I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL
  have h := ((hasFDerivAt_expSubOne (finrank_real_complex_lt_two_mul hs) (ι F)).restrictScalars
    ℝ).comp F ι.hasFDerivAt
  convert h using 1
  · exact funext fun G ↦ subOne_expGauge_eq_expSubOne hs G
  · ext G : 1
    simp [subOne_expGauge_eq_expSubOne hs F, ι, add_comm]

/-- At `F = 0` the derivative of `F ↦ exp (i F) - 1` is `G ↦ i G`. -/
theorem hasFDerivAt_subOne_expGauge_zero :
    HasFDerivAt (fun F ↦ subOne (expGauge hs F))
      (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL) 0 := by
  simpa using hasFDerivAt_subOne_expGauge (hs := hs) 0

/-- `u⁻¹ - 1` at `u = exp (i F)` has derivative `G ↦ -i G` at `F = 0`. -/
theorem hasFDerivAt_subOne_inv_expGauge_zero :
    HasFDerivAt (fun F ↦ subOne (expGauge hs F)⁻¹)
      (-(I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL)) 0 := by
  have hg : HasFDerivAt (fun F ↦ subOne (expGauge hs F))
      (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL) (-0) := by
    rw [neg_zero]
    exact hasFDerivAt_subOne_expGauge_zero
  have h := hg.comp (0 : realSubmodule ℂ (zero_le_one.trans hs.le)) (hasFDerivAt_id 0).neg
  simp only [Function.comp_def, AddChar.map_neg_eq_inv] at h
  exact h.congr_fderiv (ContinuousLinearMap.ext fun G ↦ by simp)

/-- **The exponential coordinate is smooth**: `F ↦ exp (i F) - 1` is a smooth map from the real
`H^s` phases to `H^s(ℂ)`, `s > 1`. -/
theorem contDiff_subOne_expGauge :
    ContDiff ℝ ∞ fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ subOne (expGauge hs F) := by
  convert ((contDiff_expSubOne (finrank_real_complex_lt_two_mul hs)).restrict_scalars ℝ).comp
    (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL).contDiff using 1
  exact funext fun G ↦ subOne_expGauge_eq_expSubOne hs G

/-- At `F = 0` the derivative of `F ↦ Re (exp (i F)) - 1` vanishes: in `H^s(ℂ)` this is the
element `reSubOne (exp (i F)) = cos F - 1`, which is quadratically small in `F`. -/
theorem hasFDerivAt_reSubOne_expGauge_zero :
    HasFDerivAt (fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ reSubOne (expGauge hs F))
      (0 : realSubmodule ℂ (zero_le_one.trans hs.le) →L[ℝ] H^{s}(ℂ)) 0 := by
  simp only [reSubOne_def]
  exact ((hasFDerivAt_subOne_expGauge_zero.add hasFDerivAt_subOne_inv_expGauge_zero).const_smul
    (2 : ℂ)⁻¹).congr_fderiv (by simp)

/-- At `F = 0` the derivative of `F ↦ Im (exp (i F))` is `G ↦ G`: in `H^s(ℂ)` this is the element
`imPart (exp (i F)) = sin F`, whose linear part is the phase itself. -/
theorem hasFDerivAt_imPart_expGauge_zero :
    HasFDerivAt (fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ imPart (expGauge hs F))
      (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL 0 := by
  simp only [imPart_def]
  refine ((hasFDerivAt_subOne_expGauge_zero.sub hasFDerivAt_subOne_inv_expGauge_zero).const_smul
    (-(I / 2))).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun G ↦ ?_
  have hI : -(I / 2 * (2 * I)) = 1 := by linear_combination (-1 : ℂ) * I_sq
  simp [← two_smul ℂ, smul_smul, hI]

/-! ### The Lie group structure -/

/-- The inverse `F ↦ u exp (i F)` of the chart of `G_s` at `u` is smooth on the whole space of
real phases. -/
theorem contMDiff_gaugeChart_symm (n : WithTop ℕ∞) (u : SobolevTopologicalGaugeGroup hs) :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le))
      𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) n (gaugeChart u).symm := by
  have h := contMDiffOn_chart_symm (I := 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)))
    (n := n) (x := u)
  rw [chartAt_eq, gaugeChart_target] at h
  exact contMDiffOn_univ.1 h

namespace SobolevTopologicalGaugeGroup

/-- **`G_s` is a Lie group** for every smoothness class over `ℝ`, including analytic, modelled on
the real `H^s` phases: in the exponential charts, multiplication is addition of phases and
inversion is negation. -/
instance instLieGroup (n : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) n
      (SobolevTopologicalGaugeGroup hs) where
  contMDiff_mul := by
    rintro ⟨u, v⟩
    -- In the charts at `u`, `v` and `u v`, the product is `(F, G) ↦ F + G`.
    have h := (contMDiff_gaugeChart_symm n (u * v)).comp
      (contMDiff_iff_contDiff.2 (contDiff_fst.add contDiff_snd))
    rw [contMDiffAt_iff_source, extChartAt_prod]
    simpa [Function.comp_def, AddChar.map_add_eq_mul, mul_mul_mul_comm u] using
      h.contMDiffAt.contMDiffWithinAt
  contMDiff_inv := by
    intro u
    -- In the charts at `u` and `u⁻¹`, inversion is `F ↦ -F`.
    have h := (contMDiff_gaugeChart_symm n u⁻¹).comp (contMDiff_iff_contDiff.2 contDiff_neg)
    rw [contMDiffAt_iff_source]
    simpa [Function.comp_def, AddChar.map_neg_eq_inv, mul_comm] using
      h.contMDiffAt.contMDiffWithinAt

end SobolevTopologicalGaugeGroup

/-- **The exponential is smooth** from the real phases to `G_s`: it is the inverse of the chart
of `G_s` at the identity. -/
theorem contMDiff_expGauge (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le))
      𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) n (expGauge hs) := by
  refine (contMDiff_gaugeChart_symm n 1).congr fun F ↦ ?_
  rw [gaugeChart_symm_apply, one_mul]

namespace SobolevTopologicalGaugeGroup

/-- **The coordinate `u ↦ u - 1` is smooth** from `G_s` to `H^s(ℂ)`. In the chart at `u` it is
`F ↦ (u - 1) + (exp (i F) - 1) + (u - 1) (exp (i F) - 1)`. -/
theorem contMDiff_subOne :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, H^{s}(ℂ)) ∞
      (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  intro u
  set M := mulCLM (finrank_real_complex_lt_two_mul hs)
  have hg : ContDiff ℝ ∞ fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦
      subOne u + subOne (expGauge hs F) + M (subOne u) (subOne (expGauge hs F)) :=
    (contDiff_const.add contDiff_subOne_expGauge).add
      (((M (subOne u)).restrictScalars ℝ).contDiff.comp contDiff_subOne_expGauge)
  rw [contMDiffAt_iff_source]
  simpa [Function.comp_def, subOne_mul] using
    (contMDiff_iff_contDiff.2 hg).contMDiffAt.contMDiffWithinAt

/-- **The coordinate `Re u - 1` is smooth** from `G_s` to `H^s(ℂ)`: it is
`((u - 1) + (u⁻¹ - 1)) / 2`, and inversion and `u ↦ u - 1` are smooth. -/
theorem contMDiff_reSubOne :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, H^{s}(ℂ)) ∞
      (reSubOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  have h := (contMDiff_subOne (hs := hs)).add
    ((contMDiff_subOne (hs := hs)).comp (contMDiff_inv 𝓘(ℝ, realSubmodule ℂ _) ∞))
  refine (((((2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ H^{s}(ℂ)).restrictScalars ℝ).contMDiff).comp
    h).congr fun u ↦ ?_
  simp [reSubOne_def]

/-- **The coordinate `Im u` is smooth** from `G_s` to `H^s(ℂ)`: it is
`-i ((u - 1) - (u⁻¹ - 1)) / 2`, and inversion and `u ↦ u - 1` are smooth. -/
theorem contMDiff_imPart :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, H^{s}(ℂ)) ∞
      (imPart : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  have h := (contMDiff_subOne (hs := hs)).sub
    ((contMDiff_subOne (hs := hs)).comp (contMDiff_inv 𝓘(ℝ, realSubmodule ℂ _) ∞))
  refine ((((-(I / 2) • ContinuousLinearMap.id ℂ H^{s}(ℂ)).restrictScalars ℝ).contMDiff).comp
    h).congr fun u ↦ ?_
  simp [imPart_def]

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
