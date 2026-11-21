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

## Main results

* `TauCeti.Vortex.subOne_expGauge_eq_expSubOne`: `exp (i F) - 1` is `expSubOne` at `i F`.
* `TauCeti.Vortex.hasFDerivAt_subOne_expGauge`, `TauCeti.Vortex.hasFDerivAt_subOne_expGauge_zero`:
  the derivative of `F ↦ exp (i F) - 1`, which is `G ↦ i G` at `F = 0`.
* `TauCeti.Vortex.contDiff_subOne_expGauge`: `F ↦ exp (i F) - 1` is smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instLieGroup`: `G_s` is a Lie group.
* `TauCeti.Vortex.contMDiff_gaugeChart_symm`, `TauCeti.Vortex.contMDiff_expGauge`: the inverse
  charts `F ↦ u exp (i F)`, and in particular the exponential, are smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_subOne`: `u ↦ u - 1` is smooth.

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
  · rw [subOne_expGauge_eq_expSubOne hs F, add_comm]
    rfl

/-- At `F = 0` the derivative of `F ↦ exp (i F) - 1` is `G ↦ i G`. -/
theorem hasFDerivAt_subOne_expGauge_zero :
    HasFDerivAt (fun F ↦ subOne (expGauge hs F))
      (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL) 0 := by
  simpa using hasFDerivAt_subOne_expGauge (hs := hs) 0

/-- **The exponential coordinate is smooth**: `F ↦ exp (i F) - 1` is a smooth map from the real
`H^s` phases to `H^s(ℂ)`, `s > 1`. -/
theorem contDiff_subOne_expGauge :
    ContDiff ℝ ∞ fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ subOne (expGauge hs F) := by
  convert ((contDiff_expSubOne (finrank_real_complex_lt_two_mul hs)).restrict_scalars ℝ).comp
    (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL).contDiff using 1
  exact funext fun G ↦ subOne_expGauge_eq_expSubOne hs G

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

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
