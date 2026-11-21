/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Series
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries

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
(`BesselPotentialSpace.mulCLM`), the power series of the exponential act on it. For a real phase
`G`, the remainder `exp (i G) - 1 - i G` is the series `∑_{n ≥ 1} (i G) ^ (n + 1) / (n + 1)!`,
which is quadratically small:
`‖(exp (i G) - 1) - i G‖_{H^s} ≤ C ‖G‖² exp (C ‖G‖)`
(`TauCeti.Vortex.exists_norm_subOne_expGauge_sub_smul_le`). With the product law
`exp (i (F + G)) - 1 = (exp (i F) - 1) + (exp (i G) - 1) + (exp (i F) - 1) (exp (i G) - 1)`,
this says that `F ↦ exp (i F) - 1` has derivative `G ↦ i (1 + (exp (i F) - 1)) G` at `F`
(`TauCeti.Vortex.hasFDerivAt_subOne_expGauge`). The derivative is an affine function of the value,
so the map is smooth (`TauCeti.Vortex.contDiff_subOne_expGauge`), and the embedding `u ↦ u - 1`
of `G_s` into `H^s(ℂ)` is smooth (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_subOne`).
Since `Re u - 1 = ((u - 1) + (u⁻¹ - 1)) / 2` and `Im u = -i ((u - 1) - (u⁻¹ - 1)) / 2`, the
coordinates `Re u - 1` and `Im u` are smooth too, with derivatives `0` and `G ↦ G` at the identity
in exponential coordinates.

## Main results

* `TauCeti.Vortex.exists_norm_subOne_expGauge_sub_smul_le`: the quadratic Taylor estimate for
  the exponential of a real phase.
* `TauCeti.Vortex.hasFDerivAt_subOne_expGauge`, `TauCeti.Vortex.hasFDerivAt_subOne_expGauge_zero`:
  the derivative of `F ↦ exp (i F) - 1`, which is `G ↦ i G` at `F = 0`.
* `TauCeti.Vortex.contDiff_subOne_expGauge`: `F ↦ exp (i F) - 1` is smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instLieGroup`: `G_s` is a Lie group.
* `TauCeti.Vortex.contMDiff_gaugeChart_symm`, `TauCeti.Vortex.contMDiff_expGauge`: the inverse
  charts `F ↦ u exp (i F)`, and in particular the exponential, are smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_subOne`: `u ↦ u - 1` is smooth.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_reSubOne`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_imPart`: `u ↦ Re u - 1` and `u ↦ Im u`
  are smooth.
* `TauCeti.Vortex.hasFDerivAt_subOne_inv_expGauge_zero`,
  `TauCeti.Vortex.hasFDerivAt_reSubOne_expGauge_zero`,
  `TauCeti.Vortex.hasFDerivAt_imPart_expGauge_zero`: at `F = 0`, the maps
  `F ↦ exp (i F)⁻¹ - 1`, `F ↦ Re (exp (i F)) - 1` and `F ↦ Im (exp (i F))` have derivatives
  `G ↦ -i G`, `0` and `G ↦ G`.

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

/-- **The quadratic Taylor estimate for the exponential of a real phase.** For `s > 1` there is
`C ≥ 0` such that `‖(exp (i G) - 1) - i G‖_{H^s} ≤ C ‖G‖² exp (C ‖G‖)` for every real phase
`G ∈ H^s(ℂ)`. -/
theorem exists_norm_subOne_expGauge_sub_smul_le (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ G : realSubmodule ℂ (zero_le_one.trans hs.le),
      ‖subOne (expGauge hs G) - I • (G : H^{s}(ℂ))‖ ≤ C * ‖G‖ ^ 2 * Real.exp (C * ‖G‖) := by
  obtain ⟨C, hC, hpow⟩ := exists_hasSum_mul_pow (finrank_real_complex_lt_two_mul hs)
  refine ⟨C, hC, fun G ↦ ?_⟩
  have h : 0 ≤ s := zero_le_one.trans hs.le
  have hd := finrank_real_complex_lt_two_mul hs
  -- The `L²` function `U = i G` and its `H^s` element `i G`.
  set X := (inclusion h (G : H^{s}(ℂ))).toLp with hXe
  have hX : MemSobolev s 2 (X : 𝓢'(ℂ, ℂ)) := memSobolev_toLp_inclusion h _
  have hU := hX.toTemperedDistribution_smul I
  have hUG : hU.toBesselPotentialSpace = I • (G : H^{s}(ℂ)) := by
    rw [hX.toBesselPotentialSpace_toTemperedDistribution_smul I hU,
      toBesselPotentialSpace_memSobolev_toLp_inclusion]
  have hnorm : ‖hU.toBesselPotentialSpace‖ = ‖G‖ := by
    rw [hUG, norm_smul, norm_I, one_mul, Submodule.norm_coe]
  obtain ⟨hsum, hle⟩ := summable_and_tsum_norm_expRemainderCoeff_le
    (mul_nonneg hC (norm_nonneg hU.toBesselPotentialSpace))
  -- The remainder series of `U` defines an `H^s` element `v` with the majorant bound.
  obtain ⟨v, hv, hvs, hvle⟩ := hpow hU hsum
  have hXG : X =ᵐ[volume] fun z ↦ (continuousRep G z : ℂ) := by
    simp only [X, toLp_inclusion]
    exact coeFn_inclusionLp_ae_eq_continuousRep hd G
  -- `v + i G = exp (i G) - 1`, by comparing `L²` functions.
  have hveq : hvs.toBesselPotentialSpace + I • (G : H^{s}(ℂ)) = subOne (expGauge hs G) := by
    refine toLp_inclusion_injective h (Lp.ext ?_)
    filter_upwards [coeFn_toLp_inclusion_add h hvs.toBesselPotentialSpace (I • (G : H^{s}(ℂ))),
      coeFn_toLp_inclusion_smul h I (G : H^{s}(ℂ)), coeFn_toLp_inclusion_subOne_expGauge hs h G,
      hv, Lp.coeFn_smul I X, hXG] with z h₁ h₂ h₃ h₄ h₅ h₆
    rw [← hXe] at h₂
    rw [h₁, Pi.add_apply, h₂, toLp_inclusion_toBesselPotentialSpace h hvs rfl, Pi.smul_apply,
      h₃]
    rw [h₅, Pi.smul_apply, h₆] at h₄
    rw [h₄.unique (hasSum_expRemainderCoeff _), h₆]
    simp only [smul_eq_mul, Circle.coe_exp]
    ring_nf
  rw [← hveq, add_sub_cancel_right]
  calc ‖hvs.toBesselPotentialSpace‖
      ≤ ‖G‖ * ∑' n, ‖expRemainderCoeff n‖ * (C * ‖G‖) ^ n := by rw [← hnorm]; exact hvle
    _ ≤ ‖G‖ * ((C * ‖G‖) * Real.exp (C * ‖G‖)) := by
        gcongr; rwa [hnorm] at hle
    _ = C * ‖G‖ ^ 2 * Real.exp (C * ‖G‖) := by ring

/-! ### Smoothness of the exponential coordinate -/

variable {hs : 1 < s}

/-- **The derivative of the exponential coordinate.** The map `F ↦ exp (i F) - 1` from the real
phases to `H^s(ℂ)` has derivative `G ↦ i (1 + (exp (i F) - 1)) G` at `F`, the product being that
of `H^s(ℂ)`. -/
theorem hasFDerivAt_subOne_expGauge (F : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    HasFDerivAt (fun F ↦ subOne (expGauge hs F))
      (((mulCLM (finrank_real_complex_lt_two_mul hs) (subOne (expGauge hs F))).restrictScalars ℝ +
          .id ℝ H^{s}(ℂ)) ∘L (I • (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL)) F := by
  obtain ⟨C, hC, hrem⟩ := exists_norm_subOne_expGauge_sub_smul_le hs
  set M := mulCLM (finrank_real_complex_lt_two_mul hs)
  set w := subOne (expGauge hs F)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- The increment is `(1 + w) ((exp (i G) - 1) - i G)`, which is quadratically small.
  have hinc (G : realSubmodule ℂ (zero_le_one.trans hs.le)) :
      subOne (expGauge hs (F + G)) - w -
          (((M w).restrictScalars ℝ + .id ℝ H^{s}(ℂ)) ∘L (I • (realSubmodule ℂ _).subtypeL)) G =
        M w (subOne (expGauge hs G) - I • (G : H^{s}(ℂ))) +
          (subOne (expGauge hs G) - I • (G : H^{s}(ℂ))) := by
    rw [AddChar.map_add_eq_mul, subOne_mul, map_sub]
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_add, Pi.add_apply,
      ContinuousLinearMap.coe_restrictScalars', FunLike.coe_smul, Pi.smul_apply,
      Submodule.subtypeL_apply, ContinuousLinearMap.id_apply]
    abel
  refine IsLittleO.congr_left ?_ fun G ↦ (hinc G).symm
  refine IsBigO.trans_isLittleO (g := fun G : realSubmodule ℂ _ ↦ ‖G‖ ^ 2) ?_
    (isLittleO_norm_pow_id one_lt_two)
  refine IsBigO.of_bound ((‖M w‖ + 1) * (C * Real.exp C)) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : realSubmodule ℂ _) zero_lt_one] with G hG
  rw [mem_ball_zero_iff] at hG
  have hR := hrem G
  have hexp : Real.exp (C * ‖G‖) ≤ Real.exp C :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right hC hG.le)
  calc ‖M w (subOne (expGauge hs G) - I • (G : H^{s}(ℂ))) +
        (subOne (expGauge hs G) - I • (G : H^{s}(ℂ)))‖
      ≤ ‖M w‖ * ‖subOne (expGauge hs G) - I • (G : H^{s}(ℂ))‖ +
          ‖subOne (expGauge hs G) - I • (G : H^{s}(ℂ))‖ :=
        (norm_add_le _ _).trans (by gcongr; exact (M w).le_opNorm _)
    _ = (‖M w‖ + 1) * ‖subOne (expGauge hs G) - I • (G : H^{s}(ℂ))‖ := by ring
    _ ≤ (‖M w‖ + 1) * (C * ‖G‖ ^ 2 * Real.exp C) := by
        gcongr
        exact hR.trans (by gcongr)
    _ = (‖M w‖ + 1) * (C * Real.exp C) * ‖‖G‖ ^ 2‖ := by
        rw [Real.norm_of_nonneg (by positivity)]
        ring

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

/-- At `F = 0` the map `F ↦ Re (exp (i F)) - 1` from the real phases to `H^s(ℂ)` has derivative
zero. -/
theorem hasFDerivAt_reSubOne_expGauge_zero :
    HasFDerivAt (fun F ↦ reSubOne (expGauge hs F))
      (0 : realSubmodule ℂ (zero_le_one.trans hs.le) →L[ℝ] H^{s}(ℂ)) 0 := by
  simp only [reSubOne_def]
  exact ((hasFDerivAt_subOne_expGauge_zero.add hasFDerivAt_subOne_inv_expGauge_zero).const_smul
    (2 : ℂ)⁻¹).congr_fderiv (by simp)

/-- At `F = 0` the map `F ↦ Im (exp (i F))` from the real phases to `H^s(ℂ)` has derivative the
inclusion `G ↦ G` of the real phases. -/
theorem hasFDerivAt_imPart_expGauge_zero :
    HasFDerivAt (fun F ↦ imPart (expGauge hs F))
      (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL 0 := by
  simp only [imPart_def]
  refine ((hasFDerivAt_subOne_expGauge_zero.sub hasFDerivAt_subOne_inv_expGauge_zero).const_smul
    (-(I / 2))).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun G ↦ ?_
  have hI : -(I / 2 * (2 * I)) = 1 := by linear_combination (-1 : ℂ) * I_sq
  simp [← two_smul ℂ, smul_smul, hI]

/-- **The exponential coordinate is smooth**: `F ↦ exp (i F) - 1` is a smooth map from the real
`H^s` phases to `H^s(ℂ)`, `s > 1`. -/
theorem contDiff_subOne_expGauge :
    ContDiff ℝ ∞ fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ subOne (expGauge hs F) := by
  set M := mulCLM (finrank_real_complex_lt_two_mul hs)
  -- The derivative is `Φ (exp (i F) - 1)` for the continuous affine map `Φ` below.
  set Φ : H^{s}(ℂ) → realSubmodule ℂ (zero_le_one.trans hs.le) →L[ℝ] H^{s}(ℂ) := fun w ↦
    ((M w).restrictScalars ℝ + .id ℝ H^{s}(ℂ)) ∘L (I • (realSubmodule ℂ _).subtypeL)
  have hΦ : ContDiff ℝ ∞ Φ := by
    have hM : ContDiff ℝ ∞ fun w : H^{s}(ℂ) ↦ (M w).restrictScalars ℝ :=
      ((ContinuousLinearMap.restrictScalarsL ℂ H^{s}(ℂ) H^{s}(ℂ) ℝ ℂ).restrictScalars ℝ ∘L
        M.restrictScalars ℝ).contDiff
    exact (hM.add contDiff_const).clm_comp contDiff_const
  refine contDiff_infty.2 fun n ↦ ?_
  induction n with
  | zero => exact contDiff_zero.2 (continuous_iff.1 (continuous_expGauge hs))
  | succ n ih =>
    exact contDiff_succ_iff_hasFDerivAt.2
      ⟨fun F ↦ Φ (subOne (expGauge hs F)), (hΦ.of_le (by exact_mod_cast le_top)).comp ih,
        hasFDerivAt_subOne_expGauge⟩

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

/-- **`u ↦ Re u - 1` is smooth** from `G_s` to `H^s(ℂ)`, since
`Re u - 1 = ((u - 1) + (u⁻¹ - 1)) / 2` and inversion is smooth. -/
theorem contMDiff_reSubOne :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, H^{s}(ℂ)) ∞
      (reSubOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  convert (((2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ H^{s}(ℂ)).restrictScalars ℝ).contDiff
    |>.comp_contMDiff
            (contMDiff_subOne.add (contMDiff_subOne.comp (contMDiff_inv _ _))) using 1
  funext u
  simp [reSubOne_def]

/-- **`u ↦ Im u` is smooth** from `G_s` to `H^s(ℂ)`, since `Im u = -i ((u - 1) - (u⁻¹ - 1)) / 2`
and inversion is smooth. -/
theorem contMDiff_imPart :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, H^{s}(ℂ)) ∞
      (imPart : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  convert ((-(I / 2) • ContinuousLinearMap.id ℂ H^{s}(ℂ)).restrictScalars ℝ).contDiff
    |>.comp_contMDiff
      (contMDiff_subOne.sub (contMDiff_subOne.comp (contMDiff_inv _ _))) using 1
  funext u
  simp [imPart_def]

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
