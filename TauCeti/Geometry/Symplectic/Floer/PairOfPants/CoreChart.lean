/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
import TauCeti.MeasureTheory.Integral.PolarCoord
import TauCeti.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The core of the pair of pants as a cylinder from its input circles to its output circle

The truncation `S₀ = TauCeti.ThricePuncturedSphere.truncation 0` of the pair of pants
`S = ℂ ∖ {0, 1}` is what remains of `S` after removing the three cylindrical ends at height `0`:
the points with `1/2 ≤ ‖w‖`, `1/2 ≤ ‖w - 1‖` and `‖w‖ ≤ 2`. Its boundary consists of the circles
of the two input ends `0` and `1` at height `0`, which are the circles of radius `1/2` about `0`
and about `1`, and the circle `‖w‖ = 2` of the output end `∞` at height `0`. The two input circles
touch at the point `1/2`, so together they form a figure eight, and `S₀` is the region between this
figure eight and the output circle.

Seen from `1/2`, this region is star-shaped. On the ray from `1/2` at the angle `θ`, the circle
about `0` lies at distance `-cos θ` and the circle about `1` at distance `cos θ`, so the region
runs from the distance `|cos θ|` out to the distance `R θ = (-cos θ + √(cos² θ + 15)) / 2` of the
output circle. This file sweeps out `S₀` along these rays. The rays through the left half-plane
`cos θ ≤ 0` cover the part of `S₀` next to the input end `0`, and those through the right
half-plane cover the part next to the input end `1`; on each half the inner end of the ray runs
once around the circle of the input end, in the direction of its angular coordinate.

The **core chart** `TauCeti.Floer.pairOfPantsCoreChart` is the loopwise concatenation
(`TauCeti.loopwiseTrans`) of these two halves. It is a smooth map of the cylinder `ℝ × ℝ / ℤ`
(`TauCeti.Floer.contDiff_pairOfPantsCoreChart`,
`TauCeti.Floer.pairOfPantsCoreChart_apply_add_one`) into `S₀`
(`TauCeti.Floer.pairOfPantsCoreChart_mem_preimage_truncation`). It is constant in `s` for
`s ≤ 0` and for `s ≥ 1` (`TauCeti.Floer.pairOfPantsCoreChart_mk_of_nonpos`,
`TauCeti.Floer.pairOfPantsCoreChart_mk_of_one_le`). At `s = 0` it runs through the collared
concatenation of the end loops of the inputs `0` and `1` at height `0`, both starting at `1/2`
(`TauCeti.Floer.pairOfPantsCoreChart_mk_zero`), and at `s = 1` through the points of the output
circle `‖w‖ = 2` on the same rays from `1/2` (`TauCeti.Floer.pairOfPantsCoreChart_mk_one`,
`TauCeti.Floer.norm_symm_pairOfPantsCoreChart_mk_one`). It thus runs once clockwise around that
circle, like the end loop of the output at height `0`, but at the speed of the angle about `1/2`
rather than about `0`; this file does not compare the two loops.

For a map `u` of the pair of pants into a manifold `M`:

* **The area of the core.** If `u` is `C¹` on `S`, then for every continuous two-form `φ` on `M`
  the integral of `φ` over `u` composed with the core chart is minus the integral of `u^* φ` over
  `S₀` (`TauCeti.Floer.rectangleIntegral_comp_pairOfPantsCoreChart`). The sign is that of the
  orientation of the chart: its angle runs clockwise about `1/2` while its radius grows.
* **The core as a cylinder.** If `u` is `C²` on `S`, then `u` composed with the core chart is a
  cylinder (`TauCeti.IsLoopCylinder`) from the collared concatenation of the input loops of `u`
  at height `0` to the loop of `u` along the output circle
  (`TauCeti.Floer.isLoopCylinder_comp_pairOfPantsCoreChart`).
* **Gluing discs of the inputs.** Two maps `D₀`, `D₁` ending at the two input loops of `u` and
  sharing their seam, such as discs bounding these loops, placed side by side and followed by the
  core of `u`, give a map ending at the output loop, whose integral is that over `D₀` plus that
  over `D₁` minus the integral of `u^* φ` over `S₀`
  (`TauCeti.Floer.rectangleIntegral_rectangleTrans_loopwiseTrans_comp_pairOfPantsCoreChart`).

This is the form in which the topological term `∫ u^* ω` of the energy identity of a Floer pair of
pants is expressed through caps: on `S₀` it is the area of the caps of the inputs minus the area
of the cap of the output obtained by gluing them to `u`.

The area formula is proved in polar coordinates about `1/2`: by Fubini's theorem with the angle
outermost (`Complex.integral_comp_polarCoord_symm`), the integral over `S₀` is an iterated
integral over the angle and over the segment of radii of `S₀` on each ray, and rescaling the radius
and the angle of each half to `[0, 1]` turns it into the integral over the core chart
(`TauCeti.intervalIntegral.integral_integral_deriv_smul_comp_of_deriv_nonneg`). The module-valued
basis-determinant identity `AlternatingMap.eq_basis_det_smulRight`, at the standard basis of
`ℝ × ℝ`, reads the pulled-back form along the chart as its Jacobian times the area density of `u`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and the energy of its solutions.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  capped orbits and the action of glued caps.
-/

public section

noncomputable section

open Set Real Function MeasureTheory Manifold TauCeti.ThricePuncturedSphere

namespace TauCeti.Floer

/-! ### The core in polar coordinates about `1/2` -/

/-- The distance from `1/2` to the output circle `‖w‖ = 2` along the ray at the angle `θ`, the
positive root of `ρ² + ρ cos θ = 15/4`. -/
def pairOfPantsOuterRadius (θ : ℝ) : ℝ :=
  (-Real.cos θ + √(Real.cos θ ^ 2 + 15)) / 2

theorem pairOfPantsOuterRadius_def (θ : ℝ) :
    pairOfPantsOuterRadius θ = (-Real.cos θ + √(Real.cos θ ^ 2 + 15)) / 2 :=
  (rfl)

/-- The outer radius is a root of `ρ² + ρ cos θ = 15/4`. -/
theorem pairOfPantsOuterRadius_sq_add (θ : ℝ) :
    pairOfPantsOuterRadius θ ^ 2 + Real.cos θ * pairOfPantsOuterRadius θ = 15 / 4 := by
  have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2 + 15)
  simp only [pairOfPantsOuterRadius]
  linear_combination h / 4

/-- The output circle lies at distance more than `1` from `1/2` along every ray. -/
theorem one_lt_pairOfPantsOuterRadius (θ : ℝ) : 1 < pairOfPantsOuterRadius θ := by
  have hc := Real.cos_le_one θ
  have h : 2 + Real.cos θ < √(Real.cos θ ^ 2 + 15) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  simp only [pairOfPantsOuterRadius]
  linarith

private theorem abs_cos_le_pairOfPantsOuterRadius (θ : ℝ) :
    |Real.cos θ| ≤ pairOfPantsOuterRadius θ :=
  (abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).trans (one_lt_pairOfPantsOuterRadius θ).le

/-- The outer radius is `2π`-periodic in the angle. -/
theorem pairOfPantsOuterRadius_add_two_pi (θ : ℝ) :
    pairOfPantsOuterRadius (θ + 2 * π) = pairOfPantsOuterRadius θ := by
  simp [pairOfPantsOuterRadius]

/-- The outer radius is a smooth function of the angle. -/
theorem contDiff_pairOfPantsOuterRadius {n : ℕ∞} : ContDiff ℝ n pairOfPantsOuterRadius := by
  have h : ContDiff ℝ n fun θ ↦ √(Real.cos θ ^ 2 + 15) :=
    ((Real.contDiff_cos.pow 2).add contDiff_const).sqrt fun θ ↦ by positivity
  exact (Real.contDiff_cos.neg.add h).div_const 2

private theorem norm_sq_circleMap_half (ρ θ : ℝ) :
    ‖circleMap (1 / 2 : ℂ) ρ θ‖ ^ 2 = 1 / 4 + ρ * Real.cos θ + ρ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem norm_sq_circleMap_half_sub_one (ρ θ : ℝ) :
    ‖circleMap (1 / 2 : ℂ) ρ θ - 1‖ ^ 2 = 1 / 4 - ρ * Real.cos θ + ρ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **The outer radius reaches the output circle.** The point at the outer radius on the ray from
`1/2` at the angle `θ` lies on the output circle `‖w‖ = 2`. -/
theorem norm_circleMap_half_pairOfPantsOuterRadius (θ : ℝ) :
    ‖circleMap (1 / 2 : ℂ) (pairOfPantsOuterRadius θ) θ‖ = 2 := by
  have h := norm_sq_circleMap_half (pairOfPantsOuterRadius θ) θ
  rw [add_assoc, mul_comm, add_comm (Real.cos θ * _), pairOfPantsOuterRadius_sq_add] at h
  nlinarith [norm_nonneg (circleMap (1 / 2 : ℂ) (pairOfPantsOuterRadius θ) θ)]

private theorem mem_truncation_zero_iff {w : ℂ} :
    w ∈ truncation 0 ↔ 1 / 2 ≤ ‖w‖ ∧ 1 / 2 ≤ ‖w - 1‖ ∧ ‖w‖ ≤ 2 := by
  rw [truncation_eq]
  simp [and_assoc]

/-- On the ray from `1/2` at the angle `θ`, the truncation `S₀` is the segment of radii
`[|cos θ|, R θ]`. -/
private theorem circleMap_half_mem_truncation_zero_iff {ρ θ : ℝ} (hρ : 0 < ρ) :
    circleMap (1 / 2 : ℂ) ρ θ ∈ truncation 0 ↔
      |Real.cos θ| ≤ ρ ∧ ρ ≤ pairOfPantsOuterRadius θ := by
  have h₁ := norm_sq_circleMap_half ρ θ
  have h₂ := norm_sq_circleMap_half_sub_one ρ θ
  have hR := pairOfPantsOuterRadius_sq_add θ
  have hR₁ := one_lt_pairOfPantsOuterRadius θ
  have hc := Real.neg_one_le_cos θ
  have hn₁ := norm_nonneg (circleMap (1 / 2 : ℂ) ρ θ)
  have hn₂ := norm_nonneg (circleMap (1 / 2 : ℂ) ρ θ - 1)
  rw [mem_truncation_zero_iff, abs_le]
  constructor
  · rintro ⟨ha, hb, hc'⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith
  · rintro ⟨⟨ha, hb⟩, hc'⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

private theorem circleMap_half_mem_truncation_zero {ρ θ : ℝ} (h₁ : |Real.cos θ| ≤ ρ)
    (h₂ : ρ ≤ pairOfPantsOuterRadius θ) : circleMap (1 / 2 : ℂ) ρ θ ∈ truncation 0 := by
  rcases (abs_nonneg _).trans h₁ |>.lt_or_eq with hρ | hρ
  · exact (circleMap_half_mem_truncation_zero_iff hρ).2 ⟨h₁, h₂⟩
  · subst hρ
    rw [mem_truncation_zero_iff]
    norm_num [circleMap]

/-! ### Polar integration over the core -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Polar Fubini over the core**, with the angle outermost: the integral over `S₀` is the
integral over the angles of the integrals over the segments of radii `[|cos θ|, R θ]`. -/
private theorem integral_truncation_zero_eq_intervalIntegral {f : ℂ → F}
    (hf : IntegrableOn f (truncation 0)) :
    ∫ w in truncation 0, f w =
      ∫ θ in -π..π, ∫ ρ in |Real.cos θ|..pairOfPantsOuterRadius θ,
        ρ • f (circleMap (1 / 2) ρ θ) := by
  have hS : MeasurableSet (truncation 0) := (isCompact_truncation 0).isClosed.measurableSet
  set g := (truncation 0).indicator f
  have hg : Integrable g := hf.integrable_indicator hS
  have hp := TauCeti.integrableOn_comp_complexPolarCoord_symm_iff.mpr
    (hg.comp_add_left (1 / 2 : ℂ))
  rw [← integral_indicator hS, ← integral_add_left_eq_self g (1 / 2 : ℂ),
    ← Complex.integral_comp_polarCoord_symm]
  rw [polarCoord_target, Measure.volume_eq_prod] at hp ⊢
  rw [setIntegral_prod _ hp, integral_integral_swap (by rw [Measure.prod_restrict]; exact hp),
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ ↦ ?_
  have hslice : EqOn (fun ρ : ℝ ↦ ρ • g (1 / 2 + Complex.polarCoord.symm (ρ, θ)))
      ((Icc |Real.cos θ| (pairOfPantsOuterRadius θ)).indicator
        fun ρ ↦ ρ • f (circleMap (1 / 2) ρ θ)) (Ioi 0) := fun ρ hρ ↦ by
    have hmem := circleMap_half_mem_truncation_zero_iff (θ := θ) (mem_Ioi.1 hρ)
    simp only [g, TauCeti.add_polarCoord_symm_eq_circleMap]
    by_cases h : |Real.cos θ| ≤ ρ ∧ ρ ≤ pairOfPantsOuterRadius θ
    · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]
    · rw [indicator_of_notMem (mt hmem.1 h), indicator_of_notMem h, smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hslice, setIntegral_congr_set Ioi_ae_eq_Ici,
    setIntegral_indicator measurableSet_Icc,
    inter_eq_right.mpr (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr (abs_nonneg _))),
    integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (abs_cos_le_pairOfPantsOuterRadius θ)]

/-- The radius `|cos θ| + σ (R θ - |cos θ|)`, running from the inner to the outer boundary of the
core along the ray at the angle `θ` as `σ` runs over `[0, 1]`. -/
private def coreRayRadius (θ σ : ℝ) : ℝ :=
  |Real.cos θ| + σ * (pairOfPantsOuterRadius θ - |Real.cos θ|)

/-- The integral over the segment of the core on the ray at the angle `θ`, with the radius
rescaled to `[0, 1]`. -/
private def coreAngularIntegrand (f : ℂ → F) (θ : ℝ) : F :=
  ∫ σ in (0 : ℝ)..1, ((pairOfPantsOuterRadius θ - |Real.cos θ|) * coreRayRadius θ σ) •
    f (circleMap (1 / 2) (coreRayRadius θ σ) θ)

private theorem intervalIntegral_eq_coreAngularIntegrand (f : ℂ → F) (θ : ℝ) :
    ∫ ρ in |Real.cos θ|..pairOfPantsOuterRadius θ, ρ • f (circleMap (1 / 2) ρ θ) =
      coreAngularIntegrand f θ := by
  simp only [coreAngularIntegrand, coreRayRadius]
  set k := |Real.cos θ|
  set h := pairOfPantsOuterRadius θ - k
  have hkh : k + h = pairOfPantsOuterRadius θ := by simp only [h]; ring
  have := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun ρ ↦ ρ • f (circleMap (1 / 2) ρ θ)) h k
  simp only [mul_zero, add_zero, mul_one] at this
  rw [← hkh, ← this, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun σ _ ↦ ?_
  simp only [smul_smul]
  congr 1 <;> [ring; (congr 2; ring)]

private theorem continuous_coreAngularIntegrand {f : ℂ → F}
    (hf : ContinuousOn f (truncation 0)) : Continuous (coreAngularIntegrand f) := by
  -- Clamping the rescaled radius to `[0, 1]` changes nothing on the interval of integration and
  -- keeps every point in the core, where `f` is continuous.
  have hR := contDiff_pairOfPantsOuterRadius (n := 0).continuous
  have hρ : Continuous fun p : ℝ × ℝ ↦ coreRayRadius p.1 (projIcc 0 1 zero_le_one p.2) := by
    unfold coreRayRadius
    fun_prop
  have hmem (p : ℝ × ℝ) :
      circleMap (1 / 2 : ℂ) (coreRayRadius p.1 (projIcc 0 1 zero_le_one p.2)) p.1 ∈
        truncation 0 := by
    have h₀ := (projIcc 0 1 zero_le_one p.2).prop.1
    have h₁ := (projIcc 0 1 zero_le_one p.2).prop.2
    have h := abs_cos_le_pairOfPantsOuterRadius p.1
    refine circleMap_half_mem_truncation_zero ?_ ?_ <;> simp only [coreRayRadius] <;> nlinarith
  have hc : Continuous fun p : ℝ × ℝ ↦
      circleMap (1 / 2 : ℂ) (coreRayRadius p.1 (projIcc 0 1 zero_le_one p.2)) p.1 := by
    unfold circleMap
    fun_prop
  have hcont : Continuous fun p : ℝ × ℝ ↦
      ((pairOfPantsOuterRadius p.1 - |Real.cos p.1|) *
        coreRayRadius p.1 (projIcc 0 1 zero_le_one p.2)) •
        f (circleMap (1 / 2) (coreRayRadius p.1 (projIcc 0 1 zero_le_one p.2)) p.1) :=
    ((hR.comp continuous_fst).sub (continuous_abs.comp (Real.continuous_cos.comp
      continuous_fst))).mul hρ |>.smul (hf.comp_continuous hc hmem)
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun θ σ ↦ ((pairOfPantsOuterRadius θ - |Real.cos θ|) *
      coreRayRadius θ (projIcc 0 1 zero_le_one σ)) •
      f (circleMap (1 / 2) (coreRayRadius θ (projIcc 0 1 zero_le_one σ)) θ))
    hcont 0 1).congr fun θ ↦ ?_
  refine intervalIntegral.integral_congr fun σ hσ ↦ ?_
  rw [uIcc_of_le zero_le_one] at hσ
  simp only [projIcc_of_mem zero_le_one hσ]

private theorem coreAngularIntegrand_add_two_pi (f : ℂ → F) (θ : ℝ) :
    coreAngularIntegrand f (θ + 2 * π) = coreAngularIntegrand f θ := by
  simp only [coreAngularIntegrand, coreRayRadius, pairOfPantsOuterRadius_add_two_pi,
    Real.cos_add_two_pi, periodic_circleMap _ _ θ]

/-- The clockwise angle about `1/2` of the ray through the lobe of the input end `0` (for
`a = 1/4`) or of the input end `1` (for `a = 3/4`), at the parameter `r ∈ [0, 1]`. -/
private def lobeAngle (a r : ℝ) : ℝ := -(2 * π * (a + r / 2))

/-- The radius along the ray of a lobe, from `sin (π r) = |cos θ|` at `σ = 0` to the output
circle at `σ = 1`. -/
private def lobeRadius (a σ r : ℝ) : ℝ :=
  Real.sin (π * r) + σ * (pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r))

/-- The point of the core on the ray of a lobe at the rescaled radius `σ`. -/
private def lobePoint (a σ r : ℝ) : ℂ :=
  circleMap (1 / 2) (lobeRadius a σ r) (lobeAngle a r)

private theorem cos_lobeAngle_quarter (r : ℝ) :
    Real.cos (lobeAngle (1 / 4) r) = -Real.sin (π * r) := by
  rw [lobeAngle, Real.cos_neg, show 2 * π * (1 / 4 + r / 2) = π * r + π / 2 by ring,
    Real.cos_add_pi_div_two]

private theorem cos_lobeAngle_three_quarters (r : ℝ) :
    Real.cos (lobeAngle (3 / 4) r) = Real.sin (π * r) := by
  rw [lobeAngle, Real.cos_neg, show 2 * π * (3 / 4 + r / 2) = π * r + π / 2 + π by ring,
    Real.cos_add_pi, Real.cos_add_pi_div_two, neg_neg]

private theorem abs_cos_lobeAngle {a r : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) (hr : r ∈ Icc 0 1) :
    |Real.cos (lobeAngle a r)| = Real.sin (π * r) := by
  have hs : 0 ≤ Real.sin (π * r) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, hr.1])
      (by nlinarith [Real.pi_pos, hr.2])
  rcases ha with rfl | rfl
  · rw [cos_lobeAngle_quarter, abs_neg, abs_of_nonneg hs]
  · rw [cos_lobeAngle_three_quarters, abs_of_nonneg hs]

private theorem lobeRadius_eq_coreRayRadius {a r : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4)
    (hr : r ∈ Icc 0 1) (σ : ℝ) : lobeRadius a σ r = coreRayRadius (lobeAngle a r) σ := by
  rw [lobeRadius, coreRayRadius, abs_cos_lobeAngle ha hr]

private theorem lobePoint_mem_truncation {a : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) {σ r : ℝ}
    (hσ : σ ∈ Icc 0 1) (hr : r ∈ Icc 0 1) : lobePoint a σ r ∈ truncation 0 := by
  rw [lobePoint, lobeRadius_eq_coreRayRadius ha hr]
  have h := abs_cos_le_pairOfPantsOuterRadius (lobeAngle a r)
  refine circleMap_half_mem_truncation_zero ?_ ?_ <;> simp only [coreRayRadius] <;>
    nlinarith [hσ.1, hσ.2]

/-- **The integral over the core as the sum of the integrals over its two lobes**, in the
coordinates `(r, σ) ∈ [0, 1]²` of each lobe, with polar Jacobian `π (R - sin (π r)) ρ`. -/
private theorem integral_truncation_zero_eq_lobes {f : ℂ → F}
    (hf : ContinuousOn f (truncation 0)) :
    ∫ w in truncation 0, f w = π • ((∫ r in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1,
        ((pairOfPantsOuterRadius (lobeAngle (1 / 4) r) - Real.sin (π * r)) *
          lobeRadius (1 / 4) σ r) •
          f (lobePoint (1 / 4) σ r)) +
      ∫ r in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1,
        ((pairOfPantsOuterRadius (lobeAngle (3 / 4) r) - Real.sin (π * r)) *
          lobeRadius (3 / 4) σ r) •
          f (lobePoint (3 / 4) σ r)) := by
  have hG := continuous_coreAngularIntegrand hf
  have hper : Periodic (coreAngularIntegrand f) (2 * π) := coreAngularIntegrand_add_two_pi f
  rw [integral_truncation_zero_eq_intervalIntegral
    (hf.integrableOn_compact (isCompact_truncation 0))]
  simp_rw [intervalIntegral_eq_coreAngularIntegrand]
  -- Shift the window of angles to `[-5π/2, -π/2]` and split it into the two lobes.
  have hshift := hper.intervalIntegral_add_eq (-π) (-(5 * π / 2))
  rw [show -π + 2 * π = π by ring, show -(5 * π / 2) + 2 * π = -(π / 2) by ring] at hshift
  rw [hshift, ← intervalIntegral.integral_add_adjacent_intervals (b := -(3 * π / 2))
    (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _), add_comm, smul_add]
  -- On each lobe the angle is `lobeAngle a r = -2πa - πr` for `r ∈ [0, 1]`.
  have hlobe (a : ℝ) (ha : a = 1 / 4 ∨ a = 3 / 4) :
      ∫ θ in (-(2 * π * a) - π)..(-(2 * π * a)), coreAngularIntegrand f θ =
        π • ∫ r in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1,
          ((pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r)) * lobeRadius a σ r) •
            f (lobePoint a σ r) := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
      (coreAngularIntegrand f) (-π) (-(2 * π * a))
    simp only [mul_zero, add_zero, mul_one, ← sub_eq_add_neg] at h
    rw [intervalIntegral.integral_symm, ← h, neg_smul, neg_neg]
    refine congrArg (π • ·) (intervalIntegral.integral_congr fun r hr ↦ ?_)
    rw [uIcc_of_le zero_le_one] at hr
    have hθ : -(2 * π * a) + -π * r = lobeAngle a r := by rw [lobeAngle]; ring
    simp only [hθ, coreAngularIntegrand, lobePoint, lobeRadius_eq_coreRayRadius ha hr,
      abs_cos_lobeAngle ha hr]
  have h₁ := hlobe (1 / 4) (.inl rfl)
  have h₃ := hlobe (3 / 4) (.inr rfl)
  rw [show -(2 * π * (1 / 4)) - π = -(3 * π / 2) by ring,
    show -(2 * π * (1 / 4)) = -(π / 2) by ring] at h₁
  rw [show -(2 * π * (3 / 4)) - π = -(5 * π / 2) by ring,
    show -(2 * π * (3 / 4)) = -(3 * π / 2) by ring] at h₃
  rw [h₁, h₃]

/-! ### The core chart -/

/-- The lobe of the input end `0` (for `a = 1/4`) or `1` (for `a = 3/4`) in real coordinates: the
point at the rescaled radius `β s` on the ray at the parameter `r`, where `β` is the smooth
transition `Real.smoothTransition`, constant for `s ≤ 0` and for `s ≥ 1`. -/
private def lobeChart (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (lobePoint a (smoothTransition z.1) z.2)

/-- A smooth reparametrization of the line which is the identity on `[0, 1]` and takes values in
`(-1/2, 3/2)`, on which the lobes stay in the pair of pants. -/
private def lobeClamp (r : ℝ) : ℝ :=
  1 / 2 + (r - 1 / 2) * smoothTransition (2 - 4 * (r - 1 / 2) ^ 2)

/-- The lobe composed with `lobeClamp`: it agrees with `lobeChart` for `r ∈ [0, 1]`, and it takes
values in the pair of pants for all `(s, r)`, so that a map `C^k` on the pair of pants composes to
a map `C^k` on the whole plane. -/
private def coreLobe (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  lobeChart a (z.1, lobeClamp z.2)

/-- The **core chart** of the pair of pants `S = ℂ ∖ {0, 1}`, in the real coordinates
`ℝ × ℝ ≃ ℂ`: a smooth map, `1`-periodic in its second variable, onto the truncation `S₀` of `S`
at height `0`, the region between the circles of the input ends `0` and `1` at height `0` and the
circle `‖w‖ = 2` of the output end at height `0`. At the parameter `(s, t)` it lies on a ray from
`1/2`: for `t ∈ [0, 1/2]` on the side of the input end `0`, for `t ∈ [1/2, 1]` on the side of the
input end `1`, at the radius running from the input circle for `s ≤ 0` to the output circle for
`s ≥ 1`. It is the loopwise concatenation of the two halves of `S₀`. -/
def pairOfPantsCoreChart : ℝ × ℝ → ℝ × ℝ :=
  loopwiseTrans (coreLobe (1 / 4)) (coreLobe (3 / 4))

private theorem lobeClamp_of_mem {r : ℝ} (hr : r ∈ Icc 0 1) : lobeClamp r = r := by
  rw [lobeClamp, smoothTransition.one_of_one_le (by nlinarith [hr.1, hr.2])]
  ring

private theorem abs_lobeClamp_sub_half_lt (r : ℝ) : |lobeClamp r - 1 / 2| < 1 := by
  rw [lobeClamp, add_sub_cancel_left, abs_mul, abs_of_nonneg (smoothTransition.nonneg _)]
  by_cases h : 2 - 4 * (r - 1 / 2) ^ 2 ≤ 0
  · rw [smoothTransition.zero_of_nonpos h, mul_zero]
    exact one_pos
  · have h₁ : |r - 1 / 2| < 1 := by
      rw [abs_lt]; constructor <;> nlinarith
    exact (mul_le_of_le_one_right (abs_nonneg _) (smoothTransition.le_one _)).trans_lt h₁

private theorem contDiff_lobeClamp {n : ℕ∞} : ContDiff ℝ n lobeClamp := by
  unfold lobeClamp
  have := (smoothTransition.contDiff (n := n)).comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 2)) :
      ContDiff ℝ n fun r : ℝ ↦ 2 - 4 * (r - 1 / 2) ^ 2)
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul this)

private theorem coreLobe_of_mem {a : ℝ} {z : ℝ × ℝ} (hz : z.2 ∈ Icc 0 1) :
    coreLobe a z = lobeChart a z := by
  rw [coreLobe, lobeClamp_of_mem hz]

private theorem contDiff_lobeRadius {n : ℕ∞} (a : ℝ) :
    ContDiff ℝ n fun p : ℝ × ℝ ↦ lobeRadius a p.1 p.2 := by
  unfold lobeRadius lobeAngle
  have hR := (contDiff_pairOfPantsOuterRadius (n := n)).comp
    (contDiff_const.mul (contDiff_const.add (contDiff_snd.div_const 2)) :
      ContDiff ℝ n fun p : ℝ × ℝ ↦ 2 * π * (a + p.2 / 2)).neg
  have hs : ContDiff ℝ n fun p : ℝ × ℝ ↦ Real.sin (π * p.2) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)
  exact hs.add (contDiff_fst.mul (hR.sub hs))

private theorem contDiff_lobePoint {n : ℕ∞} (a : ℝ) :
    ContDiff ℝ n fun p : ℝ × ℝ ↦ lobePoint a p.1 p.2 := by
  have hθ : ContDiff ℝ n fun p : ℝ × ℝ ↦ lobeAngle a p.2 := by
    unfold lobeAngle
    exact (contDiff_const.mul (contDiff_const.add (contDiff_snd.div_const 2))).neg
  have h := ContDiff.comp (g := fun p : ℝ × ℝ ↦ (1 / 2 : ℂ) + Complex.polarCoord.symm p)
    (f := fun p : ℝ × ℝ ↦ (lobeRadius a p.1 p.2, lobeAngle a p.2))
    (TauCeti.contDiff_add_polarCoord_symm _) ((contDiff_lobeRadius a).prodMk hθ)
  have he : (fun p : ℝ × ℝ ↦ lobePoint a p.1 p.2) = (fun p : ℝ × ℝ ↦ (1 / 2 : ℂ) +
      Complex.polarCoord.symm p) ∘ fun p : ℝ × ℝ ↦ (lobeRadius a p.1 p.2, lobeAngle a p.2) := by
    funext p
    simp only [Function.comp_apply, TauCeti.add_polarCoord_symm_eq_circleMap, lobePoint]
  rw [he]
  exact h

private theorem contDiff_lobeChart {n : ℕ∞} (a : ℝ) : ContDiff ℝ n (lobeChart a) :=
  Complex.equivRealProdCLM.contDiff.comp ((contDiff_lobePoint a).comp
    ((smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd))

private theorem contDiff_coreLobe {n : ℕ∞} (a : ℝ) : ContDiff ℝ n (coreLobe a) :=
  (contDiff_lobeChart a).comp (contDiff_fst.prodMk (contDiff_lobeClamp.comp contDiff_snd))

private theorem symm_coreLobe_mem_truncation {a : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) {z : ℝ × ℝ}
    (hz : z.2 ∈ Icc 0 1) : Complex.equivRealProdCLM.symm (coreLobe a z) ∈ truncation 0 := by
  rw [coreLobe_of_mem hz, lobeChart, ContinuousLinearEquiv.symm_apply_apply]
  exact lobePoint_mem_truncation ha ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩ hz

private theorem sin_pi_mul_lobeClamp_gt (r : ℝ) : -1 < Real.sin (π * lobeClamp r) := by
  have h := abs_lobeClamp_sub_half_lt r
  rw [abs_lt] at h
  -- `sin x = -cos (x + π/2)`, and `cos < 1` on `(0, 2π)`.
  have hx : π * lobeClamp r = (π * lobeClamp r + π / 2) - π / 2 := by ring
  rw [hx, Real.sin_sub_pi_div_two, neg_lt_neg_iff]
  refine lt_of_le_of_ne (Real.cos_le_one _) fun h1 ↦ ?_
  have := (Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])).1 h1
  nlinarith [Real.pi_pos]

/-- For every parameter the lobes avoid the punctures `0` and `1`. -/
private theorem coreLobe_mem_thricePuncturedSphereReal {a : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4)
    (z : ℝ × ℝ) : coreLobe a z ∈ thricePuncturedSphereReal := by
  set r := lobeClamp z.2
  set S := Real.sin (π * r)
  set ρ := lobeRadius a (smoothTransition z.1) r
  have hS₁ : S ≤ 1 := Real.sin_le_one _
  have hS₀ : -1 < S := sin_pi_mul_lobeClamp_gt z.2
  have hR := one_lt_pairOfPantsOuterRadius (lobeAngle a r)
  have hσ₀ := smoothTransition.nonneg z.1
  have hρ : S ≤ ρ := by
    simp only [ρ, lobeRadius]
    nlinarith
  have hc : Real.cos (lobeAngle a r) = -S ∨ Real.cos (lobeAngle a r) = S := by
    rcases ha with rfl | rfl
    · exact .inl (cos_lobeAngle_quarter r)
    · exact .inr (cos_lobeAngle_three_quarters r)
  have h₁ := norm_sq_circleMap_half ρ (lobeAngle a r)
  have h₂ := norm_sq_circleMap_half_sub_one ρ (lobeAngle a r)
  have hS : 0 < (S + 1) * (1 - S) ∨ S = 1 := by
    rcases hS₁.lt_or_eq with h | h
    · exact .inl (mul_pos (by linarith) (by linarith))
    · exact .inr h
  rw [mem_thricePuncturedSphereReal_iff, coreLobe, lobeChart,
    ContinuousLinearEquiv.symm_apply_apply, lobePoint]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, norm_zero] at h₁
    rcases hc with hc | hc <;> rw [hc] at h₁ <;> rcases hS with hS | hS <;>
      nlinarith [sq_nonneg (ρ - S / 2), sq_nonneg (ρ + S / 2)]
  · rw [h, sub_self, norm_zero] at h₂
    rcases hc with hc | hc <;> rw [hc] at h₂ <;> rcases hS with hS | hS <;>
      nlinarith [sq_nonneg (ρ - S / 2), sq_nonneg (ρ + S / 2)]

private theorem coreLobe_quarter_one (s : ℝ) :
    coreLobe (1 / 4) (s, 1) = coreLobe (3 / 4) (s, 0) := by
  rw [coreLobe_of_mem (by simp), coreLobe_of_mem (by simp), lobeChart, lobeChart, lobePoint,
    lobePoint, lobeRadius, lobeRadius,
    show lobeAngle (1 / 4) 1 = lobeAngle (3 / 4) 0 by rw [lobeAngle, lobeAngle]; ring]
  simp

private theorem coreLobe_three_quarters_one (s : ℝ) :
    coreLobe (3 / 4) (s, 1) = coreLobe (1 / 4) (s, 0) := by
  rw [coreLobe_of_mem (by simp), coreLobe_of_mem (by simp), lobeChart, lobeChart, lobePoint,
    lobePoint, lobeRadius, lobeRadius,
    show lobeAngle (3 / 4) 1 = lobeAngle (1 / 4) 0 + -(2 * π) by rw [lobeAngle, lobeAngle]; ring]
  have hR : pairOfPantsOuterRadius (lobeAngle (1 / 4) 0 + -(2 * π)) =
      pairOfPantsOuterRadius (lobeAngle (1 / 4) 0) := by
    rw [← pairOfPantsOuterRadius_add_two_pi, neg_add_cancel_right]
  have hc (ρ : ℝ) : circleMap (1 / 2 : ℂ) ρ (lobeAngle (1 / 4) 0 + -(2 * π)) =
      circleMap (1 / 2) ρ (lobeAngle (1 / 4) 0) := by
    rw [← periodic_circleMap (1 / 2 : ℂ) ρ, neg_add_cancel_right]
  rw [hR, hc]
  simp

/-- On the ray from `1/2` at the angle `θ`, the point at the signed distance `cos θ` is
`1 + e^{2iθ}/2`, on the circle of radius `1/2` about `1`. -/
private theorem circleMap_half_cos (θ : ℝ) :
    circleMap (1 / 2 : ℂ) (Real.cos θ) θ = 1 + Complex.exp (2 * θ * Complex.I) / 2 := by
  have h : Complex.exp (-θ * Complex.I) * Complex.exp (θ * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  rw [circleMap, Complex.ofReal_cos, Complex.cos,
    show (2 : ℂ) * θ * Complex.I = θ * Complex.I + θ * Complex.I by ring, Complex.exp_add]
  linear_combination h / 2

/-- On the ray from `1/2` at the angle `θ`, the point at the signed distance `-cos θ` is
`-e^{2iθ}/2`, on the circle of radius `1/2` about `0`. -/
private theorem circleMap_half_neg_cos (θ : ℝ) :
    circleMap (1 / 2 : ℂ) (-Real.cos θ) θ = -(Complex.exp (2 * θ * Complex.I) / 2) := by
  have h : Complex.exp (-θ * Complex.I) * Complex.exp (θ * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  rw [circleMap, Complex.ofReal_neg, Complex.ofReal_cos, Complex.cos,
    show (2 : ℂ) * θ * Complex.I = θ * Complex.I + θ * Complex.I by ring, Complex.exp_add]
  linear_combination -h / 2

/-- At `s = 0` the lobe of the input end `0` is its end chart at height `0`. -/
private theorem coreLobe_quarter_mk_zero {r : ℝ} (hr : r ∈ Icc 0 1) :
    coreLobe (1 / 4) (0, r) = endChart Puncture.zero (0, r) := by
  rw [coreLobe_of_mem hr, lobeChart, endChart_apply, smoothTransition.zero, lobePoint, lobeRadius,
    zero_mul, add_zero]
  congr 1
  have he : Complex.equivRealProdCLM.symm ((0 : ℝ), r) = r * Complex.I := by
    apply Complex.ext <;> simp
  rw [he, Puncture.cylindricalEndLift_zero, ← neg_neg (Real.sin (π * r)),
    ← cos_lobeAngle_quarter, circleMap_half_neg_cos]
  -- The doubled angle is `-2πr - π`, and `e^{iπ} = -1`.
  rw [show 2 * (lobeAngle (1 / 4) r : ℂ) * Complex.I =
      -(2 * π) * (r * Complex.I) - π * Complex.I by rw [lobeAngle]; push_cast; ring,
    Complex.exp_sub, Complex.exp_pi_mul_I]
  ring

/-- At `s = 0` the lobe of the input end `1` is its end chart at height `0`. -/
private theorem coreLobe_three_quarters_mk_zero {r : ℝ} (hr : r ∈ Icc 0 1) :
    coreLobe (3 / 4) (0, r) = endChart Puncture.one (0, r) := by
  rw [coreLobe_of_mem hr, lobeChart, endChart_apply, smoothTransition.zero, lobePoint, lobeRadius,
    zero_mul, add_zero]
  congr 1
  have he : Complex.equivRealProdCLM.symm ((0 : ℝ), r) = r * Complex.I := by
    apply Complex.ext <;> simp
  rw [he, Puncture.cylindricalEndLift_one, ← cos_lobeAngle_three_quarters, circleMap_half_cos]
  -- The doubled angle is `-2πr - π - 2π`, `e^{iπ} = -1` and `e^{2πi} = 1`.
  rw [show 2 * (lobeAngle (3 / 4) r : ℂ) * Complex.I =
      -(2 * π) * (r * Complex.I) - π * Complex.I - 2 * π * Complex.I by
        rw [lobeAngle]; push_cast; ring,
    Complex.exp_sub, Complex.exp_sub, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I]
  ring

private theorem norm_symm_coreLobe_mk_one (a : ℝ) {r : ℝ} (hr : r ∈ Icc 0 1) :
    ‖Complex.equivRealProdCLM.symm (coreLobe a (1, r))‖ = 2 := by
  rw [coreLobe_of_mem hr, lobeChart, ContinuousLinearEquiv.symm_apply_apply,
    smoothTransition.one, lobePoint, lobeRadius, one_mul, add_sub_cancel]
  have h := norm_sq_circleMap_half (pairOfPantsOuterRadius (lobeAngle a r)) (lobeAngle a r)
  have h' := pairOfPantsOuterRadius_sq_add (lobeAngle a r)
  have hn := norm_nonneg
    (circleMap (1 / 2 : ℂ) (pairOfPantsOuterRadius (lobeAngle a r)) (lobeAngle a r))
  nlinarith

/-- The core chart is `1`-periodic in its second variable. -/
@[simp]
theorem pairOfPantsCoreChart_apply_add_one (s t : ℝ) :
    pairOfPantsCoreChart (s, t + 1) = pairOfPantsCoreChart (s, t) :=
  loopwiseTrans_apply_add_one _ _ s t

/-- The core chart is smooth. -/
theorem contDiff_pairOfPantsCoreChart {n : ℕ∞} : ContDiff ℝ n pairOfPantsCoreChart := by
  rw [← contMDiff_iff_contDiff]
  exact contMDiff_loopwiseTrans (contDiff_coreLobe _).contMDiff (contDiff_coreLobe _).contMDiff
    coreLobe_quarter_one coreLobe_three_quarters_one

/-- The core chart takes values in the truncation `S₀` of the pair of pants at height `0`. -/
theorem pairOfPantsCoreChart_mem_preimage_truncation (z : ℝ × ℝ) :
    pairOfPantsCoreChart z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation 0 := by
  obtain ⟨s, t⟩ := z
  exact loopwiseTrans_mem (fun _ hr ↦ symm_coreLobe_mem_truncation (.inl rfl) hr)
    (fun _ hr ↦ symm_coreLobe_mem_truncation (.inr rfl) hr)

/-- **The input loop of the core chart.** For `s = 0` the core chart runs through the collared
concatenation of the end charts of the input ends `0` and `1` at height `0`, the circles of
radius `1/2` about `0` and about `1`, both starting at `1/2`. -/
theorem pairOfPantsCoreChart_mk_zero (t : ℝ) :
    pairOfPantsCoreChart (0, t) = loopwiseTrans (fun z ↦ endChart Puncture.zero (0, z.2))
      (fun z ↦ endChart Puncture.one (0, z.2)) (0, t) :=
  loopwiseTrans_congr (fun _ hr ↦ coreLobe_quarter_mk_zero hr)
    (fun _ hr ↦ coreLobe_three_quarters_mk_zero hr)

/-- For `s ≤ 0` the core chart is constant in `s`: it runs through its input loop. -/
theorem pairOfPantsCoreChart_mk_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) :
    pairOfPantsCoreChart (s, t) = pairOfPantsCoreChart (0, t) := by
  have h (a r : ℝ) : coreLobe a (s, r) = coreLobe a (0, r) := by
    simp only [coreLobe, lobeChart, smoothTransition.zero_of_nonpos hs, smoothTransition.zero]
  exact loopwiseTrans_congr (fun r _ ↦ h _ r) (fun r _ ↦ h _ r)

/-- For `s ≥ 1` the core chart is constant in `s`: it runs through its output loop. -/
theorem pairOfPantsCoreChart_mk_of_one_le {s : ℝ} (hs : 1 ≤ s) (t : ℝ) :
    pairOfPantsCoreChart (s, t) = pairOfPantsCoreChart (1, t) := by
  have h (a r : ℝ) : coreLobe a (s, r) = coreLobe a (1, r) := by
    simp only [coreLobe, lobeChart, smoothTransition.one_of_one_le hs, smoothTransition.one]
  exact loopwiseTrans_congr (fun r _ ↦ h _ r) (fun r _ ↦ h _ r)

/-- **The output loop of the core chart.** For `s = 1` the core chart runs through the circle
`‖w‖ = 2` of the output end at height `0`. -/
theorem norm_symm_pairOfPantsCoreChart_mk_one (t : ℝ) :
    ‖Complex.equivRealProdCLM.symm (pairOfPantsCoreChart (1, t))‖ = 2 :=
  loopwiseTrans_mem (A := {w | ‖Complex.equivRealProdCLM.symm w‖ = 2})
    (fun _ hr ↦ norm_symm_coreLobe_mk_one _ hr) (fun _ hr ↦ norm_symm_coreLobe_mk_one _ hr)

/-- **The output loop of the core chart, explicitly.** For `s = 1` the core chart runs through
the points `1/2 + R e^{iθ}` of the circle `‖w‖ = 2` on the rays from `1/2` at the angles
`θ = -π/2 - π r` on the side of the input end `0`, and `θ = -3π/2 - π r` on the side of the input
end `1`, for `r ∈ [0, 1]`. Here `R = (-cos θ + √(cos² θ + 15)) / 2` is the distance from `1/2` to
that circle along the ray, where `-cos θ` is `sin (π r)` on the side of the input end `0` and
`-sin (π r)` on the side of the input end `1`. -/
theorem pairOfPantsCoreChart_mk_one (t : ℝ) :
    pairOfPantsCoreChart (1, t) = loopwiseTrans
      (fun z ↦ Complex.equivRealProdCLM (circleMap (1 / 2)
        ((Real.sin (π * z.2) + √(Real.sin (π * z.2) ^ 2 + 15)) / 2) (-(π / 2) - π * z.2)))
      (fun z ↦ Complex.equivRealProdCLM (circleMap (1 / 2)
        ((-Real.sin (π * z.2) + √(Real.sin (π * z.2) ^ 2 + 15)) / 2) (-(3 * π / 2) - π * z.2)))
      (1, t) := by
  refine loopwiseTrans_congr (fun r hr ↦ ?_) (fun r hr ↦ ?_) <;>
    rw [coreLobe_of_mem hr, lobeChart, smoothTransition.one, lobePoint, lobeRadius, one_mul,
      add_sub_cancel, pairOfPantsOuterRadius]
  · rw [cos_lobeAngle_quarter, neg_neg, neg_sq,
      show lobeAngle (1 / 4) r = -(π / 2) - π * r by rw [lobeAngle]; ring]
  · rw [cos_lobeAngle_three_quarters,
      show lobeAngle (3 / 4) r = -(3 * π / 2) - π * r by rw [lobeAngle]; ring]

/-! ### The Jacobian of a lobe -/

private theorem hasDerivAt_lobeAngle (a r : ℝ) : HasDerivAt (lobeAngle a) (-π) r := by
  have h : lobeAngle a = fun r ↦ -(2 * π * a) + -π * r := by
    funext r
    rw [lobeAngle]
    ring
  rw [h]
  simpa using ((hasDerivAt_id r).const_mul (-π)).const_add (-(2 * π * a))

private theorem hasDerivAt_lobePoint_fst (a σ r : ℝ) :
    HasDerivAt (fun σ ↦ lobePoint a σ r)
      (((pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r) : ℝ) : ℂ) *
        Complex.exp (lobeAngle a r * Complex.I)) σ := by
  have h : HasDerivAt (fun σ : ℝ ↦ (lobeRadius a σ r : ℂ))
      ((pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r) : ℝ) : ℂ) σ := by
    have := ((hasDerivAt_id σ).mul_const
      (pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r))).const_add (Real.sin (π * r))
    simpa [lobeRadius] using this.ofReal_comp
  simpa [lobePoint, circleMap] using
    (h.mul_const (Complex.exp (lobeAngle a r * Complex.I))).const_add (1 / 2 : ℂ)

private theorem hasDerivAt_lobePoint_snd (a σ r : ℝ) :
    HasDerivAt (fun r ↦ lobePoint a σ r)
      (((deriv (lobeRadius a σ) r : ℝ) : ℂ) * Complex.exp (lobeAngle a r * Complex.I) +
        (lobeRadius a σ r : ℂ) * (Complex.exp (lobeAngle a r * Complex.I) * (-π * Complex.I)))
      r := by
  have hρ : HasDerivAt (fun r ↦ (lobeRadius a σ r : ℂ)) ((deriv (lobeRadius a σ) r : ℝ) : ℂ) r :=
    (((contDiff_lobeRadius (n := 1) a).comp (contDiff_const.prodMk contDiff_id)).differentiable
      one_ne_zero r).hasDerivAt.ofReal_comp
  have hθ : HasDerivAt (fun r : ℝ ↦ (lobeAngle a r : ℂ) * Complex.I) (-π * Complex.I) r := by
    simpa using (hasDerivAt_lobeAngle a r).ofReal_comp.mul_const Complex.I
  simpa [lobePoint, circleMap] using (hρ.mul hθ.cexp).const_add (1 / 2 : ℂ)

/-- The radial partial derivative of a lobe. -/
private theorem fderiv_lobeChart_apply_one_zero (a : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (lobeChart a) z (1, 0) = Complex.equivRealProdCLM
      (((deriv smoothTransition z.1 : ℝ) : ℂ) *
        (((pairOfPantsOuterRadius (lobeAngle a z.2) - Real.sin (π * z.2) : ℝ) : ℂ) *
          Complex.exp (lobeAngle a z.2 * Complex.I))) := by
  have hβ : HasDerivAt smoothTransition (deriv smoothTransition z.1) z.1 :=
    (smoothTransition.contDiff (n := 1).differentiable one_ne_zero z.1).hasDerivAt
  have h := ((contDiff_lobeChart (n := 1) a).differentiable one_ne_zero z).hasFDerivAt
    |>.comp_hasDerivAt z.1 ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have h' := Complex.equivRealProdCLM.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_lobePoint_fst a (smoothTransition z.1) z.2).scomp z.1 hβ)
  rw [ContinuousLinearEquiv.coe_coe, ← Complex.real_smul] at h'
  exact h.unique h'

/-- The angular partial derivative of a lobe. -/
private theorem fderiv_lobeChart_apply_zero_one (a : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (lobeChart a) z (0, 1) = Complex.equivRealProdCLM
      (((deriv (lobeRadius a (smoothTransition z.1)) z.2 : ℝ) : ℂ) *
          Complex.exp (lobeAngle a z.2 * Complex.I) +
        (lobeRadius a (smoothTransition z.1) z.2 : ℂ) *
          (Complex.exp (lobeAngle a z.2 * Complex.I) * (-π * Complex.I))) := by
  have h := ((contDiff_lobeChart (n := 1) a).differentiable one_ne_zero z).hasFDerivAt
    |>.comp_hasDerivAt z.2 ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have h' := Complex.equivRealProdCLM.hasFDerivAt.comp_hasDerivAt z.2
    (hasDerivAt_lobePoint_snd a (smoothTransition z.1) z.2)
  rw [ContinuousLinearEquiv.coe_coe] at h'
  exact h.unique h'

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- **The pullback of a two-form along a lobe**: on the coordinate vectors it is the Jacobian
`-π β' (R - sin (π r)) ρ` of the lobe times the pullback along `u` at the point of the lobe. The
angle of the lobe runs clockwise while its radius grows, so the Jacobian is not positive. -/
private theorem mpullback_comp_lobeChart_apply (a : ℝ) {u : ℝ × ℝ → M} (φ : RoughForm I M F 2)
    (z : ℝ × ℝ) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (lobeChart a z)) :
    mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ lobeChart a) φ z ![(1, 0), (0, 1)] =
      (-(π * deriv smoothTransition z.1 *
          (pairOfPantsOuterRadius (lobeAngle a z.2) - Real.sin (π * z.2)) *
          lobeRadius a (smoothTransition z.1) z.2)) •
        mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (lobeChart a z) ![(1, 0), (0, 1)] := by
  have hL := ((contDiff_lobeChart (n := 1) a).differentiable one_ne_zero z).hasFDerivAt
  rw [mpullback_comp_apply_of_hasFDerivAt hL hu]
  -- Read the pullback along `u` as a form on the plane, whose tangent spaces are `ℝ × ℝ`.
  let ψ : (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (lobeChart a z)
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply ψ _ _).trans ?_
  have hv : (fderiv ℝ (lobeChart a) z ∘ ![((1 : ℝ), (0 : ℝ)), (0, 1)]) =
      ![fderiv ℝ (lobeChart a) z (1, 0), fderiv ℝ (lobeChart a) z (0, 1)] := by
    funext i
    fin_cases i <;> simp
  -- An alternating map of two vectors of `ℝ × ℝ` is their determinant times its value on the
  -- standard basis vectors.
  have hdet := congrArg (· ![fderiv ℝ (lobeChart a) z (1, 0), fderiv ℝ (lobeChart a) z (0, 1)])
    (ψ.toAlternatingMap.eq_basis_det_smulRight (Module.Basis.finTwoProd ℝ))
  rw [AlternatingMap.smulRight_apply, Module.Basis.det_finTwoProd_apply,
    Module.Basis.coe_finTwoProd] at hdet
  refine (congrArg ψ hv).trans (hdet.trans ?_)
  refine congrArg (· • ψ ![(1, 0), (0, 1)]) ?_
  rw [fderiv_lobeChart_apply_one_zero, fderiv_lobeChart_apply_zero_one]
  set e := Complex.exp (lobeAngle a z.2 * Complex.I)
  have he : e.re ^ 2 + e.im ^ 2 = 1 := by
    simp only [e, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    exact Real.cos_sq_add_sin_sq _
  simp only [Complex.equivRealProdCLM_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  linear_combination (-(π * deriv smoothTransition z.1 *
    (pairOfPantsOuterRadius (lobeAngle a z.2) - Real.sin (π * z.2)) *
    lobeRadius a (smoothTransition z.1) z.2)) * he

/-! ### The area of the core -/

private theorem lobeChart_mem_thricePuncturedSphereReal {a : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4)
    {z : ℝ × ℝ} (hz : z.2 ∈ Icc 0 1) : lobeChart a z ∈ thricePuncturedSphereReal := by
  rw [← coreLobe_of_mem hz]
  exact coreLobe_mem_thricePuncturedSphereReal ha z

/-- The area density `φ (u z) (∂ₛu, ∂ₜu)` of a map `u` of the plane. -/
private def areaDensity (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (z : ℝ × ℝ) : F :=
  φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)]

/-- The integrand of the integral over a lobe, in the coordinates `(r, σ)`, is continuous. -/
private theorem continuousOn_lobeIntegrand [IsManifold I 1 M] {a : ℝ}
    (ha : a = 1 / 4 ∨ a = 3 / 4)
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    ContinuousOn (fun p : ℝ × ℝ ↦ (-(π * (pairOfPantsOuterRadius (lobeAngle a p.1) -
      Real.sin (π * p.1)) * lobeRadius a p.2 p.1)) •
        areaDensity φ u (Complex.equivRealProdCLM (lobePoint a p.2 p.1)))
      (Icc 0 1 ×ˢ Icc 0 1) := by
  have hθ : Continuous (lobeAngle a) := by unfold lobeAngle; fun_prop
  have hR := (contDiff_pairOfPantsOuterRadius (n := 0)).continuous
  have hρ := (contDiff_lobeRadius (n := 0) a).continuous
  have hP : Continuous fun p : ℝ × ℝ ↦ Complex.equivRealProdCLM (lobePoint a p.2 p.1) :=
    Complex.equivRealProdCLM.continuous.comp (Continuous.comp
      (g := fun p : ℝ × ℝ ↦ lobePoint a p.1 p.2) (f := fun p : ℝ × ℝ ↦ (p.2, p.1))
      (contDiff_lobePoint (n := 0) a).continuous (continuous_snd.prodMk continuous_fst))
  have hg : ContinuousOn (areaDensity φ u) thricePuncturedSphereReal :=
    hφ.continuousOn_apply_mfderiv isOpen_thricePuncturedSphereReal hu _ _
  refine ContinuousOn.smul ?_ (ContinuousOn.comp (g := areaDensity φ u)
    (f := fun p : ℝ × ℝ ↦ Complex.equivRealProdCLM (lobePoint a p.2 p.1)) hg hP.continuousOn
      fun p hp ↦ ?_)
  · exact ((continuous_const.mul ((hR.comp (hθ.comp continuous_fst)).sub (by fun_prop))).mul
      (hρ.comp (continuous_snd.prodMk continuous_fst))).neg.continuousOn
  · rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
    exact truncation_subset 0 (lobePoint_mem_truncation ha hp.2 hp.1)

/-- **The integral over a lobe**, in the coordinates `(r, σ) ∈ [0, 1]²` of the lobe. -/
private theorem rectangleIntegral_comp_lobeChart [IsManifold I 1 M] {a : ℝ}
    (ha : a = 1 / 4 ∨ a = 3 / 4) {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    rectangleIntegral φ (u ∘ lobeChart a) (0, 0) (1, 1) =
      -(π • ∫ r in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1,
        ((pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r)) * lobeRadius a σ r) •
          areaDensity φ u (Complex.equivRealProdCLM (lobePoint a σ r))) := by
  -- On the square the pullback is the Jacobian of the lobe times the area density of `u`.
  have hpt (s r : ℝ) (hr : r ∈ uIcc (0 : ℝ) 1) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ lobeChart a) φ (s, r) ![(1, 0), (0, 1)] =
        deriv smoothTransition s • (-(π * (pairOfPantsOuterRadius (lobeAngle a r) -
          Real.sin (π * r)) * lobeRadius a (smoothTransition s) r)) •
            areaDensity φ u (Complex.equivRealProdCLM (lobePoint a (smoothTransition s) r)) := by
    rw [uIcc_of_le zero_le_one] at hr
    rw [mpullback_comp_lobeChart_apply a φ (s, r) ((hu.contMDiffAt
        (isOpen_thricePuncturedSphereReal.mem_nhds
          (lobeChart_mem_thricePuncturedSphereReal ha hr))).mdifferentiableAt one_ne_zero),
      smul_smul]
    congr 1
    · ring
    · exact mpullback_apply_pair u φ _ _ _
  rw [rectangleIntegral_def]
  dsimp only
  rw [intervalIntegral.integral_congr fun s _ ↦ intervalIntegral.integral_congr fun r hr ↦
    hpt s r hr]
  -- Exchange the two integrals and substitute `σ = β s` for the smooth transition `β`.
  have hsub := TauCeti.intervalIntegral.integral_integral_deriv_smul_comp_of_deriv_nonneg
    (K := fun r σ ↦
      (-(π * (pairOfPantsOuterRadius (lobeAngle a r) - Real.sin (π * r)) * lobeRadius a σ r)) •
        areaDensity φ u (Complex.equivRealProdCLM (lobePoint a σ r)))
    (c := 0) (d := 1) zero_le_one
    (fun s _ ↦ (smoothTransition.contDiff (n := 1).differentiable one_ne_zero s).hasDerivAt)
    ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).continuousOn
    (fun _ _ ↦ smoothTransition.monotone.deriv_nonneg)
    (by
      rw [smoothTransition.zero, smoothTransition.one, uIcc_of_le zero_le_one]
      exact continuousOn_lobeIntegrand ha hφ hu)
  rw [smoothTransition.zero, smoothTransition.one] at hsub
  refine hsub.trans ?_
  simp only [neg_smul, intervalIntegral.integral_neg, mul_assoc, ← smul_smul,
    intervalIntegral.integral_smul]

/-- **The area of the core of the pair of pants.** For a continuous two-form `φ` on a manifold `M`
and a map `u` of the pair of pants `S` into `M` which is `C¹` on `S`, the integral of `φ` over `u`
composed with the core chart is minus the integral of `u^* φ` over the truncation `S₀` at
height `0`. The sign is that of the orientation of the core chart, whose angle runs clockwise
about `1/2` while its radius grows. -/
theorem rectangleIntegral_comp_pairOfPantsCoreChart [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    rectangleIntegral φ (u ∘ pairOfPantsCoreChart) (0, 0) (1, 1) =
      -∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation 0,
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  have hlobe {a : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) :
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ coreLobe a) :=
    hu.comp_contMDiff (contDiff_coreLobe a).contMDiff (coreLobe_mem_thricePuncturedSphereReal ha)
  -- On the square, the clamped lobes are the lobes.
  have hcongr {a : ℝ} : rectangleIntegral φ (u ∘ coreLobe a) (0, 0) (1, 1) =
      rectangleIntegral φ (u ∘ lobeChart a) (0, 0) (1, 1) :=
    rectangleIntegral_congr fun z hz ↦ by
      simp only [uIcc_of_le zero_le_one, mem_prod] at hz
      simp only [Function.comp_apply, coreLobe_of_mem hz.2]
  have hsplit :
      u ∘ pairOfPantsCoreChart = loopwiseTrans (u ∘ coreLobe (1 / 4)) (u ∘ coreLobe (3 / 4)) :=
    funext fun z ↦ apply_loopwiseTrans u _ _ z
  rw [hsplit, rectangleIntegral_loopwiseTrans hφ (hlobe (.inl rfl)) (hlobe (.inr rfl))
      (fun s ↦ congrArg u (coreLobe_quarter_one s))
      (fun s ↦ congrArg u (coreLobe_three_quarters_one s)) 0 1, hcongr, hcongr,
    rectangleIntegral_comp_lobeChart (.inl rfl) hφ hu,
    rectangleIntegral_comp_lobeChart (.inr rfl) hφ hu, ← neg_add, ← smul_add]
  -- Transport the integral over the core to `ℂ` and use polar coordinates about `1/2`.
  have hg : ContinuousOn (fun w : ℂ ↦ areaDensity φ u (Complex.equivRealProdCLM w))
      (truncation 0) := by
    refine (hφ.continuousOn_apply_mfderiv isOpen_thricePuncturedSphereReal hu _ _).comp
      Complex.equivRealProdCLM.continuous.continuousOn fun w hw ↦ ?_
    rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
    exact truncation_subset 0 hw
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Complex.equivRealProdCLM.symm ⁻¹' truncation 0) = truncation 0 := by
    ext w
    simp [Complex.measurableEquivRealProd]
  rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding _ _, hpre,
    Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM]
  exact congrArg (fun x ↦ -x) (integral_truncation_zero_eq_lobes hg).symm

/-! ### The core as a cylinder -/

private theorem contMDiff_comp_pairOfPantsCoreChart {n : ℕ∞} {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u thricePuncturedSphereReal) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (u ∘ pairOfPantsCoreChart) :=
  hu.comp_contMDiff contDiff_pairOfPantsCoreChart.contMDiff fun z ↦ by
    have h := truncation_subset 0 (pairOfPantsCoreChart_mem_preimage_truncation z)
    rwa [mem_thricePuncturedSphereReal_iff]

/-- **The core of the pair of pants as a cylinder.** For a map `u` of the pair of pants `S` into
a manifold `M` which is `C²` on `S`, the composite of `u` with the core chart is a cylinder from
the collared concatenation of the loops of `u` along the circles of the input ends `0` and `1` at
height `0` to the loop of `u` along the output circle `‖w‖ = 2`. -/
theorem isLoopCylinder_comp_pairOfPantsCoreChart {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u thricePuncturedSphereReal) :
    IsLoopCylinder I (u ∘ pairOfPantsCoreChart)
      (fun t ↦ loopwiseTrans (fun z ↦ u (endChart Puncture.zero (0, z.2)))
        (fun z ↦ u (endChart Puncture.one (0, z.2))) (0, t))
      fun t ↦ u (pairOfPantsCoreChart (1, t)) where
  contMDiff := contMDiff_comp_pairOfPantsCoreChart hu
  apply_add_one z := by
    simp only [Function.comp_apply, pairOfPantsCoreChart_apply_add_one]
  apply_zero t := by
    rw [Function.comp_apply, pairOfPantsCoreChart_mk_zero, apply_loopwiseTrans u]
    simp only [Function.comp_def]
  apply_one _ := Function.comp_apply

/-- **Gluing discs of the inputs to the core.** Let `u` be a map of the pair of pants `S` into a
manifold `M`, `C¹` on `S`, and let `D₀` and `D₁` be `C¹` maps of the plane which end at `s = 1`
at the loops of `u` along the circles of the input ends `0` and `1` at height `0`, and share
their seam, `D₀ (s, 1) = D₁ (s, 0)` and `D₁ (s, 1) = D₀ (s, 0)`; for instance discs bounding these
loops whose seams run to a common centre. Placing them side by side and following them by the
core of `u` gives a map ending at the loop of `u` along the output circle, and for every
continuous two-form `φ` its integral is the sum of the integrals over `D₀` and `D₁` minus the
integral of `u^* φ` over the truncation `S₀` at height `0`. -/
theorem rectangleIntegral_rectangleTrans_loopwiseTrans_comp_pairOfPantsCoreChart
    [IsManifold I 1 M] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {D₀ D₁ : ℝ × ℝ → M}
    (hD₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₀) (hD₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₁)
    (h₀₁ : ∀ s, D₀ (s, 1) = D₁ (s, 0)) (h₁₀ : ∀ s, D₁ (s, 1) = D₀ (s, 0))
    (h₀ : ∀ t, D₀ (1, t) = u (endChart Puncture.zero (0, t)))
    (h₁ : ∀ t, D₁ (1, t) = u (endChart Puncture.one (0, t))) :
    rectangleIntegral φ (rectangleTrans (loopwiseTrans D₀ D₁) (u ∘ pairOfPantsCoreChart))
        (0, 0) (1, 1) =
      rectangleIntegral φ D₀ (0, 0) (1, 1) + rectangleIntegral φ D₁ (0, 0) (1, 1) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation 0,
          φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  have hmatch (t : ℝ) : loopwiseTrans D₀ D₁ (1, t) = (u ∘ pairOfPantsCoreChart) (0, t) := by
    rw [Function.comp_apply, pairOfPantsCoreChart_mk_zero, apply_loopwiseTrans u]
    exact loopwiseTrans_congr (fun r _ ↦ h₀ r) (fun r _ ↦ h₁ r)
  rw [rectangleIntegral_rectangleTrans hφ (contMDiff_loopwiseTrans hD₀ hD₁ h₀₁ h₁₀)
    (contMDiff_comp_pairOfPantsCoreChart hu) hmatch 0 1,
    rectangleIntegral_loopwiseTrans hφ hD₀ hD₁ h₀₁ h₁₀ 0 1,
    rectangleIntegral_comp_pairOfPantsCoreChart hφ hu, ← sub_eq_add_neg]

end TauCeti.Floer
