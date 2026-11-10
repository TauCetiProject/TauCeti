/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.PolarCoord
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The integral of a two-form over a disc swept out radially

A disc in the plane `ℂ ≅ ℝ × ℝ` is swept out by the radial segments from its centre to the points
of its boundary circle. Composing a map `u` of the plane with this sweep gives a map of the unit
square,

`D(r, t) = u(ρ r exp (2π i ε t))`, for `ε = ±1`,

which is constant at `u(0)` along the edge `r = 0` and runs along the boundary loop
`t ↦ u(ρ exp (2π i ε t))` of the disc along the edge `r = 1`, counterclockwise for `ε = 1` and
clockwise for `ε = -1`. It is a disc bounding that loop in the sense of the capped action
`TauCeti.cappedLoopAction`, whose area term is the integral `TauCeti.rectangleIntegral` of a
two-form over a map of the unit square.

This file computes that integral as an integral over the disc in the plane: for a continuous
two-form `ω` on a manifold `M` and a `C¹` map `u`,

`∫_D ω = ε ∫_{‖z‖ ≤ ρ} ω(∂_s u, ∂_t u)`

(`TauCeti.SmoothTwoForm.rectangleIntegral_circleMap`). The sweep has Jacobian determinant
`2π ε ρ² r`, so the area density of `D` is `2π ε ρ² r` times that of `u`; the angular integral
over one period, run in either direction, and the radial integral are then the polar-coordinate
integral over the disc (`TauCeti.integral_annulus_eq_integral_circleMap`). This converts area
integrals of maps of a disc, as they appear in energy identities, into the area of the
corresponding capping disc of the boundary loop. No closedness of `ω` is used.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Real

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

/-- The radial sweep `(r, t) ↦ ρ r exp (2π i ε t)` has derivative sending the coordinate vectors
to `ρ (cos θ, sin θ)` and `2π ε ρ r (-sin θ, cos θ)`, for `θ = 2π ε t`. -/
private theorem hasFDerivAt_circleMap (ρ ε : ℝ) (z : ℝ × ℝ) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ × ℝ,
      HasFDerivAt (fun w : ℝ × ℝ ↦ Complex.equivRealProdCLM
        (circleMap 0 (ρ * w.1) (ε * (2 * π * w.2)))) L z ∧
      L (1, 0) = (ρ * Real.cos (ε * (2 * π * z.2)), ρ * Real.sin (ε * (2 * π * z.2))) ∧
      L (0, 1) = (-(ε * (2 * π)) * (ρ * z.1) * Real.sin (ε * (2 * π * z.2)),
        ε * (2 * π) * (ρ * z.1) * Real.cos (ε * (2 * π * z.2))) := by
  let A : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ρ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((ε * (2 * π)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hA (w : ℝ × ℝ) : A w = (ρ * w.1, ε * (2 * π * w.2)) := by
    simp [A, mul_assoc]
  have hf : (fun w : ℝ × ℝ ↦ Complex.equivRealProdCLM
      (circleMap 0 (ρ * w.1) (ε * (2 * π * w.2)))) = polarCoord.symm ∘ A := by
    funext w
    -- The inverse complex polar map is the inverse real polar map read in `ℂ`.
    have h := add_polarCoord_symm_eq_circleMap 0 (ρ * w.1, ε * (2 * π * w.2))
    rw [zero_add] at h
    rw [Function.comp_apply, hA, ← h, ← Complex.measurableEquivRealProd_symm_polarCoord_symm_apply]
    exact Complex.equivRealProdCLM.apply_symm_apply _
  refine ⟨(fderivPolarCoordSymm (A z)).comp A, ?_, ?_, ?_⟩
  · rw [hf]
    exact (hasFDerivAt_polarCoord_symm (A z)).comp z A.hasFDerivAt
  · simp [hA, fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap, mul_comm]
  · simp [hA, fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap]
    constructor <;> ring

/-- The area density of the radial sweep of `u` is `2π ε ρ² r` times that of `u`. -/
private theorem apply_mfderiv_circleMap (ω : SmoothTwoForm I M) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (ρ ε : ℝ) (z : ℝ × ℝ) :
    ω.1 (u (Complex.equivRealProdCLM (circleMap 0 (ρ * z.1) (ε * (2 * π * z.2)))))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w : ℝ × ℝ ↦ u (Complex.equivRealProdCLM
            (circleMap 0 (ρ * w.1) (ε * (2 * π * w.2))))) z (1, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w : ℝ × ℝ ↦ u (Complex.equivRealProdCLM
            (circleMap 0 (ρ * w.1) (ε * (2 * π * w.2))))) z (0, 1)] =
      ε * (2 * π) * ρ ^ 2 * z.1 * SmoothBundleForm.eval₂ ω
        (u (Complex.equivRealProdCLM (circleMap 0 (ρ * z.1) (ε * (2 * π * z.2)))))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u
          (Complex.equivRealProdCLM (circleMap 0 (ρ * z.1) (ε * (2 * π * z.2)))) (1, 0))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u
          (Complex.equivRealProdCLM (circleMap 0 (ρ * z.1) (ε * (2 * π * z.2)))) (0, 1)) := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun w ↦ Complex.equivRealProdCLM
    (circleMap 0 (ρ * w.1) (ε * (2 * π * w.2)))
  obtain ⟨L, hL, hL₁, hL₂⟩ := hasFDerivAt_circleMap ρ ε z
  -- The chain rule, and the expansion of `du` on the coordinate directions.
  have hd (v : ℝ × ℝ) : mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ Φ) z v =
      (L v).1 • mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Φ z) (1, 0) +
        (L v).2 • mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Φ z) (0, 1) := by
    have h : mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ Φ) z v =
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Φ z) (fderiv ℝ Φ z v) := by
      rw [mfderiv_comp z ((hu _).mdifferentiableAt one_ne_zero)
        hL.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv]
      exact ContinuousLinearMap.comp_apply _ _ _
    rw [h, hL.fderiv]
    have hlin := LinearMap.apply_stdComplexLine (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Φ z)).toLinearMap (L v)
    rw [stdComplexLineReal_eq, stdComplexLineImag_eq] at hlin
    exact hlin
  have h := ω.eval₂_smul_add_smul (u (Φ z)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Φ z) (1, 0))
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Φ z) (0, 1)) (L (1, 0)).1 (L (1, 0)).2 (L (0, 1)).1
    (L (0, 1)).2
  rw [SmoothBundleForm.eval₂_apply, ← hd, ← hd, hL₁, hL₂] at h
  refine h.trans ?_
  have hcs := Real.cos_sq_add_sin_sq (ε * (2 * π * z.2))
  congr 1
  linear_combination (ε * (2 * π) * ρ ^ 2 * z.1) * hcs

/-- Over one period, the angular integral along the circle of radius `r`, run at speed `2π` in
either direction `ε = ±1`, is the average of the integral over `[-π, π]`. -/
private theorem intervalIntegral_circleMap_mul (f : ℂ → ℝ) {ε : ℝ} (hε : |ε| = 1) (r : ℝ) :
    ∫ t in (0 : ℝ)..1, f (circleMap 0 r (ε * (2 * π * t))) =
      (2 * π)⁻¹ * ∫ θ in -π..π, f (circleMap 0 r θ) := by
  have hper : Function.Periodic (fun θ ↦ f (circleMap 0 r θ)) (2 * π) := fun θ ↦ by
    simp only [periodic_circleMap 0 r θ]
  have hc : ε * (2 * π) ≠ 0 := mul_ne_zero (by rintro rfl; simp at hε) (by positivity)
  have hmul (t : ℝ) : ε * (2 * π * t) = ε * (2 * π) * t := by ring
  simp_rw [hmul]
  rw [intervalIntegral.integral_comp_mul_left (fun θ ↦ f (circleMap 0 r θ)) hc, smul_eq_mul,
    mul_zero, mul_one]
  rcases abs_eq (zero_le_one' ℝ) |>.1 hε with rfl | rfl
  · have h := hper.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at h
    rw [one_mul, h]
  · have h := hper.intervalIntegral_add_eq (-(2 * π)) (-π)
    rw [neg_add_cancel, show -π + 2 * π = π by ring] at h
    rw [neg_one_mul, intervalIntegral.integral_symm, h, inv_neg, neg_mul_neg]

/-- **The integral of a two-form over a disc swept out radially.** Let `ω` be a continuous
two-form on a manifold `M`, `u : ℝ × ℝ → M` a `C¹` map of the plane `ℂ ≅ ℝ × ℝ`, `ρ ≥ 0` and
`ε = ±1`. The map `D(r, t) = u(ρ r exp (2π i ε t))` of the unit square sweeps out the disc of
radius `ρ` radially, from its centre at `r = 0` to its boundary circle at `r = 1`, which `t` runs
through counterclockwise for `ε = 1` and clockwise for `ε = -1`. The integral of `ω` over `D` is
`ε` times the symplectic area of `u` over the disc:

`∫_D ω = ε ∫_{‖z‖ ≤ ρ} ω(∂_s u, ∂_t u)`. -/
theorem rectangleIntegral_circleMap (ω : SmoothTwoForm I M) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {ρ : ℝ} (hρ : 0 ≤ ρ) {ε : ℝ} (hε : |ε| = 1) :
    rectangleIntegral ω.1
        (fun z ↦ u (Complex.equivRealProdCLM (circleMap 0 (ρ * z.1) (ε * (2 * π * z.2)))))
        (0, 0) (1, 1) =
      ε * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 ρ,
        SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)) := by
  set A : ℝ × ℝ → ℝ := fun z ↦ SmoothBundleForm.eval₂ ω (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1))
  have hA : Continuous A := by
    have h := (ω.isSmoothForm.of_le (by simp)).continuous_apply_mfderiv hu (1, 0) (0, 1)
    simpa only [A, SmoothBundleForm.eval₂_apply] using h
  set f : ℂ → ℝ := fun w ↦ A (Complex.equivRealProdCLM w)
  -- The area density of the sweep is `2π ε ρ² r` times that of `u`, and its angular integral
  -- over one period is the average over `[-π, π]`.
  have hsweep : rectangleIntegral ω.1
      (fun z ↦ u (Complex.equivRealProdCLM (circleMap 0 (ρ * z.1) (ε * (2 * π * z.2)))))
      (0, 0) (1, 1) = ε * ρ * ∫ r in (0 : ℝ)..1, (fun r ↦ r * ∫ θ in -π..π, f (circleMap 0 r θ))
        (ρ * r) := by
    rw [rectangleIntegral_eq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    refine (intervalIntegral.integral_congr fun t _ ↦ apply_mfderiv_circleMap ω hu ρ ε (r, t)).trans
      ?_
    refine (intervalIntegral.integral_const_mul (ε * (2 * π) * ρ ^ 2 * r)
      fun t ↦ f (circleMap 0 (ρ * r) (ε * (2 * π * t)))).trans ?_
    rw [intervalIntegral_circleMap_mul f hε]
    field_simp
  -- The radial integral is the polar-coordinate integral over the disc.
  have hdisc : {z : ℂ | 0 ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ} = Metric.closedBall 0 ρ := by
    ext z
    simp
  have hpolar := integral_annulus_eq_integral_circleMap (f := f) (z₀ := 0) le_rfl hρ
    (by rw [hdisc]; exact (hA.comp Complex.equivRealProdCLM.continuous).continuousOn)
  rw [hdisc] at hpolar
  have hρr := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun r ↦ r * ∫ θ in -π..π, f (circleMap 0 r θ)) ρ
  rw [smul_eq_mul, mul_zero, mul_one] at hρr
  rw [hsweep, mul_assoc, hρr]
  simp only [smul_eq_mul] at hpolar
  rw [← hpolar]
  congr 1
  -- In real coordinates, the disc in `ℂ` is the preimage of the disc.
  have h := (Complex.volume_preserving_equiv_real_prod.symm).setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding f (Metric.closedBall 0 ρ)
  refine h.symm.trans ?_
  refine setIntegral_congr_fun ?_ fun z _ ↦ ?_
  · exact measurableSet_closedBall.preimage Complex.measurableEquivRealProd.symm.measurable
  · exact congrArg A (Complex.equivRealProdCLM.apply_symm_apply z)

end SmoothTwoForm

end TauCeti
