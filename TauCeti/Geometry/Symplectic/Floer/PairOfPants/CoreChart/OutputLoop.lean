/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CoreChart
-- The rotation runs along the rays of the core chart to the output circle, so this file needs the
-- definitions of these rays and of the angles of the lobes, not only the API of the core chart.
import all TauCeti.Geometry.Symplectic.Floer.PairOfPants.CoreChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The output loop of the core of the pair of pants

The core chart `TauCeti.Floer.pairOfPantsCoreChart` of the pair of pants `S = ℂ ∖ {0, 1}` is a
cylinder from the figure eight formed by the circles of the two input ends at height `0` to the
circle `‖w‖ = 2` of the output end at height `0`. It runs once clockwise around that circle, but
along the rays from `1/2`, starting at `1/2 - i √15 / 2` and at the speed of the angle about `1/2`.
The end chart of the output end at height `0` runs around the same circle from `2`, at the
constant speed of the angle about `0`: `t ↦ 2 e^{-2π i t}`
(`TauCeti.Floer.endChart`). This file joins the two loops.

The **rotation of the output loop** `TauCeti.Floer.pairOfPantsOutputRotation` is a smooth map of
the cylinder `ℝ × ℝ / ℤ` (`TauCeti.Floer.contDiff_pairOfPantsOutputRotation`,
`TauCeti.Floer.pairOfPantsOutputRotation_apply_add_one`) into the circle `‖w‖ = 2`
(`TauCeti.Floer.norm_symm_pairOfPantsOutputRotation`), constant in `s` for `s ≤ 0` and for
`s ≥ 1`, which runs through the output loop of the core chart for `s ≤ 0`
(`TauCeti.Floer.pairOfPantsOutputRotation_mk_of_nonpos`) and through the end chart of the output
end at height `0` for `s ≥ 1` (`TauCeti.Floer.pairOfPantsOutputRotation_mk_of_one_le`). At the
parameter `(s, t)` it is the point of the circle on the ray from `k / 2` at an angle `θ`, where
`k` runs from `1` to `0` and `θ` from the angle of the core chart to `-2π t`. The angle of the core
chart is read through a smooth lift, decreasing by `2π` over each period.

For a map `u` of the pair of pants into a manifold `M`:

* **The rotation has zero area.** If `u` is `C¹` on `S`, then the integral of every two-form over
  `u` composed with the rotation vanishes
  (`TauCeti.Floer.rectangleIntegral_comp_pairOfPantsOutputRotation`), since the rotation runs
  through a circle (`TauCeti.rectangleIntegral_comp_eq_zero_of_sq_add_sq_eq`).
* **The rotation as a cylinder.** If `u` is `C²` on `S`, then `u` composed with the rotation is a
  cylinder (`TauCeti.IsLoopCylinder`) from the loop of `u` along the output loop of the core chart
  to the loop of `u` along the end chart of the output end at height `0`
  (`TauCeti.Floer.isLoopCylinder_comp_pairOfPantsOutputRotation`).
* **Gluing discs of the inputs.** Two maps `D₀`, `D₁` ending at the two input loops of `u` at
  height `0` and sharing their seam, placed side by side, followed by the core of `u` and then by
  the rotation of its output loop, give a map ending at the loop of `u` along the end chart of the
  output end at height `0`, whose integral is that over `D₀` plus that over `D₁` minus the
  integral of `u^* φ` over the truncation `S₀`
  (`TauCeti.Floer.rectangleIntegral_rectangleTrans_comp_pairOfPantsOutputRotation`).

So the area identity of the core chart holds with the output loop of the core replaced by the
loop of the output end at height `0`, in the end coordinates in which the Floer data of the output
end are given.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and the energy of its solutions.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  capped orbits and the action of glued caps.
-/

public section

noncomputable section

open Set Real Function Manifold TauCeti.ThricePuncturedSphere

namespace TauCeti.Floer

/-! ### The output loop of the core chart -/

/-- The parameter of the output loop of the core chart: the core chart runs through the point of
the output circle on the ray from `1/2` at the angle `-π/2 - 2π coreLoopParam t`. It increases by
`1` over each period, and it is constant near the integers. -/
private def coreLoopParam (t : ℝ) : ℝ :=
  ⌊t⌋ + (smoothTransition (6 * Int.fract t - 1) + smoothTransition (6 * Int.fract t - 4)) / 2

private theorem coreLoopParam_add_one (t : ℝ) : coreLoopParam (t + 1) = coreLoopParam t + 1 := by
  simp only [coreLoopParam, Int.floor_add_one, Int.fract_add_one, Int.cast_add, Int.cast_one]
  ring

/-- At the fractional part the integer part of the lifted parameter vanishes. -/
private theorem coreLoopParam_fract (t : ℝ) :
    coreLoopParam (Int.fract t) =
      (smoothTransition (6 * Int.fract t - 1) + smoothTransition (6 * Int.fract t - 4)) / 2 := by
  rw [coreLoopParam, Int.floor_fract, Int.fract_fract, Int.cast_zero, zero_add]

/-- The lifted parameter differs from its value at the fractional part by the integer part. -/
private theorem coreLoopParam_eq_floor_add_fract (t : ℝ) :
    coreLoopParam t = ⌊t⌋ + coreLoopParam (Int.fract t) := by
  rw [coreLoopParam_fract, coreLoopParam]

private theorem coreLoopParam_eq {n : ℤ} {t : ℝ} (h₁ : (n : ℝ) - 1 / 6 < t) (h₂ : t < n + 1) :
    coreLoopParam t =
      n + (smoothTransition (6 * (t - n) - 1) + smoothTransition (6 * (t - n) - 4)) / 2 := by
  rcases le_or_gt (n : ℝ) t with h | h
  · have hfl : ⌊t⌋ = n := Int.floor_eq_iff.2 ⟨h, h₂⟩
    rw [coreLoopParam, hfl, Int.fract, hfl]
  · -- Just below `n` the parameter has already reached `n`.
    have hfl : ⌊t⌋ = n - 1 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [coreLoopParam, Int.fract, hfl]
    push_cast
    rw [smoothTransition.one_of_one_le (by linarith), smoothTransition.one_of_one_le (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), smoothTransition.zero_of_nonpos (by linarith)]
    ring

private theorem contDiff_coreLoopParam {m : ℕ∞} : ContDiff ℝ m coreLoopParam := by
  refine contDiff_iff_contDiffAt.2 fun t₀ ↦ ?_
  set n : ℤ := ⌊t₀ + 1 / 12⌋
  have h₁ : (n : ℝ) - 1 / 6 < t₀ := by have := Int.floor_le (t₀ + 1 / 12); linarith
  have h₂ : t₀ < n + 1 := by have := Int.lt_floor_add_one (t₀ + 1 / 12); linarith
  have hev : (fun t ↦ (n : ℝ) + (smoothTransition (6 * (t - n) - 1) +
      smoothTransition (6 * (t - n) - 4)) / 2) =ᶠ[nhds t₀] coreLoopParam := by
    filter_upwards [Ioo_mem_nhds h₁ h₂] with t ht
    exact (coreLoopParam_eq ht.1 ht.2).symm
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev.symm
  have := smoothTransition.contDiff (n := m)
  fun_prop

/-- **The output loop of the core chart, along a lifted angle.** The core chart runs at `s = 1`
through the points of the output circle on the rays from `1/2` at the angles
`-π/2 - 2π coreLoopParam t`. -/
private theorem pairOfPantsCoreChart_mk_one_eq_outputRayPoint (t : ℝ) :
    pairOfPantsCoreChart (1, t) = outputRayPoint 1 (-(π / 2) - 2 * π * coreLoopParam t) := by
  set G := outputRayPoint 1
  have hG : Periodic G (2 * π) := periodic_outputRayPoint 1
  rw [pairOfPantsCoreChart_mk_one_eq_loopwiseTrans, ← apply_loopwiseTrans G]
  -- Both sides only depend on the fractional part of `t`, up to a multiple of `2π` in the angle.
  have hper : Periodic (fun t ↦ loopwiseTrans (fun z ↦ lobeAngle (1 / 4) z.2)
      (fun z ↦ lobeAngle (3 / 4) z.2) ((1 : ℝ), t)) 1 :=
    fun t ↦ loopwiseTrans_apply_add_one _ _ _ _
  have hx := hper.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one, Int.self_sub_floor] at hx
  rw [← hx, coreLoopParam_eq_floor_add_fract, show ∀ c : ℝ, -(π / 2) - 2 * π * (⌊t⌋ + c) =
    -(π / 2) - 2 * π * c - ⌊t⌋ * (2 * π) from fun c ↦ by ring, hG.sub_int_mul_eq]
  congr 1
  have hfr := Int.fract_nonneg t
  have hfr₁ := Int.fract_lt_one t
  rw [coreLoopParam_fract]
  rcases le_or_gt (Int.fract t) (1 / 2) with h | h
  · rw [loopwiseTrans_of_le _ _ hfr h,
      smoothTransition.zero_of_nonpos (show 6 * Int.fract t - 4 ≤ 0 by linarith)]
    simp only [lobeAngle]
    ring
  · rw [loopwiseTrans_of_lt _ _ h hfr₁,
      smoothTransition.one_of_one_le (show 1 ≤ 6 * Int.fract t - 1 by linarith)]
    simp only [lobeAngle]
    ring

/-! ### The rotation of the output loop -/

/-- The angle of `TauCeti.Floer.pairOfPantsOutputRotation` at `(s, t)`. -/
private def outputRotationAngle (z : ℝ × ℝ) : ℝ :=
  -(π / 2) - 2 * π * ((1 - smoothTransition z.1) * coreLoopParam z.2 +
    smoothTransition z.1 * (z.2 - 1 / 4))

/-- The **rotation of the output loop** of the pair of pants: a smooth cylinder in the output
circle `‖w‖ = 2` of `S = ℂ ∖ {0, 1}`, in the real coordinates `ℝ × ℝ ≃ ℂ`. It is constant in `s`
for `s ≤ 0`, where it runs through the output loop of the core chart
(`TauCeti.Floer.pairOfPantsOutputRotation_mk_of_nonpos`), and for `s ≥ 1`, where it runs through
the end chart of the output end at height `0`
(`TauCeti.Floer.pairOfPantsOutputRotation_mk_of_one_le`). In between it moves the point from
which the circle is seen from `1/2` to `0`, and the angle from that of the core chart to `-2π t`. -/
def pairOfPantsOutputRotation (z : ℝ × ℝ) : ℝ × ℝ :=
  outputRayPoint (1 - smoothTransition z.1) (outputRotationAngle z)

/-- The parameter `k = 1 - β s` of the point from which the rotation sees the output circle
satisfies `k² ≤ 1`. -/
private theorem sq_one_sub_smoothTransition_le (x : ℝ) : (1 - smoothTransition x) ^ 2 ≤ 1 := by
  have h₀ := smoothTransition.nonneg x
  have h₁ := smoothTransition.le_one x
  nlinarith

/-- The rotation of the output loop runs through the circle `x² + y² = 4`. -/
private theorem pairOfPantsOutputRotation_sq_add_sq (z : ℝ × ℝ) :
    (pairOfPantsOutputRotation z).1 ^ 2 + (pairOfPantsOutputRotation z).2 ^ 2 = 4 :=
  outputRayPoint_sq_add_sq ((sq_one_sub_smoothTransition_le z.1).trans (by norm_num)) _

/-- The rotation of the output loop is `1`-periodic in its second variable. -/
@[simp]
theorem pairOfPantsOutputRotation_apply_add_one (s t : ℝ) :
    pairOfPantsOutputRotation (s, t + 1) = pairOfPantsOutputRotation (s, t) := by
  have h : outputRotationAngle (s, t + 1) = outputRotationAngle (s, t) - 2 * π := by
    simp only [outputRotationAngle, coreLoopParam_add_one]
    ring
  rw [pairOfPantsOutputRotation, pairOfPantsOutputRotation, h]
  exact (periodic_outputRayPoint _).sub_eq _

/-- The rotation of the output loop is smooth. -/
theorem contDiff_pairOfPantsOutputRotation {n : ℕ∞} :
    ContDiff ℝ n pairOfPantsOutputRotation := by
  have hτ := contDiff_coreLoopParam (m := n)
  have hθ : ContDiff ℝ n outputRotationAngle := by unfold outputRotationAngle; fun_prop
  exact contDiff_outputRayPoint (by fun_prop) hθ fun z ↦
    (sq_one_sub_smoothTransition_le z.1).trans_lt (by norm_num)

/-- The rotation of the output loop runs through the circle `‖w‖ = 2`. -/
theorem norm_symm_pairOfPantsOutputRotation (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (pairOfPantsOutputRotation z)‖ = 2 := by
  rw [Complex.norm_def, Complex.normSq_apply, Complex.equivRealProdCLM_symm_apply_re,
    Complex.equivRealProdCLM_symm_apply_im, ← sq, ← sq, pairOfPantsOutputRotation_sq_add_sq,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]

/-- The rotation of the output loop takes values in the pair of pants. -/
theorem pairOfPantsOutputRotation_mem_thricePuncturedSphereReal (z : ℝ × ℝ) :
    pairOfPantsOutputRotation z ∈ thricePuncturedSphereReal :=
  mem_thricePuncturedSphereReal_of_two_le_norm (norm_symm_pairOfPantsOutputRotation z).ge

/-- **The start of the rotation.** For `s ≤ 0` the rotation of the output loop runs through the
output loop of the core chart. -/
theorem pairOfPantsOutputRotation_mk_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) :
    pairOfPantsOutputRotation (s, t) = pairOfPantsCoreChart (1, t) := by
  rw [pairOfPantsCoreChart_mk_one_eq_outputRayPoint, pairOfPantsOutputRotation,
    outputRotationAngle]
  simp only [smoothTransition.zero_of_nonpos hs, sub_zero, one_mul, zero_mul, add_zero]

/-- **The end of the rotation.** For `s ≥ 1` the rotation of the output loop runs through the end
chart of the output end at height `0`, the loop `t ↦ 2 e^{-2π i t}`. -/
theorem pairOfPantsOutputRotation_mk_of_one_le {s : ℝ} (hs : 1 ≤ s) (t : ℝ) :
    pairOfPantsOutputRotation (s, t) = endChart Puncture.inf (0, t) := by
  rw [pairOfPantsOutputRotation, outputRotationAngle, smoothTransition.one_of_one_le hs, sub_self,
    outputRayPoint_zero, endChart_mk, Puncture.cylindricalEndLift_inf]
  congr 3
  push_cast
  ring

section Manifold

variable {E HM M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The rotation of the output loop has zero area.** For a map `u` of the pair of pants into a
manifold `M` which is `C¹` on `S`, the integral of every two-form over `u` composed with the
rotation of the output loop vanishes: the rotation runs through a circle, so its two partial
derivatives are parallel. -/
theorem rectangleIntegral_comp_pairOfPantsOutputRotation (φ : RoughForm I M F 2) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (a b : ℝ × ℝ) :
    rectangleIntegral φ (u ∘ pairOfPantsOutputRotation) a b = 0 :=
  rectangleIntegral_comp_eq_zero_of_sq_add_sq_eq φ
    (contDiff_pairOfPantsOutputRotation.differentiable one_ne_zero)
    pairOfPantsOutputRotation_sq_add_sq
    (fun z ↦ (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds
      (pairOfPantsOutputRotation_mem_thricePuncturedSphereReal z))).mdifferentiableAt one_ne_zero)
    a b

/-- **The rotation of the output loop as a cylinder.** For a map `u` of the pair of pants into a
manifold `M` which is `C²` on `S`, the composite of `u` with the rotation of the output loop is a
cylinder from the loop of `u` along the output loop of the core chart to the loop of `u` along the
end chart of the output end at height `0`. -/
theorem isLoopCylinder_comp_pairOfPantsOutputRotation {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u thricePuncturedSphereReal) :
    IsLoopCylinder I (u ∘ pairOfPantsOutputRotation) (fun t ↦ u (pairOfPantsCoreChart (1, t)))
      fun t ↦ u (endChart Puncture.inf (0, t)) where
  contMDiff := hu.comp_contMDiff contDiff_pairOfPantsOutputRotation.contMDiff
    pairOfPantsOutputRotation_mem_thricePuncturedSphereReal
  apply_add_one z := by
    simp only [Function.comp_apply, pairOfPantsOutputRotation_apply_add_one]
  apply_zero t := by rw [Function.comp_apply, pairOfPantsOutputRotation_mk_of_nonpos le_rfl]
  apply_one t := by rw [Function.comp_apply, pairOfPantsOutputRotation_mk_of_one_le le_rfl]

/-- **Gluing discs of the inputs to the core, up to the output end loop.** Let `u` be a map of the
pair of pants `S` into a manifold `M`, `C¹` on `S`, and let `D₀` and `D₁` be `C¹` maps of the
plane which end at `s = 1` at the loops of `u` along the circles of the input ends `0` and `1` at
height `0`, and share their seam. Placing them side by side, following them by the core of `u`
and then by the rotation of its output loop gives a map ending at the loop of `u` along the end
chart of the output end at height `0`, and for every continuous two-form `φ` its integral is the
sum of the integrals over `D₀` and `D₁` minus the integral of `u^* φ` over the truncation `S₀`
at height `0`. -/
theorem rectangleIntegral_rectangleTrans_comp_pairOfPantsOutputRotation [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {D₀ D₁ : ℝ × ℝ → M}
    (hD₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₀) (hD₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₁)
    (h₀₁ : ∀ s, D₀ (s, 1) = D₁ (s, 0)) (h₁₀ : ∀ s, D₁ (s, 1) = D₀ (s, 0))
    (h₀ : ∀ t, D₀ (1, t) = u (endChart Puncture.zero (0, t)))
    (h₁ : ∀ t, D₁ (1, t) = u (endChart Puncture.one (0, t))) :
    rectangleIntegral φ (rectangleTrans (rectangleTrans (loopwiseTrans D₀ D₁)
        (u ∘ pairOfPantsCoreChart)) (u ∘ pairOfPantsOutputRotation)) (0, 0) (1, 1) =
      rectangleIntegral φ D₀ (0, 0) (1, 1) + rectangleIntegral φ D₁ (0, 0) (1, 1) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation 0,
          φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  have hcore : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ pairOfPantsCoreChart) :=
    hu.comp_contMDiff contDiff_pairOfPantsCoreChart.contMDiff fun z ↦
      truncation_subset 0 (pairOfPantsCoreChart_mem_preimage_truncation z)
  have hmatch (t : ℝ) : loopwiseTrans D₀ D₁ (1, t) = (u ∘ pairOfPantsCoreChart) (0, t) := by
    rw [Function.comp_apply, pairOfPantsCoreChart_mk_zero, apply_loopwiseTrans u]
    exact loopwiseTrans_congr (fun r _ ↦ h₀ r) (fun r _ ↦ h₁ r)
  have hrot : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ pairOfPantsOutputRotation) :=
    hu.comp_contMDiff contDiff_pairOfPantsOutputRotation.contMDiff
      pairOfPantsOutputRotation_mem_thricePuncturedSphereReal
  rw [rectangleIntegral_rectangleTrans hφ
    (contMDiff_rectangleTrans (contMDiff_loopwiseTrans hD₀ hD₁ h₀₁ h₁₀) hcore hmatch) hrot
    (fun t ↦ by
      rw [rectangleTrans_apply_one, Function.comp_apply, Function.comp_apply,
        pairOfPantsOutputRotation_mk_of_nonpos le_rfl]),
    rectangleIntegral_comp_pairOfPantsOutputRotation φ hu,
    rectangleIntegral_rectangleTrans_loopwiseTrans_comp_pairOfPantsCoreChart hφ hu hD₀ hD₁ h₀₁ h₁₀
      h₀ h₁, add_zero]

end Manifold

end TauCeti.Floer
