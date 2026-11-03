/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.InnerHalfSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The perimeter of a half-space

Let `F` be a finite-dimensional real inner product space of dimension `n`, let `ν` be a unit
vector and `c` a real number. The half-space `H = {x | ⟪x, ν⟫ < c}` has perimeter

`P(H; Ω) = Hⁿ⁻¹(Ω ∩ {x | ⟪x, ν⟫ = c})`

in every open set `Ω`, where `Hⁿ⁻¹ = μHE[n - 1]` is the normalized Hausdorff measure
(`TauCeti.perimeter_setOf_inner_lt`). In a ball centred on the boundary
hyperplane the perimeter is the volume `ω_{n-1} r^(n-1)` of an `(n - 1)`-dimensional ball of the
same radius (`TauCeti.perimeter_ball_setOf_inner_lt`). This is the model computation behind
De Giorgi's structure theorem: at a point of the reduced boundary, the blow-ups of a set of finite
perimeter converge to a half-space, and the perimeter of that half-space in the unit ball fixes the
density `|Dχ_E|(B_r(x)) / (ω_{n-1} r^(n-1)) → 1` of the perimeter measure.

Both bounds come from the divergence theorem on the half-space,
`∫_H div φ = ∫_{⟪x, ν⟫ = c} ⟪φ, ν⟫ dHⁿ⁻¹`
(`TauCeti.setIntegral_setOf_inner_lt_trace_fderiv`). An admissible field has `⟪φ, ν⟫ ≤ 1` and
vanishes off `Ω`, which gives the upper bound. For the lower bound, test with `χ ν`, where the
cutoff `χ` takes values in `[0, 1]` and equals one on a compact subset of
`Ω ∩ {⟪x, ν⟫ = c}`, and use the inner regularity of Lebesgue measure on the hyperplane.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 12 (sets of
  finite perimeter) and Chapter 15 (the reduced boundary and De Giorgi's structure theorem).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (the blow-up of the reduced boundary).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace TestFunction
open scoped ENNReal Distributions RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {ν : F}

/-- **The perimeter of a half-space.** For a unit vector `ν`, the perimeter of the half-space
`{x | ⟪x, ν⟫ < c}` in an open set `Ω` is the `(n - 1)`-dimensional Hausdorff measure of the part
of its boundary hyperplane `{x | ⟪x, ν⟫ = c}` lying in `Ω`. -/
theorem perimeter_setOf_inner_lt (hν : ‖ν‖ = 1) (c : ℝ) (Ω : Opens F) :
    perimeter volume Ω {x | ⟪x, ν⟫ < c} = μHE[finrank ℝ F - 1] (Ω ∩ {x | ⟪x, ν⟫ = c}) := by
  set S : Set F := {x | ⟪x, ν⟫ = c}
  have hS : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
  have hH : MeasurableSet {x : F | ⟪x, ν⟫ < c} := measurableSet_lt (by fun_prop) measurable_const
  have hdiv (φ : 𝓓(Ω, F)) : ∫ x in {x | ⟪x, ν⟫ < c}, divergenceCLM φ x =
      ∫ x in S, ⟪φ x, ν⟫ ∂μHE[finrank ℝ F - 1] := by
    simp_rw [divergenceCLM_apply]
    exact setIntegral_setOf_inner_lt_trace_fderiv hν c (φ.contDiff.of_le (by simp))
      φ.hasCompactSupport
  rw [perimeter_eq_iSup hH.nullMeasurableSet]
  refine le_antisymm (iSup₂_le fun φ hφ => ?_) ?_
  · -- An admissible field has normal component at most one on `Ω` and vanishes off `Ω`.
    have hle (x : F) : ‖⟪φ x, ν⟫‖ₑ ≤ (Ω : Set F).indicator 1 x := by
      by_cases hx : x ∈ (Ω : Set F)
      · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm, ENNReal.ofReal_le_one]
        exact (norm_inner_le_norm _ _).trans (by rw [hν, mul_one]; exact hφ x)
      · simp [image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)]
    calc ENNReal.ofReal (∫ x in {x | ⟪x, ν⟫ < c}, divergenceCLM φ x)
        ≤ ‖∫ x in S, ⟪φ x, ν⟫ ∂μHE[finrank ℝ F - 1]‖ₑ := by
          rw [hdiv]
          exact Real.ofReal_le_enorm _
      _ ≤ ∫⁻ x in S, (Ω : Set F).indicator 1 x ∂μHE[finrank ℝ F - 1] :=
          (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono hle)
      _ = μHE[finrank ℝ F - 1] (Ω ∩ S) := by
          rw [lintegral_indicator_one Ω.isOpen.measurableSet, Measure.restrict_apply
            Ω.isOpen.measurableSet]
  · -- Approximate the open part `ι ⁻¹' Ω` of the parametrizing space by compact sets.
    set ι : (ℝ ∙ ν)ᗮ → F := fun y => c • ν + (y : F)
    have hι : Continuous ι := by fun_prop
    rw [← Measure.restrict_apply' hS, euclideanHausdorffMeasure_restrict_setOf_inner_eq hν,
      Measure.map_apply hι.measurable Ω.isOpen.measurableSet,
      (Ω.isOpen.preimage hι).measure_eq_iSup_isCompact]
    refine iSup₂_le fun C hCΩ => iSup_le fun hC => ?_
    -- A cutoff `χ` equal to one on `ι '' C` gives the admissible field `χ ν`.
    obtain ⟨χ, hχ1, hχ01⟩ := exists_eventually_eq_one (n := ⊤) (hC.image hι)
      (image_subset_iff.2 hCΩ)
    let φ : 𝓓(Ω, F) := ⟨fun x => χ x • ν, χ.contDiff.smul contDiff_const,
      χ.hasCompactSupport.smul_right, (tsupport_smul_subset_left _ _).trans χ.tsupport_subset⟩
    have hφ (x : F) : ‖φ x‖ ≤ 1 := by
      simp only [φ, coe_mk, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
      exact (hχ01 x).2
    have hχι : Integrable (fun y => χ (ι y)) := by
      have h := integrableOn_setOf_inner_eq hν c χ.continuous χ.hasCompactSupport
      rwa [IntegrableOn, euclideanHausdorffMeasure_restrict_setOf_inner_eq hν,
        integrable_map_measure χ.continuous.aestronglyMeasurable hι.aemeasurable] at h
    calc volume C = ENNReal.ofReal (∫ y, C.indicator 1 y) := by
          rw [integral_indicator_one hC.measurableSet, ofReal_measureReal hC.measure_lt_top.ne]
      _ ≤ ENNReal.ofReal (∫ y, χ (ι y)) := by
          refine ENNReal.ofReal_le_ofReal (integral_mono
            ((integrable_indicator_iff hC.measurableSet).2 (integrableOn_const
              hC.measure_lt_top.ne)) hχι fun y => ?_)
          by_cases hy : y ∈ C
          · rw [indicator_of_mem hy, Pi.one_apply, hχ1.self_of_nhdsSet _ (mem_image_of_mem ι hy)]
          · rw [indicator_of_notMem hy]
            exact (hχ01 _).1
      _ = ENNReal.ofReal (∫ x in {x | ⟪x, ν⟫ < c}, divergenceCLM φ x) := by
          rw [hdiv, setIntegral_setOf_inner_eq hν]
          simp [φ, ι, real_inner_smul_left, hν]
      _ ≤ ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1),
          ENNReal.ofReal (∫ x in {x | ⟪x, ν⟫ < c}, divergenceCLM φ x) :=
          le_iSup₂_of_le (f := fun (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
            ENNReal.ofReal (∫ x in {x | ⟪x, ν⟫ < c}, divergenceCLM φ x)) φ hφ le_rfl

/-- **The perimeter of a half-space in a ball centred on its boundary.** For a unit vector `ν` and
`r > 0`, the half-space `{y | ⟪y, ν⟫ < ⟪x, ν⟫}`, whose boundary hyperplane passes through `x`, has
perimeter `ω_{n-1} r^(n-1)` in the ball `B(x, r)`, where `ω_{n-1}` is the volume of the unit ball
of `ℝ^(n-1)`. -/
theorem perimeter_ball_setOf_inner_lt (hν : ‖ν‖ = 1) (x : F) {r : ℝ} (hr : 0 < r) :
    perimeter volume ⟨ball x r, isOpen_ball⟩ {y | ⟪y, ν⟫ < ⟪x, ν⟫} =
      ENNReal.ofReal r ^ (finrank ℝ F - 1) *
        volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) 1) := by
  set c := ⟪x, ν⟫
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
  have : Nontrivial F := ⟨⟨ν, 0, hν0⟩⟩
  have : Fact (finrank ℝ F = finrank ℝ F - 1 + 1) := ⟨(Nat.sub_add_cancel finrank_pos).symm⟩
  -- The point `x` is `c • ν + x₀` with `x₀ ∈ (ℝ ∙ ν)ᗮ`, so the part of the hyperplane in the
  -- ball is the image of the ball of radius `r` about `x₀` in `(ℝ ∙ ν)ᗮ`.
  have hx₀ : x - c • ν ∈ (ℝ ∙ ν)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
    ring
  have hι := isometry_smul_add_coe (ν := ν) c
  have hpre : (fun y : (ℝ ∙ ν)ᗮ => c • ν + (y : F)) ⁻¹' ball x r = ball ⟨x - c • ν, hx₀⟩ r := by
    convert hι.preimage_ball ⟨x - c • ν, hx₀⟩ r
    simp
  -- An orthonormal basis identifies `(ℝ ∙ ν)ᗮ` with `ℝ^(n-1)`, preserving volume and unit balls.
  have hball : volume (ball (0 : (ℝ ∙ ν)ᗮ) 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) 1) := by
    let e := ((stdOrthonormalBasis ℝ (ℝ ∙ ν)ᗮ).reindex (finCongr
      (Submodule.finrank_orthogonal_span_singleton (n := finrank ℝ F - 1) hν0))).repr
    rw [← e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet,
      e.preimage_ball, map_zero]
  rw [perimeter_setOf_inner_lt hν, Opens.coe_mk,
    ← Measure.restrict_apply' (measurableSet_eq_fun (by fun_prop) measurable_const),
    euclideanHausdorffMeasure_restrict_setOf_inner_eq hν,
    Measure.map_apply hι.continuous.measurable measurableSet_ball, hpre,
    Measure.addHaar_ball_of_pos _ _ hr,
    Submodule.finrank_orthogonal_span_singleton (n := finrank ℝ F - 1) hν0,
    ENNReal.ofReal_pow hr.le, hball]

end TauCeti
