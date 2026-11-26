/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Decay
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Puncture
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Calculus.FDeriv.Puncture
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Pointwise power bounds at a puncture

Power decay of the energy of a pseudoholomorphic curve gives a power bound on its full
differential. With taming constant `c > 0` and structure bound `M ≥ 0`, the exponent is
`c / (1 + M)² - 1`, which is strictly greater than `-1`. Consequently the speed along
every radial segment is integrable up to the puncture. This supplies the finite radial
length needed to extend the curve continuously; no value or regularity at the puncture
is assumed here.

The target structure may vary with the image point. A compact image in a neighbourhood
where the structure is `C²` supplies the uniform small-energy mean-value inequality.
The energy-decay input is `SymplecticForm.integral_norm_fderiv_one_sq_ball_le_rpow`;
the punctured-disc mean-value input is
`TauCeti.exists_pos_sq_norm_fderiv_one_le_energy`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c M : ℝ} {W K : Set V}

/-- Bound the energy on all smaller discs by a fixed power, using one reference radius. -/
private theorem exists_energy_power_bound
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ A ≥ 0, ∀ r ∈ Ioo 0 (R / 2),
      (∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2) ≤ A * r ^ (2 * c / (1 + M) ^ 2) := by
  -- The Cauchy--Riemann equation bounds the full energy by the directional energy.
  have hfull : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (ball z₀ R) := by
    rw [IntegrableOn, ← Measure.restrict_congr_set (sdiff_null_ae_eq_self
      (s := ball z₀ R) (measure_singleton z₀))]
    exact integrableOn_norm_fderiv_sq_of_apply_I_eq
      (measurableSet_ball.diff (measurableSet_singleton _)) hCR hJ (henergy.mono_set sdiff_subset)
  let b := R / 2
  let α := 2 * c / (1 + M) ^ 2
  let E := ∫ z in ball z₀ b, ‖fderiv ℝ u z 1‖ ^ 2
  refine ⟨E / b ^ α, by dsimp [E, b]; positivity, fun r hr ↦ ?_⟩
  have h := ω.integral_norm_fderiv_one_sq_ball_le_rpow hg hc hu hCR htame hJ hfull
    (b := b) hr.1 hr.2.le (by dsimp [b]; linarith)
  rw [Real.div_rpow hr.1.le (half_pos hR).le] at h
  simpa only [b, α, E, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The differential of a finite-energy pseudoholomorphic curve on a punctured disc has a
power bound with exponent strictly greater than `-1`. Both the radius and the bound are
uniform in the direction of approach. The value of the curve at the puncture is unrestricted.
-/
theorem exists_pos_norm_fderiv_le_rpow
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ ε > 0, ε < R ∧ ∃ C > 0, ∀ z ∈ ball z₀ ε \ {z₀},
      ‖fderiv ℝ u z‖ ≤ C * ‖z - z₀‖ ^ (c / (1 + M) ^ 2 - 1) := by
  have hmem := circleMap_mem_ball_diff_singleton (z₀ := z₀) (half_pos hR) (half_lt_self hR) 0
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound _ hmem)
  -- Normalize the energy power bound, then choose a radius below the mean-value threshold.
  let β := c / (1 + M) ^ 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hα : 2 * c / (1 + M) ^ 2 = 2 * β := by dsimp [β]; ring
  obtain ⟨A, _, hpower⟩ := exists_energy_power_bound hg hc hR
    (hu.of_le (by norm_num)) hCR htame hbound henergy
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_sq_norm_fderiv_one_le_energy hW hJ hK hKW hJsq hu hCR huK henergy
  obtain ⟨ε, hε, hεR, B, hB⟩ := Real.exists_pos_le_sqrt_mul_rpow_sub_one_of_le_mul_rpow
    (E := fun r ↦ ∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2) (K := 32 / Real.pi) hR (by positivity)
    hβ hδ (by simpa only [hα] using hpower)
  refine ⟨ε, hε, by linarith, (1 + M) * (Real.sqrt B + 1), by positivity, fun z hz ↦ ?_⟩
  let d := ‖z - z₀‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hz.2)
  have hdε : d < ε := by simpa only [mem_ball, dist_eq_norm] using hz.1
  have hzR : z ∈ ball z₀ R \ {z₀} := ⟨ball_subset_ball (by linarith) hz.1, hz.2⟩
  -- The estimate on a disc avoiding the puncture converts energy decay into derivative decay.
  obtain ⟨hsmallE, hreal⟩ := hB d ⟨hd, hdε⟩
  have hpoint := hreal _ (hmean z
    ⟨by simpa only [mem_ball, dist_eq_norm] using hdε.trans hεR, hz.2⟩ hsmallE)
  -- The Cauchy--Riemann equation controls the full differential by its real-direction part.
  have hop : ‖fderiv ℝ u z‖ ≤ (1 + M) * ‖fderiv ℝ u z 1‖ :=
    (fderiv ℝ u z).norm_le_of_apply_I_eq (hCR z hzR) (hbound z hzR) le_rfl
  calc
    ‖fderiv ℝ u z‖ ≤ (1 + M) * (Real.sqrt B * d ^ (β - 1)) := by
      exact hop.trans (mul_le_mul_of_nonneg_left hpoint (by positivity))
    _ ≤ (1 + M) * (Real.sqrt B + 1) * d ^ (β - 1) := by
      nlinarith [Real.rpow_pos_of_pos hd (β - 1)]

/-- A finite-energy pseudoholomorphic curve has integrable velocity along every radial
segment sufficiently close to the puncture. The radius is uniform over all unit directions;
no continuous extension at the missing endpoint is assumed. -/
theorem exists_pos_integrableOn_deriv_radial
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ ε > 0, ε < R ∧ ∀ v : ℂ, ‖v‖ = 1 →
      IntegrableOn (deriv (fun t : ℝ ↦ u (z₀ + t • v))) (Ioo 0 ε) := by
  obtain ⟨ε, hε, hεR, C, _, hC⟩ := ω.exists_pos_norm_fderiv_le_rpow
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame hbound henergy
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound _
    (circleMap_mem_ball_diff_singleton (z₀ := z₀) (half_pos hR) (half_lt_self hR) 0))
  refine ⟨ε, hε, hεR, fun v hv ↦ integrableOn_deriv_radial_of_norm_fderivWithin_le_rpow
    (s := univ) (C := C) (β := c / (1 + M) ^ 2) (by positivity) hv (mapsTo_univ _ _)
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)⟩
  · have hzR : z ∈ ball z₀ R \ {z₀} := ⟨ball_subset_ball hεR.le hz.2.1, hz.2.2⟩
    exact ((hu.contDiffAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hzR)).differentiableAt
      (by norm_num)).differentiableWithinAt
  · simpa only [fderivWithin_univ] using hC z hz.2

end TauCeti.SymplecticForm
