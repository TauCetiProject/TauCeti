/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity, integrability, and Fubini identities for group convolutions

For compactly supported continuous functions `u : G → E` and `v : G → F` on a topological group `G`
and measures `μ`, `ν` finite on compact sets with `ν` left-invariant (without σ-finiteness or
second-countability hypotheses), this file records continuity, integrability, and iterated-integral
identities for parametric convolutions `s ↦ ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ` and their scalar norm
counterparts `s ↦ ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ` and `s ↦ ∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ`.

## Main statements

* `TauCeti.continuous_integral_bilinear_inv_mul`,
  `TauCeti.integrable_integral_bilinear_inv_mul`, and
  `TauCeti.integral_integral_bilinear_inv_mul`: continuity, integrability against `ν`, and
  iterated integral identity for `s ↦ ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ` with a continuous bilinear
  map `B : E →L[𝕜] F →L[𝕜] V`.
* `TauCeti.continuous_integral_norm_mul_inv_mul`, `TauCeti.integrable_integral_norm_mul_inv_mul`,
  and `TauCeti.lintegral_eNorm_mul_inv_mul_eq_ofReal_integral`: continuity, integrability
  against `ν`, and `ℝ≥0∞` conversion of `s ↦ ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ`.
* `TauCeti.integral_integral_norm_mul_inv_mul` and
  `TauCeti.lintegral_lintegral_eNorm_mul_inv_mul`: iterated norm convolution identities for
  compactly supported continuous functions against measures `μ` and `ν` finite on compacts with `ν`
  left-invariant.
-/

public section

open MeasureTheory Function
open scoped ENNReal

namespace TauCeti

section Bilinear

variable {G E F V 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
private theorem continuous_uncurry_bilinear_inv_mul [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]
    (B : E →L[𝕜] F →L[𝕜] V) {u : G → E} {v : G → F} (hu : Continuous u) (hv : Continuous v) :
    Continuous (uncurry fun s r => B (u r) (v (r⁻¹ * s))) := by
  rw [uncurry_def]
  exact B.continuous₂.comp
    ((hu.comp continuous_snd).prodMk (hv.comp (continuous_snd.inv.mul continuous_fst)))

omit [IsTopologicalGroup G] [NormedSpace ℝ V] in
private theorem mem_tsupport_bilinear_inv_mul [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]
    (B : E →L[𝕜] F →L[𝕜] V) {u : G → E} {v : G → F} {s r : G}
    (hsr : B (u r) (v (r⁻¹ * s)) ≠ 0) : r ∈ tsupport u ∧ r⁻¹ * s ∈ tsupport v :=
  mem_tsupport_and_inv_mul_mem_tsupport hsr (by intro hu0; simp [hu0]) (by intro hv0; simp [hv0])

/-- For continuous `u : G → E` with compact support, continuous `v : G → F`, and a continuous
bilinear map `B : E →L[𝕜] F →L[𝕜] V`, the parametric convolution
`s ↦ ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ` is continuous against any measure finite on compact sets. -/
theorem continuous_integral_bilinear_inv_mul [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (B : E →L[𝕜] F →L[𝕜] V) {u : G → E} {v : G → F}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v) :
    Continuous fun s => ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ :=
  continuous_integral_of_compact_support μ huc (continuous_uncurry_bilinear_inv_mul B hu hv)
    fun _ _ hsr => subset_tsupport _ (mem_support.2 fun hr => hsr (by simp [hr]))

/-- For compactly supported continuous `u : G → E` and `v : G → F` and a continuous bilinear map
`B : E →L[𝕜] F →L[𝕜] V`, the parametric convolution `s ↦ ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ` is
integrable against any measure `ν` finite on compact sets, whenever `μ` is also finite on compact
sets. -/
theorem integrable_integral_bilinear_inv_mul [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ ν : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (B : E →L[𝕜] F →L[𝕜] V) {u : G → E} {v : G → F}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun s => ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ) ν :=
  (continuous_integral_bilinear_inv_mul μ B hu huc hv).integrable_of_hasCompactSupport
    (hasCompactSupport_integral_of_inv_mul_mem μ huc hvc fun _ _ => mem_tsupport_bilinear_inv_mul B)

/-- Against measures `μ` and `ν` finite on compact sets with `ν` left-invariant (with no
σ-finiteness assumption), two compactly supported continuous functions `u : G → E` and `v : G → F`
paired via a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] V` satisfy
`∫ s, ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ ∂ν = B (∫ r, u r ∂μ) (∫ s, v s ∂ν)`. -/
theorem integral_integral_bilinear_inv_mul [RCLike 𝕜]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]
    [CompleteSpace E] [CompleteSpace F] [CompleteSpace V]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    (μ ν : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [ν.IsMulLeftInvariant] (B : E →L[𝕜] F →L[𝕜] V) {u : G → E} {v : G → F}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∫ s, ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ ∂ν) = B (∫ r, u r ∂μ) (∫ s, v s ∂ν) := by
  have hsupp : HasCompactSupport (uncurry fun s r => B (u r) (v (r⁻¹ * s))) :=
    hasCompactSupport_uncurry_of_inv_mul_mem (F := fun s r => B (u r) (v (r⁻¹ * s)))
      huc hvc fun _ _ => mem_tsupport_bilinear_inv_mul B
  calc (∫ s, ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ ∂ν)
      = ∫ r, ∫ s, B (u r) (v (r⁻¹ * s)) ∂ν ∂μ :=
        integral_integral_swap_of_hasCompactSupport (continuous_uncurry_bilinear_inv_mul B hu hv)
          hsupp
    _ = ∫ r, B (u r) (∫ s, v s ∂ν) ∂μ := by
        congr 1 with r
        have hv_int : Integrable (fun s => v (r⁻¹ * s)) ν :=
          (hv.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
            (hvc.comp_homeomorph (Homeomorph.mulLeft r⁻¹))
        rw [(B (u r)).integral_comp_comm hv_int, integral_mul_left_eq_self v r⁻¹]
    _ = B (∫ r, u r ∂μ) (∫ s, v s ∂ν) := by
        have hu_int : Integrable u μ := hu.integrable_of_hasCompactSupport huc
        exact (B.flip (∫ s, v s ∂ν)).integral_comp_comm hu_int

end Bilinear

section Seminormed

variable {G E₁ E₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂]

/-- For continuous `u : G → E₁` with compact support and continuous `v : G → E₂`, the scalar
parametric convolution `s ↦ ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ` is continuous against any measure
finite on compact sets. -/
theorem continuous_integral_norm_mul_inv_mul [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {u : G → E₁} {v : G → E₂}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v) :
    Continuous fun s => ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    continuous_integral_bilinear_inv_mul μ (ContinuousLinearMap.mul ℝ ℝ) hu.norm
      (huc.comp_left norm_zero) hv.norm

/-- For compactly supported continuous `u : G → E₁` and `v : G → E₂`, the scalar parametric
convolution `s ↦ ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ` is integrable against any measure `ν` finite on
compact sets, whenever `μ` is also finite on compact sets. -/
theorem integrable_integral_norm_mul_inv_mul [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ ν : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {u : G → E₁} {v : G → E₂} (hu : Continuous u) (huc : HasCompactSupport u)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun s => ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ) ν := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    integrable_integral_bilinear_inv_mul μ ν (ContinuousLinearMap.mul ℝ ℝ) hu.norm
      (huc.comp_left norm_zero) hv.norm (hvc.comp_left norm_zero)

/-- For continuous `u : G → E₁` with compact support and continuous `v : G → E₂`, the lower
Lebesgue parametric convolution `∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ` equals `ENNReal.ofReal` of the
Bochner integral `∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ` against any measure finite on compact sets. -/
theorem lintegral_eNorm_mul_inv_mul_eq_ofReal_integral [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {u : G → E₁} {v : G → E₂} (hu : Continuous u) (huc : HasCompactSupport u)
    (hv : Continuous v) (s : G) :
    ∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ = ENNReal.ofReal (∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ) := by
  have hint : Integrable (fun r => ‖u r‖ * ‖v (r⁻¹ * s)‖) μ :=
    (by fun_prop : Continuous fun r => ‖u r‖ * ‖v (r⁻¹ * s)‖).integrable_of_hasCompactSupport
      (huc.mono' fun _ hsr => subset_tsupport _ (mem_support.2 fun hr => hsr (by simp [hr])))
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  congr 1 with r
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- Against measures `μ` and `ν` finite on compact sets with `ν` left-invariant (with no
σ-finiteness assumption), two compactly supported continuous functions `u : G → E₁` and
`v : G → E₂` satisfy
`∫ s, ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ ∂ν = (∫ r, ‖u r‖ ∂μ) * ∫ s, ‖v s‖ ∂ν`. -/
theorem integral_integral_norm_mul_inv_mul [MeasurableSpace G] [OpensMeasurableSpace G]
    [MeasurableMul G] (μ ν : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant] {u : G → E₁} {v : G → E₂}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∫ s, ∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ ∂ν) = (∫ r, ‖u r‖ ∂μ) * ∫ s, ‖v s‖ ∂ν := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    integral_integral_bilinear_inv_mul μ ν (ContinuousLinearMap.mul ℝ ℝ) hu.norm
      (huc.comp_left norm_zero) hv.norm (hvc.comp_left norm_zero)

/-- Against measures `μ` and `ν` finite on compact sets with `ν` left-invariant (with no
σ-finiteness assumption), two compactly supported continuous functions `u : G → E₁` and
`v : G → E₂` satisfy
`∫⁻ s, ∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ ∂ν = (∫⁻ r, ‖u r‖ₑ ∂μ) * ∫⁻ s, ‖v s‖ₑ ∂ν`. -/
theorem lintegral_lintegral_eNorm_mul_inv_mul [MeasurableSpace G] [OpensMeasurableSpace G]
    [MeasurableMul G] (μ ν : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant] {u : G → E₁} {v : G → E₂}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∫⁻ s, (∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ) ∂ν) =
      (∫⁻ r, ‖u r‖ₑ ∂μ) * ∫⁻ s, ‖v s‖ₑ ∂ν := by
  have hu_norm : ENNReal.ofReal (∫ r, ‖u r‖ ∂μ) = ∫⁻ r, ‖u r‖ₑ ∂μ := by
    simpa only [Real.norm_of_nonneg (norm_nonneg _), eNorm_norm] using
      ofReal_integral_norm_eq_lintegral_eNorm
        (hu.norm.integrable_of_hasCompactSupport (huc.comp_left norm_zero)) (μ := μ)
  have hv_norm : ENNReal.ofReal (∫ s, ‖v s‖ ∂ν) = ∫⁻ s, ‖v s‖ₑ ∂ν := by
    simpa only [Real.norm_of_nonneg (norm_nonneg _), eNorm_norm] using
      ofReal_integral_norm_eq_lintegral_eNorm
        (hv.norm.integrable_of_hasCompactSupport (hvc.comp_left norm_zero)) (μ := ν)
  simp_rw [lintegral_eNorm_mul_inv_mul_eq_ofReal_integral μ hu huc hv]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_integral_norm_mul_inv_mul μ ν hu huc hv hvc)
      (.of_forall fun _ => integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    integral_integral_norm_mul_inv_mul μ ν hu huc hv hvc,
    ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _), hu_norm, hv_norm]

end Seminormed

end TauCeti
