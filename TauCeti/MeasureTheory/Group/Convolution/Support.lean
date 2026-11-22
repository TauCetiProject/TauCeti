/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Supports of convolution-type parametric integrals over a group

Convolutions over a group `G` are parametric integrals `s ↦ ∫ r, F s r ∂μ` whose integrand
vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, where `K` and `L` are the supports of the two factors.
This file records the resulting support bounds, for any normed-space valued integrand: the
parametric integral is supported in `K * L`, and for compact `K` and `L` both the integrand on
`G × G` and the parametric integral are compactly supported. For measures `μ` and `ν` finite on
compacts, with `ν` left-invariant, Fubini's theorem for compactly supported continuous functions
then evaluates the iterated `ℝ≥0∞`-norm convolution integral of two compactly supported
continuous functions as the product of their `L¹` seminorms without σ-finiteness.

## Main statements

* `TauCeti.mem_support_and_inv_mul_mem_support`, `TauCeti.mem_tsupport_and_inv_mul_mem_tsupport`:
  if `x` vanishes whenever `f r = 0` or `g (r⁻¹ * s) = 0`, then `x ≠ 0` puts `r` and `r⁻¹ * s` in
  the (topological) supports of `f` and `g`.
* `TauCeti.support_integral_subset_mul`: the parametric integral is supported in `K * L`.
* `TauCeti.hasCompactSupport_uncurry_of_inv_mul_mem`: the integrand is compactly supported on
  `G × G`.
* `TauCeti.hasCompactSupport_integral_of_inv_mul_mem`: the parametric integral is compactly
  supported.
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
open scoped CompactlySupported ENNReal Pointwise

namespace TauCeti

/-- If `x` vanishes whenever `f r = 0` or `g (r⁻¹ * s) = 0`, then `x ≠ 0` places `r` in
`support f` and `r⁻¹ * s` in `support g`. -/
theorem mem_support_and_inv_mul_mem_support {G α β E : Type*} [Inv G] [Mul G] [Zero α] [Zero β]
    [Zero E] {f : G → α} {g : G → β} {x : E} {s r : G}
    (hx : x ≠ 0) (hf : f r = 0 → x = 0) (hg : g (r⁻¹ * s) = 0 → x = 0) :
    r ∈ support f ∧ r⁻¹ * s ∈ support g :=
  ⟨mem_support.2 (mt hf hx), mem_support.2 (mt hg hx)⟩

/-- If `x` vanishes whenever `f r = 0` or `g (r⁻¹ * s) = 0`, then `x ≠ 0` places `r` in
`tsupport f` and `r⁻¹ * s` in `tsupport g`. -/
theorem mem_tsupport_and_inv_mul_mem_tsupport {G α β E : Type*} [Inv G] [Mul G]
    [TopologicalSpace G] [Zero α] [Zero β] [Zero E] {f : G → α} {g : G → β} {x : E} {s r : G}
    (hx : x ≠ 0) (hf : f r = 0 → x = 0) (hg : g (r⁻¹ * s) = 0 → x = 0) :
    r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
  (mem_support_and_inv_mul_mem_support hx hf hg).imp (subset_tsupport f ·) (subset_tsupport g ·)

section Normed

variable {G E : Type*} [Group G] [NormedAddCommGroup E] {F : G → G → E} {K L : Set G}

/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L` has its parametric
integral `s ↦ ∫ r, F s r` supported in `K * L`. -/
theorem support_integral_subset_mul [NormedSpace ℝ E] [MeasurableSpace G] (μ : Measure G)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    support (fun s => ∫ r, F s r ∂μ) ⊆ K * L := by
  intro s hs
  by_contra h
  refine hs (integral_eq_zero_of_ae (.of_forall fun r => ?_))
  by_contra hr
  obtain ⟨hrK, hrL⟩ := hF s r hr
  exact h ⟨r, hrK, r⁻¹ * s, hrL, mul_inv_cancel_left r s⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [NormedAddCommGroup E] in
/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, for compact `K`
and `L`, is compactly supported on `G × G`. -/
theorem hasCompactSupport_uncurry_of_inv_mul_mem [Zero E] (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) : HasCompactSupport (uncurry F) := by
  refine ((hK.mul hL).prod hK).closure_of_subset fun p hp => ?_
  obtain ⟨hrK, hrL⟩ := hF p.1 p.2 hp
  exact ⟨⟨p.2, hrK, p.2⁻¹ * p.1, hrL, mul_inv_cancel_left p.2 p.1⟩, hrK⟩

/-- The parametric integral `s ↦ ∫ r, F s r` of an integrand which vanishes unless `r ∈ K` and
`r⁻¹ * s ∈ L`, for compact `K` and `L`, is compactly supported. -/
theorem hasCompactSupport_integral_of_inv_mul_mem [NormedSpace ℝ E] [MeasurableSpace G]
    (μ : Measure G) (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    HasCompactSupport (fun s => ∫ r, F s r ∂μ) :=
  (hK.mul hL).closure_of_subset (support_integral_subset_mul μ hF)

end Normed

section Bilinear

variable {G E F V 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For continuous `u : G → E` with compact support, continuous `v : G → F`, and a continuous
bilinear map `B : E →L[𝕜] F →L[𝕜] V`, the parametric convolution
`s ↦ ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ` is continuous against any measure finite on compact sets. -/
theorem continuous_integral_bilinear_inv_mul [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (B : E →L[𝕜] F →L[𝕜] V) {u : G → E} {v : G → F}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v) :
    Continuous fun s => ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ := by
  refine continuous_integral_of_compact_support μ huc ?_ fun _ _ hsr =>
    subset_tsupport _ (mem_support.2 fun hr => hsr (by simp [hr]))
  rw [uncurry_def]
  exact B.continuous₂.comp
    ((hu.comp continuous_snd).prodMk (hv.comp (continuous_snd.inv.mul continuous_fst)))

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
    (hasCompactSupport_integral_of_inv_mul_mem μ huc hvc fun _ _ hsr =>
      mem_tsupport_and_inv_mul_mem_tsupport hsr
        (by intro hu0; simp [hu0]) (by intro hv0; simp [hv0]))

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
  have hcont : Continuous (uncurry fun s r => B (u r) (v (r⁻¹ * s))) := by
    rw [uncurry_def]
    exact B.continuous₂.comp
      ((hu.comp continuous_snd).prodMk (hv.comp (continuous_snd.inv.mul continuous_fst)))
  have hsupp : HasCompactSupport (uncurry fun s r => B (u r) (v (r⁻¹ * s))) :=
    hasCompactSupport_uncurry_of_inv_mul_mem (F := fun s r => B (u r) (v (r⁻¹ * s)))
      huc hvc fun _ _ hsr =>
        mem_tsupport_and_inv_mul_mem_tsupport hsr
          (by intro hu0; simp [hu0]) (by intro hv0; simp [hv0])
  calc (∫ s, ∫ r, B (u r) (v (r⁻¹ * s)) ∂μ ∂ν)
      = ∫ r, ∫ s, B (u r) (v (r⁻¹ * s)) ∂ν ∂μ :=
        integral_integral_swap_of_hasCompactSupport hcont hsupp
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

omit [Group G] [IsTopologicalGroup G] in
private theorem ofReal_integral_norm {E : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {w : G → E} (hw : Continuous w) (hwc : HasCompactSupport w) :
    ENNReal.ofReal (∫ x, ‖w x‖ ∂μ) = ∫⁻ x, ‖w x‖ₑ ∂μ := by
  have hint : Integrable (fun x => ‖w x‖) μ :=
    hw.norm.integrable_of_hasCompactSupport (hwc.comp_left norm_zero)
  rw [ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ => norm_nonneg _)]
  congr 1 with x
  exact ofReal_norm _

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
  simp_rw [lintegral_eNorm_mul_inv_mul_eq_ofReal_integral μ hu huc hv]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_integral_norm_mul_inv_mul μ ν hu huc hv hvc)
      (.of_forall fun _ => integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    integral_integral_norm_mul_inv_mul μ ν hu huc hv hvc,
    ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _),
    ofReal_integral_norm μ hu huc, ofReal_integral_norm ν hv hvc]

end Seminormed

end TauCeti
