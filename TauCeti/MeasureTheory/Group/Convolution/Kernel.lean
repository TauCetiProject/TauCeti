/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Convolution.ApproximateIdentity
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import TauCeti.MeasureTheory.Integral.PeakFunction

/-!
# A shrinking net of continuous convolution kernels

For a locally compact group with a regular left Haar measure `μ`,
`μ.approximateIdentity U` is a nonnegative compactly supported continuous function of integral
one with support closure inside the open identity neighborhood `U`. The index type is Mathlib's
`TopologicalSpace.OpenNhdsOf 1`, ordered by inclusion, and the net runs along `atBot`.
This filter is nontrivial: intersections refine any two open identity neighborhoods.
No countability or σ-finiteness assumption is needed.

The associated `L¹` classes `μ.approximateIdentityLp U` have norm one and form a two-sided
approximate identity on real `L¹`, and a left approximate identity on Banach-valued `Lᵖ`
for `1 ≤ p < ∞`.
The same net works simultaneously for every function and every such exponent. The construction
uses continuous peak functions, while convergence uses the strong continuity of translations
through `MeasureTheory.Lp.tendsto_convolutionL_left` and
`MeasureTheory.Lp.tendsto_convolutionL_right`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported

namespace MeasureTheory.Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- A nonnegative continuous kernel of integral one supported in an open identity neighborhood.
The choices for different neighborhoods need not be compatible; their shrinking supports suffice
for convolution convergence. -/
def approximateIdentity (U : OpenNhdsOf (1 : G)) : C_c(G, ℝ) :=
  (TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ
    (U.isOpen.mem_nhds U.mem)).choose

/-- The continuous kernels are nonnegative. -/
theorem approximateIdentity_nonneg (U : OpenNhdsOf (1 : G)) :
    0 ≤ μ.approximateIdentity U :=
  (TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ
    (U.isOpen.mem_nhds U.mem)).choose_spec.1

/-- The support closure of the kernel lies inside its indexing neighborhood. -/
theorem tsupport_approximateIdentity_subset (U : OpenNhdsOf (1 : G)) :
    tsupport (μ.approximateIdentity U) ⊆ (U : Set G) :=
  (TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ
    (U.isOpen.mem_nhds U.mem)).choose_spec.2.1

/-- Each continuous kernel has integral one. -/
@[simp]
theorem integral_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ∫ x, μ.approximateIdentity U x ∂μ = 1 :=
  (TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ
    (U.isOpen.mem_nhds U.mem)).choose_spec.2.2

/-- The support closures shrink to the identity, in the `Filter.smallSets` sense. -/
theorem tendsto_tsupport_approximateIdentity :
    Tendsto (fun U => tsupport (μ.approximateIdentity U)) atBot (𝓝 (1 : G)).smallSets := by
  apply tendsto_smallSets_iff.2
  intro S hS
  obtain ⟨V, -, hV⟩ := OpenNhdsOf.basis_nhds.mem_iff.1 hS
  filter_upwards [eventually_le_atBot V] with U hU
  exact (μ.tsupport_approximateIdentity_subset U).trans fun _ hx => hV (hU hx)

/-- The `L¹` class of the continuous kernel. -/
def approximateIdentityLp (U : OpenNhdsOf (1 : G)) : Lp ℝ 1 μ :=
  (μ.approximateIdentity U).continuous.integrable_of_hasCompactSupport
    (μ.approximateIdentity U).hasCompactSupport |>.toL1 _

/-- The `L¹` representative agrees almost everywhere with the continuous kernel. -/
theorem coeFn_approximateIdentityLp (U : OpenNhdsOf (1 : G)) :
    μ.approximateIdentityLp U =ᵐ[μ] μ.approximateIdentity U :=
  Integrable.coeFn_toL1 _

/-- The `L¹` kernels are nonnegative. -/
theorem approximateIdentityLp_nonneg (U : OpenNhdsOf (1 : G)) :
    0 ≤ μ.approximateIdentityLp U := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [μ.coeFn_approximateIdentityLp U] with x hx
  rw [hx]
  exact CompactlySupportedContinuousMap.le_def.1 (μ.approximateIdentity_nonneg U) x

/-- Each `L¹` kernel has integral one. -/
@[simp]
theorem integral_approximateIdentityLp (U : OpenNhdsOf (1 : G)) :
    ∫ x, μ.approximateIdentityLp U x ∂μ = 1 := by
  rw [integral_congr_ae (μ.coeFn_approximateIdentityLp U), μ.integral_approximateIdentity]

/-- Each `L¹` kernel has norm one. -/
@[simp]
theorem norm_approximateIdentityLp (U : OpenNhdsOf (1 : G)) :
    ‖μ.approximateIdentityLp U‖ = 1 := by
  rw [L1.norm_eq_integral_of_nonneg (μ.approximateIdentityLp_nonneg U),
    μ.integral_approximateIdentityLp]

/-- Each `L¹` kernel vanishes almost everywhere outside its indexing neighborhood. -/
theorem approximateIdentityLp_ae_eq_zero (U : OpenNhdsOf (1 : G)) :
    ∀ᵐ x ∂μ, x ∉ U → μ.approximateIdentityLp U x = 0 := by
  filter_upwards [μ.coeFn_approximateIdentityLp U] with x hx hxU
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport fun h =>
    hxU (μ.tsupport_approximateIdentity_subset U h)

/-- Along reverse inclusion of open identity neighborhoods, the kernels eventually vanish
almost everywhere outside any prescribed identity neighborhood. -/
theorem eventually_approximateIdentityLp_ae_eq_zero {S : Set G} (hS : S ∈ 𝓝 (1 : G)) :
    ∀ᶠ U : OpenNhdsOf (1 : G) in atBot, ∀ᵐ x ∂μ,
      x ∉ S → μ.approximateIdentityLp U x = 0 := by
  obtain ⟨V, -, hV⟩ := OpenNhdsOf.basis_nhds.mem_iff.1 hS
  filter_upwards [eventually_le_atBot V] with U hU
  filter_upwards [μ.approximateIdentityLp_ae_eq_zero U] with x hx hxS
  exact hx fun hxU => hxS (hV (hU hxU))

/-- Each continuous kernel `μ.approximateIdentity U` belongs to `Lᵖ(G, μ; ℝ)` for every
`p : ℝ≥0∞` (in particular to `L¹ ∩ L²`). -/
theorem memLp_approximateIdentity (U : OpenNhdsOf (1 : G)) (p : ℝ≥0∞) :
    MemLp (μ.approximateIdentity U) p μ :=
  (μ.approximateIdentity U).continuous.memLp_of_hasCompactSupport
    (μ.approximateIdentity U).hasCompactSupport

/-- Coerced to an `RCLike` scalar field `𝕜`, `μ.approximateIdentity U` belongs to `Lᵖ(G, μ; 𝕜)`
for every `p : ℝ≥0∞` (in particular to `L¹ ∩ L²`). -/
theorem memLp_ofReal_approximateIdentity {𝕜 : Type*} [RCLike 𝕜] (U : OpenNhdsOf (1 : G))
    (p : ℝ≥0∞) : MemLp (fun x => (μ.approximateIdentity U x : 𝕜)) p μ :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).comp_memLp' (μ.memLp_approximateIdentity U p)

/-- Coerced to an `RCLike` scalar field `𝕜`, each `L¹` kernel has integral one. -/
@[simp]
theorem integral_ofRealCLM_compLp_approximateIdentityLp {𝕜 : Type*} [RCLike 𝕜]
    (U : OpenNhdsOf (1 : G)) :
    ∫ x, ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp (μ.approximateIdentityLp U)) x ∂μ = 1 := by
  have hcomm := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integral_comp_comm
    (L1.integrable_coeFn (μ.approximateIdentityLp U))
  refine (integral_congr_ae ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLp _)).trans ?_
  rw [hcomm, μ.integral_approximateIdentityLp, RCLike.ofRealCLM_apply, RCLike.ofReal_one]

/-- Integrating the inverted kernel `z ↦ μ.approximateIdentity U z⁻¹` equals integrating
`μ.approximateIdentity U` against the modular character. -/
theorem integral_approximateIdentity_inv (U : OpenNhdsOf (1 : G)) :
    ∫ z, μ.approximateIdentity U z⁻¹ ∂μ =
      ∫ z, (modularCharacter z : ℝ) * μ.approximateIdentity U z ∂μ := by
  simpa only [smul_eq_mul] using TauCeti.integral_inv_eq_integral_modularCharacter_smul (μ := μ)
    (map_continuous (μ.approximateIdentity U)) (μ.approximateIdentity U).hasCompactSupport

/-- Integrating the modular character against the shrinking kernels `μ.approximateIdentity U`
tends to `1` along `atBot`. -/
theorem tendsto_integral_modularCharacter_mul_approximateIdentity :
    Tendsto (fun U => ∫ z, (modularCharacter z : ℝ) * μ.approximateIdentity U z ∂μ)
      atBot (𝓝 1) := by
  have hmeas (U : OpenNhdsOf (1 : G)) :
      AEStronglyMeasurable
        (fun z => μ.approximateIdentityLp U z • (modularCharacter z : ℝ)) μ := by
    have hcont : Continuous fun z =>
        μ.approximateIdentity U z • (modularCharacter z : ℝ) :=
      (map_continuous (μ.approximateIdentity U)).smul
        (NNReal.continuous_coe.comp TauCeti.continuous_modularCharacter)
    have hsupp : HasCompactSupport fun z =>
        μ.approximateIdentity U z • (modularCharacter z : ℝ) :=
      (μ.approximateIdentity U).hasCompactSupport.smul_right
    exact (hcont.integrable_of_hasCompactSupport hsupp).aestronglyMeasurable.congr <| by
      filter_upwards [μ.coeFn_approximateIdentityLp U] with z hz
      rw [hz]
  have hcont1 : Tendsto (fun z : G => (modularCharacter z : ℝ)) (𝓝 1) (𝓝 1) := by
    simpa [Function.comp_def] using
      (NNReal.continuous_coe.comp (TauCeti.continuous_modularCharacter (G := G))).tendsto 1
  have ht := TauCeti.tendsto_integral_smul_of_tendsto (𝕜 := ℝ) (C := 1)
    (.of_forall μ.integral_approximateIdentityLp)
    (.of_forall fun U => (μ.norm_approximateIdentityLp U).le)
    (fun _ hS => μ.eventually_approximateIdentityLp_ae_eq_zero hS)
    (.of_forall hmeas) hcont1
  refine ht.congr fun U => integral_congr_ae ?_
  filter_upwards [μ.coeFn_approximateIdentityLp U] with z hz
  rw [hz, smul_eq_mul, mul_comm]

/-- On non-unimodular groups, `∫ z, μ.approximateIdentity U z⁻¹ ∂μ` need not equal `1` at finite
stage, but converges to `1` along `atBot`. -/
theorem tendsto_integral_approximateIdentity_inv :
    Tendsto (fun U => ∫ z, μ.approximateIdentity U z⁻¹ ∂μ) atBot (𝓝 1) := by
  simp_rw [μ.integral_approximateIdentity_inv]
  exact μ.tendsto_integral_modularCharacter_mul_approximateIdentity

/-- The shrinking continuous kernels form a left approximate identity on Banach-valued `Lᵖ`
for every `1 ≤ p < ∞`. -/
theorem tendsto_approximateIdentityLp_convolutionL [μ.InnerRegularCompactLTTop]
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp E p μ) :
    Tendsto (fun U => Lp.convolutionL μ p hp (μ.approximateIdentityLp U) f)
      atBot (𝓝 f) :=
  Lp.tendsto_convolutionL_left (μ.approximateIdentityLp_nonneg)
    (μ.integral_approximateIdentityLp)
    (fun _ hS => μ.eventually_approximateIdentityLp_ae_eq_zero hS) f

variable [μ.Regular]

/-- The same shrinking kernels form a right approximate identity on `L¹(G, μ; 𝕜)` over any
`RCLike` scalar field `𝕜`. -/
theorem tendsto_convolutionL_ofRealCLM_compLp_approximateIdentityLp {𝕜 : Type*} [RCLike 𝕜]
    (f : Lp 𝕜 1 μ) :
    Tendsto (fun U =>
      Lp.convolutionL μ 1 ENNReal.one_ne_top f
        ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp (μ.approximateIdentityLp U)))
      atBot (𝓝 f) :=
  Lp.tendsto_convolutionL_ofRealCLM_compLp_right (μ.approximateIdentityLp_nonneg)
    (μ.integral_approximateIdentityLp)
    (fun _ hS => μ.eventually_approximateIdentityLp_ae_eq_zero hS) f

/-- The same shrinking kernels form a right approximate identity on real `L¹`. -/
theorem tendsto_convolutionL_approximateIdentityLp (f : Lp ℝ 1 μ) :
    Tendsto (fun U => Lp.convolutionL μ 1 ENNReal.one_ne_top f (μ.approximateIdentityLp U))
      atBot (𝓝 f) :=
  Lp.tendsto_convolutionL_right (μ.approximateIdentityLp_nonneg)
    (μ.integral_approximateIdentityLp)
    (fun _ hS => μ.eventually_approximateIdentityLp_ae_eq_zero hS) f

end MeasureTheory.Measure
