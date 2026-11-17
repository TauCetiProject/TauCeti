/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Star
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

Because each `μ.approximateIdentity U` is continuous and compactly supported, it belongs to `Lᵖ`
for every exponent `p : ℝ≥0∞` (in particular `L¹ ∩ L²`), and its modular-weighted integral
`∫ z, c(z) * u_U(z) ∂μ = ∫ z, u_U(z⁻¹) ∂μ` converges to `1` along `atBot` by continuity of the
modular character at `1`.

The associated `L¹` classes `μ.approximateIdentityL1 𝕜 U` (over any `RCLike` scalar field `𝕜`,
in particular `ℝ` and `ℂ`) have norm one and form a two-sided
approximate identity on `L¹(G, μ; 𝕜)` and a left approximate identity on Banach-valued `Lᵖ`
for `1 ≤ p < ∞`.
The same net works simultaneously for every function and every such exponent. The construction
uses continuous peak functions, while convergence uses the strong continuity of translations
through `MeasureTheory.Lp.tendsto_convolutionL_left_of_norm_le` and
`MeasureTheory.Lp.tendsto_convolutionL_right_of_norm_le`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §VII.9, pp. 225–226.
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

/-- Each continuous kernel belongs to `Lᵖ(G, μ)` for every exponent `p : ℝ≥0∞`
(in particular `L¹` and `L²`). -/
theorem memLp_approximateIdentity (U : OpenNhdsOf (1 : G)) (p : ℝ≥0∞) :
    MemLp (μ.approximateIdentity U) p μ :=
  (μ.approximateIdentity U).continuous.memLp_of_hasCompactSupport
    (μ.approximateIdentity U).hasCompactSupport

/-- Each continuous kernel is `μ`-integrable. -/
theorem integrable_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    Integrable (μ.approximateIdentity U) μ :=
  (μ.approximateIdentity U).continuous.integrable_of_hasCompactSupport
    (μ.approximateIdentity U).hasCompactSupport

section RCLike

variable (𝕜 : Type*) [RCLike 𝕜]

/-- Viewed in any `RCLike` scalar field `𝕜`, each continuous kernel belongs to `Lᵖ(G, μ; 𝕜)` for
every exponent `p : ℝ≥0∞` (in particular `L¹` and `L²`). -/
theorem memLp_ofReal_approximateIdentity (U : OpenNhdsOf (1 : G)) (p : ℝ≥0∞) :
    MemLp (fun x => (μ.approximateIdentity U x : 𝕜)) p μ :=
  (RCLike.continuous_ofReal.comp
    (map_continuous (μ.approximateIdentity U))).memLp_of_hasCompactSupport
    ((μ.approximateIdentity U).hasCompactSupport.comp_left RCLike.ofReal_zero)

/-- Viewed in any `RCLike` scalar field `𝕜`, each continuous kernel is `μ`-integrable. -/
theorem integrable_ofReal_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    Integrable (fun x => (μ.approximateIdentity U x : 𝕜)) μ :=
  (RCLike.continuous_ofReal.comp
    (map_continuous (μ.approximateIdentity U))).integrable_of_hasCompactSupport
    ((μ.approximateIdentity U).hasCompactSupport.comp_left RCLike.ofReal_zero)

/-- The `L¹(G, μ; 𝕜)` class of the continuous kernel `μ.approximateIdentity U` over an `RCLike`
scalar field `𝕜`. -/
def approximateIdentityL1 (U : OpenNhdsOf (1 : G)) : Lp 𝕜 1 μ :=
  (μ.integrable_ofReal_approximateIdentity 𝕜 U).toL1 _

variable {𝕜}

/-- `μ.approximateIdentityL1 𝕜 U` is represented almost everywhere by `x ↦ (u_U x : 𝕜)`. -/
theorem coeFn_approximateIdentityL1 (U : OpenNhdsOf (1 : G)) :
    μ.approximateIdentityL1 𝕜 U =ᵐ[μ] fun x => (μ.approximateIdentity U x : 𝕜) :=
  (μ.integrable_ofReal_approximateIdentity 𝕜 U).coeFn_toL1

/-- Over `ℝ`, the `L¹` kernels are nonnegative. -/
theorem approximateIdentityL1_nonneg (U : OpenNhdsOf (1 : G)) :
    0 ≤ μ.approximateIdentityL1 ℝ U := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [μ.coeFn_approximateIdentityL1 (𝕜 := ℝ) U] with x hx
  rw [hx]
  exact CompactlySupportedContinuousMap.le_def.1 (μ.approximateIdentity_nonneg U) x

/-- Each `L¹(G, μ; 𝕜)` kernel has integral one. -/
@[simp]
theorem integral_approximateIdentityL1 (U : OpenNhdsOf (1 : G)) :
    ∫ x, μ.approximateIdentityL1 𝕜 U x ∂μ = 1 := by
  rw [integral_congr_ae (μ.coeFn_approximateIdentityL1 U), integral_ofReal,
    μ.integral_approximateIdentity, RCLike.ofReal_one]

/-- Each `L¹(G, μ; 𝕜)` kernel has `L¹` norm one. -/
@[simp]
theorem norm_approximateIdentityL1 (U : OpenNhdsOf (1 : G)) :
    ‖μ.approximateIdentityL1 𝕜 U‖ = 1 := by
  have hu0 : ∀ x, 0 ≤ μ.approximateIdentity U x :=
    CompactlySupportedContinuousMap.le_def.1 (μ.approximateIdentity_nonneg U)
  rw [L1.norm_eq_integral_norm, ← μ.integral_approximateIdentity U]
  refine integral_congr_ae ((μ.coeFn_approximateIdentityL1 (𝕜 := 𝕜) U).mono fun x hx => ?_)
  simp only [hx, RCLike.norm_ofReal, abs_of_nonneg (hu0 x)]

/-- Each `L¹(G, μ; 𝕜)` kernel is fixed by pointwise `star` on `Lp`. -/
@[simp]
theorem star_approximateIdentityL1 (U : OpenNhdsOf (1 : G)) :
    star (μ.approximateIdentityL1 𝕜 U) = μ.approximateIdentityL1 𝕜 U :=
  Lp.star_eq_self_of_ae_eq_ofReal (μ.coeFn_approximateIdentityL1 U)

/-- Each `L¹(G, μ; 𝕜)` kernel vanishes almost everywhere outside its indexing neighborhood. -/
theorem approximateIdentityL1_ae_eq_zero (U : OpenNhdsOf (1 : G)) :
    ∀ᵐ x ∂μ, x ∉ U → μ.approximateIdentityL1 𝕜 U x = 0 := by
  filter_upwards [μ.coeFn_approximateIdentityL1 (𝕜 := 𝕜) U] with x hx hxU
  rw [hx, image_eq_zero_of_notMem_tsupport
    (fun h => hxU (μ.tsupport_approximateIdentity_subset U h)), RCLike.ofReal_zero]

/-- Along `atBot` on open identity neighborhoods, `μ.approximateIdentityL1 𝕜 U` eventually
vanishes almost everywhere outside any prescribed identity neighborhood. -/
theorem eventually_approximateIdentityL1_ae_eq_zero {S : Set G} (hS : S ∈ 𝓝 (1 : G)) :
    ∀ᶠ U : OpenNhdsOf (1 : G) in atBot, ∀ᵐ x ∂μ,
      x ∉ S → μ.approximateIdentityL1 𝕜 U x = 0 := by
  obtain ⟨V, -, hV⟩ := OpenNhdsOf.basis_nhds.mem_iff.1 hS
  filter_upwards [eventually_le_atBot V] with U hU
  filter_upwards [μ.approximateIdentityL1_ae_eq_zero (𝕜 := 𝕜) U] with x hx hxS
  exact hx fun hxU => hxS (hV (hU hxU))

/-- Over any `RCLike` scalar field `𝕜`, the shrinking continuous kernels form a left approximate
identity on Banach-valued `Lᵖ` for every `1 ≤ p < ∞`. -/
theorem tendsto_approximateIdentityL1_convolutionL [μ.InnerRegularCompactLTTop]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (f : Lp E p μ) :
    Tendsto (fun U => Lp.convolutionL μ p hp (μ.approximateIdentityL1 𝕜 U) f)
      atBot (𝓝 f) :=
  Lp.tendsto_convolutionL_left_of_norm_le
    (.of_forall μ.integral_approximateIdentityL1)
    (.of_forall fun U => (μ.norm_approximateIdentityL1 U).le)
    (fun _ hS => μ.eventually_approximateIdentityL1_ae_eq_zero hS) f

/-- Over any `RCLike` scalar field `𝕜`, the shrinking continuous kernels form a right approximate
identity on `L¹(G, μ; 𝕜)`. -/
theorem tendsto_convolutionL_approximateIdentityL1 [μ.Regular] (f : Lp 𝕜 1 μ) :
    Tendsto (fun U => Lp.convolutionL μ 1 ENNReal.one_ne_top f (μ.approximateIdentityL1 𝕜 U))
      atBot (𝓝 f) :=
  Lp.tendsto_convolutionL_right_of_norm_le
    (.of_forall μ.integral_approximateIdentityL1)
    (.of_forall fun U => (μ.norm_approximateIdentityL1 U).le)
    (fun _ hS => μ.eventually_approximateIdentityL1_ae_eq_zero hS) f

end RCLike

/-- By the Haar inversion formula on compactly supported integrands,
`∫ z, c(z) * u_U(z) ∂μ = ∫ z, u_U(z⁻¹) ∂μ` without any regularity hypothesis on `μ`. -/
theorem integral_modularCharacter_mul_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ∫ z, (modularCharacter z : ℝ) * μ.approximateIdentity U z ∂μ =
      ∫ z, μ.approximateIdentity U z⁻¹ ∂μ := by
  simpa only [smul_eq_mul] using
    (TauCeti.integral_inv_eq_integral_modularCharacter_smul
      (map_continuous (μ.approximateIdentity U))
      (μ.approximateIdentity U).hasCompactSupport).symm

/-- Along `atBot` on open identity neighborhoods, the modular-weighted integrals
`∫ z, c(z) * u_U(z) ∂μ` converge to `1` by continuity of the modular character at `1` and shrinking
support. -/
theorem tendsto_integral_modularCharacter_mul_approximateIdentity :
    Tendsto (fun U => ∫ z, (modularCharacter z : ℝ) * μ.approximateIdentity U z ∂μ)
      atBot (𝓝 1) := by
  have hmc : Continuous fun z : G => (modularCharacter z : ℝ) :=
    NNReal.continuous_coe.comp TauCeti.continuous_modularCharacter
  have hφ : Tendsto (fun z : G => (modularCharacter z : ℝ)) (𝓝 1) (𝓝 1) := by
    simpa only [map_one, NNReal.coe_one] using hmc.tendsto 1
  have hmeas : ∀ U : OpenNhdsOf (1 : G),
      AEStronglyMeasurable (fun z => μ.approximateIdentityL1 ℝ U z • (modularCharacter z : ℝ))
        μ := fun U => by
    have hint : Integrable (fun z => μ.approximateIdentity U z * (modularCharacter z : ℝ)) μ :=
      ((map_continuous (μ.approximateIdentity U)).mul hmc).integrable_of_hasCompactSupport
        (μ.approximateIdentity U).hasCompactSupport.mul_right
    refine hint.aestronglyMeasurable.congr ?_
    filter_upwards [μ.coeFn_approximateIdentityL1 (𝕜 := ℝ) U] with z hz
    simp only [smul_eq_mul, hz, RCLike.ofReal_real_eq_id, id_eq]
  have hlim := TauCeti.tendsto_integral_smul_of_tendsto (C := 1)
    (f := μ.approximateIdentityL1 ℝ) (φ := fun z => (modularCharacter z : ℝ))
    (.of_forall μ.integral_approximateIdentityL1)
    (.of_forall fun U => (μ.norm_approximateIdentityL1 U).le)
    (fun _ hS => μ.eventually_approximateIdentityL1_ae_eq_zero hS)
    (.of_forall hmeas) hφ
  refine hlim.congr fun U => integral_congr_ae ?_
  filter_upwards [μ.coeFn_approximateIdentityL1 (𝕜 := ℝ) U] with z hz
  simp only [smul_eq_mul, hz, RCLike.ofReal_real_eq_id, id_eq, mul_comm]

/-- Along `atBot` on open identity neighborhoods, the inverted-kernel integrals
`∫ z, u_U(z⁻¹) ∂μ` converge to `1`, even when `G` is not unimodular. -/
theorem tendsto_integral_inv_approximateIdentity :
    Tendsto (fun U => ∫ z, μ.approximateIdentity U z⁻¹ ∂μ) atBot (𝓝 1) := by
  simpa only [← μ.integral_modularCharacter_mul_approximateIdentity] using
    μ.tendsto_integral_modularCharacter_mul_approximateIdentity

end MeasureTheory.Measure
