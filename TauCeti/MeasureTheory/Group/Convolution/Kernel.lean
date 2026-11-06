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

variable [μ.Regular]

/-- The shrinking continuous kernels form a left approximate identity on Banach-valued `Lᵖ`
for every `1 ≤ p < ∞`. -/
theorem tendsto_approximateIdentityLp_convolutionL {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp E p μ) :
    Tendsto (fun U => Lp.convolutionL μ p hp (μ.approximateIdentityLp U) f)
      atBot (𝓝 f) :=
  Lp.tendsto_convolutionL_left (μ.approximateIdentityLp_nonneg)
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
