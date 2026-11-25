/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Basic
public import TauCeti.Geometry.Lie.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Sets.Opens
import TauCeti.Geometry.Manifold.Measure.PeakFunction
import TauCeti.MeasureTheory.Integral.PeakFunction

/-!
# Smooth approximate identities on a Lie group

Let `G` be a finite-dimensional real Lie group and `μ` a measure on `G` that is positive on
nonempty open sets and finite on compact sets, for instance a Haar measure. For every open
neighbourhood `U` of the identity, `smoothApproximateIdentity I μ U` is a nonnegative test function
supported in `U` with `∫ u_U dμ = 1`. It is a smooth bump function in a chart at the identity,
normalized by its integral (`TauCeti.exists_contMDiff_nonneg_tsupport_subset_integral_eq_one`).

As `U` shrinks to the identity, `∫ u_U(y) φ(y) dμ(y) → φ 1` for every continuous `φ`. The index
type is Mathlib's `TopologicalSpace.OpenNhdsOf 1`, ordered by inclusion, and the net runs along
`atBot`, as for the continuous kernels `MeasureTheory.Measure.approximateIdentity`.

## Main results

* `TauCeti.LieTestFunction.smoothApproximateIdentity I μ U`: the test function `u_U`.
* `TauCeti.LieTestFunction.tendsto_integral_smoothApproximateIdentity_smul`: integration against
  `u_U` tends to evaluation at the identity on continuous functions.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.5.
* J. R. Getz, *An introduction to automorphic representations*, §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Manifold ComplexOrder

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace LieTestFunction

variable [FiniteDimensional ℝ E] {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

variable (I)

/-- The real smooth function underlying `smoothApproximateIdentity I μ U`. -/
private theorem exists_smoothApproximateIdentity (U : OpenNhdsOf (1 : G)) :
    ∃ f : G → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ HasCompactSupport f ∧ 0 ≤ f ∧ tsupport f ⊆ U ∧
      ∫ x, f x ∂μ = 1 :=
  have := I.t2Space_of_lieGroup ∞ (G := G)
  exists_contMDiff_nonneg_tsupport_subset_integral_eq_one I μ (U.isOpen.mem_nhds U.mem)

/-- A smooth approximate identity: a nonnegative test function of integral one supported in the
open identity neighbourhood `U`. The choices for different neighbourhoods need not be
compatible. -/
def smoothApproximateIdentity (U : OpenNhdsOf (1 : G)) : LieTestFunction I G where
  toFun x := (exists_smoothApproximateIdentity I μ U).choose x
  contMDiff' := Complex.ofRealCLM.contDiff.contMDiff.comp
    (exists_smoothApproximateIdentity I μ U).choose_spec.1
  hasCompactSupport' := (exists_smoothApproximateIdentity I μ U).choose_spec.2.1.comp_left
    Complex.ofReal_zero

/-- The smooth approximate identity is the complexification of the chosen real peak function. -/
private theorem coe_smoothApproximateIdentity (U : OpenNhdsOf (1 : G)) :
    ⇑(smoothApproximateIdentity I μ U) =
      fun x ↦ ((exists_smoothApproximateIdentity I μ U).choose x : ℂ) :=
  coe_mk

/-- The smooth approximate identity takes real values. -/
theorem smoothApproximateIdentity_eq_ofReal_re (U : OpenNhdsOf (1 : G)) (x : G) :
    smoothApproximateIdentity I μ U x = (smoothApproximateIdentity I μ U x).re :=
  congrArg Complex.ofReal (Complex.ofReal_re _).symm

/-- The smooth approximate identity is nonnegative. -/
theorem smoothApproximateIdentity_nonneg (U : OpenNhdsOf (1 : G)) (x : G) :
    0 ≤ smoothApproximateIdentity I μ U x :=
  Complex.zero_le_real.2 <| (exists_smoothApproximateIdentity I μ U).choose_spec.2.2.1 x

/-- The support closure of the smooth approximate identity lies in its indexing neighbourhood. -/
theorem tsupport_smoothApproximateIdentity_subset (U : OpenNhdsOf (1 : G)) :
    tsupport (smoothApproximateIdentity I μ U) ⊆ U := by
  rw [coe_smoothApproximateIdentity]
  exact (tsupport_comp_subset Complex.ofReal_zero _).trans
    (exists_smoothApproximateIdentity I μ U).choose_spec.2.2.2.1

/-- The smooth approximate identity has integral one. -/
@[simp]
theorem integral_smoothApproximateIdentity (U : OpenNhdsOf (1 : G)) :
    ∫ x, smoothApproximateIdentity I μ U x ∂μ = 1 := by
  rw [coe_smoothApproximateIdentity, integral_complex_ofReal,
    (exists_smoothApproximateIdentity I μ U).choose_spec.2.2.2.2, Complex.ofReal_one]

/-- The support closures of the smooth approximate identities shrink to the identity, in the
`Filter.smallSets` sense. -/
theorem tendsto_tsupport_smoothApproximateIdentity :
    Tendsto (fun U ↦ tsupport (smoothApproximateIdentity I μ U)) atBot (𝓝 (1 : G)).smallSets := by
  refine tendsto_smallSets_iff.2 fun S hS ↦ ?_
  obtain ⟨V, -, hV⟩ := OpenNhdsOf.basis_nhds.mem_iff.1 hS
  filter_upwards [eventually_le_atBot V] with U hU
  exact (tsupport_smoothApproximateIdentity_subset I μ U).trans fun _ hx ↦ hV (hU hx)

/-- **Smooth approximate identities.** For a continuous function `φ` with values in a complex
Banach space, `∫ u_U(y) • φ(y) dμ(y)` tends to `φ 1` as the identity neighbourhood `U`
shrinks. -/
theorem tendsto_integral_smoothApproximateIdentity_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {φ : G → F} (hφ : Continuous φ) :
    Tendsto (fun U ↦ ∫ x, smoothApproximateIdentity I μ U x • φ x ∂μ) atBot (𝓝 (φ 1)) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hV : {x | dist (φ x) (φ 1) < ε / 2} ∈ 𝓝 (1 : G) :=
    (isOpen_lt (hφ.dist continuous_const) continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [tendsto_smallSets_iff.1 (tendsto_tsupport_smoothApproximateIdentity I μ) _ hV]
    with U hU
  obtain ⟨hf, hfc, hf0, -, hf1⟩ := (exists_smoothApproximateIdentity I μ U).choose_spec
  set f := (exists_smoothApproximateIdentity I μ U).choose
  let g : CompactlySupportedContinuousMap G ℝ := ⟨⟨f, hf.continuous⟩, hfc⟩
  have hsupp : tsupport g = tsupport (smoothApproximateIdentity I μ U) := by
    rw [coe_smoothApproximateIdentity]
    exact (tsupport_comp_eq Complex.ofReal_eq_zero _).symm
  have hint : ∫ x, smoothApproximateIdentity I μ U x • φ x ∂μ = ∫ x, g x • φ x ∂μ := by
    simp only [coe_smoothApproximateIdentity]
    congr 1 with x
  rw [dist_eq_norm, hint]
  refine (CompactlySupportedContinuousMap.norm_integral_smul_sub_le (ε := ε / 2) hf0 hf1 hφ
    fun x hx ↦ ?_).trans_lt (half_lt_self hε)
  rw [← dist_eq_norm]
  exact (hU (hsupp ▸ hx)).le

end LieTestFunction

end TauCeti
