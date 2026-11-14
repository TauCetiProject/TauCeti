/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist

/-!
# Twisting a holomorphic vector bundle by the dual of a point

Let `X` be a complex curve, that is a manifold modelled on `𝓘(ℂ)`, let `E → X` be a vector bundle
with model fibre `F` whose transition functions are `C^n` over `𝓘(ℂ)`, and let `x : X`. The point
twist `E(x)` of `TauCeti.pointTwistCore` has local frames divided by the centred chart coordinate
`z ↦ φ z - φ x` near `x`, where `φ = chartAt ℂ x`. The negative point twist `E(-x)` has them
multiplied by it instead. It is glued from the same two pieces, `X \ {x}` and the source of `φ`,
with the reversed scalar transition function `TauCeti.pointTwistFactor x j i`: it is the case
`s = false` of the signed point twist `TauCeti.signedPointTwistCore`, whose case `s = true` is
`E(x)`. Its local sections are the sections of `E` vanishing at `x`. For a holomorphic line bundle
`L` it is the line bundle `L(-x) = L ⊗ 𝒪(-x)`.

The fibre map `TauCeti.pointTwistDiv` of `E(x)`, whose scalar is `0` at `x` and `1` elsewhere and
hence its own inverse, is also the fibre map from `E(-x)` to `E` including the sections vanishing
at `x`: it is an isomorphism off `x`, zero at `x`, and sends `C^n` sections of `E(-x)` to `C^n`
sections of `E`. Conversely, `TauCeti.negPointTwistOfZero` builds a section of `E(-x)` from a
section of `E` vanishing at `x`. Off `x` it is that section, and at `x` it is the derivative of its
chart reading in the centred coordinate, so that in the chart at `x` it is the chart reading divided
by the centred coordinate, extended by Mathlib's `dslope`. It recovers every section of `E(-x)`
continuous at `x` from its image in `E`. When the model fibre `F` is complete, the removable
singularity theorem makes it holomorphic when the section of `E` is. Thus, for complete `F`, the
holomorphic sections of `E(-x)` are the holomorphic sections of `E` vanishing at `x`.

For the trivial line bundle, `TauCeti.negPointTwistPairing` is the fibrewise pairing
`𝒪(-x) × 𝒪(x) → 𝒪`. In the preferred charts it is the product of the coordinates; it is
nondegenerate on every fibre, and it takes holomorphic sections to holomorphic functions. Paired
with the canonical section `TauCeti.pointTwistSection` of `𝒪(x)` it is `pointTwistDiv`. On a
compact connected curve the trivial `𝒪(-x)` has no nonzero holomorphic sections: they are
holomorphic functions vanishing at `x`. On the Riemann sphere this is `H⁰(𝒪(-1)) = 0`.

In the proof of the Riemann–Roch theorem for line bundles over a closed Riemann surface
(McDuff–Salamon, Theorem C.1.10), the trivial bundle is twisted at the zeros of a generic section,
by `𝒪(xᵢ)` at the positive zeros and by its dual at the negative ones. This file provides the
second of these twists.

## Main definitions

* `TauCeti.negPointTwistCore`: the coordinate core of the negative point twist `E(-x)`; its `C^n`
  (for `n = ∞`, holomorphic) structure is `TauCeti.signedPointTwistCore.isContMDiff`.
* `TauCeti.negPointTwistOfZero`: the section of `E(-x)` defined by a section of `E` vanishing at
  `x`.
* `TauCeti.negPointTwistPairing`: the fibrewise pairing `𝒪(-x) × 𝒪(x) → 𝒪`.

## Main results

* `TauCeti.contMDiff_negPointTwist_pointTwistDiv_section` and
  `TauCeti.mdifferentiable_negPointTwist_pointTwistDiv_section`: the inclusion `pointTwistDiv` of
  `E(-x)` into `E` preserves `C^n` and holomorphic sections.
* `TauCeti.mdifferentiable_negPointTwistOfZero`, `TauCeti.pointTwistDiv_negPointTwistOfZero` and
  `TauCeti.negPointTwistOfZero_pointTwistDiv`: the holomorphic sections of `E(-x)` correspond to
  the holomorphic sections of `E` vanishing at `x`.
* `TauCeti.negPointTwistPairing_nondegenerate` and `TauCeti.contMDiff_negPointTwistPairing`: the
  pairing with `𝒪(x)` is nondegenerate and holomorphic.
* `TauCeti.negPointTwist_trivial_section_eq_zero`: on a compact connected curve, the trivial
  `𝒪(-x)` has no nonzero holomorphic sections.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 1, Section 1
  (divisors and line bundles).
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### The negative point-twist core -/

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  (E : X → Type*) [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

/-- The coordinate core of the negative point twist `E(-x)`, the signed point twist with sign
`false`: its coordinate changes are those of `E` multiplied by the reversed scalar transition
function of the point twist. -/
abbrev negPointTwistCore (x : X) : VectorBundleCore ℂ X F (X × Bool) :=
  signedPointTwistCore F E x false

variable {F E}

variable {n : ℕ∞ω} [IsManifold 𝓘(ℂ) n X]

/-! ### The inclusion into `E` -/

/-! The inclusion of the fibre of `E(-x)` at `z` into the fibre of `E`, multiplication by the
canonical section of `𝒪(x)`, is `TauCeti.pointTwistDiv`. In the preferred chart at `z` it is the
scalar `1` off `x` and `0` at `x`, so it is an isomorphism off `x`
(`TauCeti.pointTwistDiv_bijective_of_ne`) and zero at `x` (`TauCeti.pointTwistDiv_self`). -/

open Classical in
/-- In every chart of the negative point twist, the inclusion `pointTwistDiv` into `E` is the
scalar `pointTwistFactor x false b` in the corresponding chart of `E`. -/
theorem trivializationAt_pointTwistDiv_negPointTwistCore {x z : X} {i : X × Bool}
    (hz : z ∈ (negPointTwistCore F E x).baseSet i) (w : F) :
    (trivializationAt F E i.1 ⟨z, pointTwistDiv F E x z w⟩).2 =
      pointTwistFactor x false i.2 z • ((negPointTwistCore F E x).localTriv i ⟨z, w⟩).2 := by
  have h₀ : z ∈ (trivializationAt F E z).baseSet := mem_baseSet_trivializationAt F E z
  rw [mem_signedPointTwistCore_baseSet] at hz
  rw [signedPointTwistCore_localTriv_apply, signedPointTwistFactor_false, smul_smul, mul_comm,
    pointTwistFactor_mul_false hz.2 (mem_pointTwistBaseSet_decide x z), pointTwistDiv_apply,
    inv_pointTwistFactor_false_decide, ← map_smul, Trivialization.coordChangeL_apply _ _ ⟨h₀, hz.1⟩]

variable [ContMDiffVectorBundle n F E 𝓘(ℂ)]

/-- The inclusion of the negative point twist into `E` sends a section that is `C^n` at `z₀` to a
section of `E` that is `C^n` at `z₀`. -/
theorem contMDiffAt_negPointTwist_pointTwistDiv_section {x z₀ : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)) z₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
      (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) z₀ := by
  classical
  have hz₀ := (negPointTwistCore F E x).mem_baseSet_at z₀
  rw [signedPointTwistCore_indexAt] at hz₀
  rw [(trivializationAt F (negPointTwistCore F E x).Fiber z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt F _ z₀),
    signedPointTwistCore_trivializationAt] at hτ
  refine ((trivializationAt F E z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt F E z₀)).2 ?_
  have hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (pointTwistFactor x false (decide (z₀ = x))) z₀ :=
    (contMDiffOn_pointTwistFactor_false x _).contMDiffAt
      ((isOpen_pointTwistBaseSet x _).mem_nhds (mem_pointTwistBaseSet_decide x z₀))
  refine (hf.smul hτ).congr_of_eventuallyEq ?_
  filter_upwards [((negPointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  exact trivializationAt_pointTwistDiv_negPointTwistCore hz (τ z)

/-- The inclusion of the negative point twist into `E` sends `C^n` sections to `C^n` sections. -/
theorem contMDiff_negPointTwist_pointTwistDiv_section {x : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
      (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) :=
  fun z₀ ↦ contMDiffAt_negPointTwist_pointTwistDiv_section (hτ z₀)

/-! ### Holomorphic sections -/

section Holomorphic

omit [IsManifold 𝓘(ℂ) n X] [ContMDiffVectorBundle n F E 𝓘(ℂ)]

variable (F) in
/-- The reading of a section `σ` of `E` in the chart of `E` at `x`, as a function of the chart
coordinate at `x`. -/
def negPointTwistChartReading (x : X) (σ : ∀ z, E z) (w : ℂ) : F :=
  (trivializationAt F E x ⟨(chartAt ℂ x).symm w, σ ((chartAt ℂ x).symm w)⟩).2

omit [NormedSpace ℂ F] [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [VectorBundle ℂ F E] in
variable (F) in
theorem negPointTwistChartReading_apply (x : X) (σ : ∀ z, E z) (w : ℂ) :
    negPointTwistChartReading F x σ w =
      (trivializationAt F E x ⟨(chartAt ℂ x).symm w, σ ((chartAt ℂ x).symm w)⟩).2 :=
  (rfl)

omit [NormedSpace ℂ F] [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [VectorBundle ℂ F E] in
variable (F) in
/-- At the chart coordinate of a point `z` of the chart source, the chart reading of `σ` is `σ z`
read in the chart of `E` at `x`. -/
theorem negPointTwistChartReading_chartAt {x z : X} (σ : ∀ z, E z)
    (hz : z ∈ (chartAt ℂ x).source) :
    negPointTwistChartReading F x σ (chartAt ℂ x z) = (trivializationAt F E x ⟨z, σ z⟩).2 := by
  rw [negPointTwistChartReading_apply, (chartAt ℂ x).left_inv hz]

variable (F) in
/-- The chart reading of a section vanishing at `x` vanishes at the chart coordinate of `x`. -/
theorem negPointTwistChartReading_chartAt_self {x : X} {σ : ∀ z, E z} (hσx : σ x = 0) :
    negPointTwistChartReading F x σ (chartAt ℂ x x) = 0 := by
  rw [negPointTwistChartReading_chartAt F σ (mem_chart_source ℂ x), hσx]
  exact congrArg Prod.snd
    ((trivializationAt F E x).zeroSection ℂ (mem_baseSet_trivializationAt F E x))

variable (F) in
open Classical in
/-- The section of the negative point twist `E(-x)` determined by a section `σ` of `E` vanishing at
`x`. Off `x` it is `σ`, read in the preferred chart of `E`; at `x` it is the derivative of the
chart reading of `σ` at the chart coordinate of `x`, so that in the chart of `E(-x)` at `x` it is
the chart reading of `σ` divided by the centred coordinate. -/
def negPointTwistOfZero (x : X) (σ : ∀ z, E z) (z : X) : (negPointTwistCore F E x).Fiber z :=
  if z = x then deriv (negPointTwistChartReading F x σ) (chartAt ℂ x x)
  else (trivializationAt F E z ⟨z, σ z⟩).2

variable (F) in
@[simp] theorem negPointTwistOfZero_self (x : X) (σ : ∀ z, E z) :
    negPointTwistOfZero F x σ x = deriv (negPointTwistChartReading F x σ) (chartAt ℂ x x) :=
  ite_eq_left rfl

variable (F) in
@[simp] theorem negPointTwistOfZero_of_ne {x z : X} (h : z ≠ x) (σ : ∀ z, E z) :
    negPointTwistOfZero F x σ z = (trivializationAt F E z ⟨z, σ z⟩).2 :=
  ite_eq_right h

/-- The zero section of `E` defines the zero section of `E(-x)`. -/
@[simp] theorem negPointTwistOfZero_zero (x : X) :
    negPointTwistOfZero F x (fun z ↦ (0 : E z)) = 0 := by
  funext z
  by_cases h : z = x
  · subst h
    have hr : negPointTwistChartReading F z (fun z ↦ (0 : E z)) =ᶠ[𝓝 (chartAt ℂ z z)]
        fun _ ↦ 0 := by
      filter_upwards [(chartAt ℂ z).tendsto_symm (mem_chart_source ℂ z)
        ((trivializationAt F E z).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E z))]
        with w hw
      exact congrArg Prod.snd ((trivializationAt F E z).zeroSection ℂ hw)
    rw [negPointTwistOfZero_self, hr.deriv_eq, Pi.zero_apply]
    exact deriv_const (chartAt ℂ z z) (0 : F)
  · rw [negPointTwistOfZero_of_ne F h, Pi.zero_apply]
    exact congrArg Prod.snd
      ((trivializationAt F E z).zeroSection ℂ (mem_baseSet_trivializationAt F E z))

/-- The inclusion into `E` recovers a section vanishing at `x` from its section of `E(-x)`. -/
@[simp] theorem pointTwistDiv_negPointTwistOfZero {x : X} {σ : ∀ z, E z} (hσx : σ x = 0)
    (z : X) : pointTwistDiv F E x z (negPointTwistOfZero F x σ z) = σ z := by
  by_cases h : z = x
  · subst h
    rw [pointTwistDiv_self]
    exact hσx.symm
  · rw [negPointTwistOfZero_of_ne F h, pointTwistDiv_apply_of_ne h]
    exact (trivializationAt F E z).symm_apply_apply_mk (mem_baseSet_trivializationAt F E z) _

/-- In the chart of `E(-x)` at `x`, the section `negPointTwistOfZero F x σ` is the chart reading of
`σ` divided by the centred chart coordinate, extended at `x` by the derivative. -/
theorem negPointTwistCore_localTriv_negPointTwistOfZero {x z : X} {σ : ∀ z, E z} (hσx : σ x = 0)
    (hz : z ∈ (negPointTwistCore F E x).baseSet (x, true)) :
    ((negPointTwistCore F E x).localTriv (x, true) ⟨z, negPointTwistOfZero F x σ z⟩).2 =
      dslope (negPointTwistChartReading F x σ) (chartAt ℂ x x) (chartAt ℂ x z) := by
  classical
  have hx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
  rw [mem_signedPointTwistCore_baseSet] at hz
  have hzs : z ∈ (chartAt ℂ x).source := by simpa using hz.2
  refine (signedPointTwistCore_localTriv_apply (F := F) (E := E) x false (x, true) z
    (negPointTwistOfZero F x σ z)).trans ?_
  by_cases h : z = x
  · subst h
    rw [decide_eq_true rfl, signedPointTwistFactor_self, one_smul, dslope_same,
      negPointTwistOfZero_self, Trivialization.coordChangeL_apply _ _ ⟨hx, hx⟩,
      (trivializationAt F E z).apply_mk_symm hx]
  · have h₀ := mem_baseSet_trivializationAt F E z
    have hne : chartAt ℂ x z ≠ chartAt ℂ x x := fun h' ↦ h ((chartAt ℂ x).injOn hzs
      (mem_chart_source ℂ x) h')
    -- Off `x`, the chart of `E(-x)` at `x` reads `σ z` in the chart of `E` at `x`, divided by the
    -- centred coordinate.
    rw [decide_eq_false h, signedPointTwistFactor_false, pointTwistFactor_true_false,
      negPointTwistOfZero_of_ne F h, Trivialization.coordChangeL_apply _ _ ⟨h₀, hz.1⟩,
      (trivializationAt F E z).symm_apply_apply_mk h₀]
    -- The slope of the chart reading from the chart coordinate of `x`, where it vanishes.
    rw [dslope_of_ne _ hne, slope_def_module, negPointTwistChartReading_chartAt F σ hzs,
      negPointTwistChartReading_chartAt_self F hσx, sub_zero,
      ← pointTwistCoord_chartAt_symm ((chartAt ℂ x).map_source hzs), (chartAt ℂ x).left_inv hzs]

/-- Off `x`, in the chart of `E(-x)` at `y`, the section `negPointTwistOfZero F x σ` is `σ` read in
the chart of `E` at `y`. -/
theorem negPointTwistCore_localTriv_negPointTwistOfZero_of_ne {x y z : X} {σ : ∀ z, E z}
    (hz : z ∈ (negPointTwistCore F E x).baseSet (y, false)) :
    ((negPointTwistCore F E x).localTriv (y, false) ⟨z, negPointTwistOfZero F x σ z⟩).2 =
      (trivializationAt F E y ⟨z, σ z⟩).2 := by
  classical
  have h₀ := mem_baseSet_trivializationAt F E z
  rw [mem_signedPointTwistCore_baseSet] at hz
  have h : z ≠ x := by simpa using hz.2
  refine (signedPointTwistCore_localTriv_apply (F := F) (E := E) x false (y, false) z
    (negPointTwistOfZero F x σ z)).trans ?_
  rw [decide_eq_false h, signedPointTwistFactor_self, one_smul,
    negPointTwistOfZero_of_ne F h, Trivialization.coordChangeL_apply _ _ ⟨h₀, hz.1⟩,
    (trivializationAt F E z).symm_apply_apply_mk h₀]

variable [IsManifold 𝓘(ℂ) 1 X] [ContMDiffVectorBundle 1 F E 𝓘(ℂ)]

/-- The inclusion of the negative point twist into `E` sends a section that is holomorphic at `z₀`
to a section of `E` that is holomorphic at `z₀`. -/
theorem mdifferentiableAt_negPointTwist_pointTwistDiv_section {x z₀ : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : MDifferentiableAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) (fun z ↦ TotalSpace.mk' F z (τ z)) z₀) :
    MDifferentiableAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F))
      (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) z₀ := by
  classical
  have hz₀ := (negPointTwistCore F E x).mem_baseSet_at z₀
  rw [signedPointTwistCore_indexAt] at hz₀
  rw [(trivializationAt F (negPointTwistCore F E x).Fiber z₀).mdifferentiableAt_section_iff
    𝓘(ℂ) _ (mem_baseSet_trivializationAt F _ z₀),
    signedPointTwistCore_trivializationAt] at hτ
  refine ((trivializationAt F E z₀).mdifferentiableAt_section_iff 𝓘(ℂ) _
    (mem_baseSet_trivializationAt F E z₀)).2 ?_
  have hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (pointTwistFactor x false (decide (z₀ = x))) z₀ :=
    ((contMDiffOn_pointTwistFactor_false (n := 1) x _).contMDiffAt
      ((isOpen_pointTwistBaseSet x _).mem_nhds
        (mem_pointTwistBaseSet_decide x z₀))).mdifferentiableAt one_ne_zero
  refine (hf.smul hτ).congr_of_eventuallyEq ?_
  filter_upwards [((negPointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  exact trivializationAt_pointTwistDiv_negPointTwistCore hz (τ z)

/-- The inclusion of the negative point twist into `E` sends holomorphic sections to holomorphic
sections. -/
theorem mdifferentiable_negPointTwist_pointTwistDiv_section {x : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) (fun z ↦ TotalSpace.mk' F z (τ z))) :
    MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F))
      (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) :=
  fun z₀ ↦ mdifferentiableAt_negPointTwist_pointTwistDiv_section (hτ z₀)

/-- A holomorphic section of `E` vanishing at `x` defines a holomorphic section of the negative
point twist `E(-x)`: the chart reading divided by the centred coordinate is holomorphic by the
removable singularity theorem. -/
theorem mdifferentiable_negPointTwistOfZero [CompleteSpace F] {x : X} {σ : ∀ z, E z}
    (hσ : MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) (fun z ↦ TotalSpace.mk' F z (σ z)))
    (hσx : σ x = 0) :
    MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F))
      (fun z ↦ TotalSpace.mk' F (E := (negPointTwistCore F E x).Fiber) z
        (negPointTwistOfZero F x σ z)) := by
  intro z₀
  rw [(trivializationAt F (negPointTwistCore F E x).Fiber z₀).mdifferentiableAt_section_iff
    𝓘(ℂ) _ (mem_baseSet_trivializationAt F _ z₀)]
  by_cases h : z₀ = x
  · subst h
    rw [signedPointTwistCore_trivializationAt_self]
    set φ := chartAt ℂ z₀
    set e := trivializationAt F E z₀
    set s : Set ℂ := φ.target ∩ φ.symm ⁻¹' e.baseSet
    have hs : s ∈ 𝓝 (φ z₀) := inter_mem (chart_target_mem_nhds ℂ z₀)
      (φ.tendsto_symm (mem_chart_source ℂ z₀) (e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E z₀)))
    have hg : DifferentiableOn ℂ (negPointTwistChartReading F z₀ σ) s := by
      intro w hw
      have h₁ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, F) (fun z ↦ (e ⟨z, σ z⟩).2) (φ.symm w) :=
        (e.mdifferentiableAt_section_iff 𝓘(ℂ) σ hw.2).1 (hσ _)
      have h₂ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ.symm w :=
        mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ z₀) hw.1
      exact (h₁.comp w h₂).differentiableAt.differentiableWithinAt
    have hd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, F)
        (fun z ↦ dslope (negPointTwistChartReading F z₀ σ) (φ z₀) (φ z)) z₀ :=
      (((Complex.differentiableOn_dslope hs).2 hg).differentiableAt hs).mdifferentiableAt.comp z₀
        (mdifferentiableAt_atlas (chart_mem_atlas ℂ z₀) (mem_chart_source ℂ z₀))
    refine hd.congr_of_eventuallyEq ?_
    have hz₀ : z₀ ∈ (negPointTwistCore F E z₀).baseSet (z₀, true) :=
      mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E z₀, by simp⟩
    filter_upwards [((negPointTwistCore F E z₀).isOpen_baseSet _).mem_nhds hz₀] with z hz
    exact negPointTwistCore_localTriv_negPointTwistOfZero hσx hz
  · rw [signedPointTwistCore_trivializationAt_of_ne h]
    have hz₀ : z₀ ∈ (negPointTwistCore F E x).baseSet (z₀, false) :=
      mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E z₀, by simpa using h⟩
    refine (((trivializationAt F E z₀).mdifferentiableAt_section_iff 𝓘(ℂ) σ
      (mem_baseSet_trivializationAt F E z₀)).1 (hσ z₀)).congr_of_eventuallyEq ?_
    filter_upwards [((negPointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
    exact negPointTwistCore_localTriv_negPointTwistOfZero_of_ne hz

omit [IsManifold 𝓘(ℂ) 1 X] [ContMDiffVectorBundle 1 F E 𝓘(ℂ)] in
/-- Every section of the negative point twist `E(-x)` that is continuous at `x`, in particular
every holomorphic section, is recovered by `negPointTwistOfZero` from its image in `E`, which
vanishes at `x`. Together with `pointTwistDiv_negPointTwistOfZero` and
`mdifferentiable_negPointTwistOfZero`, for complete `F` the holomorphic sections of `E(-x)`
correspond to the holomorphic sections of `E` vanishing at `x`. -/
theorem negPointTwistOfZero_pointTwistDiv {x : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : ContinuousAt (fun z ↦ TotalSpace.mk' F (E := (negPointTwistCore F E x).Fiber) z (τ z))
      x) :
    negPointTwistOfZero F x (fun z ↦ pointTwistDiv F E x z (τ z)) = τ := by
  have hne (z : X) (h : z ≠ x) :
      negPointTwistOfZero F x (fun z ↦ pointTwistDiv F E x z (τ z)) z = τ z := by
    rw [negPointTwistOfZero_of_ne F h, ← pointTwistMul_apply_of_ne h]
    exact pointTwistMul_pointTwistDiv (F := F) h (τ z)
  funext z
  by_cases h : z = x
  · subst h
    set σ := fun z' ↦ pointTwistDiv F E z z' (τ z')
    have hσz : σ z = 0 := by
      dsimp only [σ]
      rw [pointTwistDiv_self]; exact zero_apply _
    set φ := chartAt ℂ z
    -- The chart reading `t` of `τ` at `x` is continuous at the chart coordinate of `x`.
    set t : ℂ → F := fun w ↦
      (trivializationAt F (negPointTwistCore F E z).Fiber z ⟨φ.symm w, τ (φ.symm w)⟩).2 with ht_def
    have ht : ContinuousAt t (φ z) :=
      ContinuousAt.comp_of_eq
        (g := fun z' ↦ (trivializationAt F (negPointTwistCore F E z).Fiber z ⟨z', τ z'⟩).2)
        ((FiberBundle.continuousAt_totalSpace F _).1 hτ).2
        (φ.continuousAt_symm (mem_chart_target ℂ z)) (φ.left_inv (mem_chart_source ℂ z))
    -- Off the chart coordinate of `x`, the slope of the chart reading of `σ` there is `t`, so `t`
    -- at the chart coordinate of `x` is the derivative of that chart reading.
    have hs : slope (negPointTwistChartReading F z σ) (φ z) =ᶠ[𝓝[≠] φ z] t := by
      have hb : z ∈ (negPointTwistCore F E z).baseSet (z, true) :=
        mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E z, by simp⟩
      filter_upwards [nhdsWithin_le_nhds (chart_target_mem_nhds ℂ z),
        nhdsWithin_le_nhds (φ.tendsto_symm (mem_chart_source ℂ z)
          (((negPointTwistCore F E z).isOpen_baseSet _).mem_nhds hb)), self_mem_nhdsWithin]
        with w hw hwb hwz
      have hz' : φ.symm w ≠ z := fun h' ↦ hwz (by rw [mem_singleton_iff, ← h', φ.right_inv hw])
      rw [← dslope_of_ne _ hwz, ← φ.right_inv hw,
        ← negPointTwistCore_localTriv_negPointTwistOfZero hσz hwb, hne _ hz', φ.right_inv hw,
        ht_def, signedPointTwistCore_trivializationAt_self]
    have hd : HasDerivAt (negPointTwistChartReading F z σ) (t (φ z)) (φ z) :=
      hasDerivAt_iff_tendsto_slope.2 ((ht.tendsto.mono_left nhdsWithin_le_nhds).congr' hs.symm)
    rw [negPointTwistOfZero_self, hd.deriv, ht_def]
    dsimp only
    rw [φ.left_inv (mem_chart_source ℂ z), signedPointTwistCore_trivializationAt_apply]
    exact (negPointTwistCore F E z).coordChange_self _ _
      ((negPointTwistCore F E z).mem_baseSet_at z) (τ z)
  · exact hne z h

end Holomorphic

/-! ### The pairing with the point twist -/

section Pairing

omit [IsManifold 𝓘(ℂ) n X] [ContMDiffVectorBundle n F E 𝓘(ℂ)]

/-- The fibrewise pairing `𝒪(-x) × 𝒪(x) → 𝒪` at `z`: the product of the coordinates of the two
vectors in their preferred charts at `z`. The coordinate changes of `𝒪(-x)` and `𝒪(x)` are inverse
scalars, so the product is the same in every chart. -/
def negPointTwistPairing (x z : X) :
    (negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber z →ₗ[ℂ]
      (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber z →ₗ[ℂ] ℂ :=
  LinearMap.mul ℂ ℂ

@[simp] theorem negPointTwistPairing_apply (x z : X) (u v : ℂ) :
    negPointTwistPairing x z u v = u * v :=
  (rfl)

/-- The pairing of `𝒪(-x)` with `𝒪(x)` is nondegenerate in every fibre. -/
theorem negPointTwistPairing_nondegenerate (x z : X) :
    (negPointTwistPairing x z).Nondegenerate := by
  refine ⟨fun u hu ↦ ?_, fun v hv ↦ ?_⟩
  · exact (mul_one (M := ℂ) u).symm.trans
      ((negPointTwistPairing_apply x z u 1).symm.trans (hu (1 : ℂ)))
  · exact (one_mul (M := ℂ) v).symm.trans
      ((negPointTwistPairing_apply x z 1 v).symm.trans (hv (1 : ℂ)))

/-- Paired with the canonical section of `𝒪(x)`, a vector of `𝒪(-x)` gives its image under the
inclusion into the trivial bundle. -/
theorem negPointTwistPairing_pointTwistSection (x z : X)
    (u : ℂ) :
    negPointTwistPairing x z u (pointTwistSection x z) =
      pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z u := by
  classical
  refine (negPointTwistPairing_apply x z u (pointTwistSection x z)).trans ?_
  refine (congrArg (fun t : ℂ ↦ u * t) (pointTwistSection_apply x z)).trans ?_
  rw [pointTwistDiv_apply, inv_pointTwistFactor_false_decide, mul_comm]
  exact (congrArg Prod.snd
    ((trivializationAt ℂ (Bundle.Trivial X ℂ) z).apply_mk_symm (mem_univ z) _)).symm

/-- In the chart `(y, b)`, the coordinates of vectors of `𝒪(-x)` and `𝒪(x)` multiply to their
pairing. -/
theorem negPointTwistCore_localTriv_mul_pointTwistCore_localTriv {x z : X} {i : X × Bool}
    (hz : z ∈ (negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).baseSet i)
    (u v : ℂ) :
    ((negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).localTriv i ⟨z, u⟩).2 *
        ((pointTwistCore ℂ (Bundle.Trivial X ℂ) x).localTriv i ⟨z, v⟩).2 =
      negPointTwistPairing x z u v := by
  classical
  have hb := mem_pointTwistBaseSet_decide x z
  rw [mem_signedPointTwistCore_baseSet] at hz
  -- The trivial bundle has a single trivialization, so its preferred charts all agree.
  have htriv (y : X) (w : ℂ) : (trivializationAt ℂ (Bundle.Trivial X ℂ) z).coordChangeL ℂ
      (trivializationAt ℂ (Bundle.Trivial X ℂ) y) z w = w :=
    (Trivialization.coordChangeL_apply _ _ ⟨mem_univ z, mem_univ z⟩ w).trans
      (congrArg Prod.snd ((trivializationAt ℂ (Bundle.Trivial X ℂ) z).apply_mk_symm
        (mem_univ z) w))
  rw [signedPointTwistCore_localTriv_apply (F := ℂ), signedPointTwistCore_localTriv_apply (F := ℂ),
    signedPointTwistFactor_false, signedPointTwistFactor_true, htriv, htriv,
    negPointTwistPairing_apply, smul_eq_mul, smul_eq_mul]
  calc _ = (pointTwistFactor x i.2 (decide (z = x)) z *
        pointTwistFactor x (decide (z = x)) i.2 z) * (u * v) := by ring
    _ = u * v := by rw [pointTwistFactor_mul hb hz.2 hb, pointTwistFactor_self, one_mul]

variable [IsManifold 𝓘(ℂ) n X]

/-- The pairing of `C^n` sections of `𝒪(-x)` and `𝒪(x)` is a `C^n` function; for `n = ∞`, or
`n = ω`, the pairing of holomorphic sections is holomorphic. -/
theorem contMDiff_negPointTwistPairing {x : X}
    {τ : ∀ z, (negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber z}
    {τ' : ∀ z, (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber z}
    (hτ : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) n (fun z ↦ TotalSpace.mk' ℂ z (τ z)))
    (hτ' : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) n (fun z ↦ TotalSpace.mk' ℂ z (τ' z))) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun z ↦ negPointTwistPairing x z (τ z) (τ' z)) := by
  classical
  intro z₀
  have h₁ := ((trivializationAt ℂ (negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber
    z₀).contMDiffAt_section_iff (mem_baseSet_trivializationAt ℂ _ z₀)).1 (hτ z₀)
  have h₂ := ((trivializationAt ℂ (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber
    z₀).contMDiffAt_section_iff (mem_baseSet_trivializationAt ℂ _ z₀)).1 (hτ' z₀)
  have hz₀ := (negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).mem_baseSet_at z₀
  rw [signedPointTwistCore_trivializationAt] at h₁ h₂
  rw [signedPointTwistCore_indexAt] at hz₀
  refine (h₁.smul h₂).congr_of_eventuallyEq ?_
  filter_upwards [((negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).isOpen_baseSet _).mem_nhds hz₀]
    with z hz
  exact (negPointTwistCore_localTriv_mul_pointTwistCore_localTriv hz (τ z) (τ' z)).symm

/-- On a compact connected curve, the trivial negative point twist `𝒪(-x)` has no nonzero
holomorphic sections: a holomorphic section is a holomorphic function vanishing at `x`, so it is
zero. On the Riemann sphere this is `H⁰(𝒪(-1)) = 0`. -/
theorem negPointTwist_trivial_section_eq_zero [CompactSpace X] [PreconnectedSpace X]
    [IsManifold 𝓘(ℂ) 1 X] {x : X}
    {τ : ∀ z, (negPointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber z}
    (hτ : MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) (fun z ↦ TotalSpace.mk' ℂ z (τ z))) :
    τ = 0 := by
  set σ : ∀ z, Bundle.Trivial X ℂ z := fun z ↦ pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z (τ z)
  have hσ := mdifferentiable_negPointTwist_pointTwistDiv_section hτ
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) σ := fun z ↦
    ((trivializationAt ℂ (Bundle.Trivial X ℂ) z).mdifferentiableAt_section_iff 𝓘(ℂ) σ
      (mem_univ z)).1 (hσ z)
  have h0 : σ = fun _ ↦ 0 := funext fun z ↦ (hf.apply_eq_of_compactSpace z x).trans
    (by simp only [σ, pointTwistDiv_self]; exact zero_apply _)
  rw [← negPointTwistOfZero_pointTwistDiv (hτ x).continuousAt]
  exact (congrArg (negPointTwistOfZero ℂ x) h0).trans (negPointTwistOfZero_zero x)

end Pairing

end TauCeti
