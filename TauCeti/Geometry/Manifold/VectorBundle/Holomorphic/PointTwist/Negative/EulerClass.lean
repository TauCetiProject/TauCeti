/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.EulerClass
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Negative.Basic

/-!
# The Euler number of a negative point twist

Let `X` be a compact Riemann surface, `L → X` a complex line bundle with model fibre `ℂ`, and
`x : X`. The negative point twist `L(-x)` (`TauCeti.negPointTwistCore`) is
glued from `L` over `X ∖ {x}` and from the frames of `L` multiplied by the centred chart coordinate
over the chart disc at `x`; its sections are the sections of `L` vanishing at `x`. This file proves
that twisting negatively at a point lowers the Euler number of the underlying oriented real plane
bundle by one:
`⟨e(L(-x)_ℝ), [X]⟩ = ⟨e(L_ℝ), [X]⟩ - 1`
(`TauCeti.evalFundamentalClass_complexEulerClass_negPointTwist`). Together with the positive twist
(`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist`) this is the Chern-number bookkeeping
of the reduction to the trivial bundle in the proof of the Riemann–Roch formula for real
Cauchy–Riemann operators (McDuff–Salamon, Theorem C.1.10), where the trivial bundle is twisted at
the positive zeros of a section and negatively at its negative zeros.

The proof counts zeros. The inclusion of `L(-x)` into `L` is multiplication by the canonical
section of `𝒪(x)`; on fibres it is `TauCeti.pointTwistDiv`, an isomorphism off `x` and zero at
`x` (`TauCeti.pointTwistDiv_eq_zero_iff`). Let `τ` be a continuous section of `L(-x)` with
finitely many zeros, nonzero at `x`. Then `σ = pointTwistDiv ∘ τ` is a continuous section of `L`
(`TauCeti.continuous_negPointTwist_pointTwistDiv_section`) whose zeros are those of `τ` together
with `x`.

* Away from `x`, the two sections have the same fibre coordinates in the preferred charts of `L`
  and the charts `(z, false)` of `L(-x)`, so they have the same local index
  (`TauCeti.sectionIndex_negPointTwist_pointTwistDiv_of_ne`).
* At `x`, the section `σ` reads `w ↦ (w - φ x) g(w)` in the chart `φ` of `X` at `x` and the chart
  of `L` at `x`, where `g` is the reading of `τ` in the chart `(x, true)` of `L(-x)`. Its derivative
  at `φ x` is multiplication by `g (φ x) ≠ 0`, of determinant `|g (φ x)|² > 0` over `ℝ`, so its
  local index is `1` (`TauCeti.sectionIndex_negPointTwist_pointTwistDiv_self`, through
  `TauCeti.sectionIndex_eq_one_of_hasFDerivAt_smulRight`, the case `D = (u ↦ u c)` of
  `TauCeti.sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt`).

Summing over zeros gives `⟨e(L_ℝ), [X]⟩ = ⟨e(L(-x)_ℝ), [X]⟩ + 1`
(`TauCeti.evalFundamentalClass_complexEulerClass_eq_add_one_of_setOf_eq_insert`).

## Main results

* `TauCeti.sectionIndex_negPointTwist_pointTwistDiv_of_ne` and
  `TauCeti.sectionIndex_negPointTwist_pointTwistDiv_self`: the local indices of the included
  section.
* `TauCeti.evalFundamentalClass_complexEulerClass_negPointTwist`: the Euler number of `L(-x)` is
  that of `L` minus one.

## Implementation notes

As for the positive twist, the section `τ` of `L(-x)` with finitely many zeros and `τ x ≠ 0` is a
hypothesis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class evaluated through the zeros of a section).
-/

public section

noncomputable section

open Bundle Filter Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]

/-! ### Local indices of the included section -/

variable [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ z, Module ℝ (E z)] [∀ z, IsScalarTower ℝ ℂ (E z)]

local instance instVectorBundleRealNegPointTwist : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

local instance instVectorBundleRealNegPointTwistCore (x : X) :
    VectorBundle ℝ F (negPointTwistCore F E x).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F _

variable (hF : finrank ℂ F = 1)

/-- **Local indices of the included section away from the twisting point.** Away from `x`, a
continuous section `τ` of the negative point twist `L(-x)` of a complex line bundle `L` and the
section `pointTwistDiv ∘ τ` of `L` have the same local index, for the canonical orientations of
`L`, `L(-x)` and `X`. -/
theorem sectionIndex_negPointTwist_pointTwistDiv_of_ne {x z : X} (hzx : z ≠ x)
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' F z (τ z)) :
    (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F E)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF])
        (complexHomologicalOrientation X) (continuous_negPointTwist_pointTwistDiv_section hτ) z =
      (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F (negPointTwistCore F E x).Fiber)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF])
        (complexHomologicalOrientation X) hτ z := by
  classical
  -- The chart `(z, false)` of the negative twist lies over the preferred chart of `E` at `z`.
  have hzV : z ∈ (negPointTwistCore F E x).baseSet (z, false) :=
    mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E z, by simpa using hzx⟩
  have hVe₁ : (negPointTwistCore F E x).baseSet (z, false) ⊆
      (trivializationAt F (negPointTwistCore F E x).Fiber z).baseSet := fun _ hy ↦ by
    rwa [signedPointTwistCore_trivializationAt_of_ne hzx]
  have hVe₂ : (negPointTwistCore F E x).baseSet (z, false) ⊆
      (trivializationAt F E z).baseSet := fun _ hy ↦ (mem_signedPointTwistCore_baseSet.1 hy).1
  refine VectorBundleOrientation.sectionIndex_eq_of_snd_apply_eq
    (E₁ := (negPointTwistCore F E x).Fiber) (E₂ := E) _ _ _ _ hτ _
    (trivializationAt F (negPointTwistCore F E x).Fiber z) (trivializationAt F E z)
    ((negPointTwistCore F E x).isOpen_baseSet _) hzV hVe₁ hVe₂
    (fun _ _ ↦ VectorBundleOrientation.mapOrientation_reindex_complex F _ _ _ _)
    (fun _ _ ↦ VectorBundleOrientation.mapOrientation_reindex_complex F E _ _ _) fun y hy ↦ ?_
  rw [signedPointTwistCore_trivializationAt_of_ne hzx]
  refine (trivializationAt_pointTwistDiv_negPointTwistCore (i := (z, false)) hy (τ y)).trans ?_
  rw [pointTwistFactor_self, one_smul]

/-! ### The local index at the twisting point -/

section Line

variable {L : X → Type} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealLineNegPointTwist : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

local instance instVectorBundleRealLineNegPointTwistCore (x : X) :
    VectorBundle ℝ ℂ (negPointTwistCore ℂ L x).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] in
/-- In the chart `φ` of `X` at `x` and the chart of `L` at `x`, the included section reads
`w ↦ (w - φ x) g(φ⁻¹ w)`, where `g` is the fibre coordinate of `τ` in the chart of `L(-x)` at `x`.
Its real derivative at `φ x` is multiplication by `g x`. -/
private theorem hasFDerivAt_negPointTwist_pointTwistDiv_chartAt (x : X)
    {τ : ∀ z, (negPointTwistCore ℂ L x).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' ℂ z (τ z)) :
    HasFDerivAt (fun w ↦ (trivializationAt ℂ L x (TotalSpace.mk' ℂ ((chartAt ℂ x).symm w)
          (pointTwistDiv ℂ L x ((chartAt ℂ x).symm w) (τ ((chartAt ℂ x).symm w))))).2)
      ((ContinuousLinearMap.id ℝ ℂ).smulRight
        ((trivializationAt ℂ (negPointTwistCore ℂ L x).Fiber x
          (TotalSpace.mk' ℂ x (τ x))).2))
      (chartAt ℂ x x) := by
  set φ := chartAt ℂ x
  set eN := trivializationAt ℂ (negPointTwistCore ℂ L x).Fiber x with heN
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hxN : x ∈ eN.baseSet := mem_baseSet_trivializationAt ℂ _ x
  -- The included section read in the charts is `w ↦ (w - φ x) g(w)`.
  have hfeq : (fun w ↦ (trivializationAt ℂ L x (TotalSpace.mk' ℂ (φ.symm w)
        (pointTwistDiv ℂ L x (φ.symm w) (τ (φ.symm w))))).2) =ᶠ[𝓝 (φ x)]
      fun w ↦ (w - φ x) • (eN (TotalSpace.mk' ℂ (φ.symm w) (τ (φ.symm w)))).2 := by
    filter_upwards [φ.open_target.mem_nhds (φ.map_source hxφ),
      (φ.continuousAt_symm (φ.map_source hxφ)).preimage_mem_nhds (by
        rw [φ.left_inv hxφ]
        exact eN.open_baseSet.mem_nhds hxN)] with w hw hwe
    have hwe' : φ.symm w ∈ (negPointTwistCore ℂ L x).baseSet (x, true) := by
      simpa using mem_signedPointTwistCore_trivializationAt_baseSet.1 hwe
    refine (trivializationAt_pointTwistDiv_negPointTwistCore (i := (x, true)) hwe'
      (τ (φ.symm w))).trans ?_
    rw [pointTwistFactor_false_true, pointTwistCoord_chartAt_symm hw, heN,
      signedPointTwistCore_trivializationAt_self ℂ L x false]
  exact hasFDerivAt_sub_smul_comp_chartAt_symm
    ((eN.continuousOn_snd_apply_mk hτ).continuousAt (eN.open_baseSet.mem_nhds hxN)) hfeq

/-- **The local index of the included section at the twisting point is one.** For a continuous
section `τ` of the negative point twist `L(-x)` with `τ x ≠ 0`, the section `pointTwistDiv ∘ τ`
of `L` has a zero at `x` of local index `1`, for the canonical orientations of `L` and `X`. -/
theorem sectionIndex_negPointTwist_pointTwistDiv_self (x : X)
    {τ : ∀ z, (negPointTwistCore ℂ L x).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' ℂ z (τ z)) (hτx : τ x ≠ 0) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X)
        (continuous_negPointTwist_pointTwistDiv_section hτ) x = 1 := by
  set eN := trivializationAt ℂ (negPointTwistCore ℂ L x).Fiber x
  have hgx : (eN (TotalSpace.mk' ℂ x (τ x))).2 ≠ 0 :=
    (eN.snd_apply_ne_zero_iff ℂ (v := TotalSpace.mk' ℂ x (τ x))
      (mem_baseSet_trivializationAt ℂ _ x)).2 hτx
  exact sectionIndex_eq_one_of_hasFDerivAt_smulRight x
    (continuous_negPointTwist_pointTwistDiv_section hτ)
    (congrArg (fun f : ℂ →L[ℂ] L x ↦ f (τ x)) (pointTwistDiv_self ℂ L x)) hgx
    (hasFDerivAt_negPointTwist_pointTwistDiv_chartAt x hτ)

/-! ### The Euler number of the negative point twist -/

/-- **Twisting negatively at a point lowers the Euler number by one.** Let `L` be a complex line
bundle over a compact Riemann surface `X` and `x : X`. If the negative point twist `L(-x)` has a
continuous section with finitely many zeros that does not vanish at `x`, then the Euler class of
the underlying oriented real plane bundle of `L(-x)`, evaluated on the fundamental class of `X`, is
that of `L` minus one:
`⟨e(L(-x)_ℝ), [X]⟩ = ⟨e(L_ℝ), [X]⟩ - 1`. -/
theorem evalFundamentalClass_complexEulerClass_negPointTwist [CompactSpace X] (x : X)
    {τ : ∀ z, (negPointTwistCore ℂ L x).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' ℂ z (τ z))
    (hZ : {z | τ z = 0}.Finite) (hτx : τ x ≠ 0) :
    ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ (negPointTwistCore ℂ L x).Fiber (r := 0)
          (finrank_self ℂ))).down =
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down - 1 := by
  classical
  have hZ' : {z | pointTwistDiv ℂ L x z (τ z) = 0} = insert x {z | τ z = 0} := by
    ext z
    -- `pointTwistDiv_eq_zero_iff` with the model fibre `ℂ` of `L(-x)` made explicit.
    simp only [mem_ofPred_eq, mem_insert_iff]
    exact pointTwistDiv_eq_zero_iff (F := ℂ) (E := L) _
  refine eq_sub_of_add_eq (evalFundamentalClass_complexEulerClass_eq_add_one_of_setOf_eq_insert x hτ
    (continuous_negPointTwist_pointTwistDiv_section hτ) hZ hZ' hτx
    (fun _ hz ↦ sectionIndex_negPointTwist_pointTwistDiv_of_ne (finrank_self ℂ) hz hτ)
    (sectionIndex_negPointTwist_pointTwistDiv_self x hτ hτx)).symm

end Line

end TauCeti
