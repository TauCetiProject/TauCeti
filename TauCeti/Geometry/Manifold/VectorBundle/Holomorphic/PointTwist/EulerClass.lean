/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Smul
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.PreferredChartReading
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Comparison

/-!
# The Euler number of a point twist

Let `X` be a compact Riemann surface, `L → X` a complex line bundle with model fibre `ℂ`, and
`x : X`. The point twist `L(x)` (`TauCeti.pointTwistCore`) is glued from `L` over `X ∖ {x}` and
from the frames of `L` divided by the centred chart coordinate over the chart disc at `x`. This
file proves that twisting at a point raises the Euler number of the underlying oriented real plane
bundle by one:
`⟨e(L(x)_ℝ), [X]⟩ = ⟨e(L_ℝ), [X]⟩ + 1`
(`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist`). Here `e(L_ℝ)` is the Euler class of
`L` with its canonical complex orientation (`TauCeti.complexEulerClass`), which defines the native
line first Chern class (`TauCeti.lineFirstChernClass_def`), and `[X]` is the fundamental class of
the canonical orientation of `X`. With the given section witness, this is the Chern-number half
of step 4 of the proof of the Riemann–Roch formula for real Cauchy–Riemann operators
(McDuff–Salamon, Theorem C.1.10).

The proof counts zeros. Let `s` be a continuous section of `L` with finitely many zeros, nonzero at
`x`. Multiplication by the canonical section of `𝒪(x)` (`TauCeti.pointTwistMul`) turns `s` into a
continuous section of `L(x)` whose zeros are those of `s` together with `x`.

* Away from `x`, the two sections have the same fibre coordinates in the charts `(z, false)` of
  `L(x)` and the preferred charts of `L`, which read the canonical orientations as the same
  orientation of `ℂ`, so they have the same local index
  (`TauCeti.sectionIndex_pointTwistMul_of_ne`).
* At `x`, the twisted section reads `w ↦ (w - φ x) g(w)` in the chart `φ` of `X` at `x` and the
  chart `(x, true)` of `L(x)`, with `g` continuous and `g (φ x) ≠ 0`. Its derivative at `φ x` is
  multiplication by `g (φ x)`, of determinant `|g (φ x)|² > 0` over `ℝ`, and the centred chart
  carries the canonical local orientation of `X` to that of `ℂ`
  by the canonical maximal-atlas and chart/linear-equivalence orientation comparisons,
  so its local index is `1`
  (`TauCeti.sectionIndex_pointTwistMul_self`).

Summing over zeros
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`) gives the
formula. For the trivial bundle the constant section `1` gives `⟨e(𝒪(x)_ℝ), [X]⟩ = 1`
(`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_trivial`). On the Riemann sphere with
`x = ∞` this is the Euler number `⟨e(𝒪(∞)_ℝ), [ℙ¹]⟩ = 1`, hence the native line-Chern number
`c₁(𝒪(1))[ℙ¹] = 1` by `TauCeti.lineFirstChernClass_def`
(`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_infty`,
in `TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Sphere`).

## Main results

* `TauCeti.hasFDerivAt_sub_smul_comp_chartAt_symm`: the derivative of a chart reading with a
  simple zero.
* `TauCeti.evalFundamentalClass_complexEulerClass_eq_add_one_of_setOf_eq_insert`: adding a zero of
  index one raises the Euler number by one.
* `TauCeti.sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt`: the local index at a zero is the
  sign of the Jacobian of its chart reading.
* `TauCeti.sectionIndex_eq_one_of_hasFDerivAt_smulRight`: in particular, a zero whose chart
  reading has the derivative of multiplication by a nonzero complex number has local index `1`.
* `TauCeti.sectionIndex_pointTwistMul_of_ne` and `TauCeti.sectionIndex_pointTwistMul_self`: the
  local indices of the twisted section.
* `TauCeti.evalFundamentalClass_complexEulerClass_pointTwist`: the Euler number of `L(x)` is that
  of `L` plus one.
* `TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_trivial`: the Euler number of the
  twist `𝒪(x)` of the trivial line bundle is one.

## Implementation notes

The section `s` with finitely many zeros and `s x ≠ 0` is a hypothesis. Constructing such a witness
through generic sections requires the smooth real bundle data of that separate construction.
The local index at `x` is computed for the model fibre
`ℂ`, where the chart of `X` at `x` takes values in the model fibre, as the sign of a Jacobian
determinant requires. Away from `x` the model fibre is any complex line.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class evaluated through the zeros of a section).
-/

public section

noncomputable section

open Bundle Module Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]

/-! ### Local indices of the twisted section -/

variable [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ z, Module ℝ (E z)] [∀ z, IsScalarTower ℝ ℂ (E z)]

local instance instVectorBundleRealPointTwistEuler : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

local instance instVectorBundleRealPointTwistCoreEuler (x : X) :
    VectorBundle ℝ F (pointTwistCore F E x).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F _

variable (hF : finrank ℂ F = 1)

/-- **Local indices of the twisted section away from the twisting point.** Away from `x`, a
continuous section `s` of a complex line bundle `L` and the section `pointTwistMul ∘ s` of the
point twist `L(x)` have the same local index, for the canonical orientations of `L`, `L(x)` and
`X`. -/
theorem sectionIndex_pointTwistMul_of_ne {x z : X} (hzx : z ≠ x) {s : ∀ z, E z}
    (hs : Continuous fun z ↦ TotalSpace.mk' F z (s z)) :
    (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F (pointTwistCore F E x).Fiber)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF])
        (complexHomologicalOrientation X) (continuous_pointTwistMul_section (x := x) hs) z =
      (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F E)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF])
        (complexHomologicalOrientation X) hs z := by
  classical
  -- The chart `(z, false)` of the point twist lies over the preferred chart of `E` at `z`.
  have hzV : z ∈ (pointTwistCore F E x).baseSet (z, false) := mem_signedPointTwistCore_baseSet.2
    ⟨mem_baseSet_trivializationAt F E z, by simpa using hzx⟩
  have hVe₁ : (pointTwistCore F E x).baseSet (z, false) ⊆ (trivializationAt F E z).baseSet :=
    fun _ hy ↦ (mem_signedPointTwistCore_baseSet.1 hy).1
  have hVe₂ : (pointTwistCore F E x).baseSet (z, false) ⊆
      (trivializationAt F (pointTwistCore F E x).Fiber z).baseSet := fun _ hy ↦ by
    rwa [signedPointTwistCore_trivializationAt_of_ne hzx]
  refine VectorBundleOrientation.sectionIndex_eq_of_snd_apply_eq (E₁ := E)
    (E₂ := (pointTwistCore F E x).Fiber) _ _ _ _ hs _
    (trivializationAt F E z) (trivializationAt F (pointTwistCore F E x).Fiber z)
    ((pointTwistCore F E x).isOpen_baseSet _) hzV hVe₁ hVe₂
    (fun _ _ ↦ VectorBundleOrientation.mapOrientation_reindex_complex F E _ _ _)
    (fun _ _ ↦ VectorBundleOrientation.mapOrientation_reindex_complex F _ _ _ _) fun y hy ↦ ?_
  rw [signedPointTwistCore_trivializationAt_of_ne hzx]
  refine (pointTwistCore_localTriv_pointTwistMul hy (s y)).trans ?_
  rw [pointTwistFactor_self, one_smul]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  [∀ z, Module ℝ (E z)] [∀ z, IsScalarTower ℝ ℂ (E z)] in
/-- **The derivative of a chart reading with a simple zero.** Let `φ` be the chart of `X` at `x`.
If near `φ x` a function `f` is `w ↦ (w - φ x) G(φ⁻¹ w)`, with `G` continuous at `x`, then the real
derivative of `f` at `φ x` is multiplication by `G x`. This is how the sections of the point twists
read at the twisting point. -/
theorem hasFDerivAt_sub_smul_comp_chartAt_symm {x : X} {f : ℂ → ℂ} {G : X → ℂ}
    (hG : ContinuousAt G x)
    (hf : f =ᶠ[𝓝 (chartAt ℂ x x)] fun w ↦ (w - chartAt ℂ x x) • G ((chartAt ℂ x).symm w)) :
    HasFDerivAt f ((ContinuousLinearMap.id ℝ ℂ).smulRight (G x)) (chartAt ℂ x x) := by
  set φ := chartAt ℂ x
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hG' : ContinuousAt (G ∘ φ.symm) (φ x) :=
    ContinuousAt.comp_of_eq hG (φ.continuousAt_symm (φ.map_source hxφ)) (φ.left_inv hxφ)
  have hA := (((hasFDerivAt_id (𝕜 := ℝ) (φ x)).sub_const (φ x)).smul_of_eq_zero hG'
    (sub_self _)).congr_of_eventuallyEq hf
  rwa [Function.comp_apply, φ.left_inv hxφ] at hA

section Count

variable {L₁ L₂ : X → Type} [∀ z, AddCommGroup (L₁ z)] [∀ z, Module ℂ (L₁ z)]
  [∀ z, Module ℝ (L₁ z)] [∀ z, IsScalarTower ℝ ℂ (L₁ z)] [∀ z, TopologicalSpace (L₁ z)]
  [TopologicalSpace (TotalSpace ℂ L₁)] [FiberBundle ℂ L₁] [VectorBundle ℂ ℂ L₁]
  [∀ z, AddCommGroup (L₂ z)] [∀ z, Module ℂ (L₂ z)] [∀ z, Module ℝ (L₂ z)]
  [∀ z, IsScalarTower ℝ ℂ (L₂ z)] [∀ z, TopologicalSpace (L₂ z)]
  [TopologicalSpace (TotalSpace ℂ L₂)] [FiberBundle ℂ L₂] [VectorBundle ℂ ℂ L₂]

local instance instVectorBundleRealCountPointTwistEuler₁ : VectorBundle ℝ ℂ L₁ :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L₁

local instance instVectorBundleRealCountPointTwistEuler₂ : VectorBundle ℝ ℂ L₂ :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L₂

/-- **Adding a zero of index one raises the Euler number by one.** Let `σ₁` and `σ₂` be continuous
sections of complex line bundles `L₁` and `L₂` with fibre `ℂ` over a compact Riemann surface `X`,
where `σ₁` has finitely many zeros, does not vanish at `x`, and the zeros of `σ₂` are those of `σ₁`
together with `x`. If the local indices of `σ₂` and `σ₁` agree off `x` and `σ₂` has local index `1`
at `x`, then `⟨e(L₂), [X]⟩ = ⟨e(L₁), [X]⟩ + 1`. -/
theorem evalFundamentalClass_complexEulerClass_eq_add_one_of_setOf_eq_insert [CompactSpace X]
    (x : X) {σ₁ : ∀ z, L₁ z} {σ₂ : ∀ z, L₂ z}
    (hσ₁ : Continuous fun z ↦ TotalSpace.mk' ℂ z (σ₁ z))
    (hσ₂ : Continuous fun z ↦ TotalSpace.mk' ℂ z (σ₂ z)) (hZ : {z | σ₁ z = 0}.Finite)
    (hZ₂ : {z | σ₂ z = 0} = insert x {z | σ₁ z = 0}) (hσ₁x : σ₁ x ≠ 0)
    (hne : ∀ z, z ≠ x →
      (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
          (VectorBundleOrientation.complex ℂ L₂)).sectionIndex
          Complex.finrank_real_complex (complexHomologicalOrientation X) hσ₂ z =
        (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
          (VectorBundleOrientation.complex ℂ L₁)).sectionIndex
          Complex.finrank_real_complex (complexHomologicalOrientation X) hσ₁ z)
    (hx : (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
          (VectorBundleOrientation.complex ℂ L₂)).sectionIndex
          Complex.finrank_real_complex (complexHomologicalOrientation X) hσ₂ x = 1) :
    ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L₂ (r := 0) (finrank_self ℂ))).down =
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L₁ (r := 0) (finrank_self ℂ))).down + 1 := by
  classical
  have hZx : {z | σ₂ z = 0}.Finite := hZ₂ ▸ hZ.insert x
  rw [complexEulerClass_def, complexEulerClass_def,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hσ₂ _ hZx,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hσ₁ _ hZ]
  have hfin : hZx.toFinset = insert x hZ.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, hZ₂, Set.mem_insert_iff]
  have hx' : x ∉ hZ.toFinset := by simpa using hσ₁x
  refine (Finset.sum_congr hfin fun _ _ ↦ rfl).trans ?_
  rw [Finset.sum_insert hx', add_comm]
  congr 1
  exact Finset.sum_congr rfl fun z hz ↦ hne z (by rintro rfl; exact hx' hz)

end Count

/-! ### The local index at the twisting point -/

section Line

variable {L : X → Type} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealLinePointTwistEuler : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

local instance instVectorBundleRealLinePointTwistCoreEuler (x : X) :
    VectorBundle ℝ ℂ (pointTwistCore ℂ L x).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] in
/-- In the chart `φ` of `X` at `x` and the chart `(x, true)` of the point twist, the twisted
section reads `w ↦ (w - φ x) g(φ⁻¹ w)`, where `g` is the fibre coordinate of `s` in the chart of
`L` at `x`. Its real derivative at `φ x` is multiplication by `g x`. -/
private theorem hasFDerivAt_pointTwistMul_chartAt (x : X) {s : ∀ z, L z}
    (hs : Continuous fun z ↦ TotalSpace.mk' ℂ z (s z)) :
    HasFDerivAt (fun w ↦ (trivializationAt ℂ (pointTwistCore ℂ L x).Fiber x
        (TotalSpace.mk' ℂ ((chartAt ℂ x).symm w)
          (pointTwistMul ℂ L x ((chartAt ℂ x).symm w) (s ((chartAt ℂ x).symm w))))).2)
      ((ContinuousLinearMap.id ℝ ℂ).smulRight
        ((trivializationAt ℂ L x (TotalSpace.mk' ℂ x (s x))).2))
      (chartAt ℂ x x) := by
  set φ := chartAt ℂ x
  set eL := trivializationAt ℂ L x
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hxe : x ∈ (pointTwistCore ℂ L x).baseSet (x, true) :=
    mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt ℂ L x, by simp⟩
  rw [signedPointTwistCore_trivializationAt_self ℂ L x true]
  -- The section read in the charts is `w ↦ (w - φ x) g(φ⁻¹ w)`.
  have hfeq : (fun w ↦ ((pointTwistCore ℂ L x).localTriv (x, true) (TotalSpace.mk' ℂ (φ.symm w)
        (pointTwistMul ℂ L x (φ.symm w) (s (φ.symm w))))).2) =ᶠ[𝓝 (φ x)]
      fun w ↦ (w - φ x) • (eL (TotalSpace.mk' ℂ (φ.symm w) (s (φ.symm w)))).2 := by
    filter_upwards [φ.open_target.mem_nhds (φ.map_source hxφ),
      (φ.continuousAt_symm (φ.map_source hxφ)).preimage_mem_nhds (by
        rw [φ.left_inv hxφ]
        exact ((pointTwistCore ℂ L x).isOpen_baseSet (x, true)).mem_nhds hxe)] with w hw hwe
    refine (pointTwistCore_localTriv_pointTwistMul hwe (s (φ.symm w))).trans ?_
    rw [pointTwistFactor_false_true, pointTwistCoord_chartAt_symm hw]
  exact hasFDerivAt_sub_smul_comp_chartAt_symm ((eL.continuousOn_snd_apply_mk hs).continuousAt
    (eL.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ L x))) hfeq

/-- **The local index at a zero is the sign of the Jacobian of its chart reading.** Let `σ` be a
continuous section of a complex line bundle `L` with fibre `ℂ` over a Riemann surface `X`,
vanishing at `x`. If the reading of `σ` in the chart `φ` of `X` at `x` and the chart of `L` at `x`
has, at `φ x`, a real derivative `D` with `det D ≠ 0`, then the local index of `σ` at `x`, for the
canonical orientations of `L` and `X`, is the sign of `det D`. Since `D` is injective, the zero is
isolated: the reading has no other zero near `φ x`. -/
theorem sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt (x : X) {σ : ∀ z, L z}
    (hσ : Continuous fun z ↦ TotalSpace.mk' ℂ z (σ z)) (hσx : σ x = 0) {D : ℂ →L[ℝ] ℂ}
    (hA : HasFDerivAt (preferredChartReading ℂ ℂ σ x) D (chartAt ℂ x x))
    (hD : D.det ≠ 0) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X) hσ x =
      SignType.sign D.det := by
  set φ := chartAt ℂ x
  set e := trivializationAt ℂ L x
  -- `D` is injective, hence antilipschitz, so the reading has no zero near `φ x` but `φ x`.
  have hker : LinearMap.ker (D : ℂ →ₗ[ℝ] ℂ) = ⊥ := (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hD))
  obtain ⟨K, -, hK⟩ := (D : ℂ →ₗ[ℝ] ℂ).exists_antilipschitzWith hker
  obtain ⟨U, hUo, hxU, hUz, hUe, hUφ, -⟩ :=
    VectorBundleOrientation.exists_isolating_nhds_of_hasFDerivAt
      (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)) Complex.finrank_real_complex e φ
      (mem_baseSet_trivializationAt ℂ L x) (mem_chart_source ℂ x) hσx hA ⟨K, hK⟩
  exact VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt _ _ _ _ e φ hUo hxU hUz
    hσx hUe hUφ
    (fun _ hy ↦ VectorBundleOrientation.mapOrientation_reindex_complex_eq_orientation _ _
      (hUe hy))
    (localHomologyMap_complexHomologicalOrientation_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (n := 1) x) (hUφ hxU))
    hA hD

/-- **A zero with nonzero complex-linear derivative has local index one.** Let `σ` be a continuous
section of a complex line bundle `L` with fibre `ℂ` over a Riemann surface `X`, vanishing at `x`.
If the reading of `σ` in the chart `φ` of `X` at `x` and the chart of `L` at `x` has, at `φ x`, the
real derivative of multiplication by a nonzero `c`, of determinant `|c|² > 0`, then the local index
of `σ` at `x` is `1`, for the canonical orientations of `L` and `X`. -/
theorem sectionIndex_eq_one_of_hasFDerivAt_smulRight (x : X) {σ : ∀ z, L z}
    (hσ : Continuous fun z ↦ TotalSpace.mk' ℂ z (σ z)) (hσx : σ x = 0) {c : ℂ} (hc : c ≠ 0)
    (hA : HasFDerivAt (preferredChartReading ℂ ℂ σ x) ((ContinuousLinearMap.id ℝ ℂ).smulRight c)
      (chartAt ℂ x x)) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X) hσ x = 1 := by
  -- Over `ℝ`, multiplication by `c` has determinant `|c|²`.
  have hdet : ((ContinuousLinearMap.id ℝ ℂ).smulRight c).det = Complex.normSq c := by
    simp [ContinuousLinearMap.det, LinearMap.det_complex, Complex.normSq_apply]
  rw [sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt x hσ hσx hA
    (hdet.trans_ne (Complex.normSq_pos.2 hc).ne'), hdet, sign_pos (Complex.normSq_pos.2 hc),
    SignType.coe_one]

omit [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] in
/-- **The local index of the twisted section at the twisting point is one.** For a continuous
section `s` of a complex line bundle `L` with `s x ≠ 0`, the section `pointTwistMul ∘ s` of the
point twist `L(x)` has a zero at `x` of local index `1`, for the canonical orientations of `L(x)`
and `X`. -/
theorem sectionIndex_pointTwistMul_self (x : X) {s : ∀ z, L z}
    (hs : Continuous fun z ↦ TotalSpace.mk' ℂ z (s z)) (hsx : s x ≠ 0) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ (pointTwistCore ℂ L x).Fiber)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X)
        (continuous_pointTwistMul_section (x := x) hs) x = 1 := by
  set eL := trivializationAt ℂ L x
  have hgx : (eL (TotalSpace.mk' ℂ x (s x))).2 ≠ 0 :=
    (eL.snd_apply_ne_zero_iff ℂ (v := TotalSpace.mk' ℂ x (s x))
      (mem_baseSet_trivializationAt ℂ L x)).2 hsx
  exact sectionIndex_eq_one_of_hasFDerivAt_smulRight (L := (pointTwistCore ℂ L x).Fiber) x
    (continuous_pointTwistMul_section hs)
    (congrArg (fun f : L x →L[ℂ] ℂ ↦ f (s x)) (pointTwistMul_self ℂ L x)) hgx
    (hasFDerivAt_pointTwistMul_chartAt x hs)

/-! ### The Euler number of the point twist -/

/-- **Twisting at a point raises the Euler number by one.** Let `L` be a complex line bundle over
a compact Riemann surface `X` and `x : X`. If `L` has a continuous section with finitely many zeros
that does not vanish at `x`, then the Euler class of the underlying oriented real plane bundle of
the point twist `L(x)`, evaluated on the fundamental class of `X`, is that of `L` plus one:
`⟨e(L(x)_ℝ), [X]⟩ = ⟨e(L_ℝ), [X]⟩ + 1`. -/
theorem evalFundamentalClass_complexEulerClass_pointTwist [CompactSpace X] (x : X)
    {s : ∀ z, L z} (hs : Continuous fun z ↦ TotalSpace.mk' ℂ z (s z))
    (hZ : {z | s z = 0}.Finite) (hsx : s x ≠ 0) :
    ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ (pointTwistCore ℂ L x).Fiber (r := 0) (finrank_self ℂ))).down =
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down + 1 := by
  classical
  have hZ' : {z | pointTwistMul ℂ L x z (s z) = 0} = insert x {z | s z = 0} := by
    ext z
    simp [pointTwistMul_eq_zero_iff]
  exact evalFundamentalClass_complexEulerClass_eq_add_one_of_setOf_eq_insert x hs
    (continuous_pointTwistMul_section hs) hZ hZ' hsx
    (fun _ hz ↦ sectionIndex_pointTwistMul_of_ne (finrank_self ℂ) hz hs)
    (sectionIndex_pointTwistMul_self x hs hsx)

end Line

/-- **The point twist of the trivial line bundle has Euler number one.** On a compact Riemann
surface `X`, the twist `𝒪(x)` of the trivial line bundle at a point satisfies
`⟨e(𝒪(x)_ℝ), [X]⟩ = 1`. On the Riemann sphere with `x = ∞` this is the Euler number
`⟨e(𝒪(∞)_ℝ), [ℙ¹]⟩ = 1`, hence `c₁(𝒪(1))[ℙ¹] = 1` by the native line first Chern
class definition. -/
theorem evalFundamentalClass_complexEulerClass_pointTwist_trivial [CompactSpace X] (x : X) :
    ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber (r := 0)
          (finrank_self ℂ))).down = 1 := by
  rw [evalFundamentalClass_complexEulerClass_pointTwist x (s := fun _ ↦ (1 : ℂ))
    ((Bundle.Trivial.isInducing_toProd X ℂ).continuous_iff.2
      (continuous_id.prodMk continuous_const)) (by simp) one_ne_zero, complexEulerClass_trivial]
  simp

end TauCeti
