/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.ChartLocalOrientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Basic
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
`L` with its canonical complex orientation (`TauCeti.complexEulerClass`), the class that the first
Chern class `c₁(L)` is compared with, and `[X]` is the fundamental class of the canonical
orientation of `X`. This is the Chern class half of step 4 of the proof of the Riemann–Roch
formula for real Cauchy–Riemann operators (McDuff–Salamon, Theorem C.1.10).

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
  (`TauCeti.localHomologyMap_sub_complexHomologicalOrientation`), so its local index is `1`
  (`TauCeti.sectionIndex_pointTwistMul_self`).

Summing over zeros
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`) gives the
formula. For the trivial bundle the constant section `1` gives `⟨e(𝒪(x)_ℝ), [X]⟩ = 1`
(`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_trivial`); on the Riemann sphere this
is `c₁(𝒪(1))[ℙ¹] = 1` (`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_infty`).

## Main results

* `TauCeti.continuous_pointTwistMul_section`: multiplication by the canonical section of `𝒪(x)`
  sends continuous sections of `E` to continuous sections of `E(x)`.
* `TauCeti.sectionIndex_pointTwistMul_of_ne` and `TauCeti.sectionIndex_pointTwistMul_self`: the
  local indices of the twisted section.
* `TauCeti.evalFundamentalClass_complexEulerClass_pointTwist`: the Euler number of `L(x)` is that
  of `L` plus one.
* `TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_trivial` and
  `TauCeti.evalFundamentalClass_complexEulerClass_pointTwist_infty`: the Euler number of the twist
  `𝒪(x)` of the trivial line bundle is one, in particular for `𝒪(1)` on the Riemann sphere.

## Implementation notes

The section `s` with finitely many zeros and `s x ≠ 0` is a hypothesis; any continuous section has
this property after a generic perturbation. The local index at `x` is computed for the model fibre
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

/-! ### Continuity of the twisted section -/

/-- Multiplication by the canonical section of `𝒪(x)` sends a section of `E` that is continuous
at `z₀` to a section of the point twist `E(x)` that is continuous at `z₀`. -/
theorem continuousAt_pointTwistMul_section {x z₀ : X} {σ : ∀ z, E z}
    (hσ : ContinuousAt (fun z ↦ TotalSpace.mk' F z (σ z)) z₀) :
    ContinuousAt (fun z ↦ TotalSpace.mk' F (E := (pointTwistCore F E x).Fiber) z
      (pointTwistMul F E x z (σ z))) z₀ := by
  classical
  have hz₀ : z₀ ∈ (pointTwistCore F E x).baseSet (z₀, decide (z₀ = x)) := by
    simpa using (pointTwistCore F E x).mem_baseSet_at z₀
  rw [FiberBundle.continuousAt_totalSpace] at hσ ⊢
  refine ⟨continuousAt_id, ?_⟩
  have hf : ContinuousAt (pointTwistFactor x false (decide (z₀ = x))) z₀ := by
    refine ContinuousOn.continuousAt ?_
      ((isOpen_pointTwistBaseSet x _).mem_nhds (mem_signedPointTwistCore_baseSet.1 hz₀).2)
    cases decide (z₀ = x)
    · exact continuousOn_const.congr fun z _ ↦ pointTwistFactor_self x false z
    · simp only [pointTwistBaseSet_true]
      refine ((chartAt ℂ x).continuousOn.sub (continuousOn_const (c := chartAt ℂ x x))).congr
        fun z _ ↦ ?_
      rw [pointTwistFactor_false_true, pointTwistCoord_apply]
      rfl
  refine (hf.smul hσ.2).congr_of_eventuallyEq ?_
  filter_upwards [((pointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  rw [signedPointTwistCore_trivializationAt]
  exact pointTwistCore_localTriv_pointTwistMul hz (σ z)

/-- Multiplication by the canonical section of `𝒪(x)` sends continuous sections of `E` to
continuous sections of the point twist `E(x)`. -/
theorem continuous_pointTwistMul_section {x : X} {σ : ∀ z, E z}
    (hσ : Continuous fun z ↦ TotalSpace.mk' F z (σ z)) :
    Continuous fun z ↦ TotalSpace.mk' F (E := (pointTwistCore F E x).Fiber) z
      (pointTwistMul F E x z (σ z)) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_pointTwistMul_section hσ.continuousAt

/-- Away from `x`, the twisted section vanishes exactly where the section does. -/
theorem pointTwistMul_eq_zero_iff_of_ne {x z : X} (h : z ≠ x) (v : E z) :
    pointTwistMul F E x z v = 0 ↔ v = 0 := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ by rw [hv, map_zero]⟩
  rw [← pointTwistDiv_pointTwistMul (F := F) h v, hv, map_zero]

/-- The twisted section vanishes exactly at `x` and at the zeros of the section. -/
theorem pointTwistMul_eq_zero_iff {x z : X} (v : E z) :
    pointTwistMul F E x z v = 0 ↔ z = x ∨ v = 0 := by
  by_cases h : z = x
  · subst h
    simp
  · rw [pointTwistMul_eq_zero_iff_of_ne h]
    simp [h]

/-! ### Local indices of the twisted section -/

variable [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ z, Module ℝ (E z)] [∀ z, IsScalarTower ℝ ℂ (E z)]

/-- The fibres of the signed point twist are real vector spaces through the model fibre. -/
instance signedPointTwistCore.moduleRealFiber (x : X) (s : Bool) (z : X) :
    Module ℝ ((signedPointTwistCore F E x s).Fiber z) :=
  inferInstanceAs (Module ℝ F)

/-- The real and complex scalar actions on the fibres of the signed point twist are compatible. -/
instance signedPointTwistCore.isScalarTowerFiber (x : X) (s : Bool) (z : X) :
    IsScalarTower ℝ ℂ ((signedPointTwistCore F E x s).Fiber z) :=
  inferInstanceAs (IsScalarTower ℝ ℂ F)

local instance instVectorBundleRealPointTwistEuler : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

local instance instVectorBundleRealPointTwistCoreEuler (x : X) :
    VectorBundle ℝ F (pointTwistCore F E x).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F _

omit [ChartedSpace ℂ X] [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- A complex-linear trivialization of the atlas of a complex line bundle reads the canonical
orientation, indexed by `Fin 2`, as the canonical orientation of the model fibre. -/
private theorem mapOrientation_reindex_complex {V : X → Type} [∀ z, AddCommGroup (V z)]
    [∀ z, Module ℂ (V z)] [∀ z, Module ℝ (V z)] [∀ z, IsScalarTower ℝ ℂ (V z)]
    [∀ z, TopologicalSpace (V z)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
    [VectorBundle ℂ F V] (hF : finrank ℂ F = 1)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] [e.IsLinear ℝ] {z : X}
    (hz : z ∈ e.baseSet) :
    e.mapOrientation (Fin (1 + 1)) hz
        (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
          (VectorBundleOrientation.complex F V) z) =
      Orientation.reindex ℝ F (finCongr (by rw [hF])) (complexOrientation F) := by
  rw [VectorBundleOrientation.reindex_apply, Trivialization.mapOrientation_reindex]
  congr 1
  convert VectorBundleOrientation.mapOrientation_complex F V e hz

variable (hF : finrank ℂ F = 1) (hFℝ : finrank ℝ F = 1 + 1)

/-- **Local indices of the twisted section away from the twisting point.** Away from `x`, a
continuous section `s` of a complex line bundle `L` and the section `pointTwistMul ∘ s` of the
point twist `L(x)` have the same local index, for the canonical orientations of `L`, `L(x)` and
`X`. -/
theorem sectionIndex_pointTwistMul_of_ne {x z : X} (hzx : z ≠ x) {s : ∀ z, E z}
    (hs : Continuous fun z ↦ TotalSpace.mk' F z (s z)) :
    (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F (pointTwistCore F E x).Fiber)).sectionIndex hFℝ
        (complexHomologicalOrientation X) (continuous_pointTwistMul_section (x := x) hs) z =
      (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F E)).sectionIndex hFℝ
        (complexHomologicalOrientation X) hs z := by
  classical
  by_cases hiso : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ y ∈ U, s y = 0 → y = z
  · obtain ⟨U, hU, hzU, hUz⟩ := hiso
    -- Shrink `U` into the base set of the chart `(z, false)` of the point twist.
    set V := U ∩ (pointTwistCore F E x).baseSet (z, false)
    have hV : IsOpen V := hU.inter ((pointTwistCore F E x).isOpen_baseSet _)
    have hzV : z ∈ V := ⟨hzU, mem_signedPointTwistCore_baseSet.2
      ⟨mem_baseSet_trivializationAt F E z, by simpa using hzx⟩⟩
    have hVe₁ : V ⊆ (trivializationAt F E z).baseSet := fun _ hy ↦
      (mem_signedPointTwistCore_baseSet.1 hy.2).1
    have hVe₂ : V ⊆ (trivializationAt F (pointTwistCore F E x).Fiber z).baseSet := fun _ hy ↦ by
      rw [signedPointTwistCore_trivializationAt_of_ne hzx]
      exact hy.2
    refine VectorBundleOrientation.sectionIndex_eq_of_snd_apply_eq (E₁ := E)
      (E₂ := (pointTwistCore F E x).Fiber) _ _ hFℝ _ hs _
      (trivializationAt F E z) (trivializationAt F (pointTwistCore F E x).Fiber z) hV hzV
      (fun y hy ↦ hUz y hy.1) hVe₁ hVe₂ (fun y hy ↦ mapOrientation_reindex_complex (V := E) hF _ _)
      (fun y hy ↦ mapOrientation_reindex_complex (V := (pointTwistCore F E x).Fiber) hF _ _)
      fun y hy ↦ ?_
    rw [signedPointTwistCore_trivializationAt_of_ne hzx]
    refine (pointTwistCore_localTriv_pointTwistMul hy.2 (s y)).trans ?_
    rw [pointTwistFactor_self, one_smul]
  · -- If `z` is not an isolated zero of `s`, it is not an isolated zero of the twisted section.
    have hiso' : ¬ ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ y ∈ U, pointTwistMul F E x y (s y) = 0 → y = z := by
      rintro ⟨U, hU, hzU, hUz⟩
      refine hiso ⟨U ∩ {x}ᶜ, hU.inter isOpen_compl_singleton, ⟨hzU, hzx⟩, fun y hy h0 ↦ ?_⟩
      exact hUz y hy.1 ((pointTwistMul_eq_zero_iff_of_ne hy.2 _).2 h0)
    exact (VectorBundleOrientation.sectionIndex_of_not_isolated
      (E := (pointTwistCore F E x).Fiber) _ _ _ _ hiso').trans
      (VectorBundleOrientation.sectionIndex_of_not_isolated _ _ _ _ hiso).symm

/-! ### The local index at the twisting point -/

/-- A function `w ↦ (w - w₀) g(w)` on `ℂ`, with `g` merely continuous at `w₀`, has real derivative
multiplication by `g w₀` at `w₀`. -/
private theorem hasFDerivAt_sub_mul_of_continuousAt {G : ℂ → ℂ} {w₀ : ℂ}
    (hG : ContinuousAt G w₀) :
    HasFDerivAt (fun w ↦ (w - w₀) * G w) (ContinuousLinearMap.mul ℝ ℂ (G w₀)) w₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have ht : Tendsto (fun h ↦ G (w₀ + h) - G w₀) (𝓝 0) (𝓝 0) := by
    rw [tendsto_sub_nhds_zero_iff]
    exact hG.tendsto.comp ((continuous_const_add w₀).tendsto' 0 w₀ (add_zero w₀))
  have key : (fun h : ℂ ↦ (G (w₀ + h) - G w₀) * h) =o[𝓝 0] fun h ↦ h := by
    simpa using ((Asymptotics.isLittleO_one_iff ℂ).2 ht).mul_isBigO
      (Asymptotics.isBigO_refl (fun h : ℂ ↦ h) (𝓝 0))
  refine key.congr_left fun h ↦ ?_
  simp only [add_sub_cancel_left, sub_self, zero_mul, sub_zero, ContinuousLinearMap.mul_apply']
  ring

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
/-- In the chart of `X` at `x` and the chart `(x, true)` of the point twist, the twisted section
reads `w ↦ (w - φ x) g(φ⁻¹ w)`, where `g` is the fibre coordinate of `s` in the chart of `L` at
`x`. Its real derivative at `φ x` is multiplication by `g x`. -/
private theorem hasFDerivAt_pointTwistMul_chartAt (x : X) {s : ∀ z, L z}
    (hs : Continuous fun z ↦ TotalSpace.mk' ℂ z (s z)) :
    HasFDerivAt (fun w ↦ (trivializationAt ℂ (pointTwistCore ℂ L x).Fiber x
        (TotalSpace.mk' ℂ ((chartAt ℂ x).symm w)
          (pointTwistMul ℂ L x ((chartAt ℂ x).symm w) (s ((chartAt ℂ x).symm w))))).2)
      (ContinuousLinearMap.mul ℝ ℂ ((trivializationAt ℂ L x (TotalSpace.mk' ℂ x (s x))).2))
      (chartAt ℂ x x) := by
  classical
  set φ := chartAt ℂ x
  set eL := trivializationAt ℂ L x
  set e := trivializationAt ℂ (pointTwistCore ℂ L x).Fiber x
  set g : X → ℂ := fun z ↦ (eL (TotalSpace.mk' ℂ z (s z))).2
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have he : e = (pointTwistCore ℂ L x).localTriv (x, true) :=
    signedPointTwistCore_trivializationAt_self ℂ L x true
  -- The section read in the charts is `w ↦ (w - φ x) g(φ⁻¹ w)`.
  have hfeq : (fun w ↦ (e (TotalSpace.mk' ℂ (φ.symm w)
        (pointTwistMul ℂ L x (φ.symm w) (s (φ.symm w))))).2) =ᶠ[𝓝 (φ x)]
      fun w ↦ (w - φ x) * (g ∘ φ.symm) w := by
    filter_upwards [φ.open_target.mem_nhds (φ.map_source hxφ),
      (φ.continuousAt_symm (φ.map_source hxφ)).preimage_mem_nhds
        (by rw [φ.left_inv hxφ]; exact e.open_baseSet.mem_nhds hxe)] with w hw hwe
    have hz : φ.symm w ∈ (pointTwistCore ℂ L x).baseSet (x, true) := by
      rw [he] at hwe
      exact hwe
    rw [he]
    refine (pointTwistCore_localTriv_pointTwistMul hz (s (φ.symm w))).trans ?_
    rw [pointTwistFactor_false_true, pointTwistCoord_chartAt_symm hw, smul_eq_mul]
    rfl
  have hg : ContinuousAt g x :=
    (continuous_snd.comp_continuousOn (eL.continuousOn.comp hs.continuousOn
      fun _ hz ↦ eL.mem_source.2 hz)).continuousAt
      (eL.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ L x))
  have hG : ContinuousAt (g ∘ φ.symm) (φ x) :=
    ContinuousAt.comp_of_eq hg (φ.continuousAt_symm (φ.map_source hxφ)) (φ.left_inv hxφ)
  have hA := (hasFDerivAt_sub_mul_of_continuousAt hG).congr_of_eventuallyEq hfeq
  rwa [Function.comp_apply, φ.left_inv hxφ] at hA

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
  classical
  set φ := chartAt ℂ x
  set eL := trivializationAt ℂ L x
  set e := trivializationAt ℂ (pointTwistCore ℂ L x).Fiber x
  -- The fibre coordinate `g` of `s` in the chart of `L` at `x`.
  set g : X → ℂ := fun z ↦ (eL (TotalSpace.mk' ℂ z (s z))).2
  have hg : ContinuousOn g eL.baseSet :=
    continuous_snd.comp_continuousOn
      (eL.continuousOn.comp hs.continuousOn fun _ hz ↦ eL.mem_source.2 hz)
  have hxL : x ∈ eL.baseSet := mem_baseSet_trivializationAt ℂ L x
  have hgx : g x ≠ 0 := (eL.snd_apply_ne_zero_iff ℂ (v := TotalSpace.mk' ℂ x (s x)) hxL).2 hsx
  have he : e = (pointTwistCore ℂ L x).localTriv (x, true) :=
    signedPointTwistCore_trivializationAt_self ℂ L x true
  have hmem : ∀ {z}, z ∈ e.baseSet ↔ z ∈ (pointTwistCore ℂ L x).baseSet (x, true) := by
    intro z
    rw [he]
    rfl
  have heb : ∀ {z}, z ∈ e.baseSet → z ∈ eL.baseSet ∧ z ∈ φ.source := fun hz ↦ by
    simpa using mem_signedPointTwistCore_baseSet.1 (hmem.1 hz)
  -- The neighbourhood `U` of `x` on which `s` does not vanish.
  set U := e.baseSet ∩ (eL.baseSet ∩ g ⁻¹' {0}ᶜ)
  have hU : IsOpen U :=
    e.open_baseSet.inter (hg.isOpen_inter_preimage eL.open_baseSet isOpen_compl_singleton)
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have hxU : x ∈ U := ⟨hxe, hxL, hgx⟩
  have hUz : ∀ y ∈ U, pointTwistMul ℂ L x y (s y) = 0 → y = x := fun y hy h0 ↦ by
    by_contra hyx
    have hsy := (pointTwistMul_eq_zero_iff_of_ne hyx (s y)).1 h0
    exact hy.2.2 ((not_not.1 fun h ↦
      (eL.snd_apply_ne_zero_iff ℂ (v := TotalSpace.mk' ℂ y (s y)) hy.2.1).1 h hsy))
  have hUφ : U ⊆ φ.source := fun _ hy ↦ (heb hy.1).2
  have hω : Orientation.reindex ℝ ℂ (finCongr (by rw [finrank_self])) (complexOrientation ℂ) =
      Complex.orientation :=
    reindex_complexOrientation_complex
  have hA := hasFDerivAt_pointTwistMul_chartAt x hs
  -- Over `ℝ`, multiplication by `g x` has determinant `|g x|²`.
  have hdet' : (ContinuousLinearMap.mul ℝ ℂ (g x)).det = Complex.normSq (g x) := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hdet : (ContinuousLinearMap.mul ℝ ℂ (g x)).det ≠ 0 := by
    rw [hdet']
    exact (Complex.normSq_pos.2 hgx).ne'
  rw [VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt _ _ _ _ e φ hU hxU hUz
    (pointTwistMul_self ℂ L x ▸ rfl) inter_subset_left hUφ
    (fun y hy ↦ (mapOrientation_reindex_complex (V := (pointTwistCore ℂ L x).Fiber)
      (finrank_self ℂ) e (inter_subset_left hy)).trans hω)
    (localHomologyMap_sub_complexHomologicalOrientation (k := 1)
      (IsManifold.chart_mem_maximalAtlas x) (hUφ hxU) _) hA hdet, hdet',
    sign_pos (Complex.normSq_pos.2 hgx), SignType.coe_one]

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
  have hZx : {z | pointTwistMul ℂ L x z (s z) = 0}.Finite := hZ' ▸ hZ.insert x
  rw [complexEulerClass_def, complexEulerClass_def,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _
      (continuous_pointTwistMul_section (x := x) hs) _ hZx,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hs _ hZ]
  have hfin : hZx.toFinset = insert x hZ.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, hZ']
    rfl
  have hx : x ∉ hZ.toFinset := by simpa using hsx
  refine (Finset.sum_congr hfin fun _ _ ↦ rfl).trans ?_
  rw [Finset.sum_insert hx, add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun z hz ↦
      sectionIndex_pointTwistMul_of_ne (finrank_self ℂ) Complex.finrank_real_complex
        (by rintro rfl; exact hx hz) hs
  · exact sectionIndex_pointTwistMul_self x hs hsx

end Line

/-- **The point twist of the trivial line bundle has Euler number one.** On a compact Riemann
surface `X`, the twist `𝒪(x)` of the trivial line bundle at a point satisfies
`⟨e(𝒪(x)_ℝ), [X]⟩ = 1`. On the Riemann sphere with `x = ∞` this is `c₁(𝒪(1))[ℙ¹] = 1`. -/
theorem evalFundamentalClass_complexEulerClass_pointTwist_trivial [CompactSpace X] (x : X) :
    ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber (r := 0)
          (finrank_self ℂ))).down = 1 := by
  rw [evalFundamentalClass_complexEulerClass_pointTwist x (s := fun _ ↦ (1 : ℂ))
    ((Bundle.Trivial.isInducing_toProd X ℂ).continuous_iff.2
      (continuous_id.prodMk continuous_const)) (by simp) one_ne_zero, complexEulerClass_trivial]
  simp

/-- **The Euler number of `𝒪(1)` on the Riemann sphere is one**: the twist at `∞` of the trivial
line bundle over `OnePoint ℂ` satisfies `⟨e(𝒪(∞)_ℝ), [ℙ¹]⟩ = 1`. Its holomorphic section `z`
(`TauCeti.contMDiff_pointTwistOfPole_affineChart`) has the single simple zero `0`. -/
theorem evalFundamentalClass_complexEulerClass_pointTwist_infty :
    ((complexHomologicalOrientation (OnePoint ℂ)).evalFundamentalClass
        Complex.finrank_real_complex (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id _)
        (complexEulerClass ℂ (pointTwistCore ℂ (Bundle.Trivial (OnePoint ℂ) ℂ) OnePoint.infty).Fiber
          (r := 0) (finrank_self ℂ))).down = 1 :=
  evalFundamentalClass_complexEulerClass_pointTwist_trivial _

end TauCeti
