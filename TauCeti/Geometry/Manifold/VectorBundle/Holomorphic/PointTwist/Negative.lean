/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.EulerClass

/-!
# The Euler number of a negative point twist

Let `X` be a compact Riemann surface, `L → X` a complex line bundle with model fibre `ℂ`, and
`x : X`. The negative point twist `L(-x)` (`TauCeti.signedPointTwistCore` with sign `false`) is
glued from `L` over `X ∖ {x}` and from the frames of `L` multiplied by the centred chart coordinate
over the chart disc at `x`; its sections are the sections of `L` vanishing at `x`. This file proves
that twisting negatively at a point lowers the Euler number of the underlying oriented real plane
bundle by one:
`⟨e(L(-x)_ℝ), [X]⟩ = ⟨e(L_ℝ), [X]⟩ - 1`
(`TauCeti.evalFundamentalClass_complexEulerClass_negPointTwist`). Together with the positive twist
(`TauCeti.evalFundamentalClass_complexEulerClass_pointTwist`) this is the Chern-number bookkeeping
of step 5 of the proof of the Riemann–Roch formula for real Cauchy–Riemann operators
(McDuff–Salamon, Theorem C.1.10), where the trivial bundle is twisted at the positive zeros of a
section and negatively at its negative zeros.

The proof counts zeros. The inclusion of `L(-x)` into `L` is multiplication by the canonical
section of `𝒪(x)`; on fibres it is `TauCeti.pointTwistDiv`, an isomorphism off `x` and zero at
`x`. Let `τ` be a continuous section of `L(-x)` with finitely many zeros,
nonzero at `x`. Then `σ = pointTwistDiv ∘ τ` is a continuous section of `L`
(`TauCeti.continuous_pointTwistDiv_section`) whose zeros are those of `τ` together with `x`.

* Away from `x`, the two sections have the same fibre coordinates in the preferred charts of `L`
  and the charts `(z, false)` of `L(-x)`, so they have the same local index
  (`TauCeti.sectionIndex_pointTwistDiv_of_ne`).
* At `x`, the section `σ` reads `w ↦ (w - φ x) g(w)` in the chart `φ` of `X` at `x` and the chart
  of `L` at `x`, where `g` is the reading of `τ` in the chart `(x, true)` of `L(-x)`. Its derivative
  at `φ x` is multiplication by `g (φ x) ≠ 0`, of determinant `|g (φ x)|² > 0` over `ℝ`, so its
  local index is `1` (`TauCeti.sectionIndex_pointTwistDiv_self`).

Summing over zeros gives `⟨e(L_ℝ), [X]⟩ = ⟨e(L(-x)_ℝ), [X]⟩ + 1`.

## Main results

* `TauCeti.trivializationAt_pointTwistDiv_signed`: the inclusion `pointTwistDiv` of `L(-x)` into
  `L`, read in the charts.
* `TauCeti.continuous_pointTwistDiv_section`: it sends continuous sections to continuous
  sections.
* `TauCeti.sectionIndex_pointTwistDiv_of_ne` and `TauCeti.sectionIndex_pointTwistDiv_self`:
  the local indices of the included section.
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

/-! ### The inclusion of the negative twist -/

open Classical in
/-- In every chart `(y, b)` of the negative point twist, its inclusion into `E` reads, in the chart
of `E` at `y`, as the scalar `pointTwistFactor x false b` times the coordinate in the chart
`(y, b)`. -/
theorem trivializationAt_pointTwistDiv_signed {x z : X} {i : X × Bool}
    (hz : z ∈ (signedPointTwistCore F E x false).baseSet i) (w : F) :
    (trivializationAt F E i.1 ⟨z, pointTwistDiv F E x z w⟩).2 =
      pointTwistFactor x false i.2 z •
        ((signedPointTwistCore F E x false).localTriv i ⟨z, w⟩).2 := by
  have h₀ : z ∈ (trivializationAt F E z).baseSet := mem_baseSet_trivializationAt F E z
  have hz' := mem_signedPointTwistCore_baseSet.1 hz
  rw [signedPointTwistCore_localTriv_apply, signedPointTwistFactor_false, smul_smul, mul_comm,
    pointTwistFactor_mul_false hz'.2 (mem_pointTwistBaseSet_decide x z), pointTwistDiv_apply,
    inv_pointTwistFactor_false_decide,
    ← map_smul, Trivialization.coordChangeL_apply _ _ ⟨h₀, hz'.1⟩]

/-- The included vector vanishes exactly at `x` and where the vector does. -/
theorem pointTwistDiv_eq_zero_iff {x z : X} (w : F) :
    pointTwistDiv F E x z w = 0 ↔ z = x ∨ w = 0 := by
  by_cases h : z = x
  · subst h
    simp
  · simp only [h, false_or]
    exact map_eq_zero_iff _ (pointTwistDiv_bijective_of_ne h).1

/-- The inclusion of the negative point twist sends a section continuous at `z₀` to a section of
`E` continuous at `z₀`. -/
theorem continuousAt_pointTwistDiv_section {x z₀ : X}
    {τ : ∀ z, (signedPointTwistCore F E x false).Fiber z}
    (hτ : ContinuousAt (fun z ↦ TotalSpace.mk' F z (τ z)) z₀) :
    ContinuousAt (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) z₀ := by
  classical
  have hz₀ : z₀ ∈ (signedPointTwistCore F E x false).baseSet (z₀, decide (z₀ = x)) := by
    simpa using (signedPointTwistCore F E x false).mem_baseSet_at z₀
  rw [FiberBundle.continuousAt_totalSpace] at hτ ⊢
  refine ⟨continuousAt_id, ?_⟩
  have hf : ContinuousAt (pointTwistFactor x false (decide (z₀ = x))) z₀ :=
    (contMDiffOn_pointTwistFactor_false (n := 0) x _).continuousOn.continuousAt
      ((isOpen_pointTwistBaseSet x _).mem_nhds (mem_signedPointTwistCore_baseSet.1 hz₀).2)
  rw [signedPointTwistCore_trivializationAt] at hτ
  refine (hf.smul hτ.2).congr_of_eventuallyEq ?_
  filter_upwards [((signedPointTwistCore F E x false).isOpen_baseSet _).mem_nhds hz₀] with z hz
  exact trivializationAt_pointTwistDiv_signed (i := (z₀, decide (z₀ = x))) hz (τ z)

/-- The inclusion of the negative point twist sends continuous sections to continuous sections. -/
theorem continuous_pointTwistDiv_section {x : X}
    {τ : ∀ z, (signedPointTwistCore F E x false).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' F z (τ z)) :
    Continuous fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z)) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_pointTwistDiv_section hτ.continuousAt

/-! ### Local indices of the included section -/

variable [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ z, Module ℝ (E z)] [∀ z, IsScalarTower ℝ ℂ (E z)]

local instance instVectorBundleRealNegPointTwist : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

local instance instVectorBundleRealNegPointTwistCore (x : X) :
    VectorBundle ℝ F (signedPointTwistCore F E x false).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F _

variable (hF : finrank ℂ F = 1)

/-- **Local indices of the included section away from the twisting point.** Away from `x`, a
continuous section `τ` of the negative point twist `L(-x)` of a complex line bundle `L` and the
section `pointTwistDiv ∘ τ` of `L` have the same local index, for the canonical orientations of
`L`, `L(-x)` and `X`. -/
theorem sectionIndex_pointTwistDiv_of_ne {x z : X} (hzx : z ≠ x)
    {τ : ∀ z, (signedPointTwistCore F E x false).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' F z (τ z)) :
    (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F E)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF])
        (complexHomologicalOrientation X) (continuous_pointTwistDiv_section hτ) z =
      (VectorBundleOrientation.reindex (finCongr (by rw [hF]))
        (VectorBundleOrientation.complex F (signedPointTwistCore F E x false).Fiber)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF])
        (complexHomologicalOrientation X) hτ z := by
  classical
  -- The chart `(z, false)` of the negative twist lies over the preferred chart of `E` at `z`.
  have hzV : z ∈ (signedPointTwistCore F E x false).baseSet (z, false) :=
    mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E z, by simpa using hzx⟩
  have hVe₁ : (signedPointTwistCore F E x false).baseSet (z, false) ⊆
      (trivializationAt F (signedPointTwistCore F E x false).Fiber z).baseSet := fun _ hy ↦ by
    rwa [signedPointTwistCore_trivializationAt_of_ne hzx]
  have hVe₂ : (signedPointTwistCore F E x false).baseSet (z, false) ⊆
      (trivializationAt F E z).baseSet := fun _ hy ↦ (mem_signedPointTwistCore_baseSet.1 hy).1
  refine VectorBundleOrientation.sectionIndex_eq_of_snd_apply_eq
    (E₁ := (signedPointTwistCore F E x false).Fiber) (E₂ := E) _ _ _ _ hτ _
    (trivializationAt F (signedPointTwistCore F E x false).Fiber z) (trivializationAt F E z)
    ((signedPointTwistCore F E x false).isOpen_baseSet _) hzV hVe₁ hVe₂
    (fun _ _ ↦ VectorBundleOrientation.mapOrientation_reindex_complex F _ _ _ _)
    (fun _ _ ↦ VectorBundleOrientation.mapOrientation_reindex_complex F E _ _ _) fun y hy ↦ ?_
  rw [signedPointTwistCore_trivializationAt_of_ne hzx]
  refine (trivializationAt_pointTwistDiv_signed (i := (z, false)) hy (τ y)).trans ?_
  rw [pointTwistFactor_self, one_smul]

/-! ### The local index at the twisting point -/

section Line

variable {L : X → Type} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealLineNegPointTwist : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

local instance instVectorBundleRealLineNegPointTwistCore (x : X) :
    VectorBundle ℝ ℂ (signedPointTwistCore ℂ L x false).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] in
/-- In the chart `φ` of `X` at `x` and the chart of `L` at `x`, the included section reads
`w ↦ (w - φ x) g(φ⁻¹ w)`, where `g` is the fibre coordinate of `τ` in the chart of `L(-x)` at `x`.
Its real derivative at `φ x` is multiplication by `g x`. -/
private theorem hasFDerivAt_pointTwistDiv_chartAt (x : X)
    {τ : ∀ z, (signedPointTwistCore ℂ L x false).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' ℂ z (τ z)) :
    HasFDerivAt (fun w ↦ (trivializationAt ℂ L x (TotalSpace.mk' ℂ ((chartAt ℂ x).symm w)
          (pointTwistDiv ℂ L x ((chartAt ℂ x).symm w) (τ ((chartAt ℂ x).symm w))))).2)
      ((ContinuousLinearMap.id ℝ ℂ).smulRight
        ((trivializationAt ℂ (signedPointTwistCore ℂ L x false).Fiber x
          (TotalSpace.mk' ℂ x (τ x))).2))
      (chartAt ℂ x x) := by
  set φ := chartAt ℂ x
  set eN := trivializationAt ℂ (signedPointTwistCore ℂ L x false).Fiber x
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
    have hwe' : φ.symm w ∈ (signedPointTwistCore ℂ L x false).baseSet (x, true) := by
      simpa using mem_signedPointTwistCore_trivializationAt_baseSet.1 hwe
    refine (trivializationAt_pointTwistDiv_signed (i := (x, true)) hwe' (τ (φ.symm w))).trans ?_
    rw [pointTwistFactor_false_true, pointTwistCoord_chartAt_symm hw,
      show eN = _ from signedPointTwistCore_trivializationAt_self ℂ L x false]
  have hG : ContinuousAt ((fun z ↦ (eN (TotalSpace.mk' ℂ z (τ z))).2) ∘ φ.symm) (φ x) :=
    ContinuousAt.comp_of_eq ((eN.continuousOn_snd_apply_mk hτ).continuousAt
      (eN.open_baseSet.mem_nhds hxN)) (φ.continuousAt_symm (φ.map_source hxφ)) (φ.left_inv hxφ)
  have hA := (((hasFDerivAt_id (𝕜 := ℝ) (φ x)).sub_const (φ x)).smul_of_eq_zero hG
    (sub_self _)).congr_of_eventuallyEq hfeq
  rwa [Function.comp_apply, φ.left_inv hxφ] at hA

/-- **The local index of the included section at the twisting point is one.** For a continuous
section `τ` of the negative point twist `L(-x)` with `τ x ≠ 0`, the section `pointTwistDiv ∘ τ`
of `L` has a zero at `x` of local index `1`, for the canonical orientations of `L` and `X`. -/
theorem sectionIndex_pointTwistDiv_self (x : X)
    {τ : ∀ z, (signedPointTwistCore ℂ L x false).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' ℂ z (τ z)) (hτx : τ x ≠ 0) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X)
        (continuous_pointTwistDiv_section hτ) x = 1 := by
  classical
  set φ := chartAt ℂ x
  set e := trivializationAt ℂ L x
  set eN := trivializationAt ℂ (signedPointTwistCore ℂ L x false).Fiber x
  -- The fibre coordinate `g` of `τ` in the chart of `L(-x)` at `x`.
  set g : X → ℂ := fun z ↦ (eN (TotalSpace.mk' ℂ z (τ z))).2
  have hxN : x ∈ eN.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have hgx : g x ≠ 0 := (eN.snd_apply_ne_zero_iff ℂ (v := TotalSpace.mk' ℂ x (τ x)) hxN).2 hτx
  have heb : ∀ {z}, z ∈ eN.baseSet → z ∈ e.baseSet ∧ z ∈ φ.source := fun hz ↦ by
    simpa using mem_signedPointTwistCore_baseSet.1
      (mem_signedPointTwistCore_trivializationAt_baseSet.1 hz)
  -- The neighbourhood `U` of `x` on which `τ` does not vanish.
  set U := eN.baseSet ∩ g ⁻¹' {0}ᶜ
  have hU : IsOpen U :=
    (eN.continuousOn_snd_apply_mk hτ).isOpen_inter_preimage eN.open_baseSet isOpen_compl_singleton
  have hxU : x ∈ U := ⟨hxN, hgx⟩
  have hUz : ∀ y ∈ U, pointTwistDiv ℂ L x y (τ y) = 0 → y = x := fun y hy h0 ↦ by
    refine ((pointTwistDiv_eq_zero_iff (F := ℂ) (E := L) (τ y)).1 h0).resolve_right fun hτy ↦
      hy.2 ?_
    change g y = 0
    simp only [g, hτy]
    exact congrArg Prod.snd (eN.zeroSection ℂ hy.1)
  have hUφ : U ⊆ φ.source := fun _ hy ↦ (heb hy.1).2
  have hA := hasFDerivAt_pointTwistDiv_chartAt x hτ
  -- Over `ℝ`, multiplication by `g x` has determinant `|g x|²`.
  have hdet' : ((ContinuousLinearMap.id ℝ ℂ).smulRight (g x)).det = Complex.normSq (g x) := by
    simp [ContinuousLinearMap.det, LinearMap.det_complex, Complex.normSq_apply]
  rw [VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt _ _ _ _ e φ hU hxU hUz
    (by rw [pointTwistDiv_self]; rfl) (fun _ hy ↦ (heb hy.1).1) hUφ
    (fun _ hy ↦ (VectorBundleOrientation.mapOrientation_reindex_complex ℂ L _ e
      (heb hy.1).1).trans reindex_complexOrientation_complex)
    (by
      rw [complexHomologicalOrientation_apply x]
      have hσ : (((ContinuousLinearEquiv.refl ℝ ℂ : ℂ →L[ℝ] ℂ) : C(ℂ, ℂ)).comp
          ((⟨fun y ↦ y - φ x, by fun_prop⟩ : C(ℂ, ℂ)).comp φ.sourceRestrict)) =
          (⟨fun y : φ.source ↦ φ y - φ x,
            φ.continuousOn.domRestrict.sub continuous_const⟩ : C(φ.source, ℂ)) :=
        ContinuousMap.ext fun y ↦ congrArg (fun z ↦ z - φ x) (φ.sourceRestrict_apply y)
      have hφ := φ.localHomologyMap_chart_localOrientationOfOrientedChart (hUφ hxU)
        (ContinuousLinearEquiv.refl ℝ ℂ) Complex.orientation
        Complex.finrank_real_complex Complex.finrank_real_complex (by
          rw [hσ]
          exact fun y hy ↦ Subtype.ext (φ.injOn y.property (hUφ hxU) (sub_eq_zero.1 hy)))
      simp only [hσ] at hφ
      -- `Orientation.map` uses the underlying linear identity, not the continuous structure.
      have hid : (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv = LinearEquiv.refl ℝ ℂ := (rfl)
      simpa only [hid, Orientation.map_refl, Equiv.refl_apply] using hφ)
    hA (hdet'.trans_ne (Complex.normSq_pos.2 hgx).ne'), hdet',
    sign_pos (Complex.normSq_pos.2 hgx), SignType.coe_one]

/-! ### The Euler number of the negative point twist -/

/-- **Twisting negatively at a point lowers the Euler number by one.** Let `L` be a complex line
bundle over a compact Riemann surface `X` and `x : X`. If the negative point twist `L(-x)` has a
continuous section with finitely many zeros that does not vanish at `x`, then the Euler class of
the underlying oriented real plane bundle of `L(-x)`, evaluated on the fundamental class of `X`, is
that of `L` minus one:
`⟨e(L(-x)_ℝ), [X]⟩ = ⟨e(L_ℝ), [X]⟩ - 1`. -/
theorem evalFundamentalClass_complexEulerClass_negPointTwist [CompactSpace X] (x : X)
    {τ : ∀ z, (signedPointTwistCore ℂ L x false).Fiber z}
    (hτ : Continuous fun z ↦ TotalSpace.mk' ℂ z (τ z))
    (hZ : {z | τ z = 0}.Finite) (hτx : τ x ≠ 0) :
    ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ (signedPointTwistCore ℂ L x false).Fiber (r := 0)
          (finrank_self ℂ))).down =
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down - 1 := by
  classical
  have hZ' : {z | pointTwistDiv ℂ L x z (τ z) = 0} = insert x {z | τ z = 0} := by
    ext z
    simp only [mem_ofPred_eq, mem_insert_iff]
    exact pointTwistDiv_eq_zero_iff (F := ℂ) (E := L) _
  have hZx : {z | pointTwistDiv ℂ L x z (τ z) = 0}.Finite := hZ' ▸ hZ.insert x
  rw [eq_sub_iff_add_eq, complexEulerClass_def, complexEulerClass_def,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hτ _ hZ,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _
      (continuous_pointTwistDiv_section hτ) _ hZx]
  have hfin : hZx.toFinset = insert x hZ.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, hZ', Set.mem_insert_iff]
  have hx : x ∉ hZ.toFinset := by simpa using hτx
  refine Eq.trans ?_ (Finset.sum_congr hfin fun _ _ ↦ rfl).symm
  rw [Finset.sum_insert hx, add_comm]
  congr 1
  · exact (sectionIndex_pointTwistDiv_self x hτ hτx).symm
  · exact Finset.sum_congr rfl fun z hz ↦
      (sectionIndex_pointTwistDiv_of_ne (finrank_self ℂ) (by rintro rfl; exact hx hz) hτ).symm

end Line

end TauCeti
