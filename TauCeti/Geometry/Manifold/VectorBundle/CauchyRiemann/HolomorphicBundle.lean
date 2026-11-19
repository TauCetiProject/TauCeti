/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HolomorphicFrame.Coordinates
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HolomorphicFrame.Smooth
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# The holomorphic bundle of a complex-linear Cauchy–Riemann line operator

The holomorphic structure is constructed from the local kernel frames of the given smooth
operator. A fibre type copy allows its holomorphic atlas and the original real smooth atlas to
coexist, while retaining the original fibres and total-space topology.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix C.1.
-/

public section

noncomputable section

open Bundle Module Set
open scoped ContDiff Manifold Topology TauCeti.ComplexManifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  [T2Space M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)

/-- A smooth complex-linear real Cauchy–Riemann line operator on the original smooth bundle,
with a choice of coordinate on its rank-one complex model fibre. -/
structure HolomorphicLineOperator where
  /-- A complex coordinate on the arbitrary rank-one model. -/
  modelEquiv : F ≃L[ℂ] ℂ
  /-- The real Cauchy–Riemann law for the given operator. -/
  isReal : IsRealCauchyRiemannOperator F
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D
  /-- Complex linearity of the given operator. -/
  isComplex : IsComplexLinearOperator F D
  /-- Native covariant smoothness of the given operator. -/
  regularity : ContMDiffCovariantDerivativeOn F ∞ D univ

namespace HolomorphicLineOperator

variable {D} (A : HolomorphicLineOperator (F := F) D)

/-- The fibres of the operator's holomorphic bundle, retaining the original vector spaces.
The parameter records which operator supplies the new atlas. -/
def Bundle (_A : HolomorphicLineOperator (F := F) D) (x : M) : Type _ := V x

instance instTopologicalSpaceFiber (x : M) : TopologicalSpace (A.Bundle x) :=
  inferInstanceAs (TopologicalSpace (V x))

instance instAddCommGroupFiber (x : M) : AddCommGroup (A.Bundle x) :=
  inferInstanceAs (AddCommGroup (V x))

instance instModuleComplexFiber (x : M) : Module ℂ (A.Bundle x) :=
  inferInstanceAs (Module ℂ (V x))

instance instModuleRealFiber (x : M) : Module ℝ (A.Bundle x) :=
  inferInstanceAs (Module ℝ (V x))

instance instIsScalarTowerFiber (x : M) : IsScalarTower ℝ ℂ (A.Bundle x) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (V x))

instance instIsTopologicalAddGroupFiber (x : M) : IsTopologicalAddGroup (A.Bundle x) :=
  inferInstanceAs (IsTopologicalAddGroup (V x))

instance instContinuousSMulRealFiber (x : M) : ContinuousSMul ℝ (A.Bundle x) :=
  inferInstanceAs (ContinuousSMul ℝ (V x))

instance instContinuousSMulComplexFiber (x : M) : ContinuousSMul ℂ (A.Bundle x) :=
  inferInstanceAs (ContinuousSMul ℂ (V x))

/-- The operator holomorphic bundle carries precisely the original total-space topology. -/
instance instTopologicalSpaceTotalSpace : TopologicalSpace (TotalSpace F A.Bundle) :=
  inferInstanceAs (TopologicalSpace (TotalSpace F V))

/-- A local nonzero smooth kernel frame of the given operator. -/
structure Frame (D₀ : (Π x : M, V x) →
    Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) where
  /-- The open domain of the frame. -/
  domain : TopologicalSpace.Opens M
  /-- The section, with arbitrary values outside its domain. -/
  sectionMap : Π x, V x
  /-- Smoothness, nonvanishing and the actual original kernel equation. -/
  isHolomorphic : IsNonvanishingHolomorphicOn F D₀ sectionMap domain

private def modelBasis : Basis Unit ℂ F :=
  (Basis.singleton Unit ℂ).map A.modelEquiv.symm.toLinearEquiv

include A in
/-- Every point is in the domain of an actual kernel frame of the given operator. -/
theorem exists_frame (x : M) : ∃ s : Frame (F := F) D, x ∈ s.domain := by
  have hR := A.isReal
  obtain ⟨U, hU, hxU, σ, hσ⟩ :=
    hR.exists_isNonvanishingHolomorphicOn_of_contMDiffCovariantDerivativeOn
      A.isComplex A.regularity A.modelEquiv x
  exact ⟨⟨⟨U, hU⟩, σ, hσ⟩, hxU⟩

/-- A chosen local kernel frame containing the specified point. -/
def frameAt (x : M) : Frame (F := F) D := Classical.choose (A.exists_frame x)

/-- The chosen frame contains its centre. -/
theorem mem_frameAt (x : M) : x ∈ (frameAt A x).domain :=
  Classical.choose_spec (A.exists_frame x)

/-- The trivialization of the new bundle supplied by a local kernel frame. -/
def Frame.trivialization (s : Frame (F := F) D) : Trivialization F (π F A.Bundle) :=
  s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The kernel frame trivialization has precisely its stated open domain. -/
@[simp]
theorem Frame.baseSet_trivialization (s : Frame (F := F) D) :
    (s.trivialization A).baseSet = (s.domain : Set M) := by
  exact s.isHolomorphic.baseSet_trivialization A.modelBasis s.domain.isOpen

/-- The atlas consists of the trivializations supplied by all local kernel frames. -/
instance instFiberBundle : FiberBundle F A.Bundle where
  totalSpaceMk_isInducing' x := by
    unfold instTopologicalSpaceFiber instTopologicalSpaceTotalSpace Bundle
    exact FiberBundle.totalSpaceMk_isInducing F V x
  trivializationAtlas' := range (Frame.trivialization A)
  trivializationAt' x := (frameAt A x).trivialization A
  mem_baseSet_trivializationAt' x := by
    simpa only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization,
      SetLike.mem_coe] using mem_frameAt A x
  trivialization_mem_atlas' x := mem_range_self (frameAt A x)

/-- The kernel frame atlas is a complex vector bundle atlas. -/
instance instVectorBundleComplex : VectorBundle ℂ F A.Bundle where
  trivialization_linear' e he := by
    obtain ⟨s, rfl⟩ := he.out
    exact s.isHolomorphic.isLinear_trivialization A.modelBasis s.domain.isOpen
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨s, rfl⟩ := he.out
    obtain ⟨s', rfl⟩ := he'.out
    convert (A.isReal.contMDiffOn_frameCoordChangeL A.isComplex s.isHolomorphic
      s'.isHolomorphic A.modelBasis A.modelBasis s.domain.isOpen s'.domain.isOpen).continuousOn
      using 1 <;> first
    | rfl
    | simp only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization]

/-- The underlying real vector bundle uses the same kernel-frame atlas. -/
instance instVectorBundleReal : VectorBundle ℝ F A.Bundle :=
  VectorBundle.restrictScalars ℝ ℂ F A.Bundle

/-- The frame transitions are holomorphic, giving the actual native holomorphic bundle. -/
instance instContMDiffVectorBundleComplex : ContMDiffVectorBundle ω F A.Bundle 𝓘(ℂ) where
  contMDiffOn_coordChangeL e e' he he' := by
    obtain ⟨s, rfl⟩ := he.out
    obtain ⟨s', rfl⟩ := he'.out
    convert A.isReal.contMDiffOn_frameCoordChangeL A.isComplex s.isHolomorphic
      s'.isHolomorphic A.modelBasis A.modelBasis s.domain.isOpen s'.domain.isOpen
      using 1 <;> first
    | rfl
    | simp only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization]

/-- The kernel-frame atlas is smooth for the original real smooth structure on the surface. -/
instance instContMDiffVectorBundleReal : ContMDiffVectorBundle ∞ F A.Bundle 𝓘(ℝ, ℂ) where
  contMDiffOn_coordChangeL e e' he he' := by
    obtain ⟨s, rfl⟩ := he.out
    obtain ⟨s', rfl⟩ := he'.out
    let : (s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen).IsLinear ℝ :=
      Trivialization.isLinear_restrictScalars ℝ ℂ _
    let : (s'.isHolomorphic.trivialization A.modelBasis s'.domain.isOpen).IsLinear ℝ :=
      Trivialization.isLinear_restrictScalars ℝ ℂ _
    convert Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas
      (s.isHolomorphic.trivialization_mem_maximalAtlas A.modelBasis s.domain.isOpen)
      (s'.isHolomorphic.trivialization_mem_maximalAtlas A.modelBasis s'.domain.isOpen)
      using 1 <;> rfl

/-- The identity on each original fibre, as a continuous complex-linear equivalence. -/
def toOriginalFiberEquiv (x : M) : A.Bundle x ≃L[ℂ] V x := by
  unfold Bundle instTopologicalSpaceFiber instAddCommGroupFiber instModuleComplexFiber
  exact ContinuousLinearEquiv.refl ℂ (V x)

/-- The identity on total spaces, with the original topology on both sides. -/
def toOriginalHomeomorph : TotalSpace F A.Bundle ≃ₜ TotalSpace F V := by
  unfold Bundle instTopologicalSpaceTotalSpace
  exact Homeomorph.refl (TotalSpace F V)

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The total-space identity covers the identity of the base. -/
@[simp]
theorem proj_toOriginalHomeomorph (p : TotalSpace F A.Bundle) :
    (A.toOriginalHomeomorph p).proj = p.proj := by rfl

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The inverse total-space identity covers the identity of the base. -/
@[simp]
theorem proj_toOriginalHomeomorph_symm (p : TotalSpace F V) :
    (A.toOriginalHomeomorph.symm p).proj = p.proj := by rfl

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The total-space identity acts by the complex-linear identity on each fibre. -/
@[simp]
theorem toOriginalHomeomorph_mk (x : M) (v : A.Bundle x) :
    A.toOriginalHomeomorph ⟨x, v⟩ = ⟨x, A.toOriginalFiberEquiv x v⟩ := by rfl

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The inverse total-space identity acts by the inverse fibre identity. -/
@[simp]
theorem toOriginalHomeomorph_symm_mk (x : M) (v : V x) :
    A.toOriginalHomeomorph.symm ⟨x, v⟩ = ⟨x, (A.toOriginalFiberEquiv x).symm v⟩ := by rfl

private theorem contMDiff_toOriginalHomeomorph :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      A.toOriginalHomeomorph := by
  intro p
  let s := A.frameAt p.proj
  let e := s.trivialization A
  let : MemTrivializationAtlas e := ⟨mem_range_self s⟩
  have hx : p.proj ∈ s.domain := A.mem_frameAt p.proj
  have hpe : p ∈ e.source := e.mem_source.2 (by
    rw [Frame.baseSet_trivialization]
    simpa only [SetLike.mem_coe] using hx)
  have hid : ContMDiffAt (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      (fun q : TotalSpace F A.Bundle ↦ q) p := contMDiffAt_id
  have hnew := (e.contMDiffAt_iff hpe).1 hid
  apply (Trivialization.contMDiffAt_iff_of_mem_maximalAtlas
    (s.isHolomorphic.trivialization_mem_maximalAtlas A.modelBasis s.domain.isOpen) ?_).2
  · constructor
    · convert hnew.1 using 1; rfl
    · convert hnew.2 using 1; rfl
  · apply (Trivialization.mem_source _).mpr
    rw [IsNonvanishingHolomorphicOn.baseSet_trivialization, proj_toOriginalHomeomorph]
    simpa only [SetLike.mem_coe] using hx

private theorem contMDiff_toOriginalHomeomorph_symm :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      A.toOriginalHomeomorph.symm := by
  intro p
  let s := A.frameAt p.proj
  let e := s.trivialization A
  let : MemTrivializationAtlas e := ⟨mem_range_self s⟩
  have hx : p.proj ∈ s.domain := A.mem_frameAt p.proj
  have hpe : p ∈ (s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen).source := by
    apply (Trivialization.mem_source _).mpr
    rw [IsNonvanishingHolomorphicOn.baseSet_trivialization]
    simpa only [SetLike.mem_coe] using hx
  have hid : ContMDiffAt (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      (fun q : TotalSpace F V ↦ q) p := contMDiffAt_id
  have hold := (Trivialization.contMDiffAt_iff_of_mem_maximalAtlas
    (s.isHolomorphic.trivialization_mem_maximalAtlas A.modelBasis s.domain.isOpen) hpe).1 hid
  apply (e.contMDiffAt_iff ?_).2
  · constructor
    · convert hold.1 using 1; rfl
    · convert hold.2 using 1; rfl
  · apply e.mem_source.mpr
    rw [Frame.baseSet_trivialization, proj_toOriginalHomeomorph_symm]
    simpa only [SetLike.mem_coe] using hx

/-- The identity comparison with the original bundle is a real smooth diffeomorphism and is
complex linear on every fibre, as expressed by `toOriginalHomeomorph_mk`. -/
def toOriginalDiffeomorph :
    TotalSpace F A.Bundle ≃ₘ^∞⟮𝓘(ℝ, ℂ).prod 𝓘(ℝ, F), 𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)⟯
      TotalSpace F V where
  toEquiv := A.toOriginalHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_toOriginalHomeomorph A
  contMDiff_invFun := contMDiff_toOriginalHomeomorph_symm A

/-- Read an original section as a section of the operator's holomorphic bundle. -/
def toBundleSection (τ : Π x, V x) : Π x, A.Bundle x :=
  fun x ↦ (A.toOriginalFiberEquiv x).symm (τ x)

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The section comparison is the complex-linear identity on each fibre. -/
@[simp]
theorem toBundleSection_apply (τ : Π x, V x) (x : M) :
    A.toBundleSection τ x = (A.toOriginalFiberEquiv x).symm (τ x) := by rfl

private theorem contMDiffOn_of_toBundleSection (τ : Π x, V x) {W : Set M}
    (hτ : ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) ω
      (fun x ↦ TotalSpace.mk' F x (A.toBundleSection τ x)) W) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% τ) W := by
  have hR := (hτ.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)).restrictScalars ℝ
  have hRR : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      (fun x ↦ TotalSpace.mk' F x (A.toBundleSection τ x)) W := by
    simpa only [ModelWithCorners.restrictScalars_prod,
      modelWithCornersSelf_restrictScalars] using hR
  convert A.toOriginalDiffeomorph.contMDiff.comp_contMDiffOn hRR using 1; rfl

/-- On every open set, the given operator's smooth kernel sections are exactly the holomorphic
sections of the constructed bundle. Smoothness uses the original bundle and the same operator. -/
theorem contMDiffOn_toBundleSection_iff (τ : Π x, V x) {W : Set M} (hW : IsOpen W) :
    ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) ω
      (fun x ↦ TotalSpace.mk' F x (A.toBundleSection τ x)) W ↔
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% τ) W ∧
        ∀ x ∈ W, D τ x = 0 := by
  let : FiniteDimensional ℂ F := .of_injective A.modelEquiv.toLinearMap A.modelEquiv.injective
  constructor
  · intro hτ
    have hτR := contMDiffOn_of_toBundleSection A τ hτ
    refine ⟨hτR, fun x hxW ↦ ?_⟩
    let s := A.frameAt x
    let e := s.trivialization A
    let : MemTrivializationAtlas e := ⟨mem_range_self s⟩
    have hU := s.domain.isOpen.inter hW
    have hc := (e.contMDiffOn_section_iff hU (by
      simp only [e, Frame.baseSet_trivialization, inter_subset_left])).1
        (hτ.mono inter_subset_right)
    have hold : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, F)
        (fun y ↦ (s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen ⟨y, τ y⟩).2)
        ((s.domain : Set M) ∩ W) := by
      convert hc.mdifferentiableOn (by simp) using 1; rfl
    exact ((A.isReal.mdifferentiableOn_frameCoord_iff A.isComplex s.isHolomorphic
      A.modelBasis s.domain.isOpen hU inter_subset_left (hτR.mono inter_subset_right)).1 hold)
        x ⟨A.mem_frameAt x, hxW⟩
  · rintro ⟨hτR, hker⟩ x hxW
    let s := A.frameAt x
    let e := s.trivialization A
    let : MemTrivializationAtlas e := ⟨mem_range_self s⟩
    have hU := s.domain.isOpen.inter hW
    have hc := (A.isReal.mdifferentiableOn_frameCoord_iff A.isComplex s.isHolomorphic
      A.modelBasis s.domain.isOpen hU inter_subset_left (hτR.mono inter_subset_right)).2
        (fun y hy ↦ hker y hy.2)
    have hω := hc.contMDiffOn (n := ω) hU
    apply ContMDiffAt.contMDiffWithinAt
    apply (e.contMDiffAt_section_iff ?_).2
    · convert hω.contMDiffAt (hU.mem_nhds ⟨A.mem_frameAt x, hxW⟩) using 1; rfl
    · rw [Frame.baseSet_trivialization]
      exact A.mem_frameAt x

private theorem contMDiff_compare (B : HolomorphicLineOperator (F := F) D) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, F)) (𝓘(ℂ).prod 𝓘(ℂ, F)) ω
      (fun p : TotalSpace F A.Bundle ↦ B.toOriginalHomeomorph.symm (A.toOriginalHomeomorph p)) := by
  intro p
  let s := A.frameAt p.proj
  let eA := s.trivialization A
  let eB := s.trivialization B
  let : MemTrivializationAtlas eA := ⟨mem_range_self s⟩
  let : MemTrivializationAtlas eB := ⟨mem_range_self s⟩
  have hx : p.proj ∈ s.domain := A.mem_frameAt p.proj
  have hpe : p ∈ eA.source := eA.mem_source.2 (by
    rw [Frame.baseSet_trivialization]
    exact hx)
  have hid : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, F)) (𝓘(ℂ).prod 𝓘(ℂ, F)) ω
      (fun q : TotalSpace F A.Bundle ↦ q) p := contMDiffAt_id
  have hA := (eA.contMDiffAt_iff hpe).1 hid
  let oA := s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen
  let oB := s.isHolomorphic.trivialization B.modelBasis s.domain.isOpen
  have hL : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, F →L[ℂ] F) ω
      (fun x ↦ (oA.coordChangeL ℂ oB x : F →L[ℂ] F)) s.domain := by
    simpa only [inter_self] using A.isReal.contMDiffOn_frameCoordChangeL A.isComplex
      s.isHolomorphic s.isHolomorphic A.modelBasis B.modelBasis s.domain.isOpen s.domain.isOpen
  have hvec := ((hL.contMDiffAt (s.domain.isOpen.mem_nhds hx)).comp p hA.1).clm_apply hA.2
  apply (eB.contMDiffAt_iff ?_).2
  · constructor
    · convert hA.1 using 1; rfl
    · apply hvec.congr_of_eventuallyEq
      filter_upwards [hA.1.continuousAt.preimage_mem_nhds (s.domain.isOpen.mem_nhds hx)]
        with q hq
      have hxA : q.proj ∈ oA.baseSet := by
        rw [IsNonvanishingHolomorphicOn.baseSet_trivialization]
        exact hq
      have hxB : q.proj ∈ oB.baseSet := by
        rw [IsNonvanishingHolomorphicOn.baseSet_trivialization]
        exact hq
      have hc := oA.coordChangeL_apply (R := ℂ) oB ⟨hxA, hxB⟩
        (oA ⟨q.proj, A.toOriginalFiberEquiv q.proj q.2⟩).2
      rw [oA.symm_apply_apply_mk hxA] at hc
      convert hc.symm using 1 <;> rfl
  · apply eB.mem_source.2
    rw [Frame.baseSet_trivialization, proj_toOriginalHomeomorph_symm,
      proj_toOriginalHomeomorph]
    exact hx

/-- The canonical comparison between the holomorphic structures built from two choices of
model coordinate for the same operator. It is the fibrewise complex-linear identity. -/
def compare (B : HolomorphicLineOperator (F := F) D) :
    TotalSpace F A.Bundle ≃ₘ^ω⟮𝓘(ℂ).prod 𝓘(ℂ, F), 𝓘(ℂ).prod 𝓘(ℂ, F)⟯
      TotalSpace F B.Bundle where
  toEquiv := (A.toOriginalHomeomorph.trans B.toOriginalHomeomorph.symm).toEquiv
  contMDiff_toFun := contMDiff_compare A B
  contMDiff_invFun := contMDiff_compare B A

/-- The canonical holomorphic comparison acts by the complex-linear identity on fibres. -/
@[simp]
theorem compare_mk (B : HolomorphicLineOperator (F := F) D) (x : M) (v : A.Bundle x) :
    A.compare B ⟨x, v⟩ =
      ⟨x, (B.toOriginalFiberEquiv x).symm (A.toOriginalFiberEquiv x v)⟩ := by rfl

/-- The canonical comparisons satisfy the cocycle law. -/
theorem compare_trans (B C : HolomorphicLineOperator (F := F) D) :
    (A.compare B).trans (B.compare C) = A.compare C := by
  apply DFunLike.ext
  intro p
  rfl

end HolomorphicLineOperator

variable {D}

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- Package the actual smooth complex-linear real Cauchy–Riemann operator on a rank-one model.
The model coordinate is constructed from the rank hypothesis, rather than assumed. -/
def IsRealCauchyRiemannOperator.toHolomorphicLineOperator
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (hDℂ : IsComplexLinearOperator F D) (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hF : finrank ℂ F = 1) : HolomorphicLineOperator (F := F) D := by
  let : FiniteDimensional ℂ F := .of_finrank_pos (by rw [hF]; exact Nat.zero_lt_one)
  exact ⟨ContinuousLinearEquiv.ofFinrankEq (by simpa only [finrank_self] using hF),
    hD, hDℂ, hDs⟩

end TauCeti
