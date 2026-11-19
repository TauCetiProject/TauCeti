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

## Main definitions and results

* `HolomorphicLineOperator` packages the original operator and its covariant smoothness.
* `HolomorphicLineOperator.Fiber` carries the native holomorphic bundle constructed from its
  local kernel frames, with no additional atlas input.
* `HolomorphicLineOperator.toOriginalDiffeomorph` is the smooth fibrewise complex-linear identity
  with the original bundle.
* `HolomorphicLineOperator.contMDiffOn_toBundleSection_iff` identifies its holomorphic sections
  with the original smooth kernel on every open set.
* `HolomorphicLineOperator.compare` and `HolomorphicLineOperator.compare_trans` give the canonical
  holomorphic comparisons and their cocycle law.

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
def Fiber (_A : HolomorphicLineOperator (F := F) D) (x : M) : Type _ := V x

instance instTopologicalSpaceFiber (x : M) : TopologicalSpace (A.Fiber x) :=
  inferInstanceAs (TopologicalSpace (V x))

instance instAddCommGroupFiber (x : M) : AddCommGroup (A.Fiber x) :=
  inferInstanceAs (AddCommGroup (V x))

instance instModuleComplexFiber (x : M) : Module ℂ (A.Fiber x) :=
  inferInstanceAs (Module ℂ (V x))

instance instModuleRealFiber (x : M) : Module ℝ (A.Fiber x) :=
  inferInstanceAs (Module ℝ (V x))

instance instIsScalarTowerFiber (x : M) : IsScalarTower ℝ ℂ (A.Fiber x) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (V x))

instance instIsTopologicalAddGroupFiber (x : M) : IsTopologicalAddGroup (A.Fiber x) :=
  inferInstanceAs (IsTopologicalAddGroup (V x))

instance instContinuousSMulRealFiber (x : M) : ContinuousSMul ℝ (A.Fiber x) :=
  inferInstanceAs (ContinuousSMul ℝ (V x))

instance instContinuousSMulComplexFiber (x : M) : ContinuousSMul ℂ (A.Fiber x) :=
  inferInstanceAs (ContinuousSMul ℂ (V x))

/-- The operator holomorphic bundle carries precisely the original total-space topology. -/
instance instTopologicalSpaceTotalSpace : TopologicalSpace (TotalSpace F A.Fiber) :=
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

/-- The singleton model basis induced by the chosen complex coordinate. -/
def modelBasis : Basis Unit ℂ F :=
  (Basis.singleton Unit ℂ).map A.modelEquiv.symm.toLinearEquiv

include A in
/-- Every point is in the domain of an actual kernel frame of the given operator. -/
theorem exists_frame (x : M) : ∃ s : Frame (F := F) D, x ∈ s.domain := by
  have hR := A.isReal
  obtain ⟨U, hU, hxU, σ, hσ⟩ :=
    hR.exists_isNonvanishingHolomorphicOn_of_contMDiffCovariantDerivativeOn
      A.isComplex A.regularity isOpen_univ
      (A.modelEquiv.finrank_eq.trans (finrank_self ℂ)) x (mem_univ x)
  exact ⟨⟨⟨U, hU⟩, σ, hσ⟩, hxU⟩

/-- A chosen local kernel frame containing the specified point. -/
def frameAt (x : M) : Frame (F := F) D := Classical.choose (A.exists_frame x)

/-- The chosen frame contains its centre. -/
theorem mem_frameAt (x : M) : x ∈ (frameAt A x).domain :=
  Classical.choose_spec (A.exists_frame x)

/-- The trivialization of the new bundle supplied by a local kernel frame. -/
def Frame.trivialization (s : Frame (F := F) D) (b : Basis Unit ℂ F) :
    Trivialization F (π F A.Fiber) :=
  s.isHolomorphic.trivialization b s.domain.isOpen

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The kernel frame trivialization has precisely its stated open domain. -/
@[simp]
theorem Frame.baseSet_trivialization (s : Frame (F := F) D) (b : Basis Unit ℂ F) :
    (s.trivialization A b).baseSet = (s.domain : Set M) := by
  exact s.isHolomorphic.baseSet_trivialization b s.domain.isOpen

/-- The atlas consists of the trivializations supplied by all local kernel frames. -/
instance instFiberBundle : FiberBundle F A.Fiber where
  totalSpaceMk_isInducing' x := by
    unfold instTopologicalSpaceFiber instTopologicalSpaceTotalSpace Fiber
    exact FiberBundle.totalSpaceMk_isInducing F V x
  trivializationAtlas' := range (fun p : Frame (F := F) D × Basis Unit ℂ F ↦
    p.1.trivialization A p.2)
  trivializationAt' x := (frameAt A x).trivialization A A.modelBasis
  mem_baseSet_trivializationAt' x := by
    simpa only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization,
      SetLike.mem_coe] using mem_frameAt A x
  trivialization_mem_atlas' x := mem_range_self (frameAt A x, A.modelBasis)

/-- Every kernel frame, with every complex model basis, belongs to the holomorphic atlas. -/
instance Frame.memTrivializationAtlas (s : Frame (F := F) D) (b : Basis Unit ℂ F) :
    MemTrivializationAtlas (s.trivialization A b) := ⟨mem_range_self (s, b)⟩

/-- The kernel frame atlas is a complex vector bundle atlas. -/
instance instVectorBundleComplex : VectorBundle ℂ F A.Fiber where
  trivialization_linear' e he := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    exact s.isHolomorphic.isLinear_trivialization b s.domain.isOpen
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    obtain ⟨⟨s', b'⟩, rfl⟩ := he'.out
    convert (A.isReal.contMDiffOn_coordChangeL_trivialization A.isComplex s.isHolomorphic
      s'.isHolomorphic b b' s.domain.isOpen s'.domain.isOpen).continuousOn using 1 <;> first
    | rfl
    | simp only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization]

/-- The underlying real vector bundle uses the same kernel-frame atlas. -/
instance instVectorBundleReal : VectorBundle ℝ F A.Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F A.Fiber

/-- The frame transitions are holomorphic, giving the actual native holomorphic bundle. -/
instance instContMDiffVectorBundleComplex : ContMDiffVectorBundle ω F A.Fiber 𝓘(ℂ) where
  contMDiffOn_coordChangeL e e' he he' := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    obtain ⟨⟨s', b'⟩, rfl⟩ := he'.out
    convert A.isReal.contMDiffOn_coordChangeL_trivialization A.isComplex s.isHolomorphic
      s'.isHolomorphic b b' s.domain.isOpen s'.domain.isOpen using 1 <;> first
    | rfl
    | simp only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization]

/-- The kernel-frame atlas is smooth for the original real smooth structure on the surface. -/
instance instContMDiffVectorBundleReal : ContMDiffVectorBundle ∞ F A.Fiber 𝓘(ℝ, ℂ) where
  contMDiffOn_coordChangeL e e' he he' := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    obtain ⟨⟨s', b'⟩, rfl⟩ := he'.out
    let : (s.isHolomorphic.trivialization b s.domain.isOpen).IsLinear ℝ :=
      Trivialization.isLinear_restrictScalars ℝ ℂ _
    let : (s'.isHolomorphic.trivialization b' s'.domain.isOpen).IsLinear ℝ :=
      Trivialization.isLinear_restrictScalars ℝ ℂ _
    convert Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas
      (s.isHolomorphic.trivialization_mem_maximalAtlas b s.domain.isOpen)
      (s'.isHolomorphic.trivialization_mem_maximalAtlas b' s'.domain.isOpen)
      using 1 <;> rfl

/-- The identity on each original fibre, as a continuous complex-linear equivalence. -/
def toOriginalFiberEquiv (x : M) : A.Fiber x ≃L[ℂ] V x := by
  unfold Fiber instTopologicalSpaceFiber instAddCommGroupFiber instModuleComplexFiber
  exact ContinuousLinearEquiv.refl ℂ (V x)

/-- The identity on total spaces, with the original topology on both sides. -/
def toOriginalHomeomorph : TotalSpace F A.Fiber ≃ₜ TotalSpace F V := by
  unfold Fiber instTopologicalSpaceTotalSpace
  exact Homeomorph.refl (TotalSpace F V)

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The total-space identity covers the identity of the base. -/
@[simp]
theorem proj_toOriginalHomeomorph (p : TotalSpace F A.Fiber) :
    (A.toOriginalHomeomorph p).proj = p.proj := by rfl

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The inverse total-space identity covers the identity of the base. -/
@[simp]
theorem proj_toOriginalHomeomorph_symm (p : TotalSpace F V) :
    (A.toOriginalHomeomorph.symm p).proj = p.proj := by rfl

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The total-space identity acts by the complex-linear identity on each fibre. -/
@[simp]
theorem toOriginalHomeomorph_mk (x : M) (v : A.Fiber x) :
    A.toOriginalHomeomorph ⟨x, v⟩ = ⟨x, A.toOriginalFiberEquiv x v⟩ := by rfl

omit [T2Space M] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The inverse total-space identity acts by the inverse fibre identity. -/
@[simp]
theorem toOriginalHomeomorph_symm_mk (x : M) (v : V x) :
    A.toOriginalHomeomorph.symm ⟨x, v⟩ = ⟨x, (A.toOriginalFiberEquiv x).symm v⟩ := by rfl

private theorem contMDiffAt_toOriginalHomeomorph_iff
    {G H Q : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    (J : ModelWithCorners ℝ G H) [TopologicalSpace Q] [ChartedSpace H Q]
    {f : Q → TotalSpace F A.Fiber} {q : Q} :
    ContMDiffAt J (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (A.toOriginalHomeomorph ∘ f) q ↔
      ContMDiffAt J (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ f q := by
  let s := A.frameAt (f q).proj
  let e := s.trivialization A A.modelBasis
  have hx : (f q).proj ∈ s.domain := A.mem_frameAt (f q).proj
  have hnew : f q ∈ e.source := e.mem_source.2 (by
    rw [Frame.baseSet_trivialization]
    exact hx)
  have hold : A.toOriginalHomeomorph (f q) ∈
      (s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen).source := by
    rw [Trivialization.mem_source, IsNonvanishingHolomorphicOn.baseSet_trivialization,
      proj_toOriginalHomeomorph]
    exact hx
  rw [Trivialization.contMDiffAt_iff_of_mem_maximalAtlas
    (f := A.toOriginalHomeomorph ∘ f)
    (s.isHolomorphic.trivialization_mem_maximalAtlas A.modelBasis s.domain.isOpen) hold,
    e.contMDiffAt_iff hnew]
  rfl

private theorem contMDiff_toOriginalHomeomorph :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      A.toOriginalHomeomorph := by
  intro p
  exact (contMDiffAt_toOriginalHomeomorph_iff A _).2 contMDiffAt_id

private theorem contMDiff_toOriginalHomeomorph_symm :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      A.toOriginalHomeomorph.symm := by
  intro p
  apply (contMDiffAt_toOriginalHomeomorph_iff A _).1
  simpa only [Homeomorph.self_comp_symm] using
    (contMDiffAt_id : ContMDiffAt (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F))
      (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ id p)

/-- The identity comparison with the original bundle is a real smooth diffeomorphism and is
complex linear on every fibre, as expressed by `toOriginalHomeomorph_mk`. -/
def toOriginalDiffeomorph :
    TotalSpace F A.Fiber ≃ₘ^∞⟮𝓘(ℝ, ℂ).prod 𝓘(ℝ, F), 𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)⟯
      TotalSpace F V where
  toEquiv := A.toOriginalHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_toOriginalHomeomorph A
  contMDiff_invFun := contMDiff_toOriginalHomeomorph_symm A

/-- The smooth comparison acts by the complex-linear identity on each fibre. -/
@[simp]
theorem toOriginalDiffeomorph_mk (x : M) (v : A.Fiber x) :
    A.toOriginalDiffeomorph ⟨x, v⟩ = ⟨x, A.toOriginalFiberEquiv x v⟩ := by rfl

/-- The inverse smooth comparison acts by the inverse complex-linear identity. -/
@[simp]
theorem toOriginalDiffeomorph_symm_mk (x : M) (v : V x) :
    A.toOriginalDiffeomorph.symm ⟨x, v⟩ =
      ⟨x, (A.toOriginalFiberEquiv x).symm v⟩ := by rfl

/-- Read an original section as a section of the operator's holomorphic bundle. -/
def toBundleSection (τ : Π x, V x) : Π x, A.Fiber x :=
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
  have : FiniteDimensional ℂ F := .of_injective A.modelEquiv.toLinearMap A.modelEquiv.injective
  constructor
  · intro hτ
    have hτR := contMDiffOn_of_toBundleSection A τ hτ
    refine ⟨hτR, fun x hxW ↦ ?_⟩
    let s := A.frameAt x
    let e := s.trivialization A A.modelBasis
    have hU := s.domain.isOpen.inter hW
    have hc := (e.contMDiffOn_section_iff hU (by
      simp only [e, Frame.baseSet_trivialization, inter_subset_left])).1
        (hτ.mono inter_subset_right)
    have hold : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, F)
        (fun y ↦ (s.isHolomorphic.trivialization A.modelBasis s.domain.isOpen ⟨y, τ y⟩).2)
        ((s.domain : Set M) ∩ W) := by
      convert hc.mdifferentiableOn (by simp) using 1; rfl
    exact ((A.isReal.mdifferentiableOn_trivialization_iff A.isComplex s.isHolomorphic
      A.modelBasis s.domain.isOpen hU inter_subset_left (hτR.mono inter_subset_right)).1 hold)
        x ⟨A.mem_frameAt x, hxW⟩
  · rintro ⟨hτR, hker⟩ x hxW
    let s := A.frameAt x
    let e := s.trivialization A A.modelBasis
    have hU := s.domain.isOpen.inter hW
    have hc := (A.isReal.mdifferentiableOn_trivialization_iff A.isComplex s.isHolomorphic
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
      (fun p : TotalSpace F A.Fiber ↦ B.toOriginalHomeomorph.symm (A.toOriginalHomeomorph p)) := by
  intro p
  let s := A.frameAt p.proj
  let eA := s.trivialization A A.modelBasis
  let eB := s.trivialization B A.modelBasis
  have hx : p.proj ∈ s.domain := A.mem_frameAt p.proj
  have hpe : p ∈ eA.source := eA.mem_source.2 (by
    rw [Frame.baseSet_trivialization]
    exact hx)
  have hid : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, F)) (𝓘(ℂ).prod 𝓘(ℂ, F)) ω
      (fun q : TotalSpace F A.Fiber ↦ q) p := contMDiffAt_id
  have hA := (eA.contMDiffAt_iff hpe).1 hid
  apply (eB.contMDiffAt_iff ?_).2
  · constructor
    · convert hA.1 using 1; rfl
    · convert hA.2 using 1; rfl
  · apply eB.mem_source.2
    rw [Frame.baseSet_trivialization, proj_toOriginalHomeomorph_symm,
      proj_toOriginalHomeomorph]
    exact hx

/-- The canonical comparison between the holomorphic structures built from two choices of
model coordinate for the same operator. It is the fibrewise complex-linear identity. -/
def compare (B : HolomorphicLineOperator (F := F) D) :
    TotalSpace F A.Fiber ≃ₘ^ω⟮𝓘(ℂ).prod 𝓘(ℂ, F), 𝓘(ℂ).prod 𝓘(ℂ, F)⟯
      TotalSpace F B.Fiber where
  toEquiv := (A.toOriginalHomeomorph.trans B.toOriginalHomeomorph.symm).toEquiv
  contMDiff_toFun := contMDiff_compare A B
  contMDiff_invFun := contMDiff_compare B A

/-- The canonical holomorphic comparison acts by the complex-linear identity on fibres. -/
@[simp]
theorem compare_mk (B : HolomorphicLineOperator (F := F) D) (x : M) (v : A.Fiber x) :
    A.compare B ⟨x, v⟩ =
      ⟨x, (B.toOriginalFiberEquiv x).symm (A.toOriginalFiberEquiv x v)⟩ := by rfl

/-- Comparing a holomorphic structure with itself gives the identity. -/
@[simp]
theorem compare_self : A.compare A = Diffeomorph.refl _ _ ω := by
  apply DFunLike.ext
  intro p
  rfl

/-- Reversing the choices reverses the canonical holomorphic comparison. -/
@[simp]
theorem compare_symm (B : HolomorphicLineOperator (F := F) D) :
    (A.compare B).symm = B.compare A := by
  apply DFunLike.ext
  intro p
  rfl

/-- The canonical holomorphic comparison preserves the comparison with the original bundle. -/
@[simp]
theorem toOriginalHomeomorph_compare (B : HolomorphicLineOperator (F := F) D)
    (p : TotalSpace F A.Fiber) :
    B.toOriginalHomeomorph (A.compare B p) = A.toOriginalHomeomorph p := by rfl

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
  have : FiniteDimensional ℂ F := .of_finrank_pos (by rw [hF]; exact Nat.zero_lt_one)
  exact ⟨ContinuousLinearEquiv.ofFinrankEq (by simpa only [finrank_self] using hF),
    hD, hDℂ, hDs⟩

end TauCeti
