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

* `IsComplexCauchyRiemannLineOperator` packages the original operator and its covariant smoothness.
* `IsComplexCauchyRiemannLineOperator.Fiber` carries the native holomorphic bundle constructed
  from its local kernel frames, with no additional atlas input.
* `IsComplexCauchyRiemannLineOperator.toOriginalDiffeomorph` is the smooth fibrewise
  complex-linear identity with the original bundle.
* `IsComplexCauchyRiemannLineOperator.contMDiffOn_toBundleSection_iff` identifies its
  holomorphic sections with the original smooth kernel on every open set.
* All operator data are propositions and the atlas contains all kernel frames and all model
  bases. Thus the native bundle is canonical, with no stored coordinate choice to compare.

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
on an arbitrary rank-one complex model fibre. All fields are propositions, so the resulting
bundle is independent of any packaging or model-coordinate choices. -/
structure IsComplexCauchyRiemannLineOperator : Prop where
  /-- The arbitrary complex model has rank one. -/
  finrank_eq_one : finrank ℂ F = 1
  /-- The real Cauchy–Riemann law for the given operator. -/
  isReal : IsRealCauchyRiemannOperator F
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D
  /-- Complex linearity of the given operator. -/
  isComplex : IsComplexLinearOperator F D
  /-- Native covariant smoothness of the given operator. -/
  regularity : ContMDiffCovariantDerivativeOn F ∞ D univ

namespace IsComplexCauchyRiemannLineOperator

variable {D} (A : IsComplexCauchyRiemannLineOperator (F := F) D)

/-- The fibres of the operator's holomorphic bundle, retaining the original vector spaces.
The parameter records which operator supplies the new atlas. -/
def Fiber (_A : IsComplexCauchyRiemannLineOperator (F := F) D) (x : M) : Type _ := V x

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
  /-- The section, canonically zero outside its domain. -/
  sectionMap : Π x, V x
  /-- The global representative is the zero extension of the local section. -/
  sectionMap_eq_zero : ∀ x, x ∉ domain → sectionMap x = 0
  /-- Smoothness, nonvanishing and the actual original kernel equation. -/
  isHolomorphic : IsNonvanishingHolomorphicOn F D₀ sectionMap domain

namespace Frame

omit [IsManifold 𝓘(ℂ) ∞ M] [T2Space M] [∀ x, Module ℂ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- A frame is determined by its open domain and its values there. The zero extension removes
all data outside the domain. -/
@[ext]
theorem ext {D₀ : (Π x : M, V x) →
    Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x} {s t : Frame (F := F) D₀}
    (hU : s.domain = t.domain) (hσ : ∀ x ∈ s.domain, s.sectionMap x = t.sectionMap x) : s = t := by
  cases s with
  | mk U σ hσ₀ hσH =>
    cases t with
    | mk W τ hτ₀ hτH =>
      cases hU
      have hστ : σ = τ := by
        funext x
        by_cases hx : x ∈ U
        · exact hσ x hx
        · exact (hσ₀ x hx).trans (hτ₀ x hx).symm
      cases hστ
      rfl

open Classical in
/-- Normalize a local kernel frame by zero extension. Locality of the actual real
Cauchy–Riemann operator preserves its kernel equation on the open domain. -/
def ofSection (hD : IsRealCauchyRiemannOperator F
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (U : TopologicalSpace.Opens M) (σ : Π x, V x)
    (hσ : IsNonvanishingHolomorphicOn F D σ U) : Frame (F := F) D where
  domain := U
  sectionMap x := if x ∈ U then σ x else 0
  sectionMap_eq_zero _ hx := ite_eq_right hx
  isHolomorphic := hσ.congr hD U.isOpen fun _ hx ↦ ite_eq_left hx

omit [T2Space M] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
@[simp]
theorem ofSection_domain (hD : IsRealCauchyRiemannOperator F
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (U : TopologicalSpace.Opens M) (σ : Π x, V x)
    (hσ : IsNonvanishingHolomorphicOn F D σ U) : (ofSection hD U σ hσ).domain = U := (rfl)

omit [T2Space M] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
@[simp]
theorem ofSection_apply (hD : IsRealCauchyRiemannOperator F
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (U : TopologicalSpace.Opens M) (σ : Π x, V x)
    (hσ : IsNonvanishingHolomorphicOn F D σ U) {x : M} (hx : x ∈ U) :
    (ofSection hD U σ hσ).sectionMap x = σ x := ite_eq_left hx

end Frame

/-- A model basis selected from the rank-one fact. The atlas itself contains every basis. -/
def modelBasis : Basis Unit ℂ F := Module.basisUnique Unit A.finrank_eq_one

include A in
/-- Every point is in the domain of an actual kernel frame of the given operator. -/
theorem exists_frame (x : M) : ∃ s : Frame (F := F) D, x ∈ s.domain := by
  obtain ⟨U, hU, hxU, σ, hσ⟩ :=
    A.isReal.exists_isNonvanishingHolomorphicOn_of_contMDiffCovariantDerivativeOn
      A.isComplex A.regularity isOpen_univ A.finrank_eq_one x (mem_univ x)
  exact ⟨Frame.ofSection A.isReal ⟨U, hU⟩ σ hσ, hxU⟩

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
    -- Normalize the fibre type copy and its inherited topologies before using the original
    -- bundle's inducing total-space constructor.
    unfold Fiber instTopologicalSpaceFiber instTopologicalSpaceTotalSpace
    exact FiberBundle.totalSpaceMk_isInducing F V x
  trivializationAtlas' := range (fun p : Frame (F := F) D × Basis Unit ℂ F ↦
    p.1.trivialization A p.2)
  trivializationAt' x := (frameAt A x).trivialization A A.modelBasis
  mem_baseSet_trivializationAt' x := by
    simpa only [Frame.trivialization, IsNonvanishingHolomorphicOn.baseSet_trivialization,
      SetLike.mem_coe] using mem_frameAt A x
  trivialization_mem_atlas' x := mem_range_self (frameAt A x, A.modelBasis)

/-- Every zero-extended local kernel frame, with every complex model basis, belongs to the
holomorphic atlas. -/
instance Frame.memTrivializationAtlas (s : Frame (F := F) D) (b : Basis Unit ℂ F) :
    MemTrivializationAtlas (s.trivialization A b) := ⟨mem_range_self (s, b)⟩

/-- The preferred trivialization is supplied by the chosen actual kernel frame. -/
theorem trivializationAt_eq (x : M) :
    trivializationAt F A.Fiber x = (frameAt A x).trivialization A A.modelBasis := (rfl)

/-- The native atlas consists exactly of all local kernel frames and all complex model bases. -/
theorem mem_trivializationAtlas_iff (e : Trivialization F (π F A.Fiber)) :
    e ∈ trivializationAtlas F A.Fiber ↔
      ∃ (s : Frame (F := F) D) (b : Basis Unit ℂ F), e = s.trivialization A b := by
  constructor
  · rintro ⟨⟨s, b⟩, rfl⟩
    exact ⟨s, b, rfl⟩
  · rintro ⟨s, b, rfl⟩
    exact ⟨(s, b), rfl⟩

/-- A kernel-frame trivialization is complex linear on fibres. -/
instance Frame.isLinear_trivialization (s : Frame (F := F) D) (b : Basis Unit ℂ F) :
    (s.trivialization A b).IsLinear ℂ :=
  s.isHolomorphic.isLinear_trivialization b s.domain.isOpen

omit [T2Space M] in
/-- The actual kernel-frame coordinate changes are holomorphic on their stated domains. -/
theorem Frame.contMDiffOn_coordChangeL (s t : Frame (F := F) D) (b b' : Basis Unit ℂ F) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, F →L[ℂ] F) ω
      (fun x ↦ ((s.trivialization A b).coordChangeL ℂ (t.trivialization A b') x : F →L[ℂ] F))
      ((s.domain : Set M) ∩ t.domain) :=
  A.isReal.contMDiffOn_coordChangeL_trivialization A.isComplex s.isHolomorphic
    t.isHolomorphic b b' s.domain.isOpen t.domain.isOpen

/-- The kernel frame atlas is a complex vector bundle atlas. -/
instance instVectorBundleComplex : VectorBundle ℂ F A.Fiber where
  trivialization_linear' e he := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    exact s.isHolomorphic.isLinear_trivialization b s.domain.isOpen
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    obtain ⟨⟨s', b'⟩, rfl⟩ := he'.out
    simpa only [Frame.baseSet_trivialization] using
      (s.contMDiffOn_coordChangeL A s' b b').continuousOn

/-- The underlying real vector bundle uses the same kernel-frame atlas. -/
instance instVectorBundleReal : VectorBundle ℝ F A.Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F A.Fiber

/-- The frame transitions are holomorphic, giving the actual native holomorphic bundle. -/
instance instContMDiffVectorBundleComplex : ContMDiffVectorBundle ω F A.Fiber 𝓘(ℂ) where
  contMDiffOn_coordChangeL e e' he he' := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    obtain ⟨⟨s', b'⟩, rfl⟩ := he'.out
    simpa only [Frame.baseSet_trivialization] using s.contMDiffOn_coordChangeL A s' b b'

/-- The kernel-frame atlas is smooth for the original real smooth structure on the surface. -/
instance instContMDiffVectorBundleReal : ContMDiffVectorBundle ∞ F A.Fiber 𝓘(ℝ, ℂ) where
  contMDiffOn_coordChangeL e e' he he' := by
    obtain ⟨⟨s, b⟩, rfl⟩ := he.out
    obtain ⟨⟨s', b'⟩, rfl⟩ := he'.out
    let : (s.isHolomorphic.trivialization b s.domain.isOpen).IsLinear ℝ :=
      Trivialization.isLinear_restrictScalars ℝ ℂ _
    let : (s'.isHolomorphic.trivialization b' s'.domain.isOpen).IsLinear ℝ :=
      Trivialization.isLinear_restrictScalars ℝ ℂ _
    -- `Fiber` is the type copy `V` with `inferInstanceAs` copies of the fibre modules
    -- and total-space topology. Elaborate the original-bundle statement first: elaborating
    -- it against the goal would instead read the maximal atlas through `instFiberBundle`.
    -- The statements agree after unfolding `Fiber`, `Frame.trivialization` and the copied
    -- instances; the `IsLinear ℝ` witnesses agree by proof irrelevance. The real model
    -- structures `NormedSpace.complexToReal` and
    -- `instInnerProductSpaceRealComplex.toNormedSpace` also have the same scalar action.
    have h := Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas
      (s.isHolomorphic.trivialization_mem_maximalAtlas b s.domain.isOpen)
      (s'.isHolomorphic.trivialization_mem_maximalAtlas b' s'.domain.isOpen)
    exact h

/-- The identity on each original fibre, as a continuous complex-linear equivalence. -/
def toOriginalFiberEquiv (x : M) : A.Fiber x ≃L[ℂ] V x :=
  (ContinuousLinearEquiv.refl ℂ (V x) : V x ≃L[ℂ] V x)

/-- The identity on total spaces, with the original topology on both sides. -/
def toOriginalHomeomorph : TotalSpace F A.Fiber ≃ₜ TotalSpace F V :=
  (Homeomorph.refl (TotalSpace F V) : TotalSpace F V ≃ₜ TotalSpace F V)

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

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- Reading a new-bundle vector in a kernel frame agrees with reading its original vector. -/
theorem Frame.trivialization_apply (s : Frame (F := F) D) (b : Basis Unit ℂ F)
    (p : TotalSpace F A.Fiber) :
    s.trivialization A b p =
      s.isHolomorphic.trivialization b s.domain.isOpen (A.toOriginalHomeomorph p) := (rfl)

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The kernel frame has the expected constant coordinate in the new native bundle. -/
@[simp]
theorem Frame.trivialization_apply_frame (s : Frame (F := F) D) (b : Basis Unit ℂ F)
    {x : M} (hx : x ∈ s.domain) :
    s.trivialization A b ⟨x, (A.toOriginalFiberEquiv x).symm (s.sectionMap x)⟩ = (x, b ()) :=
  s.isHolomorphic.trivialization_apply_frame b s.domain.isOpen hx

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- Inverse kernel-frame coordinates recover the original section multiple in the original
fibre, transported by the complex-linear identity. -/
@[simp]
theorem Frame.trivialization_symm_apply (s : Frame (F := F) D) (b : Basis Unit ℂ F)
    {x : M} (hx : x ∈ s.domain) (v : F) :
    (s.trivialization A b).symm x v =
      (A.toOriginalFiberEquiv x).symm (b.coord () v • s.sectionMap x) :=
  s.isHolomorphic.trivialization_symm_apply b s.domain.isOpen hx v

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
  simp only [Function.comp_apply, proj_toOriginalHomeomorph, e, Frame.trivialization_apply]

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
  simpa only [Function.comp_def, toOriginalDiffeomorph_mk, toBundleSection_apply,
    ContinuousLinearEquiv.apply_symm_apply] using
    A.toOriginalDiffeomorph.contMDiff.comp_contMDiffOn hRR

/-- On every open set, the given operator's smooth kernel sections are exactly the holomorphic
sections of the constructed bundle. Smoothness uses the original bundle and the same operator. -/
theorem contMDiffOn_toBundleSection_iff (τ : Π x, V x) {W : Set M} (hW : IsOpen W) :
    ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) ω
      (fun x ↦ TotalSpace.mk' F x (A.toBundleSection τ x)) W ↔
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% τ) W ∧
        ∀ x ∈ W, D τ x = 0 := by
  have : FiniteDimensional ℂ F := .of_basis A.modelBasis
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
      simpa only [e, Frame.trivialization_apply, toOriginalHomeomorph_mk,
        toBundleSection_apply, ContinuousLinearEquiv.apply_symm_apply] using
        hc.mdifferentiableOn (by simp)
    exact ((A.isReal.mdifferentiableOn_trivialization_iff A.isComplex s.isHolomorphic
      A.modelBasis s.domain.isOpen hU inter_subset_left
      ((hτR.mono inter_subset_right).mdifferentiableOn (by simp))).1 hold)
        x ⟨A.mem_frameAt x, hxW⟩
  · rintro ⟨hτR, hker⟩ x hxW
    let s := A.frameAt x
    let e := s.trivialization A A.modelBasis
    have hU := s.domain.isOpen.inter hW
    have hc := (A.isReal.mdifferentiableOn_trivialization_iff A.isComplex s.isHolomorphic
      A.modelBasis s.domain.isOpen hU inter_subset_left
      ((hτR.mono inter_subset_right).mdifferentiableOn (by simp))).2
        (fun y hy ↦ hker y hy.2)
    have hω := hc.contMDiffOn (n := ω) hU
    apply ContMDiffAt.contMDiffWithinAt
    apply (e.contMDiffAt_section_iff ?_).2
    · simpa only [e, Frame.trivialization_apply, toOriginalHomeomorph_mk,
        toBundleSection_apply, ContinuousLinearEquiv.apply_symm_apply] using
        hω.contMDiffAt (hU.mem_nhds ⟨A.mem_frameAt x, hxW⟩)
    · rw [Frame.baseSet_trivialization]
      exact A.mem_frameAt x

end IsComplexCauchyRiemannLineOperator

end TauCeti
