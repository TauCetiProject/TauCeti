/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Local frames: duality with the coefficient functionals, and testing hom-bundle sections

Let `V → M` be a smooth vector bundle, let `e` be a trivialization of `V` and let `b` be a basis
of the model fibre, so that `e.localFrame b` is a local frame of `V` over `e.baseSet` with
coefficient functionals `e.localFrameCoeff I b`. This file records that over `e.baseSet` the frame
and its coefficient functionals are dual to each other: the `i`-th functional takes the value `1`
on the `i`-th frame vector and `0` on the others.

It then uses a local frame of the *source* bundle to test smoothness of a section of a bundle of
continuous linear maps: such a section is `C^n` on a subset of the two base sets as soon as
its evaluations on the frame sections are. Read through a trivialization, a continuous linear map
out of a finite-dimensional space is recovered from its values on a basis by
`T = ∑ j, (b.coord j).smulRight (T (b j))`, and each summand depends continuously linearly on
`T (b j)`. This is the criterion through which a covariant derivative is proved to be `C^n`:
`ContMDiffCovariantDerivativeOn` asks for smoothness of the hom-bundle section `∇σ`, while the
constructions of connections produce smoothness of the vector fields `∇_X σ` one direction `X` at
a time.

## Main results

* `TauCeti.Manifold.localFrameCoeff_basisAt`: the coefficient functionals are dual to the basis
  `e.basisAt b hx` of the fibre at a point of `e.baseSet`.
* `TauCeti.Manifold.localFrameCoeff_localFrame`: the same duality, stated for the frame sections
  themselves.
* `TauCeti.Manifold.trace_eq_sum_localFrameCoeff`: over the base set, the trace of a fibre
  endomorphism is the sum of its diagonal local-frame coefficients.
* `TauCeti.Manifold.symmL_basis_eq_localFrame` and
  `TauCeti.Manifold.continuousLinearMapAt_localFrame`: a trivialization transports basis vectors
  to its local frame and reads those frame vectors back as basis vectors.
* `Module.Basis.eq_sum_repr_continuousLinearMapAt_smul_localFrame`: a fibre vector is the sum of
  the local-frame vectors weighted by the coordinates of its reading in `e`.
* `TauCeti.Manifold.basisAt_apply`: the basis `e.basisAt b hx` is the continuous inverse of `e`
  applied to `b`.
* `TauCeti.Manifold.contMDiffOn_symm_baseSet`: the section with constant coordinates in a
  trivialization is smooth on its base set.
* `TauCeti.Manifold.coordChangeL_toMatrix`: a trivialization coordinate change has the
  change-of-basis matrix between the corresponding local frames.
* `TauCeti.Manifold.contMDiffOn_hom_of_localFrame`: a section of the bundle of continuous linear
  maps, possibly along a base map, is `C^n` once its evaluations on a local frame of the source
  bundle are.
* `Bundle.Trivialization.exists_contMDiff_eventuallyEq_localFrame`: near a point of its base set,
  the local frame of a trivialization agrees with a family of globally smooth sections.
-/

public section

open Bundle Module Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {x : M} {ι : Type*} (b : Basis ι 𝕜 F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

section

variable [ContMDiffVectorBundle 1 F V I]

/-- A local frame is dual to its own coefficient functionals. -/
theorem localFrameCoeff_localFrame [DecidableEq ι] (hx : x ∈ e.baseSet) (i j : ι) :
    e.localFrameCoeff I b i x (e.localFrame b j x) = if i = j then 1 else 0 := by
  rw [e.localFrameCoeff_apply_of_mem_baseSet b hx, e.localFrame_apply_of_mem_baseSet b hx,
    Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

/-- A local frame is dual to its own coefficient functionals on the basis sections at `x`. -/
@[simp]
theorem localFrameCoeff_basisAt [DecidableEq ι] (hx : x ∈ e.baseSet) (i j : ι) :
    e.localFrameCoeff I b i x (e.basisAt b hx j) = if i = j then 1 else 0 := by
  rw [← e.localFrame_apply_of_mem_baseSet b hx, localFrameCoeff_localFrame b hx]

variable (I) in
/-- Over the base set of a trivialization, the trace of a fibre endomorphism is the sum of its
diagonal coefficients in the local frame. -/
theorem trace_eq_sum_localFrameCoeff [Fintype ι] (hx : x ∈ e.baseSet) (B : V x →ₗ[𝕜] V x) :
    LinearMap.trace 𝕜 (V x) B = ∑ i, e.localFrameCoeff I b i x (B (e.localFrame b i x)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 (e.basisAt b hx)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, e.localFrame_apply_of_mem_baseSet b hx]
  have h := e.localFrameCoeff_apply_of_mem_baseSet (I := I) b hx
    (FiberBundle.extend F (B (e.basisAt b hx i))) i
  rwa [FiberBundle.extend_apply_self, eq_comm] at h

end

/-- The continuous inverse of a trivialization transports a model-fibre basis vector to the
corresponding local-frame vector. -/
theorem symmL_basis_eq_localFrame (hx : x ∈ e.baseSet) (i : ι) :
    e.symmL 𝕜 x (b i) = e.localFrame b i x := by
  rw [e.symmL_apply hx]
  simp [Bundle.Trivialization.localFrame_apply_of_mem_baseSet,
    Bundle.Trivialization.basisAt, hx]

/-- The basis of a fibre given by a trivialization is the continuous inverse of the
trivialization applied to the model-fibre basis. -/
theorem basisAt_apply (hx : x ∈ e.baseSet) (i : ι) : e.basisAt b hx i = e.symmL 𝕜 x (b i) := by
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply, e.symmL_apply hx]

/-- A trivialization reads a vector of its local frame as the corresponding model-fibre basis
vector. -/
theorem continuousLinearMapAt_localFrame (hx : x ∈ e.baseSet) (i : ι) :
    e.continuousLinearMapAt 𝕜 x (e.localFrame b i x) = b i := by
  rw [← symmL_basis_eq_localFrame b hx i, e.continuousLinearMapAt_symmL hx]

/-- A vector of the fibre over a point of the base set of a trivialization `e` is the sum of the
local-frame vectors weighted by the coordinates of its reading in `e`. -/
theorem _root_.Module.Basis.eq_sum_repr_continuousLinearMapAt_smul_localFrame [Fintype ι]
    (hx : x ∈ e.baseSet) (v : V x) :
    v = ∑ i, b.repr (e.continuousLinearMapAt 𝕜 x v) i • e.localFrame b i x := by
  calc
    v = e.symmL 𝕜 x (e.continuousLinearMapAt 𝕜 x v) := (e.symmL_continuousLinearMapAt hx v).symm
    _ = e.symmL 𝕜 x (∑ i, b.repr (e.continuousLinearMapAt 𝕜 x v) i • b i) := by
      rw [b.sum_repr]
    _ = _ := by simp only [map_sum, map_smul, symmL_basis_eq_localFrame b hx]

/-- The section with constant coordinates `v` in a trivialization `e` is `C^n` on the base set of
`e`. -/
theorem contMDiffOn_symm_baseSet {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] (v : F) :
    CMDiff[e.baseSet] n (T% (fun y ↦ e.symm y v)) :=
  e.contMDiffOn_section_baseSet_iff.2 <| (contMDiffOn_const (c := v)).congr fun y hy ↦ by
    simp only [e.apply_mk_symm hy]

/-- The matrix of a coordinate change between two vector-bundle trivializations is the
change-of-basis matrix between the corresponding local frames. -/
theorem coordChangeL_toMatrix [Fintype ι] [DecidableEq ι]
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    LinearMap.toMatrix b b (e.coordChangeL 𝕜 e' x).toLinearMap =
      (e'.basisAt b hx').toMatrix (e.basisAt b hx) := by
  rw [LinearMap.toMatrix_eq_basisToMatrix, Bundle.Trivialization.basisAt,
    Module.Basis.toMatrix_map]
  congr 1
  funext i
  simp only [Function.comp_apply, LinearEquiv.symm_symm]
  exact congr_fun (Bundle.Trivialization.coe_coordChangeL e e' ⟨hx, hx'⟩) (b i)

/-! ### Testing a hom-bundle section on a local frame -/

section Hom

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x, TopologicalSpace (V' x)]
  [FiberBundle F' V'] [VectorBundle 𝕜 F' V']
  {e' : Trivialization F' (TotalSpace.proj : TotalSpace F' V' → M)} [MemTrivializationAtlas e']
  {n : ℕ∞ω}

variable [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul 𝕜 (V' x)]
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n F' V' I]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **A hom-bundle section is tested on a local frame.** Let `A y : V (f y) →L V' (f y)` be
continuous linear maps between fibres over a `C^n` base map `f : N → M` which sends `u` into
`e.baseSet ∩ e'.baseSet`. Then `y ↦ A y` is `C^n` on `u` as soon as each of its evaluations
`A y (e.localFrame b j (f y))` on the local frame of the source bundle is. For `f = id` this tests
a section of the bundle of continuous linear maps from `V` to `V'`. -/
theorem contMDiffOn_hom_of_localFrame {f : N → M} {u : Set N} (hf : ContMDiffOn J I n f u)
    (hu : MapsTo f u (e.baseSet ∩ e'.baseSet)) {A : Π y : N, V (f y) →L[𝕜] V' (f y)}
    (hA : ∀ j : ι, ContMDiffOn J (I.prod 𝓘(𝕜, F')) n
      (fun y ↦ TotalSpace.mk' F' (f y) (A y (e.localFrame b j (f y)))) u) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun x ↦ V x →L[𝕜] V' x) (f y) (A y)) u := by
  classical
  let := FiniteDimensional.fintypeBasisIndex b
  set eh := e.continuousLinearMap (RingHom.id 𝕜) e' with heh
  apply (eh.contMDiffOn_iff (fun y hy ↦ eh.mem_source.mpr (by simpa [heh] using hu hy))).2
  refine ⟨hf, ?_⟩
  -- The `j`-th coordinate of the trivialized section is the trivialized evaluation on the frame.
  have key {y : N} (hy : y ∈ u) (j : ι) :
      (eh ⟨f y, A y⟩).2 (b j) = (e' ⟨f y, A y (e.localFrame b j (f y))⟩).2 := by
    simp [heh, Bundle.Trivialization.continuousLinearMap_apply,
      symmL_basis_eq_localFrame b (hu hy).1,
      Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e' (hu hy).2]
  have hcoord (j : ι) : ContMDiffOn J 𝓘(𝕜, F') n (fun y ↦ (eh ⟨f y, A y⟩).2 (b j)) u := by
    refine ContMDiffOn.congr ?_ fun y hy ↦ key hy j
    exact ((e'.contMDiffOn_iff (fun y hy ↦ e'.mem_source.mpr (hu hy).2)).1 (hA j)).2
  have hsum : ContMDiffOn J 𝓘(𝕜, F →L[𝕜] F') n
      (fun y ↦ ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)).smulRight
        ((eh ⟨f y, A y⟩).2 (b j))) u := by
    refine contMDiffOn_finsetSum fun j _ ↦ ?_
    exact ContMDiffOn.clm_apply
      (g := fun _ ↦ ContinuousLinearMap.smulRightL 𝕜 F F'
        (LinearMap.toContinuousLinearMap (b.coord j))) contMDiffOn_const (hcoord j)
  apply hsum.congr
  intro y _
  refine ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_)
  simp [Basis.coord_apply, Finsupp.single_apply]

end Hom

end TauCeti.Manifold

namespace Bundle.Trivialization

/-- Near a point `x` of the base set of a trivialization `e` of a smooth real vector bundle over a
finite-dimensional Hausdorff manifold, the local frame `e.localFrame b` agrees with a family of
globally smooth sections. -/
theorem exists_contMDiff_eventuallyEq_localFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
    {ι : Type*} (e : Trivialization G (π G W)) [MemTrivializationAtlas e] (b : Basis ι ℝ G)
    {x : M} (hx : x ∈ e.baseSet) :
    ∃ F : ι → Π y : M, W y, (∀ i, CMDiff ∞ (T% (F i))) ∧
      ∀ i, ∀ᶠ y in nhds x, F i y = e.localFrame b i y := by
  -- Cut the frame off by a smooth bump function equal to one near `x`, supported in `e.baseSet`.
  have hnhds : e.baseSet ∈ nhds x := e.open_baseSet.mem_nhds hx
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hnhds).mem_iff.mp hnhds
  refine ⟨fun i ↦ (ρ : M → ℝ) • e.localFrame b i, fun i ↦ ?_, fun i ↦ ?_⟩
  · exact ρ.contMDiff.contMDiffOn.smul_section_of_tsupport e.open_baseSet hρ
      (e.contMDiffOn_localFrame_baseSet _ b i)
  · filter_upwards [ρ.eventuallyEq_one] with y hy
    simp [hy]

end Bundle.Trivialization
