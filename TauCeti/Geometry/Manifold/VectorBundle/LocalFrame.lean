/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.LinearAlgebra.Matrix.Basis

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
* `TauCeti.Manifold.symmL_basis_eq_localFrame` and
  `TauCeti.Manifold.continuousLinearMapAt_localFrame`: a trivialization transports basis vectors
  to its local frame and reads those frame vectors back as basis vectors.
* `TauCeti.Manifold.contMDiffOn_symm_baseSet`: the section with constant coordinates in a
  trivialization is smooth on its base set.
* `TauCeti.Manifold.coordChangeL_toMatrix`: a trivialization coordinate change has the
  change-of-basis matrix between the corresponding local frames.
* `TauCeti.Manifold.contMDiffOn_hom_of_localFrame`: a section of the bundle of continuous linear
  maps is `C^n` once its evaluations on a local frame of the source bundle are.
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

end

/-- The continuous inverse of a trivialization transports a model-fibre basis vector to the
corresponding local-frame vector. -/
theorem symmL_basis_eq_localFrame (hx : x ∈ e.baseSet) (i : ι) :
    e.symmL 𝕜 x (b i) = e.localFrame b i x := by
  rw [e.symmL_apply hx]
  simp [Bundle.Trivialization.localFrame_apply_of_mem_baseSet,
    Bundle.Trivialization.basisAt, hx]

/-- A trivialization reads a vector of its local frame as the corresponding model-fibre basis
vector. -/
theorem continuousLinearMapAt_localFrame (hx : x ∈ e.baseSet) (i : ι) :
    e.continuousLinearMapAt 𝕜 x (e.localFrame b i x) = b i := by
  rw [← symmL_basis_eq_localFrame b hx i, e.continuousLinearMapAt_symmL hx]

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
  {n : ℕ∞ω} {u : Set M}

variable [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul 𝕜 (V' x)]
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n F' V' I]

/-- **A hom-bundle section is tested on a local frame.** A section `A` of the bundle of continuous
linear maps from `V` to `V'` is `C^n` on a subset of `e.baseSet ∩ e'.baseSet` as soon as each
of its evaluations `A (e.localFrame b j)` on the local frame of the source bundle is. -/
theorem contMDiffOn_hom_of_localFrame (hu : u ⊆ e.baseSet ∩ e'.baseSet)
    {A : Π y : M, V y →L[𝕜] V' y}
    (hA : ∀ j : ι, ContMDiffOn I (I.prod 𝓘(𝕜, F')) n
      (fun y ↦ TotalSpace.mk' F' y (A y (e.localFrame b j y))) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F') y (A y)) u := by
  classical
  let := FiniteDimensional.fintypeBasisIndex b
  set eh := e.continuousLinearMap (RingHom.id 𝕜) e' with heh
  apply (eh.contMDiffOn_iff (fun y hy ↦ eh.mem_source.mpr (by simpa [heh] using hu hy))).2
  refine ⟨contMDiffOn_id, ?_⟩
  -- The `j`-th coordinate of the trivialized section is the trivialized evaluation on the frame.
  have key {y : M} (hy : y ∈ u) (j : ι) :
      (eh ⟨y, A y⟩).2 (b j) = (e' ⟨y, A y (e.localFrame b j y)⟩).2 := by
    simp [heh, Bundle.Trivialization.continuousLinearMap_apply,
      symmL_basis_eq_localFrame b (hu hy).1,
      Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e' (hu hy).2]
  have hcoord (j : ι) : ContMDiffOn I 𝓘(𝕜, F') n (fun y ↦ (eh ⟨y, A y⟩).2 (b j)) u := by
    refine ContMDiffOn.congr ?_ fun y hy ↦ key hy j
    exact ((e'.contMDiffOn_iff (fun y hy ↦ e'.mem_source.mpr (hu hy).2)).1 (hA j)).2
  have hsum : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] F') n
      (fun y ↦ ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)).smulRight
        ((eh ⟨y, A y⟩).2 (b j))) u := by
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
