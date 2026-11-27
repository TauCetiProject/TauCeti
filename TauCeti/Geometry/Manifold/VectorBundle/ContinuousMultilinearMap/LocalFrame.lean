/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousMultilinearMap
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Testing sections of the bundle of continuous multilinear maps on sections

Let `V` and `W` be vector bundles over a manifold `M`, with `V` of finite rank, and `ι` a finite
index type. A section `A` of the bundle with fibres
`ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V x) (W x)` is `C^n` on a subset of the base sets of
trivializations `e` of `V` and `e'` of `W` as soon as its evaluations `A(s_{k(1)}, …, s_{k(m)})`
on all tuples of local-frame sections of `e` are
(`TauCeti.Manifold.contMDiffOn_continuousMultilinearMap_of_localFrame`). Read through the
trivializations, a continuous multilinear map `T` on a finite-dimensional space with basis `b` is
recovered from its values on tuples of basis vectors by
`T = ∑ₖ (∏ᵢ b.coord (k i)) • T(b ∘ k)`, and each summand depends continuously linearly on
`T(b ∘ k)`. The proof follows `TauCeti.Manifold.contMDiffOn_hom_of_localFrame` step for step,
with single frame vectors replaced by tuples of them.

Over the reals, using global smooth sections that agree with a local frame near each point, a
section of this bundle is smooth exactly when it sends every family of smooth sections of `V` to a
smooth section of `W` (`TauCeti.Manifold.contMDiff_continuousMultilinearMap_iff`). This is the
multilinear form of `TauCeti.Manifold.contMDiff_hom_iff`, and the criterion through which a
tensorial operation on several sections is shown to be a smooth tensor field.

## Main results

* `TauCeti.Manifold.contMDiffOn_continuousMultilinearMap_of_localFrame`: a section of the bundle of
  continuous multilinear maps is `C^n` once its evaluations on tuples of local-frame vectors are.
* `TauCeti.Manifold.contMDiff_continuousMultilinearMap_iff`: a section of the bundle of continuous
  multilinear maps is smooth exactly when its evaluations on smooth sections are.
-/

public section

open Bundle Module Set
open scoped Manifold ContDiff Topology

namespace TauCeti.Manifold

section LocalFrame

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [FiberBundle G W] [VectorBundle 𝕜 G W]
  {ι J : Type*} [Fintype ι] (b : Basis J 𝕜 F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
  {e' : Trivialization G (TotalSpace.proj : TotalSpace G W → M)} [MemTrivializationAtlas e']
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I]

/-- **A section of the bundle of continuous multilinear maps is tested on tuples of local-frame
vectors.** A family of continuous multilinear maps `A y : (V y)^ι → W y` is a `C^n` section of the
bundle of continuous multilinear maps on a subset `u` of `e.baseSet ∩ e'.baseSet` as soon as each
evaluation `A y (e.localFrame b (k i) y)ᵢ` on a tuple of local-frame vectors of `e` is a `C^n`
section of `W` on `u`. -/
theorem contMDiffOn_continuousMultilinearMap_of_localFrame {u : Set M}
    (hu : u ⊆ e.baseSet ∩ e'.baseSet)
    {A : Π y : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V y) (W y)}
    (hA : ∀ k : ι → J, ContMDiffOn I (I.prod 𝓘(𝕜, G)) n
      (fun y ↦ TotalSpace.mk' G y (A y (fun i ↦ e.localFrame b (k i) y))) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)) n
      (fun y ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
        (E := fun z ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V z) (W z)) y (A y)) u := by
  classical
  have := FiniteDimensional.fintypeBasisIndex b
  set eh := e.continuousMultilinearMap 𝕜 ι e' with heh
  apply (eh.contMDiffOn_iff (fun y hy ↦ eh.mem_source.mpr (by simpa [heh] using hu hy))).2
  refine ⟨contMDiffOn_id, ?_⟩
  -- The value of the trivialized section on a tuple of basis vectors is the trivialized evaluation
  -- on the corresponding tuple of frame vectors.
  have key {y : M} (hy : y ∈ u) (k : ι → J) :
      (eh ⟨y, A y⟩).2 (fun i ↦ b (k i)) =
        (e' ⟨y, A y (fun i ↦ e.localFrame b (k i) y)⟩).2 := by
    simp [heh, Bundle.Trivialization.continuousMultilinearMap_apply,
      symmL_basis_eq_localFrame b (hu hy).1,
      e'.linearMapAt_def_of_mem (hu hy).2]
  have hcoord (k : ι → J) :
      ContMDiffOn I 𝓘(𝕜, G) n (fun y ↦ (eh ⟨y, A y⟩).2 (fun i ↦ b (k i))) u := by
    refine ContMDiffOn.congr ?_ fun y hy ↦ key hy k
    exact ((e'.contMDiffOn_iff (fun y hy ↦ e'.mem_source.mpr (hu hy).2)).1 (hA k)).2
  -- The product of the coordinate functionals along the tuple `k`.
  let P (k : ι → J) : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) 𝕜 :=
    (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝕜).compContinuousLinearMap
      fun i ↦ LinearMap.toContinuousLinearMap (b.coord (k i))
  have hsum : ContMDiffOn I 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G) n
      (fun y ↦ ∑ k, (P k).smulRight ((eh ⟨y, A y⟩).2 (fun i ↦ b (k i)))) u :=
    contMDiffOn_finsetSum fun k _ ↦ ContMDiffOn.clm_apply
      (g := fun _ ↦ ContinuousMultilinearMap.smulRightL 𝕜 _ G (P k)) contMDiffOn_const (hcoord k)
  refine hsum.congr fun y _ ↦ ?_
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (Basis.ext_multilinear (fun _ ↦ b) fun v ↦ ?_)
  have hprod (k : ι → J) :
      (∏ i, (Finsupp.single (v i) (1 : 𝕜)) (k i)) = if v = k then 1 else 0 := by
    simp only [Finsupp.single_apply, Finset.prod_boole, Finset.mem_univ, true_implies,
      funext_iff]
  simp [P, ContinuousMultilinearMap.smulRight_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
    hprod]

end LocalFrame

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
  {ι : Type*} [Fintype ι]

/-- **A section of the bundle of continuous multilinear maps is smooth exactly when it sends
smooth sections to smooth sections.** For finite-rank `V`, a family of continuous multilinear maps
`A x : (V x)^ι → W x` is a smooth section of the bundle of continuous multilinear maps exactly when
`x ↦ A x (s₁ x, …, sₖ x)` is a smooth section of `W` for all smooth sections `sᵢ` of `V`. -/
theorem contMDiff_continuousMultilinearMap_iff
    (A : Π x : M, ContinuousMultilinearMap ℝ (fun _ : ι ↦ V x) (W x)) :
    ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)) ∞
        (fun x ↦ TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : ι ↦ F) G)
          (E := fun z ↦ ContinuousMultilinearMap ℝ (fun _ : ι ↦ V z) (W z)) x (A x)) ↔
      ∀ s : ι → Π x : M, V x, (∀ i, CMDiff ∞ (T% (s i))) →
        ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ (fun x ↦ TotalSpace.mk' G x (A x (fun i ↦ s i x))) := by
  refine ⟨fun hA _ hs ↦ hA.continuousMultilinearMap_bundle_apply hs, fun hA ↦ ?_⟩
  refine contMDiffOn_univ.1 (contMDiffOn_of_locally_contMDiffOn fun x _ ↦ ?_)
  let e := trivializationAt F V x
  let e' := trivializationAt G W x
  let b := Basis.ofVectorSpace ℝ F
  have := FiniteDimensional.fintypeBasisIndex b
  obtain ⟨s, hs, hse⟩ :=
    e.exists_contMDiff_eventuallyEq_localFrame (I := I) (n := ∞) b le_rfl
      (mem_baseSet_trivializationAt F V x)
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 (Filter.eventually_all.2 hse)
  refine ⟨t ∩ (e.baseSet ∩ e'.baseSet), hto.inter (e.open_baseSet.inter e'.open_baseSet),
    ⟨hxt, mem_baseSet_trivializationAt F V x, mem_baseSet_trivializationAt G W x⟩, ?_⟩
  rw [univ_inter]
  refine contMDiffOn_continuousMultilinearMap_of_localFrame b inter_subset_right fun k ↦ ?_
  refine ((hA (fun i ↦ s (k i)) fun i ↦ hs (k i)).contMDiffOn).congr fun y hy ↦ ?_
  simp [ht y hy.1]

end Real

end TauCeti.Manifold
