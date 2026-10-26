/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Extending smooth data from an embedded submanifold

A smooth embedding of a boundaryless manifold admits local smooth retractions.
Consequently, vector-valued smooth data on its source extend to the ambient
manifold along any closed portion of its image. The ambient extension can be
supported inside a prescribed open neighbourhood, and has compact support when
the portion is compact. Neither the full embedded image nor the source needs to
be compact or closed.

The same holds for sections of a smooth vector bundle on the ambient manifold
given along the embedding, such as tangent vectors at the points of the image. Near
an image point, the section is moved to nearby fibres by reading it at the retracted
point in a local trivialization. The local extensions are glued by Mathlib's
`exists_contMDiffSection_forall_mem_convex_of_local`, with the convex constraint of
agreeing with the given section on the image portion and vanishing off the
prescribed neighbourhood. Here the embedding need only be a topological embedding
which is an immersion at the points of the portion.

These are the local-coordinate and partition-of-unity steps in extending an
isotopy's velocity to an ambient vector field. The local retraction uses
Mathlib's immersion normal form, projecting `(u, v)` to `u`; gluing uses
`IsClosed.exists_contMDiffMap_eqOn`. The source must be boundaryless because
that projection must land in an open source-chart target.

Reference: M. Hirsch, *Differential Topology*, Chapter 8, §1 (isotopy extension).
-/

public section

noncomputable section

open Set Function Topology Manifold
open scoped Manifold ContDiff

namespace Manifold.IsImmersionAt

section Local

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] {n : ℕ∞ω} {f : M → N} {x : M}

/-- A topological embedding with a `C^n` immersion normal form at `x` admits a
local `C^n` retraction to its boundaryless source. Its left-inverse law holds for
every source point whose image is in the chosen neighbourhood, not just for one
source chart. No immersion or smoothness hypothesis is needed away from `x`. -/
theorem exists_contMDiffOn_retraction (h : IsImmersionAt I J n f x) (hf : IsEmbedding f) :
    ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ ∃ r : N → M,
      ContMDiffOn J I n r V ∧ ∀ y, f y ∈ V → r (f y) = y := by
  let q : N → E := fun z => (h.equiv.symm ((h.codChart.extend J) z)).1
  have hq : ContMDiffOn J 𝓘(𝕜, E) n q h.codChart.source :=
    (ContinuousLinearMap.fst 𝕜 E h.complement).contDiff.contMDiff.comp_contMDiffOn
      (h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn
        (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas))
  have hqf : ∀ y ∈ h.domChart.source, q (f y) = (h.domChart.extend I) y := by
    intro y hy
    have hy' : y ∈ (h.domChart.extend I).source := by
      rwa [h.domChart.extend_source]
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hw
    simp only [q, hw, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨W, hW, hWf⟩ := hf.isInducing.isOpen_iff.mp h.domChart.open_source
  let V := (h.codChart.source ∩ q ⁻¹' (h.domChart.extend I).target) ∩ W
  have hV : IsOpen V :=
    (hq.continuousOn.isOpen_inter_preimage h.codChart.open_source
      h.domChart.isOpen_extend_target).inter hW
  have hxV : f x ∈ V := by
    refine ⟨⟨h.mem_codChart_source, ?_⟩, ?_⟩
    · rw [mem_preimage, hqf x h.mem_domChart_source]
      exact (h.domChart.extend I).map_source (by
        simpa only [h.domChart.extend_source] using h.mem_domChart_source)
    · have hx := h.mem_domChart_source
      rw [← hWf] at hx
      exact hx
  refine ⟨V, hV, hxV, (h.domChart.extend I).symm ∘ q, ?_, ?_⟩
  · have hi := contMDiffOn_extend_symm h.domChart_mem_maximalAtlas
    rw [← h.domChart.extend_target'] at hi
    exact hi.comp (hq.mono fun _ hz => hz.1.1) fun _ hz => hz.1.2
  · intro y hy
    have hydom : y ∈ h.domChart.source := by
      rw [← hWf]
      exact hy.2
    rw [Function.comp_apply, hqf y hydom]
    exact (h.domChart.extend I).left_inv (by rwa [h.domChart.extend_source])

end Local

section Bundle

open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] {n : ℕ∞ω} {f : M → N} {x : M}
  {V : N → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module 𝕜 (V y)]
  [∀ y, TopologicalSpace (V y)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V J]

/-- Near the image of a point where a topological embedding has a `C^n` immersion normal form,
a `C^n` section of a vector bundle along the embedding extends to a `C^n` local section of the
bundle on an open neighbourhood, agreeing with it at every source point whose image lies there. -/
theorem exists_contMDiffOn_section_extension (h : IsImmersionAt I J n f x) (hf : IsEmbedding f)
    (s : (x : M) → V (f x))
    (hs : ContMDiff I (J.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F (f x) (s x)) :
    ∃ W : Set N, IsOpen W ∧ f x ∈ W ∧ ∃ σ : (y : N) → V y,
      ContMDiffOn J (J.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (σ y)) W ∧
        ∀ y, f y ∈ W → σ (f y) = s y := by
  obtain ⟨W₀, hW₀, hxW₀, r, hr, hrf⟩ := h.exists_contMDiffOn_retraction hf
  -- Read the section at the retracted point in the trivialization at `f x`.
  let e := trivializationAt F V (f x)
  let g : N → TotalSpace F V := fun z => TotalSpace.mk' F (f (r z)) (s (r z))
  have hg : ContMDiffOn J (J.prod 𝓘(𝕜, F)) n g W₀ := hs.comp_contMDiffOn hr
  let W := (W₀ ∩ (fun z => f (r z)) ⁻¹' e.baseSet) ∩ e.baseSet
  have hW : IsOpen W :=
    ((hf.continuous.comp_continuousOn hr.continuousOn).isOpen_inter_preimage hW₀
      e.open_baseSet).inter e.open_baseSet
  have hxW : f x ∈ W := by
    refine ⟨⟨hxW₀, ?_⟩, FiberBundle.mem_baseSet_trivializationAt' (f x)⟩
    simp only [mem_preimage, hrf x hxW₀]
    exact FiberBundle.mem_baseSet_trivializationAt' (f x)
  refine ⟨W, hW, hxW, fun y => e.symm y (e (g y)).2, ?_, fun y hy => ?_⟩
  · rw [e.contMDiffOn_section_iff hW inter_subset_right]
    have hcoord : ContMDiffOn J 𝓘(𝕜, F) n (fun z => (e (g z)).2) W :=
      ((e.contMDiffOn_iff (f := g) fun z (hz : z ∈ W) => e.mem_source.mpr hz.1.2).mp
        (hg.mono fun z hz => hz.1.1)).2
    exact hcoord.congr fun z hz => by simp only [e.apply_mk_symm hz.2]
  · have hgy : g (f y) = TotalSpace.mk' F (f y) (s y) := by
      simp only [g]
      rw [hrf y hy.1.1]
    simp only [hgy]
    exact e.symm_apply_apply_mk hy.2 (s y)

end Bundle

end Manifold.IsImmersionAt

namespace TauCeti.SmoothEmbedding

section Global

variable {E E' F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N] {n : ℕ∞}

/-- Extend smooth vector-valued data along a closed portion of an embedded
boundaryless manifold, with topological support inside a prescribed open set.
Closedness is required only of the portion of the image where agreement is requested. -/
theorem exists_contMDiffMap_extension (f : SmoothEmbedding I J n M N)
    (g : C^n⟮I, M; 𝓘(ℝ, F), F⟯) {K : Set M} (hK : IsClosed (f '' K))
    {U : Set N} (hU : IsOpen U) (hKU : f '' K ⊆ U) :
    ∃ G : C^n⟮J, N; 𝓘(ℝ, F), F⟯, EqOn (G ∘ f) g K ∧ tsupport G ⊆ U := by
  classical
  let a : N → F := fun z => if hz : z ∈ f '' K then g (Classical.choose hz) else 0
  have ha (x : M) (hx : x ∈ K) : a (f x) = g x := by
    have hz : f x ∈ f '' K := mem_image_of_mem f hx
    dsimp only [a]
    rw [dite_eq_left hz]
    exact congrArg g (f.isEmbedding.injective (Classical.choose_spec hz).2)
  have hloc : ∀ z ∈ f '' K, ∃ V : Set N, IsOpen V ∧ z ∈ V ∧
      ∃ a' : N → F, ContMDiffOn J 𝓘(ℝ, F) n a' V ∧ EqOn a' a ((f '' K) ∩ V) := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := hz
    obtain ⟨V, hV, hxV, r, hr, hrf⟩ :=
      (f.isImmersion.isImmersionAt x).exists_contMDiffOn_retraction f.isEmbedding
    refine ⟨V, hV, hxV, g ∘ r, g.contMDiff.comp_contMDiffOn hr, ?_⟩
    rintro _ ⟨⟨y, hy, rfl⟩, hfy⟩
    rw [Function.comp_apply, hrf y hfy, ha y hy]
  obtain ⟨G, hGa, hGU⟩ := hK.exists_contMDiffMap_eqOn (I := J) hU hKU hloc
  exact ⟨G, fun x hx => (hGa (mem_image_of_mem f hx)).trans (ha x hx), hGU⟩

/-- Data on a compact portion of an embedded boundaryless manifold admit a
compactly supported smooth ambient extension inside any prescribed open neighbourhood. -/
theorem exists_contMDiffMap_extension_hasCompactSupport (f : SmoothEmbedding I J n M N)
    (g : C^n⟮I, M; 𝓘(ℝ, F), F⟯) {K : Set M} (hK : IsCompact K)
    {U : Set N} (hU : IsOpen U) (hKU : f '' K ⊆ U) :
    ∃ G : C^n⟮J, N; 𝓘(ℝ, F), F⟯,
      EqOn (G ∘ f) g K ∧ HasCompactSupport G ∧ tsupport G ⊆ U := by
  have : LocallyCompactSpace H' := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure (hK.image f.contMDiff.continuous) hU hKU
  obtain ⟨G, hG, hGV⟩ := f.exists_contMDiffMap_extension g
    (hK.image f.contMDiff.continuous).isClosed hV hKV
  exact ⟨G, hG, hcV.of_isClosed_subset isClosed_closure (hGV.trans subset_closure),
    hGV.trans (subset_closure.trans hVU)⟩

end Global

end TauCeti.SmoothEmbedding

namespace Topology.IsEmbedding

open Bundle

variable {E E' F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N] {n : ℕ∞}
  {V : N → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℝ (V y)]
  [∀ y, TopologicalSpace (V y)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V J]

/-- A `C^n` section of a vector bundle along a topological embedding of a boundaryless manifold
extends to a global `C^n` section of the bundle. The extension agrees with the given section on a
portion `K` of the source with closed image, at whose points the embedding is a `C^n` immersion,
and vanishes outside a prescribed open neighbourhood of that image. -/
theorem exists_contMDiffSection_extension {f : M → N} (hf : IsEmbedding f) {K : Set M}
    (himm : ∀ x ∈ K, IsImmersionAt I J n f x) (hK : IsClosed (f '' K)) {U : Set N}
    (hU : IsOpen U) (hKU : f '' K ⊆ U) (s : (x : M) → V (f x))
    (hs : ContMDiff I (J.prod 𝓘(ℝ, F)) n fun x => TotalSpace.mk' F (f x) (s x)) :
    ∃ σ : Cₛ^n⟮J; F, V⟯, (∀ x ∈ K, σ (f x) = s x) ∧ ∀ y ∉ U, σ y = 0 := by
  -- The admissible values at `y`: those of `s` at the points of `K` over `y`, and `0` off `U`.
  let t : (y : N) → Set (V y) := fun y =>
    (⋂ x ∈ K, ⋂ (h : f x = y), {h ▸ s x}) ∩ {v | y ∉ U → v = 0}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    refine (convex_iInter₂ fun x _ => convex_iInter fun h => convex_singleton _).inter ?_
    by_cases hy : y ∈ U
    · simpa [hy] using convex_univ
    · simp [hy]
  have hloc : ∀ y₀ : N, ∃ W ∈ 𝓝 y₀, ∃ σ : (y : N) → V y,
      ContMDiffOn J (J.prod 𝓘(ℝ, F)) n (fun y => TotalSpace.mk' F y (σ y)) W ∧
        ∀ y ∈ W, σ y ∈ t y := by
    intro y₀
    by_cases hy₀ : y₀ ∈ f '' K
    · obtain ⟨x, hx, rfl⟩ := hy₀
      obtain ⟨W, hW, hxW, σ, hσ, hσf⟩ := (himm x hx).exists_contMDiffOn_section_extension hf s hs
      refine ⟨W ∩ U, (hW.inter hU).mem_nhds ⟨hxW, hKU ⟨x, hx, rfl⟩⟩, σ,
        hσ.mono inter_subset_left, fun y hy => ⟨?_, fun h => absurd hy.2 h⟩⟩
      simp only [mem_iInter, mem_singleton_iff]
      rintro x' - rfl
      exact hσf x' hy.1
    · refine ⟨(f '' K)ᶜ, hK.isOpen_compl.mem_nhds hy₀, fun y => 0,
        (Bundle.contMDiff_zeroSection ℝ V).contMDiffOn, fun y hy => ⟨?_, fun _ => rfl⟩⟩
      simp only [mem_iInter, mem_singleton_iff]
      rintro x hx rfl
      exact absurd ⟨x, hx, rfl⟩ hy
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local (F_fiber := F) J V t ht hloc
  refine ⟨σ, fun x hx => ?_, fun y hy => (hσ y).2 hy⟩
  have h := (hσ (f x)).1
  simp only [mem_iInter, mem_singleton_iff] at h
  exact h x hx rfl

end Topology.IsEmbedding
