/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import Mathlib.Geometry.Manifold.WhitneyEmbedding
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Smooth embeddings into Euclidean space

Every compact Hausdorff boundaryless manifold has a smooth embedding into some Euclidean space
(`TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact`). This repackages Mathlib's
Whitney embedding theorem `exists_embedding_euclidean_of_compact` as a bundled
`TauCeti.SmoothEmbedding`, reading its injective differential as an immersion.

A compact subset `K` of a Hausdorff boundaryless manifold which need not be compact has an open
neighbourhood with compact closure that embeds smoothly into some Euclidean space
(`IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`). Here `K` lies in the interior of a
compact set `L`. For a finite smooth bump covering `(ρ_i)` of `L`, with `φ_i` the extended chart at
the centre of `ρ_i`, the map `x ↦ (ρ_i x • φ_i x, ρ_i x)_i` is injective on `L` with injective
differential at each point of `L`, so it embeds the interior of `L`. This map is Mathlib's
`SmoothBumpCovering.embeddingPiTangent`; Mathlib does not export it, so it is repeated here as a
private auxiliary. This reduces statements about maps with relatively compact image into an
arbitrary boundaryless manifold, such as Whitney approximation, to the case of an embedded target.
-/

public section

open Function Set Topology TopologicalSpace Module
open scoped ContDiff Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace TauCeti.SmoothEmbedding

/-- A compact Hausdorff boundaryless manifold has a smooth embedding into a Euclidean space.
This is Mathlib's Whitney embedding theorem `exists_embedding_euclidean_of_compact`, with its
injective differential read as an immersion. -/
theorem exists_nonempty_euclidean_of_compact [I.Boundaryless] [CompactSpace M] [T2Space M] :
    ∃ n : ℕ, Nonempty (SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M
      (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨n, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  exact ⟨n, ⟨.ofIsSmoothEmbedding e
    ⟨he.isImmersion_of_injective_mfderiv (by simp) hinj, hemb.isEmbedding⟩⟩⟩

/-! The map `x ↦ (f i x • φ_i x, f i x)_i` of a finite smooth bump covering `f`, where `φ_i` is the
extended chart at the centre of the `i`-th bump function, together with its injectivity and the
injectivity of its differential on the covered set. These are Mathlib's
`SmoothBumpCovering.embeddingPiTangent`, `SmoothBumpCovering.embeddingPiTangent_injOn` and
`SmoothBumpCovering.embeddingPiTangent_injective_mfderiv`, which
`Mathlib.Geometry.Manifold.WhitneyEmbedding` does not export; the proofs are Mathlib's. -/

variable {ι : Type*} [Fintype ι] {s : Set M}

/-- The Whitney map `x ↦ (f i x • φ_i x, f i x)_i` of a finite smooth bump covering. -/
private noncomputable def whitneyMap (f : SmoothBumpCovering ι I M s) : M → (ι → E × ℝ) :=
  fun x i ↦ (f i x • extChartAt I (f.c i) x, f i x)

private theorem contMDiff_whitneyMap [T2Space M] (f : SmoothBumpCovering ι I M s) :
    ContMDiff I 𝓘(ℝ, ι → E × ℝ) ∞ (whitneyMap f) :=
  contMDiff_pi_module_iff.2 fun i ↦
    ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

omit [IsManifold I ∞ M] [Fintype ι] in
private theorem injOn_whitneyMap (f : SmoothBumpCovering ι I M s) : InjOn (whitneyMap f) s := by
  intro x hx y _ h
  simp only [whitneyMap, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂, f.apply_ind x hx, one_smul, one_smul] at h₁
  exact (extChartAt I (f.c _)).injOn (f.mem_extChartAt_ind_source x hx)
    (f.mem_extChartAt_source_of_eq_one h₂.symm) h₁

private theorem injective_mfderiv_whitneyMap [T2Space M] (f : SmoothBumpCovering ι I M s)
    {x : M} (hx : x ∈ s) : Injective (mfderiv I 𝓘(ℝ, ι → E × ℝ) (whitneyMap f) x) := by
  -- Near `x` the bump function of index `f.ind x hx` is `1`, so the `E`-component of that index
  -- is the extended chart, whose differential is injective.
  let L : (ι → E × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.proj (f.ind x hx))
  have hL : L.comp (mfderiv I 𝓘(ℝ, ι → E × ℝ) (whitneyMap f) x) =
      mfderiv I I (chartAt H (f.c (f.ind x hx))) x := by
    have := L.hasMFDerivAt.comp x
      ((contMDiff_whitneyMap f).mdifferentiableAt (by simp)).hasMFDerivAt
    -- The two derivatives are read in the model space `E` through different models.
    convert! hasMFDerivAt_unique this _
    refine (hasMFDerivAt_extChartAt (f.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq ?_
    filter_upwards [f.eventuallyEq_one x hx] with y hy
    simp [L, whitneyMap, hy]
  refine LinearMap.ker_eq_bot.1 (bot_unique ?_)
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
    (f.mem_chartAt_ind_source x hx), ← hL]
  exact LinearMap.ker_le_ker_comp _ _

end TauCeti.SmoothEmbedding

open TauCeti.SmoothEmbedding in
/-- **A Euclidean embedding near a compact set.** A compact subset `K` of a Hausdorff
boundaryless manifold modelled on a finite-dimensional space has an open neighbourhood `W` with
compact closure which, as an open submanifold, has a smooth embedding into some Euclidean
space. -/
theorem IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean [I.Boundaryless] [T2Space M]
    {K : Set M} (hK : IsCompact K) :
    ∃ W : Opens M, K ⊆ W ∧ IsCompact (closure (W : Set M)) ∧ ∃ n : ℕ,
      Nonempty (TauCeti.SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ W
        (EuclideanSpace ℝ (Fin n))) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  obtain ⟨ι, _, f, -⟩ :=
    hL.exists_smoothBumpCovering_isSubordinate I (U := fun _ ↦ univ) fun _ _ ↦ Filter.univ_mem
  -- The Whitney map of a finite bump covering of `L`, read in a Euclidean space.
  let V := ι → E × ℝ
  let eV : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let F : M → EuclideanSpace ℝ (Fin (finrank ℝ V)) := eV ∘ whitneyMap f
  have hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ V))) ∞ F :=
    eV.toDiffeomorph.contMDiff.comp (contMDiff_whitneyMap f)
  have hFd {x : M} (hx : x ∈ L) :
      Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ V))) F x) := by
    rw [mfderiv_comp _ eV.differentiableAt.mdifferentiableAt
      ((contMDiff_whitneyMap f).mdifferentiableAt (by simp)), eV.mfderiv_eq]
    exact eV.injective.comp (injective_mfderiv_whitneyMap f hx)
  -- On the interior of `L` it is a smooth embedding, being injective on the compact set `L`.
  let W : Opens M := ⟨interior L, isOpen_interior⟩
  have hemb : IsEmbedding (F ∘ ((↑) : W → M)) := by
    have : CompactSpace L := isCompact_iff_compactSpace.1 hL
    exact ((hF.continuous.comp continuous_subtype_val).isClosedEmbedding
      (eV.injective.comp_injOn (injOn_whitneyMap f)).injective).isEmbedding.comp
        (IsEmbedding.inclusion interior_subset)
  refine ⟨W, hKL, hL.closure_of_subset interior_subset, _, ⟨.ofIsSmoothEmbedding _
    ⟨(hF.comp contMDiff_subtype_val).isImmersion_of_injective_mfderiv (by simp) fun x v w hvw ↦
      hFd (interior_subset x.2) ?_, hemb⟩⟩⟩
  rwa [← TauCeti.Manifold.mfderiv_comp_subtype_val_apply,
    ← TauCeti.Manifold.mfderiv_comp_subtype_val_apply]
