/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Smooth cutoff functions around compact sets

On a Hausdorff manifold modelled on a finite-dimensional real space, a compact set `K` inside an
open set `W` has a smooth cutoff function: a smooth `σ : M → [0, 1]`, equal to `1` on a
neighbourhood of `K`, whose support is a compact subset of `W`
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`).

Mathlib's smooth Urysohn lemma `exists_contMDiffMap_one_nhds_of_subset_interior` gives such a
function for a closed set, but assumes the manifold σ-compact and does not make the support
compact. Here neither is needed, since finitely many bump functions cover `K`. Cutoffs of this
form extend a vector field given near a compact set to a compactly supported one, and so a
complete one. For the same reason a compact set has a smooth bump covering indexed by a finite type
and subordinate to any given neighbourhoods of its points
(`IsCompact.exists_smoothBumpCovering_isSubordinate`), the input of Mathlib's Whitney embedding
`SmoothBumpCovering.embeddingPiTangent`, as well as a finite smooth partition of unity on `K`
subordinate to any open cover (`IsCompact.exists_finset_contMDiff_sum_eq_one_on`).

The construction, smoothing a finite sum of bump functions by `Real.smoothTransition`, follows the
bump cover in the proof of `TauCeti.exists_vectorField_mvfderiv_eq_neg_one`.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

variable (I) in
/-- **A smooth cutoff around a compact set.** If `K` is a compact subset of an open set `W` of a
Hausdorff manifold modelled on a finite-dimensional space, there is a smooth function
`σ : M → [0, 1]` equal to `1` on a neighbourhood of `K` whose topological support is a compact
subset of `W`. -/
theorem IsCompact.exists_contMDiff_one_nhds_tsupport_subset {K W : Set M} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ σ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ σ ∧ (∀ᶠ x in 𝓝ˢ K, σ x = 1) ∧ HasCompactSupport σ ∧
      tsupport σ ⊆ W ∧ ∀ x, σ x ∈ Icc 0 1 := by
  -- Bump functions at the points of `K` supported in `W`; finitely many of the open sets where
  -- one of them is `1` cover `K`.
  choose ρ hρ using fun x : K ↦
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 (hW.mem_nhds (hKW x.2))
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  -- Smoothing the sum of these bumps by a smooth step function gives a cutoff which is `1` where
  -- one of them is, and `0` off their supports.
  set C := ⋃ i ∈ t, tsupport (ρ i)
  have hC : IsCompact C := t.isCompact_biUnion fun i _ ↦ (ρ i).hasCompactSupport
  have hσC : ∀ y ∉ C, Real.smoothTransition (∑ i ∈ t, ρ i y) = 0 := fun y hy ↦ by
    have h0 : ∀ i ∈ t, ρ i y = 0 := fun i hi ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (mem_iUnion₂.2 ⟨i, hi, h⟩)
    simp [Finset.sum_eq_zero h0]
  have hsupp : tsupport (fun y ↦ Real.smoothTransition (∑ i ∈ t, ρ i y)) ⊆ C :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ mem_support.1 hy (hσC y h)) hC.isClosed
  refine ⟨fun y ↦ Real.smoothTransition (∑ i ∈ t, ρ i y),
    Real.smoothTransition.contDiff.contMDiff.comp (ContMDiff.sum fun i _ ↦ (ρ i).contMDiff),
    ?_, hC.of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans (iUnion₂_subset fun i _ ↦ (hρ i).2),
    fun y ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  filter_upwards [(isOpen_biUnion fun _ _ ↦ isOpen_interior).mem_nhdsSet.2 ht] with y hy
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
  refine Real.smoothTransition.one_of_one_le ?_
  have := Finset.single_le_sum (fun j _ ↦ (ρ j).nonneg) hi (f := fun j ↦ ρ j y)
  rwa [(interior_subset hyi : ρ i y = 1)] at this

omit [IsManifold I ∞ M] in
variable (I) in
/-- **A finite smooth bump covering of a compact set.** If `K` is a compact subset of a Hausdorff
manifold modelled on a finite-dimensional space and `U x` is a neighbourhood of `x` for every
`x ∈ K`, there is a smooth bump covering of `K` indexed by a finite type and subordinate to `U`.

Mathlib's `SmoothBumpCovering.exists_isSubordinate` covers a closed set of a σ-compact manifold,
with an index type which need not be finite. -/
theorem IsCompact.exists_smoothBumpCovering_isSubordinate {K : Set M} (hK : IsCompact K)
    {U : M → Set M} (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : SmoothBumpCovering ι I M K), f.IsSubordinate U := by
  -- Bump functions at the points of `K` supported in `U`; finitely many of the open sets where
  -- one of them is `1` cover `K`.
  choose ρ hρ using fun x : K ↦
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 (hU x x.2)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  refine ⟨t, inferInstance, ⟨fun i ↦ i.1, fun i ↦ ρ i.1, fun i ↦ i.1.2,
    locallyFinite_of_finite _, fun x hx ↦ ?_⟩, fun i ↦ (hρ i.1).2⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  exact ⟨⟨i, hi⟩, mem_interior_iff_mem_nhds.1 hxi⟩

variable (I) in
/-- **A finite smooth partition of unity on a compact set subordinate to an open cover.**
Given a compact set `K` covered by open sets `U j`, there exist a finite set of indices `s` and
compactly supported smooth functions `η j : M → [0, 1]` with `tsupport (η j) ⊆ U j` whose sum over
`s` equals `1` on `K` and is at most `1` everywhere. -/
theorem IsCompact.exists_finset_contMDiff_sum_eq_one_on {K : Set M} (hK : IsCompact K)
    {κ : Type*} {U : κ → Set M} (hUo : ∀ j, IsOpen (U j)) (hKcov : K ⊆ ⋃ j, U j) :
    ∃ (s : Finset κ) (η : κ → C^∞⟮I, M; ℝ⟯),
      (∀ j, tsupport (η j) ⊆ U j) ∧
      (∀ j, HasCompactSupport (η j)) ∧
      (∀ j x, η j x ∈ Icc 0 1) ∧
      (∀ x ∈ K, ∑ j ∈ s, η j x = 1) ∧
      ∀ x, ∑ j ∈ s, η j x ≤ 1 := by
  classical
  -- Step 1: Assign each point of `K` an open set `U (idx x)` and build a finite smooth bump cover.
  choose idx hidx using fun x : K ↦ mem_iUnion.1 (hKcov x.2)
  let W : M → Set M := fun x ↦ if hx : x ∈ K then U (idx ⟨x, hx⟩) else univ
  have hW : ∀ x ∈ K, W x ∈ 𝓝 x := fun x hx ↦ by
    simpa only [W, hx, ↓reduceDIte] using (hUo _).mem_nhds (hidx ⟨x, hx⟩)
  obtain ⟨α, _, fs, hsub⟩ := hK.exists_smoothBumpCovering_isSubordinate I hW
  let ρ : SmoothPartitionOfUnity α I M K := fs.toSmoothPartitionOfUnity
  have hρsub : ∀ b : α, tsupport (ρ b) ⊆ U (idx ⟨fs.c b, fs.c_mem' b⟩) := fun b ↦ by
    simpa only [W, fs.c_mem' b, ↓reduceDIte] using hsub.toSmoothPartitionOfUnity b
  have hρcomp : ∀ b : α, HasCompactSupport (ρ b) := fun b ↦
    (fs b).hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
      (closure_mono (fs.support_toSmoothPartitionOfUnity_subset b))
  -- Step 2: Regroup the finite partition of unity by the chosen cover index `idx (fs.c b)`.
  let s : Finset κ := Finset.univ.image (fun b : α ↦ idx ⟨fs.c b, fs.c_mem' b⟩)
  let fib : κ → Finset α :=
    fun j ↦ Finset.univ.filter (fun b : α ↦ idx ⟨fs.c b, fs.c_mem' b⟩ = j)
  let η : κ → C^∞⟮I, M; ℝ⟯ :=
    fun j ↦ ⟨fun x ↦ ∑ b ∈ fib j, ρ b x, ContMDiff.sum fun b _ ↦ (ρ b).contMDiff⟩
  have hη_supp : ∀ j, tsupport (η j) ⊆ ⋃ b ∈ fib j, tsupport (ρ b) := fun j ↦
    closure_minimal (fun y hy ↦ by
      by_contra hnot
      exact Function.mem_support.1 hy <| Finset.sum_eq_zero fun b hb ↦
        image_eq_zero_of_notMem_tsupport fun hmem ↦ hnot (mem_iUnion₂.2 ⟨b, hb, hmem⟩))
      ((fib j).finite_toSet.isClosed_biUnion fun b _ ↦ isClosed_tsupport _)
  have hsum : ∀ x, ∑ j ∈ s, η j x = ∑ᶠ b : α, ρ b x := fun x ↦
    (Finset.sum_fiberwise_of_maps_to
      (fun b _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ b)) (fun b ↦ ρ b x)).trans
      (finsum_eq_sum_of_fintype _).symm
  -- Step 3: Verify support subordination, compact support, `[0, 1]` bounds, and sum identities.
  refine ⟨s, η, fun j ↦ (hη_supp j).trans (iUnion₂_subset fun b hb ↦ ?_),
    fun j ↦ ((fib j).isCompact_biUnion fun b _ ↦ hρcomp b).of_isClosed_subset
      (isClosed_tsupport _) (hη_supp j),
    fun j x ↦ ⟨Finset.sum_nonneg fun b _ ↦ ρ.nonneg b x, ?_⟩,
    fun x hx ↦ (hsum x).trans (ρ.sum_eq_one hx),
    fun x ↦ (hsum x).trans_le (ρ.sum_le_one x)⟩
  · simp only [fib, Finset.mem_filter] at hb
    simpa only [hb.2] using hρsub b
  · exact (Finset.sum_le_univ_sum_of_nonneg fun b ↦ ρ.nonneg b x).trans
      ((finsum_eq_sum_of_fintype _).symm.trans_le (ρ.sum_le_one x))
