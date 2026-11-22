/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.BumpFunction

/-!
# Smooth cutoff functions and finite partitions of unity on compact sets

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
`SmoothBumpCovering.embeddingPiTangent`, as well as a finite `C^n` partition of unity subordinate
to any open cover of `K` (`IsCompact.exists_finset_contMDiff_sum_eq_one`), requiring neither
σ-compactness nor `C^∞` regularity of the manifold (`SmoothBumpFunction.contMDiff_of_isManifold`).

The cutoff construction, smoothing a finite sum of bump functions by `Real.smoothTransition`,
follows the bump cover in the proof of `TauCeti.exists_vectorField_mvfderiv_eq_neg_one`.
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
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 (hW.mem_nhds
        (hKW x.property))
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
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 (hU x x.property)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  refine ⟨t, inferInstance, ⟨fun i ↦ i.val, fun i ↦ ρ i.val, fun i ↦ i.val.property,
    locallyFinite_of_finite _, fun x hx ↦ ?_⟩, fun i ↦ (hρ i.val).2⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  exact ⟨⟨i, hi⟩, mem_interior_iff_mem_nhds.1 hxi⟩

omit [IsManifold I ∞ M] in
variable (I) in
/-- **A finite `C^n` partition of unity on a compact set.** Let `K` be a compact subset of a
Hausdorff `C^n` manifold (`n ≤ ∞`) modelled on a finite-dimensional real space, covered by open
sets `U j`. Then finitely many compactly supported `C^n` functions, subordinate to `U` and indexed
directly by the cover, are nonnegative, sum to at most `1` everywhere, and sum to `1` on `K`.

Unlike `SmoothPartitionOfUnity.exists_isSubordinate`, this requires neither σ-compactness of the
manifold nor `C^∞` regularity of the atlas. -/
theorem IsCompact.exists_finset_contMDiff_sum_eq_one
    {n : ℕ∞ω} [IsManifold I n M] (hn : n ≤ ∞)
    {K : Set M} (hK : IsCompact K) {κ : Type*} {U : κ → Set M}
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x ∈ K, ∃ j, x ∈ U j) :
    ∃ (s : Finset κ) (ρ : κ → C^n⟮I, M; ℝ⟯),
      (∀ j, tsupport (ρ j) ⊆ U j) ∧
      (∀ j, HasCompactSupport (ρ j)) ∧
      (∀ j x, 0 ≤ ρ j x) ∧
      (∀ x, ∑ j ∈ s, ρ j x ≤ 1) ∧
      (∀ x ∈ K, ∑ j ∈ s, ρ j x = 1) := by
  classical
  have : ENat.LEInfty n := ⟨hn⟩
  -- Choose a cover member for each point of `K`, then a finite subordinate bump covering.
  let W : M → Set M := fun x ↦ if hx : x ∈ K then U (hcover x hx).choose else univ
  have hW : ∀ x ∈ K, W x ∈ 𝓝 x := fun x hx ↦ by
    simpa only [W, dite_eq_left hx] using (hU _).mem_nhds (hcover x hx).choose_spec
  obtain ⟨ι, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate I hW
  let b : BumpCovering ι M K :=
    { toFun := fun i ↦ ⟨f i, ((f i).contMDiff_of_isManifold (n := n)).continuous⟩
      locallyFinite' := f.locallyFinite
      nonneg' := fun i _ ↦ (f i).nonneg
      le_one' := fun i _ ↦ (f i).le_one
      eventuallyEq_one' := f.eventuallyEq_one' }
  let P := b.toPartitionOfUnity
  have hP_cont (i : ι) : CMDiff n (P i) := by
    have heq : (P i : M → ℝ) = fun x ↦ f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x) :=
      funext (b.toPartitionOfUnity_apply i)
    rw [heq]
    refine (f i).contMDiff_of_isManifold.mul <|
      (contMDiff_finprod_cond fun j _ ↦ contMDiff_const.sub (f j).contMDiff_of_isManifold) ?_
    simpa only [mulSupport_one_sub] using f.locallyFinite
  have hP_tsupp (i : ι) : tsupport (P i) ⊆ tsupport (f i) :=
    closure_mono (b.support_toPartitionOfUnity_subset i)
  let j₀ : ι → κ := fun i ↦ (hcover (f.c i) (f.c_mem' i)).choose
  have hP_sub (i : ι) : tsupport (P i) ⊆ U (j₀ i) := by
    have hfi : tsupport (f i) ⊆ W (f.c i) := hf i
    simpa only [W, dite_eq_left (f.c_mem' i), j₀] using (hP_tsupp i).trans hfi
  have hP_cpt (i : ι) : HasCompactSupport (P i) :=
    (f i).hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (hP_tsupp i)
  -- Group the partition functions by their assigned cover index.
  let s : Finset κ := Finset.univ.image j₀
  let ρ : κ → C^n⟮I, M; ℝ⟯ := fun j ↦
    ⟨fun x ↦ ∑ i ∈ Finset.univ with j₀ i = j, P i x,
      ContMDiff.sum fun i _ ↦ hP_cont i⟩
  have hρ (j : κ) (x : M) : ρ j x = ∑ i ∈ Finset.univ with j₀ i = j, P i x := rfl
  have hsupp (j : κ) :
      tsupport (ρ j) ⊆ ⋃ i ∈ Finset.univ.filter (fun i ↦ j₀ i = j), tsupport (P i) :=
    closure_minimal (fun x hx ↦ by
      obtain ⟨i, hi, hPi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hρ j x ▸ mem_support.1 hx)
      exact mem_biUnion hi (subset_tsupport _ hPi))
      (isClosed_biUnion_finset fun _ _ ↦ isClosed_tsupport _)
  have hsum_eq (x : M) : ∑ j ∈ s, ρ j x = ∑ᶠ i, P i x := by
    simp_rw [hρ]
    rw [Finset.sum_fiberwise_of_maps_to
      (fun i _ ↦ Finset.mem_image_of_mem j₀ (Finset.mem_univ i)) (fun i ↦ P i x),
      finsum_eq_sum_of_fintype]
  refine ⟨s, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine (hsupp j).trans (iUnion₂_subset fun i hi ↦ ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi ▸ hP_sub i
  · intro j
    exact (Finset.isCompact_biUnion _ fun i _ ↦ hP_cpt i).of_isClosed_subset
      (isClosed_tsupport _) (hsupp j)
  · intro j x
    rw [hρ]
    exact Finset.sum_nonneg fun i _ ↦ P.nonneg i x
  · intro x
    rw [hsum_eq]
    exact P.sum_le_one x
  · intro x hx
    rw [hsum_eq]
    exact P.sum_eq_one hx
