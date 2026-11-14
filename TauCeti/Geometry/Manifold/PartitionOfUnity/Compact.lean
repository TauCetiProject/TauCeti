/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth cutoff functions and finite partitions of unity around compact sets

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
`SmoothBumpCovering.embeddingPiTangent`.

On a `C^n` manifold (`n : ℕ∞`), each `SmoothBumpFunction` is of class `C^n`
(`SmoothBumpFunction.contMDiff_of_isManifold`), and any `BumpCovering` by `C^n` functions yields a
`C^n` partition of unity (`BumpCovering.contMDiff_toPartitionOfUnity_of_le`). Combining these with
`IsCompact.exists_smoothBumpCovering_isSubordinate` gives a finite `C^n` partition of unity by
compactly supported functions subordinate to any neighbourhood cover of `K`, without assuming
σ-compactness (`IsCompact.exists_contMDiffMap_partitionOfUnity`).

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

section FiniteOrder

omit [IsManifold I ∞ M]

/-- On a `C^n` manifold (`n : ℕ∞`), every `SmoothBumpFunction` is of class `C^n`. Mathlib's
`SmoothBumpFunction.contMDiff` assumes `C^∞` manifold structure, whereas the coordinate bump is
`C^∞` and only requires the extended chart to be `C^n`. -/
theorem SmoothBumpFunction.contMDiff_of_isManifold {n : ℕ∞} [IsManifold I n M] {c : M}
    (f : SmoothBumpFunction I c) : ContMDiff I 𝓘(ℝ) n f := by
  refine contMDiff_of_tsupport fun x hx ↦ ?_
  have hxs : x ∈ (chartAt H c).source := f.tsupport_subset_chartAt_source hx
  refine ContMDiffAt.congr_of_eventuallyEq ?_ <| f.eqOn_source.eventuallyEq_of_mem <|
    (chartAt H c).open_source.mem_nhds hxs
  exact (f.contDiffAt.of_le (by exact_mod_cast le_top)).contMDiffAt.comp _
    (contMDiffAt_extChartAt' hxs)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- If every function in a `BumpCovering` is `C^n`, each weight of its associated partition of
unity is `C^n`. -/
theorem BumpCovering.contMDiff_toPartitionOfUnity_of_le {ι : Type*} {s : Set M} {n : ℕ∞ω}
    (f : BumpCovering ι M s) (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) (i : ι) :
    ContMDiff I 𝓘(ℝ) n (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ ↦ contMDiff_const.sub (hf j)) <| by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

variable (I) in
/-- **A finite `C^n` partition of unity on a compact set.** Let `K` be a compact subset of a
Hausdorff `C^n` manifold (`n : ℕ∞`) modelled on a finite-dimensional real space, and let `U` be a
family of sets such that every point of `K` has some `U j` as a neighbourhood. Then there is a
finite family `χ : ι → C^n⟮I, M; 𝓘(ℝ), ℝ⟯` of compactly supported nonnegative `C^n` functions,
each supported in one of the `U j`, whose sum is at most `1` everywhere and equals `1` on `K`. No
σ-compactness hypothesis on `M` is needed. -/
theorem IsCompact.exists_contMDiffMap_partitionOfUnity {n : ℕ∞} [IsManifold I n M]
    {K : Set M} (hK : IsCompact K) {κ : Type*} {U : κ → Set M}
    (hU : ∀ x ∈ K, ∃ j, U j ∈ 𝓝 x) :
    ∃ (ι : Type u) (_ : Fintype ι) (r : ι → κ) (χ : ι → C^n⟮I, M; 𝓘(ℝ), ℝ⟯),
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ U (r i)) ∧
      (∀ i x, 0 ≤ χ i x) ∧
      (∀ x, ∑ i, χ i x ≤ 1) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  classical
  let V : M → Set M := fun x ↦ if hx : x ∈ K then U (hU x hx).choose else univ
  obtain ⟨ι, hfin, f, hfsub⟩ := hK.exists_smoothBumpCovering_isSubordinate I (U := V) fun x hx ↦ by
    simpa only [V, hx, ↓reduceDIte] using (hU x hx).choose_spec
  let r : ι → κ := fun i ↦ (hU (f.c i) (f.c_mem' i)).choose
  let B : BumpCovering ι M K :=
    { toFun i := ⟨f i, (f i).contMDiff_of_isManifold (n := n).continuous⟩
      locallyFinite' := f.locallyFinite
      nonneg' i _ := (f i).nonneg
      le_one' i _ := (f i).le_one
      eventuallyEq_one' := f.eventuallyEq_one' }
  let χ : ι → C^n⟮I, M; 𝓘(ℝ), ℝ⟯ := fun i ↦
    ⟨B.toPartitionOfUnity i,
      B.contMDiff_toPartitionOfUnity_of_le (fun j ↦ (f j).contMDiff_of_isManifold) i⟩
  have hsupp (i : ι) : tsupport (χ i) ⊆ tsupport (f i) :=
    closure_mono (B.support_toPartitionOfUnity_subset i)
  refine ⟨ι, hfin, r, χ,
    fun i ↦ (f i).hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (hsupp i),
    fun i ↦ (hsupp i).trans ?_,
    fun i x ↦ B.toPartitionOfUnity.nonneg i x,
    fun x ↦ ?_, fun x hx ↦ ?_⟩
  · simpa only [V, f.c_mem' i, ↓reduceDIte] using hfsub i
  · simpa only [← finsum_eq_sum_of_fintype, χ, ContMDiffMap.coeFn_mk] using
      B.toPartitionOfUnity.sum_le_one x
  · simpa only [← finsum_eq_sum_of_fintype, χ, ContMDiffMap.coeFn_mk] using
      B.toPartitionOfUnity.sum_eq_one hx

end FiniteOrder
