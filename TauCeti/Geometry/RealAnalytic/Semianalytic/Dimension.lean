/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
import TauCeti.Analysis.Analytic.Submanifold.ZeroDimensional
import TauCeti.Data.Set.Lattice
import TauCeti.Geometry.RealAnalytic.Semianalytic.Decomposition

/-!
# Dimension of semianalytic sets

We use the intrinsic dimension `TauCeti.semialgebraicDim` of subsets of `ℝ ^ n`: the supremum of
the `d` such that the set contains a nonempty subset homeomorphic to an open subset of `ℝ ^ d`,
with the empty set of dimension `⊥`. A `d`-dimensional analytic submanifold has dimension `d`
(`TauCeti.IsAnalyticSubmanifold.semialgebraicDim_eq`), since its analytic charts identify it
locally with open subsets of `ℝ ^ d`. Since analytic submanifolds are locally closed, the dimension
of a finite union of them is their largest dimension
(`TauCeti.semialgebraicDim_sUnion_of_isLocallyClosed`). So if an open set `U` is partitioned into
finitely many analytic submanifolds each inside or outside a set `s`, as by a local normal
decomposition of a semianalytic germ, the dimension of `s ∩ U` is the largest dimension of the
pieces inside `s`; in particular this maximum does not depend on the decomposition.

The frontier condition of the local normal decompositions
(`TauCeti.exists_isAnalyticSubmanifold_partition_subset_or_disjoint`) controls the dimension of
closures. Near any point, the closure of a semianalytic set `s` is covered by the pieces lying in
the closure of a piece contained in `s`, and such a piece is either that piece or has strictly
smaller dimension. Since the dimension of a set is attained near one of its points
(`TauCeti.exists_forall_mem_nhds_semialgebraicDim_inter_eq`), this gives:

* the closure of a semianalytic set has the same dimension as the set
  (`TauCeti.IsSemianalytic.semialgebraicDim_closure`);
* the points of the closure of a nonempty semianalytic set `s` outside `s` form a set of strictly
  smaller dimension (`TauCeti.IsSemianalytic.semialgebraicDim_closure_diff_lt`).

The empty set has dimension `⊥` (`TauCeti.semialgebraicDim_empty`), and a semianalytic set has
dimension at most `0` exactly when it is closed and discrete
(`TauCeti.IsSemianalytic.semialgebraicDim_le_zero_iff`): its pieces in a local normal decomposition
are then connected and zero-dimensional, hence points, so the set is locally finite.

These statements concern the set `closure s \ s`, not the topological frontier of `s`: the
frontier of a closed set of lower dimension than the ambient space is the set itself.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §§15–17.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {n d : ℕ} {s S : Set (Fin n → ℝ)}

/-! ### Dimension of analytic submanifolds -/

/-- Through the first `d` coordinates of an analytic chart of `S` in dimension `d ≤ n`, the part of
`S` in the source of the chart is homeomorphic to an open subset of `ℝ ^ d`. -/
private theorem IsAnalyticChart.isOpenEmbedding_firstCoords
    {e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} (he : IsAnalyticChart d S e)
    (hd : d ≤ n) : IsOpenEmbedding fun y : ↥(e.source ∩ S) ↦ firstCoords ℝ n d (e y) := by
  -- `firstCoords ℝ d n` recovers the chart image of a point of `S` from its first coordinates.
  have hleft (y : ↥(e.source ∩ S)) : firstCoords ℝ d n (firstCoords ℝ n d (e y)) = e y :=
    he.firstCoords_firstCoords_apply y.property.1 y.property.2
  have hemb : IsEmbedding fun y : ↥(e.source ∩ S) ↦ e y :=
    e.isOpenEmbedding_restrict.isEmbedding.comp (IsEmbedding.inclusion inter_subset_left)
  refine ⟨.of_comp ((firstCoords ℝ n d).continuous.comp hemb.continuous)
    (firstCoords ℝ d n).continuous (by simpa only [Function.comp_def, hleft] using hemb), ?_⟩
  -- The image is the open set of `u` with `(u, 0)` in the target of the chart.
  suffices h : range (fun y : ↥(e.source ∩ S) ↦ firstCoords ℝ n d (e y)) =
      firstCoords ℝ d n ⁻¹' e.target by
    rw [h]
    exact e.open_target.preimage (firstCoords ℝ d n).continuous
  ext u
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    rw [mem_preimage, hleft]
    exact e.map_source y.property.1
  · have hsource := e.map_target hu
    refine ⟨⟨e.symm (firstCoords ℝ d n u), hsource, (he.mem_iff hsource).2 fun i hi ↦ ?_⟩, ?_⟩
    · rw [e.right_inv hu]
      exact firstCoords_apply_of_le u hi
    · simp only [e.right_inv hu, firstCoords_firstCoords_of_le hd]

/-- **Dimension of analytic submanifolds.** A `d`-dimensional analytic submanifold of `ℝ ^ n` has
dimension `d`. -/
theorem IsAnalyticSubmanifold.semialgebraicDim_eq (hS : IsAnalyticSubmanifold d S) :
    semialgebraicDim S = d := by
  obtain ⟨x, hx, hdim⟩ := exists_forall_mem_nhds_semialgebraicDim_inter_eq hS.nonempty
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
  rw [← hdim e.source (e.open_source.mem_nhds hxe), inter_comm]
  exact semialgebraicDim_eq_of_isOpenEmbedding (s := e.source ∩ S) ⟨x, hxe, hx⟩
    (he.isOpenEmbedding_firstCoords hS.le)

/-! ### Closures of semianalytic sets -/

/-- In a finite partition of an open set `U` into pieces each inside or outside `s`, satisfying the
first part of the frontier condition, every point of `closure s ∩ U` lies in a piece contained in
the closure of a piece contained in `s`. -/
private theorem exists_mem_subset_closure_of_mem_closure_inter {s U : Set (Fin n → ℝ)}
    {𝒞 : Set (Set (Fin n → ℝ))} (hUo : IsOpen U) (h𝒞fin : 𝒞.Finite) (h𝒞cov : ⋃₀ 𝒞 = U)
    (hs : ∀ C ∈ 𝒞, C ⊆ s ∨ Disjoint C s)
    (h𝒞front : ∀ B ∈ 𝒞, ∀ C ∈ 𝒞, (B ∩ closure C).Nonempty → B ⊆ closure C)
    {y : Fin n → ℝ} (hy : y ∈ closure s ∩ U) :
    ∃ B ∈ 𝒞, y ∈ B ∧ ∃ C ∈ 𝒞, C ⊆ s ∧ B ⊆ closure C := by
  obtain ⟨B, hB, hyB⟩ := mem_sUnion.1 (h𝒞cov ▸ hy.2)
  -- Since `U` is open, `y` lies in the closure of `s ∩ U`, the union of the pieces in `s`.
  have hyC : y ∈ closure (⋃ C ∈ {C ∈ 𝒞 | C ⊆ s}, C) := by
    rw [← sUnion_eq_biUnion, sUnion_sep_subset_eq_inter hs, h𝒞cov]
    exact hUo.inter_closure ⟨hy.2, hy.1⟩ |> closure_mono (inter_comm U s).subset
  rw [(h𝒞fin.subset (sep_subset _ _)).closure_biUnion] at hyC
  obtain ⟨C, ⟨hC, hCs⟩, hyC⟩ := mem_iUnion₂.1 hyC
  exact ⟨B, hB, hyB, C, hC, hCs, h𝒞front B hB C hC ⟨y, hyB, hyC⟩⟩

/-- Near a point at which `s` is semianalytic, the closure of `s` has dimension at most that of
`s`, and the points of the closure outside `s` have strictly smaller dimension when `s` is
nonempty. -/
private theorem SemianalyticAt.exists_semialgebraicDim_closure_inter {x : Fin n → ℝ}
    (hs : SemianalyticAt s x) :
    ∃ U ∈ 𝓝 x, semialgebraicDim (closure s ∩ U) ≤ semialgebraicDim s ∧
      (s.Nonempty → semialgebraicDim ((closure s \ s) ∩ U) < semialgebraicDim s) := by
  obtain ⟨U, 𝒞, hUo, hxU, -, -, h𝒞fin, -, h𝒞cov, h𝒞cell, h𝒞front, h𝒞dim, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint (fun _ : Unit ↦ hs) univ_mem
  have hdim (C : Set (Fin n → ℝ)) (hC : C ∈ 𝒞) :
      ∃ d : ℕ, IsAnalyticSubmanifold d C ∧ semialgebraicDim C = d := by
    obtain ⟨d, -, hd⟩ := (h𝒞cell C hC).2.2.1
    exact ⟨d, hd, hd.semialgebraicDim_eq⟩
  -- A piece in the closure of a different piece has strictly smaller dimension.
  have hlt (B : Set (Fin n → ℝ)) (hB : B ∈ 𝒞) (C : Set (Fin n → ℝ)) (hC : C ∈ 𝒞)
      (hBC : B ⊆ closure C) (hne : B ≠ C) : semialgebraicDim B < semialgebraicDim C := by
    obtain ⟨d, hBd, hd⟩ := hdim B hB
    obtain ⟨e, hCe, he⟩ := hdim C hC
    rw [hd, he]
    exact_mod_cast h𝒞dim B hB C hC hBC hne d e hBd hCe
  have hcover (y : Fin n → ℝ) (hy : y ∈ closure s ∩ U) :=
    exists_mem_subset_closure_of_mem_closure_inter hUo h𝒞fin h𝒞cov
      (fun C hC ↦ (h𝒞cell C hC).2.2.2 ()) h𝒞front hy
  -- The dimension of a set covered by finitely many pieces is bounded by their dimensions.
  have hbound (t : Set (Fin n → ℝ)) (P : Set (Fin n → ℝ) → Prop)
      (ht : t ⊆ ⋃₀ {B ∈ 𝒞 | P B}) :
      semialgebraicDim t ≤ ⨆ B ∈ {B ∈ 𝒞 | P B}, semialgebraicDim B :=
    (semialgebraicDim_mono ht).trans_eq <| semialgebraicDim_sUnion_of_isLocallyClosed
      (h𝒞fin.subset (sep_subset _ _)) fun B hB ↦ (hdim B hB.1).choose_spec.1.isLocallyClosed
  refine ⟨U, hUo.mem_nhds hxU, ?_, fun hne ↦ ?_⟩
  · refine (hbound _ (fun B ↦ ∃ C ∈ 𝒞, C ⊆ s ∧ B ⊆ closure C) fun y hy ↦ ?_).trans <|
      iSup₂_le fun B ⟨hB, C, hC, hCs, hBC⟩ ↦ ?_
    · obtain ⟨B, hB, hyB, hBC⟩ := hcover y hy
      exact ⟨B, ⟨hB, hBC⟩, hyB⟩
    · rcases eq_or_ne B C with rfl | hne
      · exact semialgebraicDim_mono hCs
      · exact (hlt B hB C hC hBC hne).le.trans (semialgebraicDim_mono hCs)
  · -- The points outside `s` lie in pieces disjoint from `s`, of smaller dimension.
    let P (B : Set (Fin n → ℝ)) : Prop := ¬B ⊆ s ∧ ∃ C ∈ 𝒞, C ⊆ s ∧ B ⊆ closure C
    have hP (B : Set (Fin n → ℝ)) (hB : B ∈ {B ∈ 𝒞 | P B}) :
        semialgebraicDim B < semialgebraicDim s := by
      obtain ⟨hB, hBs, C, hC, hCs, hBC⟩ := hB
      exact (hlt B hB C hC hBC fun h ↦ hBs (h ▸ hCs)).trans_le (semialgebraicDim_mono hCs)
    refine (hbound _ P fun y hy ↦ ?_).trans_lt ?_
    · obtain ⟨B, hB, hyB, hBC⟩ := hcover y ⟨hy.1.1, hy.2⟩
      exact ⟨B, ⟨hB, fun h ↦ hy.1.2 (h hyB), hBC⟩, hyB⟩
    rcases eq_empty_or_nonempty {B ∈ 𝒞 | P B} with h | h
    · rw [h]
      simpa [bot_lt_iff_ne_bot] using hne.ne_empty
    · obtain ⟨B₀, hB₀, hmax⟩ := exists_max_image _ semialgebraicDim
        (h𝒞fin.subset (sep_subset _ _)) h
      exact (iSup₂_le hmax).trans_lt (hP B₀ hB₀)

/-- **Dimension of the closure.** The closure of a semianalytic subset of `ℝ ^ n` has the same
dimension as the set. -/
@[simp]
theorem IsSemianalytic.semialgebraicDim_closure (hs : IsSemianalytic s) :
    semialgebraicDim (closure s) = semialgebraicDim s := by
  refine le_antisymm ?_ (semialgebraicDim_mono subset_closure)
  rcases (closure s).eq_empty_or_nonempty with h | hne
  · simp [h]
  obtain ⟨x, -, hx⟩ := exists_forall_mem_nhds_semialgebraicDim_inter_eq hne
  obtain ⟨U, hU, hle, -⟩ := (hs.semianalyticAt x).exists_semialgebraicDim_closure_inter
  exact hx U hU ▸ hle

/-- **Dimension drop at the frontier.** For a nonempty semianalytic subset `s` of `ℝ ^ n`, the
points of the closure of `s` outside `s` form a set of strictly smaller dimension than `s`. -/
theorem IsSemianalytic.semialgebraicDim_closure_diff_lt (hs : IsSemianalytic s)
    (hne : s.Nonempty) : semialgebraicDim (closure s \ s) < semialgebraicDim s := by
  rcases (closure s \ s).eq_empty_or_nonempty with h | hne'
  · simpa [h, bot_lt_iff_ne_bot] using hne.ne_empty
  obtain ⟨x, -, hx⟩ := exists_forall_mem_nhds_semialgebraicDim_inter_eq hne'
  obtain ⟨U, hU, -, hlt⟩ := (hs.semianalyticAt x).exists_semialgebraicDim_closure_inter
  exact hx U hU ▸ hlt hne

/-- **Zero-dimensional semianalytic sets.** A semianalytic subset of `ℝ ^ n` has dimension at most
`0`, that is, it is empty or zero-dimensional, if and only if it is closed and discrete. -/
theorem IsSemianalytic.semialgebraicDim_le_zero_iff (hs : IsSemianalytic s) :
    semialgebraicDim s ≤ 0 ↔ IsClosed s ∧ IsDiscrete s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.2.semialgebraicDim_le_zero⟩
  -- It suffices that `s` meets some neighborhood of each point in a finite set.
  rw [← compl_mem_codiscrete_iff, Filter.codiscrete,
    codiscreteWithin_iff_locallyFiniteComplementWithin]
  intro x _
  obtain ⟨U, 𝒞, hUo, hxU, -, -, h𝒞fin, -, h𝒞cov, h𝒞cell, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint (fun _ : Unit ↦ hs.semianalyticAt x)
      univ_mem
  refine ⟨U, hUo.mem_nhds hxU, ?_⟩
  rw [← compl_eq_univ_sdiff, compl_compl, inter_comm, ← h𝒞cov,
    ← sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒞cell C hC).2.2.2 ()]
  -- Each piece in `s` is a connected zero-dimensional analytic submanifold, hence a point.
  refine (h𝒞fin.subset (sep_subset _ _)).sUnion fun C ⟨hC, hCs⟩ ↦ ?_
  obtain ⟨hCc, -, ⟨d, -, hCd⟩, -⟩ := h𝒞cell C hC
  have hd : d ≤ 0 := by exact_mod_cast hCd.semialgebraicDim_eq ▸ (semialgebraicDim_mono hCs).trans h
  obtain rfl := Nat.le_zero.1 hd
  have := hCd.isDiscrete.to_subtype
  have := isPreconnected_iff_preconnectedSpace.1 hCc.isPreconnected
  exact (subsingleton_coe C).1 subsingleton_of_preconnected_totallyDisconnected |>.finite

end TauCeti
