/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Analysis.Analytic.Submanifold.Dimension
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
import TauCeti.Analysis.Analytic.Submanifold.ZeroDimensional
import TauCeti.Data.Set.Lattice
import TauCeti.Geometry.RealAnalytic.Semianalytic.Decomposition
import TauCeti.Topology.Closure
import TauCeti.Topology.Connected.TotallyDisconnected
import TauCeti.Topology.DiscreteSubset

/-!
# Dimension of semianalytic sets

This file proves the dimension theory of semianalytic subsets of `ℝⁿ` that follows from the
frontier condition of the local normal decomposition
(`TauCeti.exists_isAnalyticSubmanifold_partition_subset_or_disjoint`), for two notions of
dimension: the analytic dimension `TauCeti.analyticDim` and the intrinsic dimension
`TauCeti.semialgebraicDim`.

## Analytic dimension

The dimension of a subset `A` of `ℝⁿ` is its analytic dimension `TauCeti.analyticDim A`, the
supremum of the dimensions of the analytic submanifolds contained in `A`, and its local dimension
at `x` is `TauCeti.analyticDimAt A x`, the smallest analytic dimension of a trace of `A` on a
neighbourhood of `x`. By `TauCeti.analyticDimAt_eq_iSup_of_subset_iUnion`, the local dimension is
the largest dimension of a piece contained in `A` of any local normal decomposition near `x`
compatible with `A` whose pieces have `x` in their closures, and the dimension is the supremum of
the local dimensions (`TauCeti.iSup_analyticDimAt`).

For this dimension, taking the closure does not raise the dimension, the part `closure A \ A` of
the closure outside a nonempty semianalytic set has strictly smaller dimension, and a
semianalytic germ of dimension zero is finite.

## Intrinsic dimension

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
smaller dimension. So on some neighborhood `U` of the point, `closure s ∩ U` has dimension at
most that of `s ∩ U`, and `(closure s \ s) ∩ U` has strictly smaller dimension when `s` meets
`U` (`TauCeti.SemianalyticAt.exists_mem_nhds_semialgebraicDim_closure_inter`). Since the
dimension of a set is attained near one of its points
(`TauCeti.exists_forall_mem_nhds_semialgebraicDim_inter_eq`), this gives:

* the closure of a semianalytic set has the same dimension as the set
  (`TauCeti.IsSemianalytic.semialgebraicDim_closure`), generalizing the semialgebraic case
  `TauCeti.IsSemialgebraic.semialgebraicDim_closure`, which has a direct proof that does not use
  local normal decompositions;
* the points of the closure of a nonempty semianalytic set `s` outside `s` form a set of strictly
  smaller dimension (`TauCeti.IsSemianalytic.semialgebraicDim_closure_diff_lt`).

The empty set has dimension `⊥` (`TauCeti.semialgebraicDim_empty`), and a semianalytic set has
dimension at most `0` exactly when it is closed and discrete
(`TauCeti.IsSemianalytic.semialgebraicDim_le_zero_iff`): its pieces in a local normal decomposition
are then connected and zero-dimensional, hence points, so the set is locally finite.

These statements concern the set `closure s \ s`, not the topological frontier of `s`: the
frontier of a closed set of lower dimension than the ambient space is the set itself. For
instance, for the segment `[0, 1] × {0}` in `ℝ²` the frontier is the segment itself, of the same
dimension.

## Main results

* `TauCeti.SemianalyticAt.analyticDimAt_closure`, `TauCeti.IsSemianalytic.analyticDim_closure`:
  the closure of a semianalytic set has the same local dimensions and the same dimension.
* `TauCeti.SemianalyticAt.analyticDimAt_closure_diff_lt`,
  `TauCeti.IsSemianalytic.analyticDim_closure_diff_lt`: the part of the closure outside a
  semianalytic set has strictly smaller local dimension at each point of the closure, and strictly
  smaller dimension when the set is nonempty.
* `TauCeti.SemianalyticAt.exists_mem_nhds_finite_inter`: a set semianalytic at `x` of local
  dimension at most `0` there is finite near `x`.
* `TauCeti.IsAnalyticSubmanifold.semialgebraicDim_eq`: a `d`-dimensional analytic submanifold has
  intrinsic dimension `d`.
* `TauCeti.SemianalyticAt.exists_mem_nhds_semialgebraicDim_closure_inter`,
  `TauCeti.IsSemianalytic.semialgebraicDim_closure`,
  `TauCeti.IsSemianalytic.semialgebraicDim_closure_diff_lt`: the intrinsic dimension of the
  closure, and of the part of the closure outside a semianalytic set, locally and globally.
* `TauCeti.IsSemianalytic.semialgebraicDim_le_zero_iff`: a semianalytic set has intrinsic
  dimension at most `0` if and only if it is closed and discrete.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §§15–17.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
-/

public section

open Filter Set Topology

namespace TauCeti

section AnalyticDim

variable {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}

/-- A local normal decomposition near `x` compatible with `A`, in the form used for dimension
estimates: every piece inside `A` has analytic dimension at most the local dimension of `A` at
`x`, and every piece meeting the closure of `A` is either a piece inside `A` or of strictly smaller
analytic dimension than such a piece. -/
private theorem SemianalyticAt.exists_partition_analyticDim (hA : SemianalyticAt A x) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x ∈ U ∧ 𝒞.Finite ∧ ⋃₀ 𝒞 = U ∧
      (∀ C ∈ 𝒞, IsConnected C ∧ (∃ d, IsAnalyticSubmanifold d C) ∧ (C ⊆ A ∨ Disjoint C A)) ∧
      (∀ C ∈ 𝒞, C ⊆ A → analyticDim C ≤ analyticDimAt A x) ∧
      ∀ B ∈ 𝒞, (B ∩ closure A).Nonempty →
        ∃ C ∈ 𝒞, C ⊆ A ∧ (B = C ∨ analyticDim B < analyticDim C) := by
  -- Decompose inside a neighbourhood `W` on which the local dimension of `A` is attained.
  obtain ⟨W, hW, hWeq⟩ := exists_mem_nhds_analyticDim_inter_eq A x
  obtain ⟨U, 𝒞, hUo, hxU, hUW, -, h𝒞fin, -, h𝒞cov, h𝒞cell, h𝒞front, h𝒞dim, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint (fun _ : Unit ↦ hA) hW
  -- Read off the cell data once, forgetting semianalyticity and the bound `d ≤ n`.
  have hcell : ∀ C ∈ 𝒞, IsConnected C ∧ (∃ d, IsAnalyticSubmanifold d C) ∧
      (C ⊆ A ∨ Disjoint C A) := fun C hC ↦ by
    obtain ⟨hCc, -, ⟨d, -, hd⟩, hCA⟩ := h𝒞cell C hC
    exact ⟨hCc, ⟨d, hd⟩, hCA ()⟩
  refine ⟨U, 𝒞, hUo, hxU, h𝒞fin, h𝒞cov, hcell, fun C hC hCA ↦
    hWeq W hW subset_rfl ▸ analyticDim_mono
      (subset_inter hCA ((h𝒞cov ▸ subset_sUnion_of_mem hC).trans hUW)), ?_⟩
  rintro B hB ⟨y, hyB, hyA⟩
  -- Near `y ∈ U`, the closure of `A` is the union of the closures of the pieces inside `A`.
  have hyU : y ∈ U := h𝒞cov ▸ subset_sUnion_of_mem hB hyB
  have hAU : U ∩ A = ⋃₀ {C ∈ 𝒞 | C ⊆ A} := by
    rw [sUnion_sep_subset_eq_inter fun C hC ↦ (hcell C hC).2.2, h𝒞cov, inter_comm]
  have hy : y ∈ ⋃ C ∈ {C ∈ 𝒞 | C ⊆ A}, closure C := by
    rw [← (h𝒞fin.subset (sep_subset _ _)).closure_sUnion, ← hAU]
    exact hUo.inter_closure ⟨hyU, hyA⟩
  obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := mem_iUnion₂.1 hy
  refine ⟨C, hC, hCA, or_iff_not_imp_left.2 fun hBC ↦ ?_⟩
  obtain ⟨d, hd⟩ := (hcell B hB).2.1
  obtain ⟨e, he⟩ := (hcell C hC).2.1
  rw [hd.analyticDim_eq, he.analyticDim_eq]
  exact_mod_cast h𝒞dim B hB C hC (h𝒞front B hB C hC ⟨y, hyB, hyC⟩) hBC d e hd he

/-- **The closure of a semianalytic germ has the same local dimension.** -/
theorem SemianalyticAt.analyticDimAt_closure (hA : SemianalyticAt A x) :
    analyticDimAt (closure A) x = analyticDimAt A x := by
  refine le_antisymm ?_ (analyticDimAt_mono subset_closure)
  obtain ⟨U, 𝒞, hUo, hxU, h𝒞fin, h𝒞cov, h𝒞cell, h𝒞A, h𝒞front⟩ := hA.exists_partition_analyticDim
  refine (analyticDimAt_le_analyticDim_inter (hUo.mem_nhds hxU)).trans <|
    analyticDim_le_iff.2 fun S hS d hd ↦ ?_
  -- `S ⊆ closure A ∩ U` is covered by the pieces meeting `closure A`.
  obtain ⟨B, hB, hBA, hdB⟩ := hd.exists_le_analyticDim_of_subset_inter_sUnion h𝒞fin
    (fun B hB ↦ (h𝒞cell B hB).2.1) (h𝒞cov ▸ hS)
  obtain ⟨C, hC, hCA, hBC⟩ := h𝒞front B hB hBA
  have hBC' : analyticDim B ≤ analyticDim C := hBC.elim (fun h ↦ h ▸ le_rfl) le_of_lt
  exact hdB.trans <| hBC'.trans <| h𝒞A C hC hCA

/-- **The part of the closure outside a semianalytic germ has smaller local dimension.** At a
point of the closure of a set semianalytic there, the part `closure A \ A` of the closure outside
`A` has strictly smaller local dimension than `A`. -/
theorem SemianalyticAt.analyticDimAt_closure_diff_lt (hA : SemianalyticAt A x)
    (hx : x ∈ closure A) : analyticDimAt (closure A \ A) x < analyticDimAt A x := by
  obtain ⟨U, 𝒞, hUo, hxU, h𝒞fin, h𝒞cov, h𝒞cell, h𝒞A, h𝒞front⟩ := hA.exists_partition_analyticDim
  refine (analyticDimAt_le_analyticDim_inter (hUo.mem_nhds hxU)).trans_lt ?_
  rcases ((closure A \ A) ∩ U).eq_empty_or_nonempty with h | h
  · simpa [h, bot_lt_iff_ne_bot] using hx
  obtain ⟨S, hS, d, hdim, hd⟩ := exists_isAnalyticSubmanifold_analyticDim_eq h
  rw [hdim]
  -- `S` is covered by the pieces meeting `closure A \ A`; none of them is a piece inside `A`.
  obtain ⟨B, hB, ⟨y, hyB, hyA, hyA'⟩, hdB⟩ := hd.exists_le_analyticDim_of_subset_inter_sUnion
    h𝒞fin (fun B hB ↦ (h𝒞cell B hB).2.1) (h𝒞cov ▸ hS)
  obtain ⟨C, hC, hCA, hBC⟩ := h𝒞front B hB ⟨y, hyB, hyA⟩
  have hBC' : analyticDim B < analyticDim C :=
    hBC.resolve_left fun h ↦ hyA' (hCA (h ▸ hyB))
  exact hdB.trans_lt <| hBC'.trans_le <| h𝒞A C hC hCA

/-- **The closure of a semianalytic set has the same dimension.** -/
theorem IsSemianalytic.analyticDim_closure (hA : IsSemianalytic A) :
    analyticDim (closure A) = analyticDim A := by
  simp_rw [← iSup_analyticDimAt, (hA.semianalyticAt _).analyticDimAt_closure]

/-- **The part of the closure outside a semianalytic set has smaller dimension.** For a nonempty
semianalytic set `A`, the part `closure A \ A` of the closure outside `A` has strictly smaller
dimension than `A`. -/
theorem IsSemianalytic.analyticDim_closure_diff_lt (hA : IsSemianalytic A) (hne : A.Nonempty) :
    analyticDim (closure A \ A) < analyticDim A := by
  rcases (closure A \ A).eq_empty_or_nonempty with h | h
  · simpa [h, bot_lt_iff_ne_bot] using hne.ne_empty
  obtain ⟨S, hS, d, hdim, hd⟩ := exists_isAnalyticSubmanifold_analyticDim_eq h
  obtain ⟨y, hy⟩ := hd.nonempty
  rw [hdim]
  exact ((hd.le_analyticDimAt hS (subset_closure hy)).trans_lt
    ((hA.semianalyticAt y).analyticDimAt_closure_diff_lt (hS hy).1)).trans_le
    analyticDimAt_le_analyticDim

/-- **Zero-dimensional semianalytic germs are finite.** If `A` is semianalytic at `x` and its local
dimension at `x` is at most `0`, then `A` is finite near `x`. -/
theorem SemianalyticAt.exists_mem_nhds_finite_inter (hA : SemianalyticAt A x)
    (h : analyticDimAt A x ≤ 0) : ∃ U ∈ 𝓝 x, (A ∩ U).Finite := by
  obtain ⟨U, 𝒞, hUo, hxU, h𝒞fin, h𝒞cov, h𝒞cell, h𝒞A, -⟩ := hA.exists_partition_analyticDim
  refine ⟨U, hUo.mem_nhds hxU, ?_⟩
  -- `A ∩ U` is the union of the pieces inside `A`, which are connected and zero-dimensional.
  rw [← h𝒞cov, ← sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒞cell C hC).2.2]
  refine (h𝒞fin.subset (sep_subset _ _)).sUnion fun C ⟨hC, hCA⟩ ↦ ?_
  obtain ⟨hCc, ⟨d, hd⟩, -⟩ := h𝒞cell C hC
  have hd0 : d = 0 := by
    have := hd.analyticDim_eq ▸ (h𝒞A C hC hCA).trans h
    exact_mod_cast le_antisymm this (by positivity)
  subst hd0
  exact (hd.isDiscrete.isTotallyDisconnected C subset_rfl hCc.isPreconnected).finite

end AnalyticDim

section SemialgebraicDim

variable {n d : ℕ} {s S : Set (Fin n → ℝ)}

/-! ### Dimension of analytic submanifolds -/

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

/-- **Local dimension of the closure.** Near a point at which `s` is semianalytic, on some
neighborhood `U`, `closure s ∩ U` has dimension at most that of `s ∩ U`, and `(closure s \ s) ∩ U`
has strictly smaller dimension than `s ∩ U` when `s` meets `U`. -/
theorem SemianalyticAt.exists_mem_nhds_semialgebraicDim_closure_inter {x : Fin n → ℝ}
    (hs : SemianalyticAt s x) :
    ∃ U ∈ 𝓝 x, semialgebraicDim (closure s ∩ U) ≤ semialgebraicDim (s ∩ U) ∧
      ((s ∩ U).Nonempty → semialgebraicDim ((closure s \ s) ∩ U) < semialgebraicDim (s ∩ U)) := by
  obtain ⟨U, 𝒞, hUo, hxU, -, -, h𝒞fin, -, h𝒞cov, h𝒞cell, h𝒞front, h𝒞dim, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint (fun _ : Unit ↦ hs) univ_mem
  -- A piece inside `s` has dimension at most that of `s ∩ U`.
  have hsU (C : Set (Fin n → ℝ)) (hC : C ∈ 𝒞) (hCs : C ⊆ s) :
      semialgebraicDim C ≤ semialgebraicDim (s ∩ U) :=
    semialgebraicDim_mono (subset_inter hCs (h𝒞cov ▸ subset_sUnion_of_mem hC))
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
    exists_mem_subset_closure_of_mem_closure_inter hUo h𝒞fin h𝒞cov.ge
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
      · exact hsU B hC hCs
      · exact (hlt B hB C hC hBC hne).le.trans (hsU C hC hCs)
  · -- The points outside `s` lie in pieces disjoint from `s`, of smaller dimension.
    let P (B : Set (Fin n → ℝ)) : Prop := ¬B ⊆ s ∧ ∃ C ∈ 𝒞, C ⊆ s ∧ B ⊆ closure C
    have hP (B : Set (Fin n → ℝ)) (hB : B ∈ {B ∈ 𝒞 | P B}) :
        semialgebraicDim B < semialgebraicDim (s ∩ U) := by
      obtain ⟨hB, hBs, C, hC, hCs, hBC⟩ := hB
      exact (hlt B hB C hC hBC fun h ↦ hBs (h ▸ hCs)).trans_le (hsU C hC hCs)
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
  obtain ⟨U, hU, hle, -⟩ := (hs.semianalyticAt x).exists_mem_nhds_semialgebraicDim_closure_inter
  exact hx U hU ▸ hle.trans (semialgebraicDim_mono inter_subset_left)

/-- **Dimension drop on `closure s \ s`.** For a nonempty semianalytic subset `s` of `ℝ ^ n`, the
points of the closure of `s` outside `s` form a set of strictly smaller dimension than `s`. -/
theorem IsSemianalytic.semialgebraicDim_closure_diff_lt (hs : IsSemianalytic s)
    (hne : s.Nonempty) : semialgebraicDim (closure s \ s) < semialgebraicDim s := by
  rcases (closure s \ s).eq_empty_or_nonempty with h | hne'
  · simpa [h, bot_lt_iff_ne_bot] using hne.ne_empty
  obtain ⟨x, hx, hxU⟩ := exists_forall_mem_nhds_semialgebraicDim_inter_eq hne'
  obtain ⟨U, hU, -, hlt⟩ := (hs.semianalyticAt x).exists_mem_nhds_semialgebraicDim_closure_inter
  -- `U` meets `s`, since it is a neighborhood of a point of the closure of `s`.
  have hsU : (s ∩ U).Nonempty := (mem_closure_iff_nhds.1 hx.1 U hU).mono (inter_comm U s).subset
  exact hxU U hU ▸ (hlt hsU).trans_le (semialgebraicDim_mono inter_subset_left)

/-- **Zero-dimensional semianalytic sets.** A semianalytic subset of `ℝ ^ n` has dimension at most
`0`, that is, it is empty or zero-dimensional, if and only if it is closed and discrete. -/
theorem IsSemianalytic.semialgebraicDim_le_zero_iff (hs : IsSemianalytic s) :
    semialgebraicDim s ≤ 0 ↔ IsClosed s ∧ IsDiscrete s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.2.semialgebraicDim_le_zero⟩
  -- It suffices that `s` meets some neighborhood of each point in a finite set.
  refine isClosed_and_isDiscrete_iff_forall_finite_inter.2 fun x ↦ ?_
  obtain ⟨U, 𝒞, hUo, hxU, -, -, h𝒞fin, -, h𝒞cov, h𝒞cell, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint (fun _ : Unit ↦ hs.semianalyticAt x)
      univ_mem
  refine ⟨U, hUo.mem_nhds hxU, ?_⟩
  rw [← h𝒞cov, ← sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒞cell C hC).2.2.2 ()]
  -- Each piece in `s` is a connected zero-dimensional analytic submanifold, hence a point.
  refine (h𝒞fin.subset (sep_subset _ _)).sUnion fun C ⟨hC, hCs⟩ ↦ ?_
  obtain ⟨hCc, -, ⟨d, -, hCd⟩, -⟩ := h𝒞cell C hC
  have hd : d ≤ 0 := by exact_mod_cast hCd.semialgebraicDim_eq ▸ (semialgebraicDim_mono hCs).trans h
  obtain rfl := Nat.le_zero.1 hd
  have := hCd.isDiscrete.to_subtype
  have := isPreconnected_iff_preconnectedSpace.1 hCc.isPreconnected
  exact (subsingleton_coe C).1 subsingleton_of_preconnected_totallyDisconnected |>.finite

end SemialgebraicDim

end TauCeti
