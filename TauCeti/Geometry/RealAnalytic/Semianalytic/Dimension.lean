/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Dimension
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
import TauCeti.Analysis.Analytic.Submanifold.ZeroDimensional
import TauCeti.Data.Set.Lattice
import TauCeti.Geometry.RealAnalytic.Semianalytic.Decomposition
import TauCeti.Topology.Connected.TotallyDisconnected

/-!
# Dimension of semianalytic sets

The dimension of a subset `A` of `ℝⁿ` is its analytic dimension `TauCeti.analyticDim A`, the
supremum of the dimensions of the analytic submanifolds contained in `A`, and its local dimension
at `x` is `TauCeti.analyticDimAt A x`, the smallest analytic dimension of a trace of `A` on a
neighbourhood of `x`. By `TauCeti.analyticDimAt_eq_iSup_of_subset_iUnion`, the local dimension is
the largest dimension of a piece contained in `A` of any local normal decomposition near `x`
compatible with `A` whose pieces have `x` in their closures, and the dimension is the supremum of
the local dimensions (`TauCeti.iSup_analyticDimAt`).

This file proves the dimension theory of semianalytic sets that follows from the frontier
condition of the local normal decomposition
(`TauCeti.exists_isAnalyticSubmanifold_partition_subset_or_disjoint`): taking the closure does not
raise the dimension, the part `closure A \ A` of the closure outside a nonempty semianalytic set
has strictly smaller dimension, and a semianalytic germ of dimension zero is finite.

The statement concerns `closure A \ A`, not the ambient boundary: for the segment
`[0, 1] × {0}` in `ℝ²` the frontier is the segment itself, of the same dimension.

## Main results

* `TauCeti.SemianalyticAt.analyticDimAt_closure`, `TauCeti.IsSemianalytic.analyticDim_closure`:
  the closure of a semianalytic set has the same local dimensions and the same dimension.
* `TauCeti.SemianalyticAt.analyticDimAt_closure_diff_lt`,
  `TauCeti.IsSemianalytic.analyticDim_closure_diff_lt`: the part of the closure outside a
  semianalytic set has strictly smaller local dimension at each point of the closure, and strictly
  smaller dimension when the set is nonempty.
* `TauCeti.SemianalyticAt.exists_mem_nhds_finite_inter`: a set semianalytic at `x` of local
  dimension at most `0` there is finite near `x`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
-/

public section

open Set Topology

namespace TauCeti

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
  refine ⟨U, 𝒞, hUo, hxU, h𝒞fin, h𝒞cov, fun C hC ↦ ⟨(h𝒞cell C hC).1,
    (h𝒞cell C hC).2.2.1.imp fun _ h ↦ h.2, (h𝒞cell C hC).2.2.2 ()⟩, fun C hC hCA ↦
    hWeq W hW subset_rfl ▸ analyticDim_mono
      (subset_inter hCA ((h𝒞cov ▸ subset_sUnion_of_mem hC).trans hUW)), ?_⟩
  rintro B hB ⟨y, hyB, hyA⟩
  -- Near `y ∈ U`, the closure of `A` is the union of the closures of the pieces inside `A`.
  have hyU : y ∈ U := h𝒞cov ▸ subset_sUnion_of_mem hB hyB
  have hAU : U ∩ A = ⋃₀ {C ∈ 𝒞 | C ⊆ A} := by
    rw [sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒞cell C hC).2.2.2 (), h𝒞cov, inter_comm]
  have hy : y ∈ ⋃ C ∈ {C ∈ 𝒞 | C ⊆ A}, closure C := by
    rw [← (h𝒞fin.subset (sep_subset _ _)).closure_sUnion, ← hAU]
    exact hUo.inter_closure ⟨hyU, hyA⟩
  obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := mem_iUnion₂.1 hy
  refine ⟨C, hC, hCA, or_iff_not_imp_left.2 fun hBC ↦ ?_⟩
  obtain ⟨d, hd⟩ := (h𝒞cell B hB).2.2.1.imp fun _ h ↦ h.2
  obtain ⟨e, he⟩ := (h𝒞cell C hC).2.2.1.imp fun _ h ↦ h.2
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
  obtain ⟨B, ⟨hB, hBA⟩, hdB⟩ := hd.exists_le_analyticDim_of_subset_sUnion
    (𝒞 := {B ∈ 𝒞 | (B ∩ closure A).Nonempty}) (h𝒞fin.subset (sep_subset _ _))
    (fun B hB ↦ (h𝒞cell B hB.1).2.1) fun y hy ↦ by
      obtain ⟨B, hB, hyB⟩ := mem_sUnion.1 (h𝒞cov ▸ (hS hy).2)
      exact ⟨B, ⟨hB, y, hyB, (hS hy).1⟩, hyB⟩
  obtain ⟨C, hC, hCA, hBC⟩ := h𝒞front B hB hBA
  have hBC' : analyticDim B ≤ analyticDim C := hBC.elim (fun h ↦ h ▸ le_rfl) le_of_lt
  exact hdB.trans <| hBC'.trans <| h𝒞A C hC hCA

/-- **The frontier of a semianalytic germ has smaller local dimension.** At a point of the closure
of a set semianalytic there, the part `closure A \ A` of the closure outside `A` has strictly
smaller local dimension than `A`. -/
theorem SemianalyticAt.analyticDimAt_closure_diff_lt (hA : SemianalyticAt A x)
    (hx : x ∈ closure A) : analyticDimAt (closure A \ A) x < analyticDimAt A x := by
  obtain ⟨U, 𝒞, hUo, hxU, h𝒞fin, h𝒞cov, h𝒞cell, h𝒞A, h𝒞front⟩ := hA.exists_partition_analyticDim
  refine (analyticDimAt_le_analyticDim_inter (hUo.mem_nhds hxU)).trans_lt ?_
  rcases ((closure A \ A) ∩ U).eq_empty_or_nonempty with h | h
  · rw [h, analyticDim_empty, bot_lt_iff_ne_bot, Ne, analyticDimAt_eq_bot_iff, not_not]
    exact hx
  obtain ⟨S, hS, d, hdim, hd⟩ := exists_isAnalyticSubmanifold_analyticDim_eq h
  rw [hdim]
  -- `S` is covered by the pieces meeting `closure A \ A`; none of them is a piece inside `A`.
  obtain ⟨B, ⟨hB, y, hyB, hyA, hyA'⟩, hdB⟩ := hd.exists_le_analyticDim_of_subset_sUnion
    (𝒞 := {B ∈ 𝒞 | (B ∩ (closure A \ A)).Nonempty}) (h𝒞fin.subset (sep_subset _ _))
    (fun B hB ↦ (h𝒞cell B hB.1).2.1) fun y hy ↦ by
      obtain ⟨B, hB, hyB⟩ := mem_sUnion.1 (h𝒞cov ▸ (hS hy).2)
      exact ⟨B, ⟨hB, y, hyB, (hS hy).1⟩, hyB⟩
  obtain ⟨C, hC, hCA, hBC⟩ := h𝒞front B hB ⟨y, hyB, hyA⟩
  have hBC' : analyticDim B < analyticDim C :=
    hBC.resolve_left fun h ↦ hyA' (hCA (h ▸ hyB))
  exact hdB.trans_lt <| hBC'.trans_le <| h𝒞A C hC hCA

/-- **The closure of a semianalytic set has the same dimension.** -/
theorem IsSemianalytic.analyticDim_closure (hA : IsSemianalytic A) :
    analyticDim (closure A) = analyticDim A := by
  simp_rw [← iSup_analyticDimAt, (hA.semianalyticAt _).analyticDimAt_closure]

/-- **The frontier of a semianalytic set has smaller dimension.** For a nonempty semianalytic set
`A`, the part `closure A \ A` of the closure outside `A` has strictly smaller dimension than `A`.
-/
theorem IsSemianalytic.analyticDim_closure_diff_lt (hA : IsSemianalytic A) (hne : A.Nonempty) :
    analyticDim (closure A \ A) < analyticDim A := by
  rcases (closure A \ A).eq_empty_or_nonempty with h | h
  · rw [h, analyticDim_empty, bot_lt_iff_ne_bot, Ne, analyticDim_eq_bot_iff]
    exact hne.ne_empty
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

end TauCeti
