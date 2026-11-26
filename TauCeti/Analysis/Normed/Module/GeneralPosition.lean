/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import TauCeti.Analysis.Normed.Affine.Generic

/-!
# Points in general position are generic

Finitely many points of a real normed space `E` can be moved, each within a prescribed nonempty
open set, into general position: for `k ≤ dim E`, so that every `k` or fewer of them are linearly
independent (`TauCeti.exists_forall_mem_and_linearIndepOn`). The points are chosen one at a time,
each avoiding the spans of fewer than `k` of the points chosen before it. These spans are proper
subspaces, and finitely many of them have open dense common complement
(`AffineSubspace.exists_mem_open_genericLocus`). In particular, taking the open sets to be small
balls, families in general position are dense.

This is the general-position step in approximating maps into `ℝⁿ` by maps missing `0`: a convex
combination of at most `k` points, every `k` of which are linearly independent, is nonzero.
-/

public section

open Module Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inductive step of `TauCeti.exists_forall_mem_and_linearIndepOn`: if every `k` or fewer of
the points `y i`, `i ∈ t`, are linearly independent, and `z` lies outside the span of every fewer
than `k` of them, then every `k` or fewer of the points of `update y a z` indexed by `insert a t`
are linearly independent. -/
private theorem linearIndepOn_update {ι : Type*} [DecidableEq ι] {k : ℕ} {y : ι → E} {t : Set ι}
    (hy : ∀ s ⊆ t, s.encard ≤ k → LinearIndepOn ℝ y s) {a : ι} {z : E}
    (hz : ∀ s ⊆ t, s.encard < k → z ∉ Submodule.span ℝ (y '' s)) {s : Set ι}
    (hs : s ⊆ insert a t) (hsk : s.encard ≤ k) : LinearIndepOn ℝ (Function.update y a z) s := by
  have hEq {u : Set ι} (hu : a ∉ u) : EqOn (Function.update y a z) y u :=
    fun i hi ↦ Function.update_of_ne (ne_of_mem_of_not_mem hi hu) z y
  by_cases ha : a ∈ s
  · -- Split off the new point `a`; the others are old points, fewer than `k` of them.
    have hsa : s \ {a} ⊆ t := fun i hi ↦ (hs hi.1).resolve_left hi.2
    have hlt : (s \ {a}).encard < k := by
      rw [← encard_sdiff_singleton_add_one ha] at hsk
      have hne : (s \ {a}).encard ≠ ⊤ :=
        ((le_self_add.trans hsk).trans_lt (ENat.natCast_lt_top k)).ne
      exact (ENat.add_one_le_iff hne).1 hsk
    have hnot : a ∉ s \ {a} := fun h ↦ h.2 rfl
    rw [← insert_sdiff_self_of_mem ha, linearIndepOn_insert hnot,
      linearIndepOn_congr (hEq hnot), image_congr (hEq hnot), Function.update_self]
    exact ⟨hy _ hsa hlt.le, hz _ hsa hlt⟩
  · exact (linearIndepOn_congr (hEq ha)).2
      (hy s (fun i hi ↦ (hs hi).resolve_left (ne_of_mem_of_not_mem hi ha)) hsk)

/-- **Points in general position are generic.** Given nonempty open sets `O i` of a real normed
space `E`, indexed by a finite type, and `k ≤ dim E`, there are points `y i ∈ O i` every `k` or
fewer of which are linearly independent. -/
theorem exists_forall_mem_and_linearIndepOn {ι : Type*} [Finite ι] {k : ℕ}
    (hk : k ≤ finrank ℝ E) {O : ι → Set E} (hO : ∀ i, IsOpen (O i)) (hne : ∀ i, (O i).Nonempty) :
    ∃ y : ι → E, (∀ i, y i ∈ O i) ∧ ∀ s : Set ι, s.encard ≤ k → LinearIndepOn ℝ y s := by
  classical
  have := Fintype.ofFinite ι
  choose c hc using hne
  -- With `k = 0` only the empty family must be independent.
  rcases k.eq_zero_or_pos with rfl | hk0
  · refine ⟨c, hc, fun s hs ↦ ?_⟩
    rw [Nat.cast_zero, nonpos_iff_eq_zero, encard_eq_zero] at hs
    exact hs ▸ linearIndepOn_empty ℝ c
  have := Module.finite_of_finrank_pos (hk0.trans_le hk)
  -- Choose the points one at a time: the points chosen so far are in general position.
  suffices ∀ t : Finset ι, ∃ y : ι → E, (∀ i, y i ∈ O i) ∧
      ∀ s ⊆ (t : Set ι), s.encard ≤ k → LinearIndepOn ℝ y s by
    obtain ⟨y, hyO, hy⟩ := this Finset.univ
    exact ⟨y, hyO, fun s hs ↦ hy s (by simp) hs⟩
  intro t
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨c, hc, fun s hs _ ↦ ?_⟩
    rw [Finset.coe_empty, subset_empty_iff] at hs
    exact hs ▸ linearIndepOn_empty ℝ c
  | insert a t _ ih =>
    obtain ⟨y, hyO, hy⟩ := ih
    -- The new point avoids the spans of fewer than `k` old points, which are proper subspaces.
    let S := {s : Set ι // s ⊆ t ∧ s.encard < k}
    have hproper (s : S) : (Submodule.span ℝ (y '' s.val) : AffineSubspace ℝ E) ≠ ⊤ := by
      rw [← Submodule.toAffineSubspace_top, Ne, Submodule.toAffineSubspace_inj]
      have hs : (s.val.ncard : ℕ∞) < k := (toFinite s.val).cast_ncard_eq ▸ s.property.2
      exact (span_lt_top_of_ncard_lt_finrank ((toFinite s.val).image y)
        (((ncard_image_le (toFinite s.val)).trans_lt (by exact_mod_cast hs)).trans_le hk)).ne
    obtain ⟨z, hzO, hzS⟩ := AffineSubspace.exists_mem_open_genericLocus _ hproper (hO a) ⟨c a, hc a⟩
    refine ⟨Function.update y a z, fun i ↦ ?_, fun s hs hsk ↦ ?_⟩
    · rcases eq_or_ne i a with rfl | hi
      · simpa using hzO
      · simpa [hi] using hyO i
    rw [Finset.coe_insert] at hs
    exact linearIndepOn_update hy (fun u hut huk ↦ hzS ⟨u, hut, huk⟩) hs hsk

end TauCeti
