/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith

/-!
# Common zero loci of affine functions on convex sets

For a finite family of nonpositive affine functions on a nonempty convex set,
`Convex.exists_mem_zero_iff_forall` finds a single point detecting which functions vanish on
the whole set. This supplies the active-inequality classification of polyhedral faces.
A segment between a strictly feasible point and a point violating one affine row
crosses that row at zero, while the other rows remain strict.

Adapted from `Mei/Geometry/Convex/Polyhedron/Face.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
The single-active crossing lemma is adapted from
`Mei/Geometry/Convex/Polyhedron/Face/Facet.lean` at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`, with the same copyright and author.
-/

public section

open Set

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonempty convex set has a point where each member of a finite family of
nonpositive affine functions vanishes exactly when it vanishes on the whole set. -/
theorem Convex.exists_mem_zero_iff_forall {F : Set V} (hF : Convex ℝ F) (hne : F.Nonempty)
    [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ)) (hg : ∀ j, ∀ x ∈ F, g j x ≤ 0) :
    ∃ p ∈ F, ∀ j, g j p = 0 ↔ ∀ x ∈ F, g j x = 0 := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ p ∈ F, ∀ j ∈ s, g j p = 0 ↔ ∀ x ∈ F, g j x = 0 by
    obtain ⟨p, hp, h⟩ := this Finset.univ
    exact ⟨p, hp, fun j => h j (Finset.mem_univ j)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, by simp⟩
  | @insert j s hjs ih =>
    obtain ⟨p, hp, hps⟩ := ih
    by_cases hj : ∀ x ∈ F, g j x = 0
    · refine ⟨p, hp, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact iff_of_true (hj p hp) hj
      · exact hps k hk
    · push Not at hj
      obtain ⟨q, hq, hqj⟩ := hj
      refine ⟨AffineMap.lineMap p q (1 / 2 : ℝ), hF.lineMap_mem hp hq (by norm_num), ?_⟩
      have hmid (k : ι) :
          g k (AffineMap.lineMap p q (1 / 2 : ℝ)) = (g k p + g k q) / 2 := by
        rw [(g k).apply_lineMap, AffineMap.lineMap_apply_ring]
        ring
      intro k hk
      constructor
      · intro hzero x hx
        have h₁ := hg k p hp
        have h₂ := hg k q hq
        rw [hmid] at hzero
        have hpzero : g k p = 0 := by linarith
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact absurd (by linarith) hqj
        · exact (hps k hk).mp hpzero x hx
      · intro hall
        rw [hmid, hall p hp, hall q hq]
        norm_num

namespace TauCeti

/-- The segment from a strictly feasible point to a point violating just row `j` crosses that
row at zero while all the other rows remain strict. -/
theorem exists_mem_openSegment_single_active (g : ι → (V →ᵃ[ℝ] ℝ)) (j : ι) {q x : V}
    (hq : ∀ l, g l q < 0) (hxj : 0 < g j x) (hx : ∀ l ≠ j, g l x ≤ 0) :
    ∃ p ∈ openSegment ℝ q x, g j p = 0 ∧ ∀ l ≠ j, g l p < 0 := by
  have hzero : 0 ∈ (g j) '' openSegment ℝ q x := by
    rw [image_openSegment, openSegment_eq_Ioo ((hq j).trans hxj)]
    exact ⟨hq j, hxj⟩
  obtain ⟨p, hp, hpj⟩ := hzero
  refine ⟨p, hp, hpj, fun l hl => ?_⟩
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  rw [(g l).apply_lineMap, AffineMap.lineMap_apply_ring]
  exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) (hq l))
    (mul_nonpos_of_nonneg_of_nonpos ht.1.le (hx l hl))

end TauCeti
