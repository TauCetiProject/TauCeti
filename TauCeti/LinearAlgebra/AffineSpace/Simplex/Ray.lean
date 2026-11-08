/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import TauCeti.Algebra.Order.Field.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rays leaving a simplex

A nonconstant ray starting in the interior of a simplex and lying in its affine
span leaves it at a finite positive parameter. Before that parameter it lies
in the interior, at the exit it lies on a face, and afterwards it misses the
simplex. For a triangle, a ray avoiding the vertices meets exactly one edge,
in its interior, and misses every other edge. This gives the exit-face geometry
for transverse triangles meeting a one-sided wall near a joint. The statements
work over an ordered field, without a topology or an ambient dimension hypothesis.

The exit parameter is the least time at which one of the barycentric weights
becomes zero. The construction uses Mathlib's
`eq_affineCombination_of_mem_affineSpan_of_fintype`,
`Simplex.affineCombination_mem_closedInterior_iff`, and
`Finset.exists_pos_forall_nonneg_add_mul_iff`. The triangle specialization uses
`Simplex.closedInterior_sdiff_interior` and the barycentric descriptions of
face interiors to distinguish an edge crossing from a vertex crossing.

Adapted from `Mei/Geometry/Affine/Simplex/Ray.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

open Set Finset

namespace Affine.Simplex

variable {𝕜 V P : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AffineSpace V P] {n : ℕ}

/-- A nonconstant ray in a simplex's affine span, starting at an interior point,
has a positive exit parameter. The closed simplex is met exactly up to the exit,
and the interior exactly before it. -/
theorem exists_ray_exit (s : Simplex 𝕜 P n) {p q : P} (hp : p ∈ s.interior)
    (hq : q ∈ affineSpan 𝕜 (range s.points)) (hne : q ≠ p) :
    ∃ T : 𝕜, 0 < T ∧ ∀ t : 𝕜, 0 ≤ t →
      (AffineMap.lineMap p q t ∈ s.closedInterior ↔ t ≤ T) ∧
      (AffineMap.lineMap p q t ∈ s.interior ↔ t < T) := by
  classical
  obtain ⟨b, hb, hb01, hbp⟩ := hp
  obtain ⟨c, hc, hcq⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  let a : Fin (n + 1) → 𝕜 := fun j => c j - b j
  have ha : ∑ j, a j = 0 := by simp [a, sum_sub_distrib, hb, hc]
  -- A nonconstant motion with constant total weight has a decreasing coordinate.
  have hneg : ∃ j, a j < 0 := by
    by_contra! hn
    have hz := (sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp ha
    have hcb : c = b := funext fun j => sub_eq_zero.mp (hz j (mem_univ j))
    exact hne (by rw [hcq, hcb, hbp])
  obtain ⟨T, hT, hbounds⟩ := univ.exists_pos_forall_nonneg_add_mul_iff b a
    (fun i _ => (hb01 i).1) (by simpa using hneg)
  simp only [Finset.mem_univ, forall_const] at hbounds
  -- The affine ray is obtained by varying these weights linearly.
  have hsum (t : 𝕜) : ∑ i, (b i + t * a i) = 1 := by
    rw [sum_add_distrib, ← mul_sum, ha, mul_zero, add_zero, hb]
  have hline (t : 𝕜) : AffineMap.lineMap p q t =
      univ.affineCombination 𝕜 s.points (fun i => b i + t * a i) := by
    rw [hcq, ← hbp, ← (univ.affineCombination 𝕜 s.points).apply_lineMap]
    congr 1
    ext i
    simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a]
    ring
  -- Nonnegative weights summing to one are at most one; positive weights are below one.
  refine ⟨T, hT, fun t ht => ⟨?_, ?_⟩⟩
  · rw [hline, affineCombination_mem_closedInterior_iff (hsum t)]
    constructor
    · exact fun hall => ((hbounds t ht).1).mp (fun i => (hall i).1)
    · intro htT i
      refine ⟨((hbounds t ht).1).mpr htT i, ?_⟩
      rw [← hsum t]
      exact single_le_sum (fun i _ => ((hbounds t ht).1).mpr htT i) (mem_univ i)
  · rw [hline, affineCombination_mem_interior_iff (hsum t)]
    constructor
    · exact fun hall => ((hbounds t ht).2).mp (fun i => (hall i).1)
    · intro htT i
      have hni : ∃ k : Fin (n + 1), k ≠ i := by
        by_contra! h
        have hb' : ∑ k, b k = b i := sum_eq_single i
          (fun k _ hki => (hki (h k)).elim) (by simp)
        linarith [(hb01 i).2]
      obtain ⟨k, hki⟩ := hni
      refine ⟨((hbounds t ht).2).mpr htT i, ?_⟩
      rw [← hsum t]
      exact single_lt_sum hki (mem_univ i) (mem_univ k) (((hbounds t ht).2).mpr htT k)
        (fun k _ _ => (((hbounds t ht).2).mpr htT k).le)

end Affine.Simplex

namespace Affine.Triangle

variable {𝕜 V P : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AffineSpace V P]

/-- A ray from the interior of a triangle that avoids its vertices meets
exactly one edge, at a positive parameter and in that edge's interior.
Every other edge is disjoint from the whole nonnegative ray. -/
theorem exists_ray_exit_edge (s : Triangle 𝕜 P) {p q : P} (hp : p ∈ s.interior)
    (hq : q ∈ affineSpan 𝕜 (range s.points)) (hne : q ≠ p)
    (hvertices : ∀ t : 𝕜, 0 < t → ∀ j, AffineMap.lineMap p q t ≠ s.points j) :
    ∃ (T : 𝕜) (l : Fin 3), 0 < T ∧
      AffineMap.lineMap p q T ∈ (s.faceOpposite l).interior ∧
      ∀ t : 𝕜, 0 ≤ t → ∀ m : Fin 3,
        (AffineMap.lineMap p q t ∈ (s.faceOpposite m).closedInterior ↔ t = T ∧ m = l) := by
  classical
  obtain ⟨T, hT, hbounds⟩ := s.exists_ray_exit hp hq hne
  have hclosed := ((hbounds T hT.le).1).mpr le_rfl
  have hnot : AffineMap.lineMap p q T ∉ s.interior := by
    rw [(hbounds T hT.le).2]
    exact lt_irrefl T
  obtain ⟨l, hl⟩ : ∃ l, AffineMap.lineMap p q T ∈ (s.faceOpposite l).closedInterior := by
    have hm : AffineMap.lineMap p q T ∈ s.closedInterior \ s.interior := ⟨hclosed, hnot⟩
    rw [s.closedInterior_sdiff_interior] at hm
    exact Set.mem_iUnion.mp hm
  -- The exit lies on an edge, and vertex avoidance puts it in the open edge.
  have hint : AffineMap.lineMap p q T ∈ (s.faceOpposite l).interior := by
    rw [(s.faceOpposite l).closedInterior_eq_interior_union] at hl
    rcases hl with hi | hi
    · exact hi
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      rw [Simplex.closedInterior_eq_singleton] at hj
      have he : AffineMap.lineMap p q T = (s.faceOpposite l).points j.rev := by
        simpa only [Set.mem_singleton_iff, Simplex.faceOpposite_point_eq_point_rev] using hj
      exact (hvertices T hT _
        (he.trans (s.faceOpposite_point_eq_point_succAbove l j.rev))).elim
  have hunique (m : Fin 3)
      (hm : AffineMap.lineMap p q T ∈ (s.faceOpposite m).closedInterior) : m = l := by
    obtain ⟨w, hw, he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (s.closedInterior_subset_affineSpan hclosed)
    have hi := hint
    rw [he, Simplex.faceOpposite,
      s.affineCombination_mem_interior_face_iff_pos (by simp [Finset.card_compl]) hw] at hi
    rw [he, Simplex.faceOpposite,
      s.affineCombination_mem_closedInterior_face_iff_nonneg (by simp [Finset.card_compl]) hw] at hm
    by_contra hml
    have hpw : 0 < w m := hi.1 m (by simp [hml])
    have hzw : w m = 0 := hm.2 m (by simp)
    exact hpw.ne' hzw
  refine ⟨T, l, hT, hint, fun t ht m => ⟨fun hm => ?_, ?_⟩⟩
  · have htm : t ≤ T := ((hbounds t ht).1).mp
      (s.closedInterior_faceOpposite_subset_closedInterior m hm)
    have htT : t = T := by
      by_contra hn
      have hit := ((hbounds t ht).2).mpr (lt_of_le_of_ne htm hn)
      exact (Set.disjoint_left.mp (s.disjoint_interior_closedInterior_faceOpposite m) hit hm)
    subst t
    exact ⟨rfl, hunique m hm⟩
  · rintro ⟨rfl, rfl⟩
    exact Simplex.interior_subset_closedInterior _ hint

end Affine.Triangle
