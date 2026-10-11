/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

import Mathlib.Algebra.Order.Pi

/-!
# Nonnegative vectors and linear relations

A nonnegative vector can be moved along any finitely supported direction supported on its
nonzero coordinates, with at least one positive coordinate, until a coordinate first reaches
zero. The resulting vector stays nonnegative and has strictly smaller support. This gives the
support-reduction step used in inductive arguments about nonnegative linear relations, over any
linearly ordered division ring and without requiring the index type to be finite.

The cone hull of the natural-number relations among a finite family consists of nonnegative
relations among its images under an additive map, over any ordered semiring. Conversely,
membership in the intersection of two finitely generated cones gives a nonnegative relation
between the first family and the negatives of the second family. These tools express cone
intersections in terms of nonnegative linear relations without imposing lattice hypotheses on the
ambient geometry.

## Main declarations

* `TauCeti.exists_pos_sub_smul_nonneg_support_ssubset`: move a nonnegative vector to strictly
  smaller support along a finitely supported direction.
* `AddMonoidHom.nonneg_relation_of_mem_hull_natCast_relations`: the cone hull of natural-number
  relations consists of nonnegative relations over an ordered semiring.
* `PointedCone.exists_nonneg_relation_of_mem_inf_hull_range`: a point of the intersection of
  two cone hulls determines a nonnegative relation between their generating families.
-/

public section

namespace TauCeti

/-- Moving a nonnegative vector `c` along a finitely supported direction `-k`, where `k`
vanishes off the support of `c` and has a positive coordinate, reaches a nonnegative vector with
strictly smaller support at a positive time. The support of `c` may be infinite. -/
theorem exists_pos_sub_smul_nonneg_support_ssubset {ι K : Type*}
    [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K] {c k : ι → K}
    (hc : 0 ≤ c) (hfin : (Function.support k).Finite)
    (hk : ∀ j, c j = 0 → k j = 0) (hpos : ∃ j, 0 < k j) :
    ∃ s : K, 0 < s ∧ 0 ≤ c - s • k ∧ Function.support (c - s • k) ⊂ Function.support c := by
  classical
  let P := hfin.toFinset.filter fun j ↦ 0 < k j
  have hmem : ∀ j, j ∈ P ↔ 0 < k j := by
    intro j
    simp only [P, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support]
    exact ⟨And.right, fun hj ↦ ⟨hj.ne', hj⟩⟩
  have hP : P.Nonempty := let ⟨j, hj⟩ := hpos; ⟨j, (hmem j).2 hj⟩
  obtain ⟨j₁, hj₁, hs⟩ := P.exists_mem_eq_inf' hP fun j ↦ c j / k j
  have hkj₁ : 0 < k j₁ := (hmem j₁).1 hj₁
  have hcpos : ∀ j, 0 < k j → 0 < c j := fun j hj ↦
    (hc j).lt_of_ne' fun h ↦ hj.ne' (hk j h)
  have hs₀ : 0 < P.inf' hP fun j ↦ c j / k j := by
    rw [hs]
    exact div_pos (hcpos j₁ hkj₁) hkj₁
  refine ⟨P.inf' hP fun j ↦ c j / k j, hs₀, fun j ↦ ?_, ?_⟩
  · simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    rcases lt_or_ge 0 (k j) with hkj | hkj
    · exact (le_div_iff₀ hkj).1 (P.inf'_le _ ((hmem j).2 hkj))
    · exact (mul_nonpos_of_nonneg_of_nonpos hs₀.le hkj).trans (hc j)
  · refine (Set.ssubset_iff_of_subset (Function.support_subset_iff'.2 fun j hj ↦ ?_)).2
      ⟨j₁, (hcpos j₁ hkj₁).ne', ?_⟩
    · rw [Function.notMem_support] at hj
      simp [hj, hk j hj]
    · rw [Function.notMem_support, hs]
      simp [div_mul_cancel₀ _ hkj₁.ne']

end TauCeti

namespace AddMonoidHom

/-- Over an ordered semiring, a nonnegative combination of natural-number relations among the
`v j` is a nonnegative relation among the `i (v j)`. The vectors `v j` may belong to any additive
commutative monoid. -/
theorem nonneg_relation_of_mem_hull_natCast_relations
    {R N V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [AddCommMonoid N] [AddCommMonoid V] [Module R V]
    {ι : Type*} [Fintype ι]
    {v : ι → N} {c : ι → R} (i : N →+ V)
    (hc : c ∈ PointedCone.hull R
      ((fun k : ι → ℕ ↦ fun j ↦ (k j : R)) '' {k | ∑ j, k j • v j = 0})) :
    0 ≤ c ∧ ∑ j, c j • i (v j) = 0 := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨fun j ↦ Nat.cast_nonneg _, ?_⟩
    simpa only [map_sum, map_nsmul, map_zero, Nat.cast_smul_eq_nsmul] using congrArg i hk
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨add_nonneg hx.1 hy.1, by simp [add_smul, Finset.sum_add_distrib, hx.2, hy.2]⟩
  | smul r x _ hx =>
    refine ⟨fun j ↦ mul_nonneg r.2 (hx.1 j), ?_⟩
    simp [← Nonneg.coe_smul, mul_smul, ← Finset.smul_sum, hx.2]

end AddMonoidHom

namespace PointedCone

/-- A point of the intersection of the cone hulls of two finite families is a nonnegative
linear combination of the first family, with coefficients that extend to a nonnegative relation
between the first family and the negatives of the second family. -/
theorem exists_nonneg_relation_of_mem_inf_hull_range
    {R V α β : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [AddCommGroup V] [Module R V] [Fintype α] [Fintype β]
    {a : α → V} {b : β → V} {x : V}
    (hx : x ∈ hull R (Set.range a) ⊓ hull R (Set.range b)) :
    ∃ c : α ⊕ β → R, 0 ≤ c ∧
      ∑ j, c j • Sum.elim a (-b) j = 0 ∧ x = ∑ j : α, c (.inl j) • a j := by
  obtain ⟨hxσ, hxτ⟩ := hx
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun] at hxσ hxτ
  obtain ⟨cσ, hcσ⟩ := hxσ
  obtain ⟨cτ, hcτ⟩ := hxτ
  have hcσ' : ∑ j, (cσ j : R) • a j = x := by
    simpa only [← Nonneg.coe_smul] using hcσ
  have hcτ' : ∑ j, (cτ j : R) • b j = x := by
    simpa only [← Nonneg.coe_smul] using hcτ
  refine ⟨Sum.elim (fun j ↦ (cσ j : R)) fun j ↦ (cτ j : R), fun j ↦ ?_, ?_, ?_⟩
  · rcases j with j | j
    exacts [(cσ j).2, (cτ j).2]
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, smul_neg,
      Finset.sum_neg_distrib]
    rw [hcσ', hcτ', add_neg_cancel]
  · simpa only [Sum.elim_inl] using hcσ'.symm

end PointedCone
