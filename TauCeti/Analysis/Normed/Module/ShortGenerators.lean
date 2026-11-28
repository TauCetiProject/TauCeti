/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Short generators of an image of a product of differences

Let `L` be the additive subgroup of integral vectors and let a family of additive seminorms
measure their sizes. A list of endomorphisms preserving `L` and taking each size observation
to one bounded by another observation in the family gives a product of difference operators
`1 - T`. Each difference at most doubles the uniform bound on the observations, so the
image of the product has short integral generators with a factor of four per operator in squared
size. Additive seminorms allow observations obtained by conjugating coordinates by a field
automorphism, without assuming those observations are continuous or complex-linear.

This is the quantitative step in `New.Data.isShort_ramifyingOp` and
`New.Data.span_isShort_ramifiedSourceForms_eq_top` in `New/UpperBound/Size/ShortColumns.lean`
of lsernau/grh-lean at `72fead1`, where the endomorphisms are right translations.
-/

public section

open Set

/-- A product of differences preserves the integral subgroup. Each output seminorm is bounded
by `2 ^ l.length` times some input seminorm in the same family. For translations the input and
output observations can be evaluations at different points. -/
theorem AddSubgroup.mem_and_exists_seminorm_list_prod_one_sub_le {R V ι : Type*} [Semiring R]
    [AddCommGroup V] [Module R V] (L : AddSubgroup V) (p : ι → AddGroupSeminorm V)
    {l : List (Module.End R V)} (hL : ∀ T ∈ l, MapsTo T L L)
    (hp : ∀ T ∈ l, ∀ x ∈ L, ∀ i, ∃ j, p i (T x) ≤ p j x)
    {x : V} (hx : x ∈ L) :
    let F : Module.End R V := (l.map (1 - ·)).prod
    F x ∈ L ∧ ∀ i, ∃ j, p i (F x) ≤ 2 ^ l.length * p j x := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_apply_eq_self, List.length_nil, pow_zero, one_mul]
    exact ⟨hx, fun i ↦ ⟨i, le_rfl⟩⟩
  | cons T l ih =>
    have hT : T ∈ T :: l := List.mem_cons_self
    have hy := ih (fun S hS ↦ hL S (List.mem_cons_of_mem _ hS))
      (fun S hS ↦ hp S (List.mem_cons_of_mem _ hS))
    let G : Module.End R V := (l.map (1 - ·)).prod
    let y := G x
    have hyL : y ∈ L := hy.1
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, LinearMap.sub_apply,
      one_apply_eq_self, List.length_cons]
    refine ⟨L.sub_mem hyL (hL T hT hyL), fun i ↦ ?_⟩
    obtain ⟨j, hj⟩ := hp T hT y hyL i
    obtain ⟨a, ha⟩ := hy.2 i
    obtain ⟨b, hb⟩ := hy.2 j
    obtain ⟨c, hac, hbc⟩ : ∃ c, p a x ≤ p c x ∧ p b x ≤ p c x := by
      rcases le_total (p a x) (p b x) with h | h
      · exact ⟨b, h, le_rfl⟩
      · exact ⟨a, le_rfl, h⟩
    refine ⟨c, ?_⟩
    calc
      p i (y - T y) ≤ p i y + p i (T y) := map_sub_le_add _ _ _
      _ ≤ 2 * (2 ^ l.length * p c x) := by
        rw [two_mul]
        exact add_le_add (ha.trans (by gcongr)) (hj.trans (hb.trans (by gcongr)))
      _ = 2 ^ (l.length + 1) * p c x := by rw [pow_succ', mul_assoc]

namespace TauCeti

/-- Apply a product of `1 - T` to short integral generators. Its range is spanned by integral
vectors whose squared seminorms are bounded by the original bound times `4 ^ l.length`.
The seminorms may be permuted, or more generally dominated by members of the family after
applying each operator. No commutativity or finite-order condition is needed. -/
theorem span_short_list_prod_one_sub_eq_range {R V ι : Type*} [Semiring R] [AddCommGroup V]
    [Module R V] {L : AddSubgroup V} {p : ι → AddGroupSeminorm V} {l : List (Module.End R V)}
    (hL : ∀ T ∈ l, MapsTo T L L) (hp : ∀ T ∈ l, ∀ x ∈ L, ∀ i, ∃ j, p i (T x) ≤ p j x)
    {B : ℝ} (hspan : Submodule.span R {x | x ∈ L ∧ ∀ i, (p i x) ^ 2 ≤ B} = ⊤) :
    Submodule.span R {x | x ∈ LinearMap.range (l.map (1 - ·)).prod ∧
      x ∈ L ∧ ∀ i, (p i x) ^ 2 ≤ 4 ^ l.length * B} = LinearMap.range (l.map (1 - ·)).prod := by
  let F : Module.End R V := (l.map (1 - ·)).prod
  refine le_antisymm (Submodule.span_le.mpr fun x hx ↦ hx.1) ?_
  have heq : LinearMap.range F = Submodule.span R (F '' {x | x ∈ L ∧ ∀ i, (p i x) ^ 2 ≤ B}) := by
    rw [← Submodule.map_span, hspan, Submodule.map_top]
  refine heq.le.trans (Submodule.span_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  have hy := L.mem_and_exists_seminorm_list_prod_one_sub_le p hL hp hx.1
  refine ⟨F.mem_range_self x, hy.1, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := hy.2 i
  calc
    (p i (F x)) ^ 2 ≤ (2 ^ l.length * p j x) ^ 2 := by gcongr
    _ = 4 ^ l.length * (p j x) ^ 2 := by
      rw [mul_pow, pow_right_comm (2 : ℝ) l.length 2]
      norm_num
    _ ≤ 4 ^ l.length * B := by gcongr; exact hx.2 j

end TauCeti
