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
measure their sizes. A list of endomorphisms preserving `L` and contracting these seminorms gives
a product of difference operators `1 - T`. Each difference at most doubles the seminorm, so the
image of the product has short integral generators with a factor of four per operator in squared
size. Additive seminorms allow observations obtained by conjugating coordinates by a field
automorphism, without assuming those observations are continuous or complex-linear.

This is the quantitative step in `New.Data.isShort_ramifyingOp` and
`New.Data.span_isShort_ramifiedSourceForms_eq_top` in `New/UpperBound/Size/ShortColumns.lean`
of lsernau/grh-lean at `72fead1`, where the endomorphisms are right translations.
-/

public section

open Set

/-- A product of differences of integral-preserving contractions preserves integrality.
Its expansion factor in each additive seminorm is at most two to the number of factors. -/
theorem AddSubgroup.mem_and_seminorm_list_prod_one_sub_le {R V ι : Type*} [Semiring R]
    [AddCommGroup V] [Module R V] (L : AddSubgroup V) (p : ι → AddGroupSeminorm V)
    {l : List (Module.End R V)} (hL : ∀ T ∈ l, MapsTo T L L)
    (hp : ∀ T ∈ l, ∀ x ∈ L, ∀ i, p i (T x) ≤ p i x) {x : V} (hx : x ∈ L) :
    let F : Module.End R V := (l.map (1 - ·)).prod
    F x ∈ L ∧ ∀ i, p i (F x) ≤ 2 ^ l.length * p i x := by
  induction l with
  | nil => simp [hx]
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
    calc
      p i (y - T y) ≤ p i y + p i (T y) := map_sub_le_add _ _ _
      _ ≤ 2 * (2 ^ l.length * p i x) := by
        rw [two_mul]
        exact add_le_add (hy.2 i) ((hp T hT y hyL i).trans (hy.2 i))
      _ = 2 ^ (l.length + 1) * p i x := by rw [pow_succ', mul_assoc]

namespace TauCeti

/-- Apply a product of `1 - T` to short integral generators. Its range is spanned by integral
vectors whose squared seminorms are bounded by the original bound times `4 ^ l.length`.
The product is ordered; no commutativity or finite-order condition is needed. -/
theorem span_short_list_prod_one_sub_eq_range {R V ι : Type*} [Semiring R] [AddCommGroup V]
    [Module R V] {L : AddSubgroup V} {p : ι → AddGroupSeminorm V} {l : List (Module.End R V)}
    (hL : ∀ T ∈ l, MapsTo T L L) (hp : ∀ T ∈ l, ∀ x ∈ L, ∀ i, p i (T x) ≤ p i x)
    {B : ℝ} (hspan : Submodule.span R {x | x ∈ L ∧ ∀ i, (p i x) ^ 2 ≤ B} = ⊤) :
    Submodule.span R {x | x ∈ LinearMap.range (l.map (1 - ·)).prod ∧
      x ∈ L ∧ ∀ i, (p i x) ^ 2 ≤ 4 ^ l.length * B} = LinearMap.range (l.map (1 - ·)).prod := by
  let F : Module.End R V := (l.map (1 - ·)).prod
  refine le_antisymm (Submodule.span_le.mpr fun x hx ↦ hx.1) ?_
  have heq : LinearMap.range F = Submodule.span R (F '' {x | x ∈ L ∧ ∀ i, (p i x) ^ 2 ≤ B}) := by
    rw [← Submodule.map_span, hspan, Submodule.map_top]
  refine heq.le.trans (Submodule.span_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  have hy := L.mem_and_seminorm_list_prod_one_sub_le p hL hp hx.1
  refine ⟨F.mem_range_self x, hy.1, fun i ↦ ?_⟩
  calc
    (p i (F x)) ^ 2 ≤ (2 ^ l.length * p i x) ^ 2 := by gcongr; exact hy.2 i
    _ = 4 ^ l.length * (p i x) ^ 2 := by
      rw [mul_pow, pow_right_comm (2 : ℝ) l.length 2]
      norm_num
    _ ≤ 4 ^ l.length * B := by gcongr; exact hx.2 i

end TauCeti
