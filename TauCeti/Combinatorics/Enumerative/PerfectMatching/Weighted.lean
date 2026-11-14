/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted sums over perfect matchings

The edges of a perfect matching are unordered pairs, each counted once. A product of edge
weights therefore needs neither an ordering of the vertices nor a choice of representatives.
Removing one edge factors this product into its weight and the product for the remaining
matching. Summing by the partner of a distinguished vertex gives the corresponding recurrence
for the sum of weighted matchings. The decomposition reuses `PerfectMatching.partnerEquiv`,
which groups matchings by the partner and the matching on the remaining vertices.

This recurrence is the combinatorial step in Wick's formula: an edge carries the covariance
of its two positions, and contracting one position removes it together with its partner.
`Sym2.lift` turns a symmetric covariance function into the unordered-pair weights used here.
-/

public section

open Finset

namespace TauCeti.PerfectMatching

variable {α β R : Type*} [Fintype α] [DecidableEq α]

/-- The unordered edges of a perfect matching, each appearing once. -/
def edgeFinset (D : PerfectMatching α) : Finset (Sym2 α) :=
  univ.image fun a ↦ s(a, D.val a)

/-- The edge set is the image of the vertices under the endpoint-pair map. -/
theorem edgeFinset_def (D : PerfectMatching α) :
    D.edgeFinset = univ.image fun a ↦ s(a, D.val a) := (rfl)

/-- Every edge is the unordered pair of a vertex and its partner. -/
theorem mem_edgeFinset (D : PerfectMatching α) (e : Sym2 α) :
    e ∈ D.edgeFinset ↔ ∃ a, e = s(a, D.val a) := by
  simp [edgeFinset, eq_comm]

/-- An unordered pair is an edge exactly when its endpoints are matched. -/
@[simp]
theorem mk_mem_edgeFinset (D : PerfectMatching α) (a b : α) :
    s(a, b) ∈ D.edgeFinset ↔ D.val a = b := by
  simp only [edgeFinset, mem_image, mem_univ, true_and, Sym2.eq_iff]
  constructor
  · rintro ⟨x, (⟨rfl, h⟩ | ⟨h, rfl⟩)⟩
    · exact h
    · simp only [h, D.apply_apply]
  · intro h
    exact ⟨a, Or.inl ⟨rfl, h⟩⟩

/-- No edge of a perfect matching is diagonal. -/
theorem not_isDiag_of_mem_edgeFinset (D : PerfectMatching α) {e : Sym2 α}
    (he : e ∈ D.edgeFinset) : ¬e.IsDiag := by
  obtain ⟨a, rfl⟩ := (D.mem_edgeFinset e).mp he
  simpa using (D.apply_ne a).symm

/-- A diagonal pair cannot be an edge of a perfect matching. -/
@[simp]
theorem notMem_edgeFinset_of_isDiag (D : PerfectMatching α) {e : Sym2 α}
    (he : e.IsDiag) : e ∉ D.edgeFinset :=
  fun h ↦ D.not_isDiag_of_mem_edgeFinset h he

/-- Each unordered edge accounts for exactly two vertices. -/
theorem two_mul_card_edgeFinset (D : PerfectMatching α) :
    2 * #D.edgeFinset = Fintype.card α := by
  have hfiber (e : Sym2 α) (he : e ∈ D.edgeFinset) :
      #{x : α | s(x, D.val x) = e} = 2 := by
    obtain ⟨a, rfl⟩ := (D.mem_edgeFinset e).mp he
    have hset : (univ.filter fun x : α ↦ s(x, D.val x) = s(a, D.val a)) =
        {a, D.val a} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Sym2.eq_iff, mem_insert, mem_singleton]
      constructor
      · exact fun h ↦ h.imp And.left And.left
      · rintro (rfl | rfl) <;> simp
    rw [hset, card_pair (D.apply_ne a).symm]
  have hcard := card_eq_sum_card_fiberwise (s := (univ : Finset α))
    (t := D.edgeFinset) (f := fun a ↦ s(a, D.val a)) (fun a _ ↦ by simp)
  simpa [mul_comm] using (hcard.trans (sum_congr rfl hfiber)).symm

/-- A perfect matching has half as many edges as vertices. -/
@[simp]
theorem card_edgeFinset (D : PerfectMatching α) :
    #D.edgeFinset = Fintype.card α / 2 := by
  rw [← D.two_mul_card_edgeFinset, Nat.mul_div_right _ (by decide : 0 < 2)]

/-- A matching on an empty vertex type has no edges. -/
@[simp]
theorem edgeFinset_of_isEmpty [IsEmpty α] (D : PerfectMatching α) : D.edgeFinset = ∅ := by
  simp [edgeFinset]

/-- The unordered edges determine the matching. -/
theorem ext_edgeFinset {D E : PerfectMatching α} (h : D.edgeFinset = E.edgeFinset) : D = E := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact ((E.mk_mem_edgeFinset a (D.val a)).mp (by simp [← h])).symm

/-- Two matchings have the same edge set exactly when they are equal. -/
@[simp]
theorem edgeFinset_inj {D E : PerfectMatching α} : D.edgeFinset = E.edgeFinset ↔ D = E :=
  ⟨ext_edgeFinset, congrArg edgeFinset⟩

/-- Transporting a matching transports its unordered edges. -/
theorem edgeFinset_congr [Fintype β] [DecidableEq β] (e : α ≃ β) (D : PerfectMatching α) :
    (congr e D).edgeFinset = D.edgeFinset.image (Sym2.map e) := by
  rw [edgeFinset, edgeFinset, ← image_univ_equiv e, image_image, image_image]
  simp only [Function.comp_def, congr_val_apply_apply, Sym2.map_mk]

/-- Transporting a matching pulls its edge weights back along the vertex equivalence. -/
@[simp]
theorem prod_edgeFinset_congr [Fintype β] [DecidableEq β] [CommMonoid R]
    (e : α ≃ β) (D : PerfectMatching α) (w : Sym2 β → R) :
    (∏ z ∈ (congr e D).edgeFinset, w z) =
      ∏ z ∈ D.edgeFinset, w (Sym2.map e z) := by
  rw [edgeFinset_congr, prod_image (Sym2.map.injective e.injective).injOn]

/-- Relabeling the vertices transports the sum of edge-weight products. -/
theorem sum_prod_edgeFinset_congr [Fintype β] [DecidableEq β] [CommMonoid R]
    [AddCommMonoid R] (e : α ≃ β) (w : Sym2 β → R) :
    (∑ E : PerfectMatching β, ∏ z ∈ E.edgeFinset, w z) =
      ∑ D : PerfectMatching α, ∏ z ∈ D.edgeFinset, w (Sym2.map e z) := by
  rw [← (congr e).sum_comp]
  simp only [prod_edgeFinset_congr]

/-- Adjoining an edge inserts that edge alongside the edges of the smaller matching. -/
theorem edgeFinset_extend {a b : α} (hab : a ≠ b)
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).edgeFinset =
      insert s(a, b) (E.edgeFinset.image (Sym2.map Subtype.val)) := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    rw [mk_mem_edgeFinset]
    simp only [mem_insert, Sym2.eq_iff, edgeFinset, image_image, mem_image,
      mem_univ, true_and, Function.comp_apply, Sym2.map_mk]
    constructor
    · intro h
      by_cases hx : x ≠ a ∧ x ≠ b
      · right
        refine ⟨⟨x, hx⟩, Or.inl ⟨rfl, ?_⟩⟩
        exact (extend_apply_of_mem hab E hx).symm.trans h
      · left
        by_cases hxa : x = a
        · subst x
          exact Or.inl ⟨rfl, h.symm.trans (extend_apply_left hab E)⟩
        · have hxb : x = b := by tauto
          subst x
          exact Or.inr ⟨rfl, h.symm.trans (extend_apply_right hab E)⟩
    · rintro (h | ⟨u, h⟩)
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact extend_apply_left hab E
        · exact extend_apply_right hab E
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact extend_apply_of_mem hab E u.2
        · apply (extend hab E).apply_eq_comm.mpr
          exact extend_apply_of_mem hab E u.2

/-- Restricting away a matched pair erases exactly that edge. -/
theorem image_edgeFinset_restrict (D : PerfectMatching α) {a b : α} (hab : D.val a = b) :
    (D.restrict hab).edgeFinset.image (Sym2.map Subtype.val) =
      D.edgeFinset.erase s(a, b) := by
  have hnot : s(a, b) ∉ (D.restrict hab).edgeFinset.image (Sym2.map Subtype.val) := by
    rintro h
    obtain ⟨e, _, he⟩ := mem_image.mp h
    have ha := Sym2.mem_map.mp (he.symm ▸ Sym2.mem_mk_left a b)
    obtain ⟨x, _, hx⟩ := ha
    exact x.2.1 hx
  have hext := edgeFinset_extend (fun h ↦ D.apply_ne a (hab.trans h.symm)) (D.restrict hab)
  rw [extend_restrict] at hext
  rw [hext, erase_insert hnot]

/-- Adjoining a pair multiplies the edge-weight product by the weight of that pair. -/
@[simp]
theorem prod_edgeFinset_extend [CommMonoid R] {a b : α} (hab : a ≠ b)
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) (w : Sym2 α → R) :
    (∏ e ∈ (extend hab E).edgeFinset, w e) =
      w s(a, b) * ∏ e ∈ E.edgeFinset, w (Sym2.map Subtype.val e) := by
  have himage := image_edgeFinset_restrict (extend hab E) (extend_apply_left hab E)
  rw [restrict_extend] at himage
  have hnot : s(a, b) ∉ E.edgeFinset.image (Sym2.map Subtype.val) := by
    rw [himage]
    exact notMem_erase _ _
  rw [edgeFinset_extend, prod_insert hnot,
    prod_image (Sym2.map.injective Subtype.val_injective).injOn]

/-- Removing a matched pair factors a product of unordered edge weights. -/
theorem prod_edgeFinset_eq_mul_prod_restrict [CommMonoid R] (D : PerfectMatching α)
    {a b : α} (hab : D.val a = b) (w : Sym2 α → R) :
    (∏ e ∈ D.edgeFinset, w e) = w s(a, b) *
      ∏ e ∈ (D.restrict hab).edgeFinset, w (Sym2.map Subtype.val e) := by
  conv_lhs => rw [← extend_restrict (fun h ↦ D.apply_ne a (hab.trans h.symm)) D hab]
  exact prod_edgeFinset_extend _ _ w

/-- The weighted matching sum satisfies the contraction recurrence at any distinguished
vertex. No order on vertices or symmetry hypothesis on weights is needed, since weights
are indexed by unordered pairs. -/
theorem sum_prod_edgeFinset_eq_sum_mul_sum [CommSemiring R] (w : Sym2 α → R) (a : α) :
    (∑ D : PerfectMatching α, ∏ e ∈ D.edgeFinset, w e) =
      ∑ b : {b : α // b ≠ a}, w s(a, b.val) *
        ∑ E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b.val},
          ∏ e ∈ E.edgeFinset, w (Sym2.map Subtype.val e) := by
  rw [← (partnerEquiv a).symm.sum_comp, Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro E _
  simp only [partnerEquiv_symm_apply, prod_edgeFinset_extend]

end TauCeti.PerfectMatching
