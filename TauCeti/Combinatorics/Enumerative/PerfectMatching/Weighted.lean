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
for the sum of weighted matchings. The decomposition reuses `PerfectMatching.fiberEquiv`,
which identifies matchings with a prescribed edge with matchings of its complement.

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

/-- The unordered edges determine the matching. -/
@[ext]
theorem ext_edgeFinset {D E : PerfectMatching α} (h : D.edgeFinset = E.edgeFinset) : D = E := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact ((E.mk_mem_edgeFinset a (D.val a)).mp (by simp [← h])).symm

/-- Transporting a matching transports its unordered edges. -/
theorem edgeFinset_congr [Fintype β] [DecidableEq β] (e : α ≃ β) (D : PerfectMatching α) :
    (congr e D).edgeFinset = D.edgeFinset.image (Sym2.map e) := by
  ext z
  induction z using Sym2.inductionOn with
  | _ a b =>
    rw [mk_mem_edgeFinset, congr_val_apply]
    simp only [edgeFinset, image_image, mem_image, mem_univ, true_and,
      Function.comp_apply, Sym2.map_mk, Sym2.eq_iff]
    constructor
    · intro h
      exact ⟨e.symm a, Or.inl ⟨e.apply_symm_apply a, h⟩⟩
    · rintro ⟨x, (⟨h, h'⟩ | ⟨h, h'⟩)⟩
      · simpa [← h] using h'
      · have hx : D.val x = e.symm a := e.injective (by simpa using h')
        rw [← hx, D.apply_apply, h]

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

/-- Adjoining a pair multiplies the edge-weight product by the weight of that pair. -/
theorem prod_edgeFinset_extend [CommMonoid R] {a b : α} (hab : a ≠ b)
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) (w : Sym2 α → R) :
    (∏ e ∈ (extend hab E).edgeFinset, w e) =
      w s(a, b) * ∏ e ∈ E.edgeFinset, w (Sym2.map Subtype.val e) := by
  have hnot : s(a, b) ∉ E.edgeFinset.image (Sym2.map Subtype.val) := by
    simp only [edgeFinset, image_image, mem_image, mem_univ, true_and,
      Function.comp_apply, Sym2.map_mk, Sym2.eq_iff]
    rintro ⟨x, (⟨h, _⟩ | ⟨_, h⟩)⟩
    · exact x.2.1 h
    · exact (E.val x).2.1 h
  rw [edgeFinset_extend, prod_insert hnot,
    prod_image (Sym2.map.injective Subtype.val_injective).injOn]

/-- Removing a matched pair factors a product of unordered edge weights. -/
theorem prod_edgeFinset_eq_mul_prod_restrict [CommMonoid R] (D : PerfectMatching α)
    (w : Sym2 α → R) (a : α) :
    (∏ e ∈ D.edgeFinset, w e) = w s(a, D.val a) *
      ∏ e ∈ (D.restrict (a := a) rfl).edgeFinset, w (Sym2.map Subtype.val e) := by
  conv_lhs => rw [← extend_restrict (D.apply_ne a).symm D rfl]
  exact prod_edgeFinset_extend _ _ w

omit [Fintype α] in
/-- Group all perfect matchings by the partner of `a`, and remove that pair. -/
def partnerEquiv (a : α) : PerfectMatching α ≃
    (b : {b : α // b ≠ a}) × PerfectMatching {x : α // x ≠ a ∧ x ≠ b.val} :=
  (Equiv.sigmaSubtypeFiberEquiv (fun D : PerfectMatching α ↦ D.val a)
    (· ≠ a) (fun D ↦ D.apply_ne a)).symm.trans
      (Equiv.sigmaCongrRight fun b ↦ fiberEquiv b.2.symm)

omit [Fintype α] in
/-- The matching reconstructed from a partner and a matching of the complement adjoins
exactly that pair. -/
@[simp]
theorem partnerEquiv_symm_apply (a : α) (b : {b : α // b ≠ a})
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b.val}) :
    (partnerEquiv a).symm ⟨b, E⟩ = extend b.2.symm E := by
  simp [partnerEquiv, Equiv.sigmaSubtypeFiberEquiv, Equiv.sigmaSubtypeEquivOfSubset,
    Equiv.subtypeSigmaEquiv, Equiv.sigmaCongrRight]

omit [Fintype α] in
/-- The partner decomposition records the partner and restricts away its edge. -/
@[simp]
theorem partnerEquiv_apply (a : α) (D : PerfectMatching α) :
    partnerEquiv a D = ⟨⟨D.val a, D.apply_ne a⟩, D.restrict rfl⟩ := by
  apply (partnerEquiv a).symm.injective
  simp only [Equiv.symm_apply_apply, partnerEquiv_symm_apply, extend_restrict]

/-- The weighted matching sum satisfies the contraction recurrence at any distinguished
vertex. No order on vertices or symmetry hypothesis on weights is needed, since weights
are indexed by unordered pairs. -/
theorem sum_prod_edgeFinset_eq_sum_partner [CommSemiring R] (w : Sym2 α → R) (a : α) :
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

/-- The empty vertex type has one matching, whose edge-weight product is the empty product. -/
@[simp]
theorem sum_prod_edgeFinset_of_isEmpty [IsEmpty α] [CommSemiring R] (w : Sym2 α → R) :
    (∑ D : PerfectMatching α, ∏ e ∈ D.edgeFinset, w e) = 1 := by
  have hcard := card_perfectMatching α (m := 0) (by simp)
  simp [edgeFinset, hcard]

end TauCeti.PerfectMatching
