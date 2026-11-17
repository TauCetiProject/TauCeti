/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Filter

/-!
# Products and sums over increasing pairs and triples in lexicographic products

In a lexicographic product `α ×ₗ β`, each element `a : α` becomes a cluster `{a} × β` ordered
internally by `β`, with distinct clusters ordered according to `α`. A strictly increasing pair
`x < y` therefore lies either inside one cluster (`(ofLex x).1 = (ofLex y).1` and
`(ofLex x).2 < (ofLex y).2`) or across two ordered clusters (`(ofLex x).1 < (ofLex y).1`, with
arbitrary second coordinates). Likewise, a strictly increasing triple `x < y < z` falls into one
of four disjoint incidence patterns according to whether `(ofLex x).1 ≤ (ofLex y).1 ≤ (ofLex z).1`
has two strict steps, one equality on the left, one equality on the right, or two equalities.

This file decomposes products, sums, and cardinalities over strictly increasing pairs and triples
of `(s ×ˢ t).map toLex.toEmbedding` (and over `Finset.univ` when `α` and `β` are finite types) into
those cluster-incidence pieces, requiring only preorders on `α` and `β`. When within-cluster pairs
or repeated-cluster triples carry trivial factors and inter-cluster factors depend only on the `α`
coordinates, the pair product raises the base product to `#t ^ 2` (or multiplies the base sum by
`#t ^ 2`) and the triple product raises the base product to `#t ^ 3` (or multiplies the base sum by
`#t ^ 3`).

## Main results

* `Finset.prod_filter_lt_map_toLex`, `Finset.sum_filter_lt_map_toLex`: upper-ray product and sum
  above a point in `(s ×ˢ t).map toLex.toEmbedding`.
* `Finset.prod_product_filter_lt_map_toLex`, `Finset.sum_product_filter_lt_map_toLex`:
  decomposition of products and sums over strictly increasing pairs in
  `(s ×ˢ t).map toLex.toEmbedding`, with cardinality formula
  `Finset.card_product_filter_lt_map_toLex` and quadratic collapse
  `Finset.prod_product_filter_lt_map_toLex_eq_pow_card_sq`.
* `Finset.prod_product_filter_lt_lt_map_toLex`, `Finset.sum_product_filter_lt_lt_map_toLex`:
  four-way decomposition of products and sums over strictly increasing triples in
  `(s ×ˢ t).map toLex.toEmbedding`, with cardinality formula
  `Finset.card_product_filter_lt_lt_map_toLex` and cubic collapse
  `Finset.prod_product_filter_lt_lt_map_toLex_eq_pow_card_cube`.
* `Fintype.prod_product_filter_lt_prodLex`, `Fintype.prod_product_filter_lt_lt_prodLex`,
  `Fintype.sum_product_filter_lt_prodLex_eq_card_sq_mul`, and
  `Fintype.sum_product_filter_lt_lt_prodLex_eq_card_cube_mul`: specializations to `Finset.univ` on
  finite types.

## References

* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, doi:10.5281/zenodo.23245792, Lemma 6 (cubic triangle-defect counting under balanced
  lexicographic replication).
-/

public section

open Prod.Lex

namespace Finset

section Preorder

variable {α β M : Type*} [Preorder α] [Preorder β]
  [DecidableLT α] [DecidableLT (α ×ₗ β)] [CommMonoid M]

section DecidableLT

variable [DecidableLT β]

/-- The product over the elements of `(s ×ˢ t).map toLex.toEmbedding` strictly above `x` splits
into the elements strictly above `(ofLex x).2` in the cluster of `(ofLex x).1` (when
`(ofLex x).1 ∈ s`) and the full clusters strictly above `(ofLex x).1`. -/
@[to_additive /-- The sum over the elements of `(s ×ˢ t).map toLex.toEmbedding` strictly above `x`
splits into the elements strictly above `(ofLex x).2` in the cluster of `(ofLex x).1` (when
`(ofLex x).1 ∈ s`) and the full clusters strictly above `(ofLex x).1`. -/]
theorem prod_filter_lt_map_toLex [DecidableEq α] (s : Finset α) (t : Finset β) (x : α ×ₗ β)
    (f : (α ×ₗ β) → M) :
    (∏ y ∈ (s ×ˢ t).map toLex.toEmbedding with x < y, f y) =
      (if (ofLex x).1 ∈ s then ∏ b ∈ t with (ofLex x).2 < b, f (toLex ((ofLex x).1, b)) else 1) *
        ∏ a ∈ s with (ofLex x).1 < a, ∏ b ∈ t, f (toLex (a, b)) := by
  rw [filter_map, prod_map]
  simp_rw [Function.comp_def, Equiv.coe_toEmbedding, prod_filter, prod_product]
  have hcluster {a : α} (hne : (ofLex x).1 ≠ a) :
      (∏ b ∈ t, if x < toLex (a, b) then f (toLex (a, b)) else 1) =
        if (ofLex x).1 < a then ∏ b ∈ t, f (toLex (a, b)) else 1 := by
    by_cases hxa : (ofLex x).1 < a <;> simp [Prod.Lex.lt_iff, hne, hxa]
  by_cases hx : (ofLex x).1 ∈ s
  · rw [ite_eq_left hx, ← mul_prod_erase s _ hx,
      ← mul_prod_erase s (fun a ↦ if (ofLex x).1 < a then ∏ b ∈ t, f (toLex (a, b)) else 1) hx,
      ite_eq_right (lt_irrefl _), one_mul]
    congr 1
    · simp [Prod.Lex.lt_iff]
    · exact prod_congr rfl fun a ha ↦ hcluster (mem_erase.mp ha).1.symm
  · rw [ite_eq_right hx, one_mul]
    exact prod_congr rfl fun a ha ↦ hcluster fun h ↦ hx (h ▸ ha)

/-- When `a₁ ∈ s`, the product over `y ∈ (s ×ˢ t).map toLex.toEmbedding` strictly above
`toLex (a₁, b₁)` splits into the upper ray in `{a₁} × t` and the full clusters above `a₁`, with no
decidable-equality assumption on `α`. -/
@[to_additive /-- When `a₁ ∈ s`, the sum over `y ∈ (s ×ˢ t).map toLex.toEmbedding` strictly above
`toLex (a₁, b₁)` splits into the upper ray in `{a₁} × t` and the full clusters above `a₁`, with no
decidable-equality assumption on `α`. -/]
theorem prod_filter_lt_map_toLex_of_mem (s : Finset α) {a₁ : α} (ha₁ : a₁ ∈ s) (t : Finset β)
    (b₁ : β) (f : (α ×ₗ β) → M) :
    (∏ y ∈ (s ×ˢ t).map toLex.toEmbedding with toLex (a₁, b₁) < y, f y) =
      (∏ b₂ ∈ t with b₁ < b₂, f (toLex (a₁, b₂))) *
        ∏ a₂ ∈ s with a₁ < a₂, ∏ b₂ ∈ t, f (toLex (a₂, b₂)) := by
  have : DecidableEq α := Classical.decEq α
  rw [prod_filter_lt_map_toLex, ofLex_toLex, ite_eq_left ha₁]

@[to_additive]
private theorem prod_prod_filter_lt_map_toLex_of_mem {γ : Type*} (s : Finset α) (t : Finset β)
    (u : Finset γ) (a : γ → α) (ha : ∀ c ∈ u, a c ∈ s) (b : γ → β)
    (f : γ → (α ×ₗ β) → M) :
    (∏ c ∈ u, ∏ y ∈ (s ×ˢ t).map toLex.toEmbedding with toLex (a c, b c) < y, f c y) =
      (∏ c ∈ u, ∏ b' ∈ t with b c < b', f c (toLex (a c, b'))) *
        ∏ c ∈ u, ∏ a' ∈ s with a c < a', ∏ b' ∈ t, f c (toLex (a', b')) := by
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun c hc ↦ s.prod_filter_lt_map_toLex_of_mem (ha c hc) t (b c) (f c)

/-- A product over strictly increasing pairs in `(s ×ˢ t).map toLex.toEmbedding` splits into the
within-cluster strictly increasing pairs and the inter-cluster pairs across strictly increasing
elements of `s`. -/
@[to_additive /-- A sum over strictly increasing pairs in `(s ×ˢ t).map toLex.toEmbedding` splits
into the within-cluster strictly increasing pairs and the inter-cluster pairs across strictly
increasing elements of `s`. -/]
theorem prod_product_filter_lt_map_toLex (s : Finset α) (t : Finset β)
    (f : (α ×ₗ β) → (α ×ₗ β) → M) :
    (∏ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2, f p.1 p.2) =
      (∏ a ∈ s, ∏ q ∈ t ×ˢ t with q.1 < q.2, f (toLex (a, q.1)) (toLex (a, q.2))) *
        ∏ e ∈ s ×ˢ s with e.1 < e.2, ∏ b₁ ∈ t, ∏ b₂ ∈ t,
          f (toLex (e.1, b₁)) (toLex (e.2, b₂)) := by
  rw [prod_filter_product, prod_map, prod_product]
  simp_rw [Equiv.coe_toEmbedding]
  have hstep (a₁ : α) (ha₁ : a₁ ∈ s) :=
    prod_prod_filter_lt_map_toLex_of_mem s t t (fun _ ↦ a₁) (fun _ _ ↦ ha₁) (fun b₁ ↦ b₁)
      (fun b₁ y ↦ f (toLex (a₁, b₁)) y)
  rw [prod_congr rfl hstep, prod_mul_distrib]
  refine congrArg₂ (· * ·)
    (prod_congr rfl fun _ _ ↦ (prod_filter_product t t (· < ·) _).symm) ?_
  exact (prod_congr rfl fun _ _ ↦ prod_comm).trans (prod_filter_product s s (· < ·) _).symm

/-- The number of strictly increasing pairs in `(s ×ˢ t).map toLex.toEmbedding` is the number of
within-cluster increasing pairs `#s * #{q ∈ t ×ˢ t | q.1 < q.2}` plus the number of inter-cluster
pairs `#{e ∈ s ×ˢ s | e.1 < e.2} * #t ^ 2`. -/
theorem card_product_filter_lt_map_toLex (s : Finset α) (t : Finset β) :
    #{p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding) | p.1 < p.2} =
      #s * #{q ∈ t ×ˢ t | q.1 < q.2} + #{e ∈ s ×ˢ s | e.1 < e.2} * #t ^ 2 := by
  simpa [sq, mul_assoc] using sum_product_filter_lt_map_toLex s t (fun _ _ ↦ (1 : ℕ))

/-- A product over strictly increasing triples `p.1 < p.2.1 < p.2.2` in
`(s ×ˢ t).map toLex.toEmbedding` decomposes into four cluster-incidence factors: three distinct
clusters, two elements in the lower cluster and one in the upper, one element in the lower cluster
and two in the upper, and all three elements in one cluster. -/
@[to_additive /-- A sum over strictly increasing triples `p.1 < p.2.1 < p.2.2` in
`(s ×ˢ t).map toLex.toEmbedding` decomposes into four cluster-incidence terms: three distinct
clusters, two elements in the lower cluster and one in the upper, one element in the lower cluster
and two in the upper, and all three elements in one cluster. -/]
theorem prod_product_filter_lt_lt_map_toLex (s : Finset α) (t : Finset β)
    (f : (α ×ₗ β) → (α ×ₗ β) → (α ×ₗ β) → M) :
    (∏ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ
          ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2.1 ∧ p.2.1 < p.2.2, f p.1 p.2.1 p.2.2) =
      (∏ u ∈ s ×ˢ s ×ˢ s with u.1 < u.2.1 ∧ u.2.1 < u.2.2,
          ∏ b₁ ∈ t, ∏ b₂ ∈ t, ∏ b₃ ∈ t,
            f (toLex (u.1, b₁)) (toLex (u.2.1, b₂)) (toLex (u.2.2, b₃))) *
        (∏ e ∈ s ×ˢ s with e.1 < e.2, ∏ q ∈ t ×ˢ t with q.1 < q.2, ∏ b₃ ∈ t,
            f (toLex (e.1, q.1)) (toLex (e.1, q.2)) (toLex (e.2, b₃))) *
        (∏ e ∈ s ×ˢ s with e.1 < e.2, ∏ b₁ ∈ t, ∏ q ∈ t ×ˢ t with q.1 < q.2,
            f (toLex (e.1, b₁)) (toLex (e.2, q.1)) (toLex (e.2, q.2))) *
        (∏ a ∈ s, ∏ v ∈ t ×ˢ t ×ˢ t with v.1 < v.2.1 ∧ v.2.1 < v.2.2,
            f (toLex (a, v.1)) (toLex (a, v.2.1)) (toLex (a, v.2.2))) := by
  set S := (s ×ˢ t).map toLex.toEmbedding
  rw [prod_filter_product_product_and S S S (· < ·) (fun _ y z ↦ y < z) f,
    prod_product_filter_lt_map_toLex s t (fun x y ↦ ∏ z ∈ S with y < z, f x y z)]
  -- Extend each within-cluster pair to a third element in the same cluster or a higher cluster.
  have hwithin (a : α) (ha : a ∈ s) :
      (∏ q ∈ t ×ˢ t with q.1 < q.2,
          ∏ z ∈ S with toLex (a, q.2) < z, f (toLex (a, q.1)) (toLex (a, q.2)) z) =
        (∏ v ∈ t ×ˢ t ×ˢ t with v.1 < v.2.1 ∧ v.2.1 < v.2.2,
            f (toLex (a, v.1)) (toLex (a, v.2.1)) (toLex (a, v.2.2))) *
          ∏ a₃ ∈ s with a < a₃, ∏ q ∈ t ×ˢ t with q.1 < q.2, ∏ b₃ ∈ t,
            f (toLex (a, q.1)) (toLex (a, q.2)) (toLex (a₃, b₃)) := by
    rw [prod_prod_filter_lt_map_toLex_of_mem s t _ (fun _ ↦ a) (fun _ _ ↦ ha) Prod.snd
      (fun q z ↦ f (toLex (a, q.1)) (toLex (a, q.2)) z)]
    exact congrArg₂ (· * ·)
      (prod_filter_product_product_and t t t (· < ·) (fun _ b₂ b₃ ↦ b₂ < b₃)
        fun b₁ b₂ b₃ ↦ f (toLex (a, b₁)) (toLex (a, b₂)) (toLex (a, b₃))).symm prod_comm
  -- Extend each inter-cluster pair to a third element in the upper cluster or a third cluster.
  have hinter (e : α × α) (he : e ∈ {e ∈ s ×ˢ s | e.1 < e.2}) :
      (∏ b₁ ∈ t, ∏ b₂ ∈ t,
          ∏ z ∈ S with toLex (e.2, b₂) < z, f (toLex (e.1, b₁)) (toLex (e.2, b₂)) z) =
        (∏ b₁ ∈ t, ∏ q ∈ t ×ˢ t with q.1 < q.2,
            f (toLex (e.1, b₁)) (toLex (e.2, q.1)) (toLex (e.2, q.2))) *
          ∏ a₃ ∈ s with e.2 < a₃, ∏ b₁ ∈ t, ∏ b₂ ∈ t, ∏ b₃ ∈ t,
            f (toLex (e.1, b₁)) (toLex (e.2, b₂)) (toLex (a₃, b₃)) := by
    have he₂ : e.2 ∈ s := (mem_product.mp (mem_filter.mp he).1).2
    have hinner (b₁ : β) (_ : b₁ ∈ t) :=
      prod_prod_filter_lt_map_toLex_of_mem s t t (fun _ ↦ e.2) (fun _ _ ↦ he₂) (fun b₂ ↦ b₂)
        (fun b₂ z ↦ f (toLex (e.1, b₁)) (toLex (e.2, b₂)) z)
    rw [prod_congr rfl hinner, prod_mul_distrib]
    refine congrArg₂ (· * ·)
      (prod_congr rfl fun _ _ ↦ (prod_filter_product t t (· < ·) _).symm) ?_
    exact (prod_congr rfl fun _ _ ↦ prod_comm).trans prod_comm
  rw [prod_congr rfl hwithin, prod_mul_distrib, prod_congr rfl hinter, prod_mul_distrib,
    ← prod_filter_product s s (· < ·),
    prod_filter_product_product_and s s s (· < ·) (fun _ a₂ a₃ ↦ a₂ < a₃)
      fun a₁ a₂ a₃ ↦ ∏ b₁ ∈ t, ∏ b₂ ∈ t, ∏ b₃ ∈ t,
        f (toLex (a₁, b₁)) (toLex (a₂, b₂)) (toLex (a₃, b₃))]
  ac_rfl

/-- The number of strictly increasing triples in `(s ×ˢ t).map toLex.toEmbedding` decomposes into
`#t ^ 3` lifts of each strictly increasing triple of `s`, `2 * #{q ∈ t ×ˢ t | q.1 < q.2} * #t`
lifts of each strictly increasing pair of `s`, and `#s` copies of the strictly increasing triples of
`t`. -/
theorem card_product_filter_lt_lt_map_toLex (s : Finset α) (t : Finset β) :
    #{p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ
        ((s ×ˢ t).map toLex.toEmbedding) | p.1 < p.2.1 ∧ p.2.1 < p.2.2} =
      #{u ∈ s ×ˢ s ×ˢ s | u.1 < u.2.1 ∧ u.2.1 < u.2.2} * #t ^ 3 +
        2 * #{e ∈ s ×ˢ s | e.1 < e.2} * #{q ∈ t ×ˢ t | q.1 < q.2} * #t +
        #s * #{v ∈ t ×ˢ t ×ˢ t | v.1 < v.2.1 ∧ v.2.1 < v.2.2} := by
  have h := sum_product_filter_lt_lt_map_toLex s t (fun _ _ _ ↦ (1 : ℕ))
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at h
  rw [h]
  ring

end DecidableLT

/-- When within-cluster strictly increasing pairs have trivial value `1` and inter-cluster pairs
depend only on their first coordinates, the product over strictly increasing pairs in
`(s ×ˢ t).map toLex.toEmbedding` raises the base pair product to `#t ^ 2`. -/
@[to_additive sum_product_filter_lt_map_toLex_eq_card_sq_nsmul
/-- When within-cluster strictly increasing pairs vanish and inter-cluster pairs depend only on
their first coordinates, the sum over strictly increasing pairs in `(s ×ˢ t).map toLex.toEmbedding`
multiplies the base pair sum by `#t ^ 2`. -/]
theorem prod_product_filter_lt_map_toLex_eq_pow_card_sq (s : Finset α) (t : Finset β)
    (f : (α ×ₗ β) → (α ×ₗ β) → M) (g : α → α → M)
    (hdiag : ∀ a ∈ s, ∀ b₁ ∈ t, ∀ b₂ ∈ t, b₁ < b₂ → f (toLex (a, b₁)) (toLex (a, b₂)) = 1)
    (hinter : ∀ a₁ ∈ s, ∀ a₂ ∈ s, a₁ < a₂ → ∀ b₁ ∈ t, ∀ b₂ ∈ t,
      f (toLex (a₁, b₁)) (toLex (a₂, b₂)) = g a₁ a₂) :
    (∏ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2, f p.1 p.2) =
      (∏ e ∈ s ×ˢ s with e.1 < e.2, g e.1 e.2) ^ (#t ^ 2) := by
  have : DecidableLT β := Classical.decRel _
  rw [prod_product_filter_lt_map_toLex]
  have h1 : (∏ a ∈ s, ∏ q ∈ t ×ˢ t with q.1 < q.2, f (toLex (a, q.1)) (toLex (a, q.2))) = 1 := by
    refine prod_eq_one fun a ha ↦ prod_eq_one fun q hq ↦ ?_
    simp only [mem_filter, mem_product] at hq
    exact hdiag a ha q.1 hq.1.1 q.2 hq.1.2 hq.2
  have h2 :
      (∏ e ∈ s ×ˢ s with e.1 < e.2, ∏ b₁ ∈ t, ∏ b₂ ∈ t,
          f (toLex (e.1, b₁)) (toLex (e.2, b₂))) =
        (∏ e ∈ s ×ˢ s with e.1 < e.2, g e.1 e.2) ^ (#t ^ 2) := by
    rw [← prod_pow]
    refine prod_congr rfl fun e he ↦ ?_
    simp only [mem_filter, mem_product] at he
    have heq :
        (∏ b₁ ∈ t, ∏ b₂ ∈ t, f (toLex (e.1, b₁)) (toLex (e.2, b₂))) =
          ∏ _b₁ ∈ t, ∏ _b₂ ∈ t, g e.1 e.2 :=
      prod_congr rfl fun b₁ hb₁ ↦ prod_congr rfl fun b₂ hb₂ ↦
        hinter e.1 he.1.1 e.2 he.1.2 he.2 b₁ hb₁ b₂ hb₂
    rw [heq]
    simp [sq, pow_mul]
  rw [h1, one_mul, h2]

/-- When triples with two equal adjacent first coordinates have trivial value `1` and three-cluster
triples depend only on their first coordinates, the product over strictly increasing triples in
`(s ×ˢ t).map toLex.toEmbedding` raises the base triple product to `#t ^ 3`. -/
@[to_additive sum_product_filter_lt_lt_map_toLex_eq_card_cube_nsmul
/-- When triples with two equal adjacent first coordinates vanish and three-cluster triples depend
only on their first coordinates, the sum over strictly increasing triples in
`(s ×ˢ t).map toLex.toEmbedding` multiplies the base triple sum by `#t ^ 3`. -/]
theorem prod_product_filter_lt_lt_map_toLex_eq_pow_card_cube (s : Finset α) (t : Finset β)
    (f : (α ×ₗ β) → (α ×ₗ β) → (α ×ₗ β) → M) (g : α → α → α → M)
    (hdeg : ∀ x ∈ (s ×ˢ t).map toLex.toEmbedding, ∀ y ∈ (s ×ˢ t).map toLex.toEmbedding,
      ∀ z ∈ (s ×ˢ t).map toLex.toEmbedding, x < y → y < z →
        ((ofLex x).1 = (ofLex y).1 ∨ (ofLex y).1 = (ofLex z).1) → f x y z = 1)
    (hinter : ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ a₃ ∈ s, a₁ < a₂ → a₂ < a₃ →
      ∀ b₁ ∈ t, ∀ b₂ ∈ t, ∀ b₃ ∈ t,
        f (toLex (a₁, b₁)) (toLex (a₂, b₂)) (toLex (a₃, b₃)) = g a₁ a₂ a₃) :
    (∏ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ
          ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2.1 ∧ p.2.1 < p.2.2, f p.1 p.2.1 p.2.2) =
      (∏ u ∈ s ×ˢ s ×ˢ s with u.1 < u.2.1 ∧ u.2.1 < u.2.2, g u.1 u.2.1 u.2.2) ^ (#t ^ 3) := by
  have : DecidableLT β := Classical.decRel _
  have hmem {a : α} (ha : a ∈ s) {b : β} (hb : b ∈ t) :
      toLex (a, b) ∈ (s ×ˢ t).map toLex.toEmbedding :=
    mem_map.mpr ⟨(a, b), mem_product.mpr ⟨ha, hb⟩, rfl⟩
  rw [prod_product_filter_lt_lt_map_toLex]
  have h1 :
      (∏ u ∈ s ×ˢ s ×ˢ s with u.1 < u.2.1 ∧ u.2.1 < u.2.2,
          ∏ b₁ ∈ t, ∏ b₂ ∈ t, ∏ b₃ ∈ t,
            f (toLex (u.1, b₁)) (toLex (u.2.1, b₂)) (toLex (u.2.2, b₃))) =
        (∏ u ∈ s ×ˢ s ×ˢ s with u.1 < u.2.1 ∧ u.2.1 < u.2.2, g u.1 u.2.1 u.2.2) ^ (#t ^ 3) := by
    rw [← prod_pow]
    refine prod_congr rfl fun u hu ↦ ?_
    simp only [mem_filter, mem_product] at hu
    have heq :
        (∏ b₁ ∈ t, ∏ b₂ ∈ t, ∏ b₃ ∈ t,
            f (toLex (u.1, b₁)) (toLex (u.2.1, b₂)) (toLex (u.2.2, b₃))) =
          ∏ _b₁ ∈ t, ∏ _b₂ ∈ t, ∏ _b₃ ∈ t, g u.1 u.2.1 u.2.2 :=
      prod_congr rfl fun b₁ hb₁ ↦ prod_congr rfl fun b₂ hb₂ ↦ prod_congr rfl fun b₃ hb₃ ↦
        hinter u.1 hu.1.1 u.2.1 hu.1.2.1 u.2.2 hu.1.2.2 hu.2.1 hu.2.2 b₁ hb₁ b₂ hb₂ b₃ hb₃
    rw [heq]
    simp [pow_succ, pow_mul]
  have h2 :
      (∏ e ∈ s ×ˢ s with e.1 < e.2, ∏ q ∈ t ×ˢ t with q.1 < q.2, ∏ b₃ ∈ t,
          f (toLex (e.1, q.1)) (toLex (e.1, q.2)) (toLex (e.2, b₃))) = 1 := by
    refine prod_eq_one fun e he ↦ prod_eq_one fun q hq ↦ prod_eq_one fun b₃ hb₃ ↦ ?_
    simp only [mem_filter, mem_product] at he hq
    exact hdeg _ (hmem he.1.1 hq.1.1) _ (hmem he.1.1 hq.1.2) _ (hmem he.1.2 hb₃)
      (toLex_lt_toLex.mpr (.inr ⟨rfl, hq.2⟩)) (toLex_lt_toLex.mpr (.inl he.2)) (.inl rfl)
  have h3 :
      (∏ e ∈ s ×ˢ s with e.1 < e.2, ∏ b₁ ∈ t, ∏ q ∈ t ×ˢ t with q.1 < q.2,
          f (toLex (e.1, b₁)) (toLex (e.2, q.1)) (toLex (e.2, q.2))) = 1 := by
    refine prod_eq_one fun e he ↦ prod_eq_one fun b₁ hb₁ ↦ prod_eq_one fun q hq ↦ ?_
    simp only [mem_filter, mem_product] at he hq
    exact hdeg _ (hmem he.1.1 hb₁) _ (hmem he.1.2 hq.1.1) _ (hmem he.1.2 hq.1.2)
      (toLex_lt_toLex.mpr (.inl he.2)) (toLex_lt_toLex.mpr (.inr ⟨rfl, hq.2⟩)) (.inr rfl)
  have h4 :
      (∏ a ∈ s, ∏ v ∈ t ×ˢ t ×ˢ t with v.1 < v.2.1 ∧ v.2.1 < v.2.2,
          f (toLex (a, v.1)) (toLex (a, v.2.1)) (toLex (a, v.2.2))) = 1 := by
    refine prod_eq_one fun a ha ↦ prod_eq_one fun v hv ↦ ?_
    simp only [mem_filter, mem_product] at hv
    exact hdeg _ (hmem ha hv.1.1) _ (hmem ha hv.1.2.1) _ (hmem ha hv.1.2.2)
      (toLex_lt_toLex.mpr (.inr ⟨rfl, hv.2.1⟩)) (toLex_lt_toLex.mpr (.inr ⟨rfl, hv.2.2⟩)) (.inl rfl)
  rw [h1, h2, h3, h4, mul_one, mul_one, mul_one]

end Preorder

section Semiring

variable {α β R : Type*} [Preorder α] [Preorder β]
  [DecidableLT α] [DecidableLT (α ×ₗ β)] [Semiring R]

/-- Semiring form of `Finset.sum_product_filter_lt_map_toLex_eq_card_sq_nsmul`: replicating across
`t` multiplies an increasing-pair sum by `(#t : R) ^ 2`. -/
theorem sum_product_filter_lt_map_toLex_eq_card_sq_mul (s : Finset α) (t : Finset β)
    (f : (α ×ₗ β) → (α ×ₗ β) → R) (g : α → α → R)
    (hdiag : ∀ a ∈ s, ∀ b₁ ∈ t, ∀ b₂ ∈ t, b₁ < b₂ → f (toLex (a, b₁)) (toLex (a, b₂)) = 0)
    (hinter : ∀ a₁ ∈ s, ∀ a₂ ∈ s, a₁ < a₂ → ∀ b₁ ∈ t, ∀ b₂ ∈ t,
      f (toLex (a₁, b₁)) (toLex (a₂, b₂)) = g a₁ a₂) :
    (∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2, f p.1 p.2) =
      (#t : R) ^ 2 * ∑ e ∈ s ×ˢ s with e.1 < e.2, g e.1 e.2 := by
  simpa [nsmul_eq_mul, Nat.cast_pow] using
    sum_product_filter_lt_map_toLex_eq_card_sq_nsmul s t f g hdiag hinter

/-- Semiring form of `Finset.sum_product_filter_lt_lt_map_toLex_eq_card_cube_nsmul`: replicating
across `t` multiplies an increasing-triple sum by `(#t : R) ^ 3`. -/
theorem sum_product_filter_lt_lt_map_toLex_eq_card_cube_mul (s : Finset α) (t : Finset β)
    (f : (α ×ₗ β) → (α ×ₗ β) → (α ×ₗ β) → R) (g : α → α → α → R)
    (hdeg : ∀ x ∈ (s ×ˢ t).map toLex.toEmbedding, ∀ y ∈ (s ×ˢ t).map toLex.toEmbedding,
      ∀ z ∈ (s ×ˢ t).map toLex.toEmbedding, x < y → y < z →
        ((ofLex x).1 = (ofLex y).1 ∨ (ofLex y).1 = (ofLex z).1) → f x y z = 0)
    (hinter : ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ a₃ ∈ s, a₁ < a₂ → a₂ < a₃ →
      ∀ b₁ ∈ t, ∀ b₂ ∈ t, ∀ b₃ ∈ t,
        f (toLex (a₁, b₁)) (toLex (a₂, b₂)) (toLex (a₃, b₃)) = g a₁ a₂ a₃) :
    (∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ
          ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2.1 ∧ p.2.1 < p.2.2, f p.1 p.2.1 p.2.2) =
      (#t : R) ^ 3 * ∑ u ∈ s ×ˢ s ×ˢ s with u.1 < u.2.1 ∧ u.2.1 < u.2.2, g u.1 u.2.1 u.2.2 := by
  simpa [nsmul_eq_mul, Nat.cast_pow] using
    sum_product_filter_lt_lt_map_toLex_eq_card_cube_nsmul s t f g hdeg hinter

end Semiring

end Finset

namespace Fintype

open Finset

section CommMonoid

variable {α β M : Type*} [Fintype α] [Fintype β] [Preorder α] [Preorder β]
  [DecidableLT α] [DecidableLT (α ×ₗ β)] [CommMonoid M]

section DecidableLT

variable [DecidableLT β]

/-- A product over strictly increasing pairs of a finite lexicographic product `α ×ₗ β` splits into
within-cluster strictly increasing pairs and inter-cluster pairs. -/
@[to_additive sum_product_filter_lt_prodLex
/-- A sum over strictly increasing pairs of a finite lexicographic product `α ×ₗ β` splits into
within-cluster strictly increasing pairs and inter-cluster pairs. -/]
theorem prod_product_filter_lt_prodLex (f : (α ×ₗ β) → (α ×ₗ β) → M) :
    (∏ p : (α ×ₗ β) × (α ×ₗ β) with p.1 < p.2, f p.1 p.2) =
      (∏ a : α, ∏ q : β × β with q.1 < q.2, f (toLex (a, q.1)) (toLex (a, q.2))) *
        ∏ e : α × α with e.1 < e.2, ∏ b₁ : β, ∏ b₂ : β,
          f (toLex (e.1, b₁)) (toLex (e.2, b₂)) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.prod_product_filter_lt_map_toLex (univ : Finset α) (univ : Finset β) f

/-- The number of strictly increasing pairs in a finite lexicographic product `α ×ₗ β`. -/
theorem card_product_filter_lt_prodLex :
    #{p : (α ×ₗ β) × (α ×ₗ β) | p.1 < p.2} =
      Fintype.card α * #{q : β × β | q.1 < q.2} +
        #{e : α × α | e.1 < e.2} * Fintype.card β ^ 2 := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.card_product_filter_lt_map_toLex (univ : Finset α) (univ : Finset β)

/-- Four-way cluster decomposition of a product over strictly increasing triples of a finite
lexicographic product `α ×ₗ β`. -/
@[to_additive sum_product_filter_lt_lt_prodLex
/-- Four-way cluster decomposition of a sum over strictly increasing triples of a finite
lexicographic product `α ×ₗ β`. -/]
theorem prod_product_filter_lt_lt_prodLex (f : (α ×ₗ β) → (α ×ₗ β) → (α ×ₗ β) → M) :
    (∏ p : (α ×ₗ β) × (α ×ₗ β) × (α ×ₗ β) with p.1 < p.2.1 ∧ p.2.1 < p.2.2, f p.1 p.2.1 p.2.2) =
      (∏ u : α × α × α with u.1 < u.2.1 ∧ u.2.1 < u.2.2,
          ∏ b₁ : β, ∏ b₂ : β, ∏ b₃ : β,
            f (toLex (u.1, b₁)) (toLex (u.2.1, b₂)) (toLex (u.2.2, b₃))) *
        (∏ e : α × α with e.1 < e.2, ∏ q : β × β with q.1 < q.2, ∏ b₃ : β,
            f (toLex (e.1, q.1)) (toLex (e.1, q.2)) (toLex (e.2, b₃))) *
        (∏ e : α × α with e.1 < e.2, ∏ b₁ : β, ∏ q : β × β with q.1 < q.2,
            f (toLex (e.1, b₁)) (toLex (e.2, q.1)) (toLex (e.2, q.2))) *
        (∏ a : α, ∏ v : β × β × β with v.1 < v.2.1 ∧ v.2.1 < v.2.2,
            f (toLex (a, v.1)) (toLex (a, v.2.1)) (toLex (a, v.2.2))) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.prod_product_filter_lt_lt_map_toLex (univ : Finset α) (univ : Finset β) f

/-- The number of strictly increasing triples in a finite lexicographic product `α ×ₗ β`. -/
theorem card_product_filter_lt_lt_prodLex :
    #{p : (α ×ₗ β) × (α ×ₗ β) × (α ×ₗ β) | p.1 < p.2.1 ∧ p.2.1 < p.2.2} =
      #{u : α × α × α | u.1 < u.2.1 ∧ u.2.1 < u.2.2} * Fintype.card β ^ 3 +
        2 * #{e : α × α | e.1 < e.2} * #{q : β × β | q.1 < q.2} * Fintype.card β +
        Fintype.card α * #{v : β × β × β | v.1 < v.2.1 ∧ v.2.1 < v.2.2} := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.card_product_filter_lt_lt_map_toLex (univ : Finset α) (univ : Finset β)

end DecidableLT

/-- When within-cluster strictly increasing pairs have trivial value `1` and inter-cluster pairs
depend only on their first coordinates, the product over strictly increasing pairs of `α ×ₗ β`
raises the base pair product to `Fintype.card β ^ 2`. -/
@[to_additive sum_product_filter_lt_prodLex_eq_card_sq_nsmul
/-- When within-cluster strictly increasing pairs vanish and inter-cluster pairs depend only on
their first coordinates, the sum over strictly increasing pairs of `α ×ₗ β` multiplies the base
pair sum by `Fintype.card β ^ 2`. -/]
theorem prod_product_filter_lt_prodLex_eq_pow_card_sq (f : (α ×ₗ β) → (α ×ₗ β) → M)
    (g : α → α → M)
    (hdiag : ∀ a b₁ b₂, b₁ < b₂ → f (toLex (a, b₁)) (toLex (a, b₂)) = 1)
    (hinter : ∀ a₁ a₂, a₁ < a₂ → ∀ b₁ b₂, f (toLex (a₁, b₁)) (toLex (a₂, b₂)) = g a₁ a₂) :
    (∏ p : (α ×ₗ β) × (α ×ₗ β) with p.1 < p.2, f p.1 p.2) =
      (∏ e : α × α with e.1 < e.2, g e.1 e.2) ^ (Fintype.card β ^ 2) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.prod_product_filter_lt_map_toLex_eq_pow_card_sq (univ : Finset α) (univ : Finset β) f g
      (fun a _ b₁ _ b₂ _ ↦ hdiag a b₁ b₂) (fun a₁ _ a₂ _ h b₁ _ b₂ _ ↦ hinter a₁ a₂ h b₁ b₂)

/-- When triples with two equal adjacent first coordinates have trivial value `1` and three-cluster
triples depend only on their first coordinates, the product over strictly increasing triples of
`α ×ₗ β` raises the base triple product to `Fintype.card β ^ 3`. -/
@[to_additive sum_product_filter_lt_lt_prodLex_eq_card_cube_nsmul
/-- When triples with two equal adjacent first coordinates vanish and three-cluster triples depend
only on their first coordinates, the sum over strictly increasing triples of `α ×ₗ β` multiplies
the base triple sum by `Fintype.card β ^ 3`. -/]
theorem prod_product_filter_lt_lt_prodLex_eq_pow_card_cube (f : (α ×ₗ β) → (α ×ₗ β) → (α ×ₗ β) → M)
    (g : α → α → α → M)
    (hdeg : ∀ x y z, x < y → y < z → ((ofLex x).1 = (ofLex y).1 ∨ (ofLex y).1 = (ofLex z).1) →
      f x y z = 1)
    (hinter : ∀ a₁ a₂ a₃, a₁ < a₂ → a₂ < a₃ → ∀ b₁ b₂ b₃,
      f (toLex (a₁, b₁)) (toLex (a₂, b₂)) (toLex (a₃, b₃)) = g a₁ a₂ a₃) :
    (∏ p : (α ×ₗ β) × (α ×ₗ β) × (α ×ₗ β) with p.1 < p.2.1 ∧ p.2.1 < p.2.2, f p.1 p.2.1 p.2.2) =
      (∏ u : α × α × α with u.1 < u.2.1 ∧ u.2.1 < u.2.2, g u.1 u.2.1 u.2.2) ^
        (Fintype.card β ^ 3) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.prod_product_filter_lt_lt_map_toLex_eq_pow_card_cube (univ : Finset α) (univ : Finset β)
      f g (fun x _ y _ z _ ↦ hdeg x y z)
      (fun a₁ _ a₂ _ a₃ _ h₁ h₂ b₁ _ b₂ _ b₃ _ ↦ hinter a₁ a₂ a₃ h₁ h₂ b₁ b₂ b₃)

end CommMonoid

section Semiring

variable {α β R : Type*} [Fintype α] [Fintype β] [Preorder α] [Preorder β]
  [DecidableLT α] [DecidableLT (α ×ₗ β)] [Semiring R]

/-- Semiring form of `Fintype.sum_product_filter_lt_prodLex_eq_card_sq_nsmul`: replicating across
`β` multiplies an increasing-pair sum by `(Fintype.card β : R) ^ 2`. -/
theorem sum_product_filter_lt_prodLex_eq_card_sq_mul (f : (α ×ₗ β) → (α ×ₗ β) → R)
    (g : α → α → R)
    (hdiag : ∀ a b₁ b₂, b₁ < b₂ → f (toLex (a, b₁)) (toLex (a, b₂)) = 0)
    (hinter : ∀ a₁ a₂, a₁ < a₂ → ∀ b₁ b₂, f (toLex (a₁, b₁)) (toLex (a₂, b₂)) = g a₁ a₂) :
    (∑ p : (α ×ₗ β) × (α ×ₗ β) with p.1 < p.2, f p.1 p.2) =
      (Fintype.card β : R) ^ 2 * ∑ e : α × α with e.1 < e.2, g e.1 e.2 := by
  simpa [nsmul_eq_mul, Nat.cast_pow] using
    sum_product_filter_lt_prodLex_eq_card_sq_nsmul f g hdiag hinter

/-- Semiring form of `Fintype.sum_product_filter_lt_lt_prodLex_eq_card_cube_nsmul`: replicating
across `β` multiplies an increasing-triple sum by `(Fintype.card β : R) ^ 3`. -/
theorem sum_product_filter_lt_lt_prodLex_eq_card_cube_mul (f : (α ×ₗ β) → (α ×ₗ β) → (α ×ₗ β) → R)
    (g : α → α → α → R)
    (hdeg : ∀ x y z, x < y → y < z → ((ofLex x).1 = (ofLex y).1 ∨ (ofLex y).1 = (ofLex z).1) →
      f x y z = 0)
    (hinter : ∀ a₁ a₂ a₃, a₁ < a₂ → a₂ < a₃ → ∀ b₁ b₂ b₃,
      f (toLex (a₁, b₁)) (toLex (a₂, b₂)) (toLex (a₃, b₃)) = g a₁ a₂ a₃) :
    (∑ p : (α ×ₗ β) × (α ×ₗ β) × (α ×ₗ β) with p.1 < p.2.1 ∧ p.2.1 < p.2.2, f p.1 p.2.1 p.2.2) =
      (Fintype.card β : R) ^ 3 *
        ∑ u : α × α × α with u.1 < u.2.1 ∧ u.2.1 < u.2.2, g u.1 u.2.1 u.2.2 := by
  simpa [nsmul_eq_mul, Nat.cast_pow] using
    sum_product_filter_lt_lt_prodLex_eq_card_cube_nsmul f g hdeg hinter

end Semiring

end Fintype
