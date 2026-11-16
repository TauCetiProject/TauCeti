/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Products of the lists `List.ofFn f`

In a monoid, the product of the letters `β (w 0) ⋯ β (w (n + 1))` of a word `w` obtained from a
word `u` of length `n` by inserting two consecutive letters `d, e` at the positions `p` and
`p + 1` factors as `L * β d * β e * R`, where `L` and `R` depend only on `u` and `p`
(`List.exists_prod_ofFn_insertNth_insertNth`). This is how a relation among the products
`β d * β e` passes to the products of all words carrying the letters `d, e` in a fixed position.

A nonempty product `f₀ f₁ ⋯ fₙ` is the left fold of `f₁, …, fₙ` starting from `f₀`
(`List.prod_ofFn_eq_foldl`), and multiplicative maps, not necessarily unital, preserve such left
folds (`List.map_foldl_ofFn_mul`). Together they move nonempty products through nonunital
homomorphisms.

The product of a word whose letters all equal `c` except for a single letter `a` in position `p`
is `c ^ p * a * c ^ (n - p)` (`List.prod_ofFn_ite`).

A monoid endomorphism fixing every letter of a word, or fixing the product of two adjacent
letters and every other letter, fixes the product of the word (`List.map_prod_ofFn_of_forall`,
`List.map_prod_ofFn_of_adjacent`). In a division monoid the inverse of a product is the product
of the inverses in the reverse order (`List.inv_prod_ofFn`).
-/

public section

namespace List

/-- Inserting two consecutive letters `d, e` into a word multiplies its product by `β d * β e` in
a fixed position. -/
theorem exists_prod_ofFn_insertNth_insertNth {D M : Type*} [Monoid M] (β : D → M)
    {n : ℕ} (p : Fin (n + 1)) (u : Fin n → D) :
    ∃ L R : M, ∀ d e : D,
      (ofFn fun t ↦
        β ((Fin.insertNth p.castSucc d (Fin.insertNth p e u) : Fin (n + 2) → D) t)).prod =
        L * β d * β e * R := by
  induction n with
  | zero =>
    obtain rfl : p = 0 := Fin.fin_one_eq_zero p
    exact ⟨1, 1, fun d e ↦ by simp [ofFn_succ, Fin.insertNth_zero']⟩
  | succ n ih =>
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨q, rfl⟩
    · exact ⟨1, (ofFn fun t ↦ β (u t)).prod, fun d e ↦ by
        simp [ofFn_succ, Fin.insertNth_zero', mul_assoc]⟩
    · obtain ⟨L, R, h⟩ := ih q (Fin.tail u)
      refine ⟨β (u 0) * L, R, fun d e ↦ ?_⟩
      rw [← Fin.cons_self_tail u, Fin.insertNth_succ_cons, ← Fin.succ_castSucc,
        Fin.insertNth_succ_cons, ofFn_succ, prod_cons]
      simp only [Fin.cons_zero, Fin.cons_succ, h, mul_assoc]

/-- A nonempty product `f₀ f₁ ⋯ fₙ` is the left fold of `f₁, …, fₙ` starting from `f₀`. -/
theorem prod_ofFn_eq_foldl {M : Type*} [Monoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    (ofFn f).prod = (ofFn fun i : Fin n ↦ f i.succ).foldl (· * ·) (f 0) := by
  rw [ofFn_succ, prod_cons, prod_eq_foldl,
    ← foldl_assoc (op := fun x y : M ↦ x * y), mul_one]

/-- A multiplicative map, not necessarily unital, carries a left fold of products to the left
fold of the images. -/
theorem map_foldl_ofFn_mul {F R S : Type*} [Mul R] [Mul S] [FunLike F R S]
    [MulHomClass F R S] (g : F) {n : ℕ} (f : Fin n → R) (x : R) :
    g ((ofFn f).foldl (· * ·) x) = (ofFn fun i ↦ g (f i)).foldl (· * ·) (g x) := by
  rw [← Function.comp_def, ← map_ofFn, foldl_map,
    foldl_hom g fun x y ↦ (map_mul g x y).symm]

/-- The product of a word of length `n + 1` whose letters all equal `c` except for the letter `a` in
position `p` is `c ^ p * a * c ^ (n - p)`. -/
theorem prod_ofFn_ite {M : Type*} [Monoid M] (a c : M) :
    ∀ (n : ℕ) (p : Fin (n + 1)),
      (ofFn fun i : Fin (n + 1) ↦ if i = p then a else c).prod =
        c ^ (p : ℕ) * a * c ^ (n - p)
  | 0, p => by
    obtain rfl : p = 0 := Fin.fin_one_eq_zero p
    simp
  | n + 1, p => by
    rw [ofFn_succ, prod_cons]
    refine Fin.cases ?_ (fun q ↦ ?_) p
    · simp [ofFn_const, pow_succ']
    · have h := prod_ofFn_ite a c n q
      have h0 : ¬ ((0 : Fin (n + 1 + 1)) = q.succ) := (Fin.succ_ne_zero q).symm
      simp only [Fin.succ_inj, h0, ite_false, Fin.val_succ] at h ⊢
      rw [h, pow_succ']
      simp [mul_assoc, Nat.add_sub_add_right]

/-- A monoid endomorphism fixing every letter of a word fixes the product of the word. -/
theorem map_prod_ofFn_of_forall {F M : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) {k : ℕ} (g : Fin k → M) (h : ∀ i, f (g i) = g i) :
    f (List.ofFn g).prod = (List.ofFn g).prod := by
  simp [map_list_prod, List.map_ofFn, Function.comp_def, h]

/-- A monoid endomorphism fixing the product of two adjacent letters of a word, and every other
letter, fixes the product of the word. -/
theorem map_prod_ofFn_of_adjacent {F M : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) {k : ℕ} (g : Fin k → M) {i i' : Fin k} (hi : (i : ℕ) + 1 = i')
    (hfix : ∀ j, j ≠ i → j ≠ i' → f (g j) = g j) (h : f (g i * g i') = g i * g i') :
    f (List.ofFn g).prod = (List.ofFn g).prod := by
  have hmap (L : List M) (hL : ∀ a ∈ L, f a = a) : f L.prod = L.prod := by
    rw [map_list_prod, List.map_congr_left hL, List.map_id']
  have hi₁ : (i : ℕ) < (List.ofFn g).length := by simp
  have hi₂ : (i : ℕ) + 1 < (List.ofFn g).length := by simp [hi]
  have hprod : (List.ofFn g).prod = ((List.ofFn g).take i).prod * (g i * g i') *
      ((List.ofFn g).drop (i' + 1)).prod := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn g), List.drop_eq_getElem_cons hi₁,
      List.drop_eq_getElem_cons hi₂]
    simp [hi, mul_assoc]
  rw [hprod, map_mul, map_mul, h, hmap, hmap]
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.1 ha
    rw [List.getElem_ofFn]
    exact hfix _ (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 ha
    rw [List.getElem_ofFn]
    exact hfix _ (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

/-- The inverse of a product `f₀ f₁ ⋯ fₙ₋₁` in a division monoid is the product of the inverses
in the reverse order. -/
theorem inv_prod_ofFn {M : Type*} [DivisionMonoid M] :
    ∀ {k : ℕ} (f : Fin k → M), (List.ofFn f).prod⁻¹ = (List.ofFn fun i ↦ (f i.rev)⁻¹).prod
  | 0, _ => by simp
  | k + 1, f => by
    rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append, List.prod_cons, List.prod_append,
      mul_inv_rev, inv_prod_ofFn]
    simp [Fin.rev_castSucc]

end List
