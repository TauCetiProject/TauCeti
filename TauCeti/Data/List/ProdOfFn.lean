/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn

/-!
# Products of the lists `List.ofFn f`

In a monoid, the product of the letters `β (w 0) ⋯ β (w (n + 1))` of a word `w` obtained from a
word `u` of length `n` by inserting two consecutive letters `d, e` at the positions `p` and
`p + 1` factors as `L * β d * β e * R`, where `L` and `R` depend only on `u` and `p`
(`List.exists_prod_ofFn_insertNth_insertNth`). This is how a relation among the products
`β d * β e` passes to the products of all words carrying the letters `d, e` in a fixed position:
in particular, any sum `∑ i ∈ s, β (g₁ i) * β (g₂ i) = 0` in a semiring annihilates the induced sum
after inserting `g₁ i` and `g₂ i` into any word and applying an additive homomorphism
(`List.sum_apply_prod_ofFn_insertNth_insertNth`).
Similarly, moving the first letter of a word to the end corresponds to moving its factor from the
left to the right (`List.apply_prod_ofFn_snoc`).

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

For a natural-indexed family `b`, the product `b 0 ⋯ b (n - 1)` of its first `n` entries splits
off its last entry (`List.prod_ofFn_val_succ`), only reads the entries below `n`
(`List.prod_ofFn_val_congr`) and splits along a concatenation (`List.prod_ofFn_val_add`).
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

/-- Summing an additive homomorphism of the word product obtained by inserting consecutive letters
`g₁ i` and `g₂ i` at positions `p` and `p + 1` vanishes whenever `∑ i ∈ s, β (g₁ i) * β (g₂ i) = 0`.
-/
theorem sum_apply_prod_ofFn_insertNth_insertNth {D ι B C F : Type*} [Semiring B]
    [AddCommMonoid C] [FunLike F B C] [AddMonoidHomClass F B C]
    (β : D → B) (f : F) (s : Finset ι) (g₁ g₂ : ι → D)
    (hβ : ∑ i ∈ s, β (g₁ i) * β (g₂ i) = 0) {n : ℕ} (p : Fin (n + 1)) (u : Fin n → D) :
    ∑ i ∈ s, f (ofFn fun t ↦
      β ((Fin.insertNth p.castSucc (g₁ i) (Fin.insertNth p (g₂ i) u) :
        Fin (n + 2) → D) t)).prod = 0 := by
  obtain ⟨L, R, h⟩ := exists_prod_ofFn_insertNth_insertNth β p u
  simp_rw [h]
  calc ∑ i ∈ s, f (L * β (g₁ i) * β (g₂ i) * R)
      = f (L * (∑ i ∈ s, β (g₁ i) * β (g₂ i)) * R) := by
        rw [Finset.mul_sum, Finset.sum_mul, map_sum]
        simp only [mul_assoc]
    _ = 0 := by rw [hβ, mul_zero, zero_mul, map_zero]

/-- Moving the first letter of a word to the end applies `g` to the image of its product under a
map `f` satisfying `f (y * β e) = g (f (β e * y))`. -/
theorem apply_prod_ofFn_snoc {D M C : Type*} [Monoid M] (β : D → M) (f : M → C) {g : C → C}
    (hf : ∀ (e : D) (y : M), f (y * β e) = g (f (β e * y))) {n : ℕ} (u : Fin n → D) (e : D) :
    f (ofFn fun t ↦ β ((Fin.snoc u e : Fin (n + 1) → D) t)).prod =
      g (f (ofFn fun t ↦ β ((Fin.cons e u : Fin (n + 1) → D) t)).prod) := by
  have hsnoc : (ofFn fun t ↦ β ((Fin.snoc u e : Fin (n + 1) → D) t)).prod =
      (ofFn fun t ↦ β (u t)).prod * β e := by
    rw [ofFn_succ', concat_eq_append, prod_append, prod_singleton]
    simp
  have hcons : (ofFn fun t ↦ β ((Fin.cons e u : Fin (n + 1) → D) t)).prod =
      β e * (ofFn fun t ↦ β (u t)).prod := by
    rw [ofFn_succ, prod_cons]
    simp
  rw [hsnoc, hcons, hf]

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

/-- The product of a word, split around two adjacent letters: the letters before them, the two
letters, and the letters after them. -/
theorem prod_ofFn_eq_take_mul_mul_drop {M : Type*} [Monoid M] {k : ℕ} (g : Fin k → M)
    {i i' : Fin k} (hi : (i : ℕ) + 1 = i') :
    (ofFn g).prod = ((ofFn g).take i).prod * (g i * g i') * ((ofFn g).drop (i' + 1)).prod := by
  have hi₁ : (i : ℕ) < (ofFn g).length := by simp
  have hi₂ : (i : ℕ) + 1 < (ofFn g).length := by simp [hi]
  conv_lhs => rw [← take_append_drop i (ofFn g), drop_eq_getElem_cons hi₁,
    drop_eq_getElem_cons hi₂]
  simp [hi, mul_assoc]

/-- A monoid endomorphism fixing the product of two adjacent letters of a word, and every other
letter, fixes the product of the word. -/
theorem map_prod_ofFn_of_adjacent {F M : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) {k : ℕ} (g : Fin k → M) {i i' : Fin k} (hi : (i : ℕ) + 1 = i')
    (hfix : ∀ j, j ≠ i → j ≠ i' → f (g j) = g j) (h : f (g i * g i') = g i * g i') :
    f (List.ofFn g).prod = (List.ofFn g).prod := by
  have hmap (L : List M) (hL : ∀ a ∈ L, f a = a) : f L.prod = L.prod := by
    rw [map_list_prod, List.map_congr_left hL, List.map_id']
  rw [prod_ofFn_eq_take_mul_mul_drop g hi, map_mul, map_mul, h, hmap, hmap]
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

section Nat

variable {M : Type*} [Monoid M]

/-- The product of the first `n + 1` entries of a natural-indexed family splits off its last
entry. -/
theorem prod_ofFn_val_succ (b : ℕ → M) (n : ℕ) :
    (ofFn fun j : Fin (n + 1) ↦ b j).prod = (ofFn fun j : Fin n ↦ b j).prod * b n := by
  rw [ofFn_succ', prod_concat]
  simp

/-- The product of the first `n` entries of a natural-indexed family only reads the entries
below `n`. -/
theorem prod_ofFn_val_congr {n : ℕ} {b b' : ℕ → M} (h : ∀ i < n, b i = b' i) :
    (ofFn fun j : Fin n ↦ b j).prod = (ofFn fun j : Fin n ↦ b' j).prod :=
  congrArg prod (ofFn_inj.2 (funext fun j ↦ h j j.isLt))

/-- The product of the first `p + d` entries of a natural-indexed family is the product of the
first `p` entries times the product of the `d` entries after them. -/
theorem prod_ofFn_val_add (b : ℕ → M) (p d : ℕ) :
    (ofFn fun j : Fin (p + d) ↦ b j).prod =
      (ofFn fun j : Fin p ↦ b j).prod * (ofFn fun j : Fin d ↦ b (p + j)).prod := by
  simp only [ofFn_add, prod_append, Fin.val_castLE, Fin.val_natAdd]

end Nat

end List
