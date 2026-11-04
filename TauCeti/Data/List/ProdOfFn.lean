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
-/

public section

namespace List

/-- Inserting two consecutive letters `d, e` into a word multiplies its product by `β d * β e` in
a fixed position. -/
theorem exists_prod_ofFn_insertNth_insertNth {D M : Type*} [Monoid M] (β : D → M)
    {n : ℕ} (p : Fin (n + 1)) (u : Fin n → D) :
    ∃ L R : M, ∀ d e : D,
      (List.ofFn fun t ↦
        β ((Fin.insertNth p.castSucc d (Fin.insertNth p e u) : Fin (n + 2) → D) t)).prod =
        L * β d * β e * R := by
  induction n with
  | zero =>
    obtain rfl : p = 0 := Fin.fin_one_eq_zero p
    exact ⟨1, 1, fun d e ↦ by simp [List.ofFn_succ, Fin.insertNth_zero']⟩
  | succ n ih =>
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨q, rfl⟩
    · exact ⟨1, (List.ofFn fun t ↦ β (u t)).prod, fun d e ↦ by
        simp [List.ofFn_succ, Fin.insertNth_zero', mul_assoc]⟩
    · obtain ⟨L, R, h⟩ := ih q (Fin.tail u)
      refine ⟨β (u 0) * L, R, fun d e ↦ ?_⟩
      rw [← Fin.cons_self_tail u, Fin.insertNth_succ_cons, ← Fin.succ_castSucc,
        Fin.insertNth_succ_cons, List.ofFn_succ, List.prod_cons]
      simp only [Fin.cons_zero, Fin.cons_succ, h, mul_assoc]

/-- A nonempty product `f₀ f₁ ⋯ fₙ` is the left fold of `f₁, …, fₙ` starting from `f₀`. -/
theorem prod_ofFn_eq_foldl {M : Type*} [Monoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    (List.ofFn f).prod = (List.ofFn fun i : Fin n ↦ f i.succ).foldl (· * ·) (f 0) := by
  rw [List.ofFn_succ, List.prod_cons, List.prod_eq_foldl,
    ← List.foldl_assoc (op := fun x y : M ↦ x * y), mul_one]

/-- A multiplicative map, not necessarily unital, carries a left fold of products to the left
fold of the images. -/
theorem map_foldl_ofFn_mul {F R S : Type*} [Mul R] [Mul S] [FunLike F R S]
    [MulHomClass F R S] (g : F) {n : ℕ} (f : Fin n → R) (x : R) :
    g ((List.ofFn f).foldl (· * ·) x) = (List.ofFn fun i ↦ g (f i)).foldl (· * ·) (g x) := by
  rw [← Function.comp_def, ← List.map_ofFn, List.foldl_map,
    List.foldl_hom g fun x y ↦ (map_mul g x y).symm]

end List
