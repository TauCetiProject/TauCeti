/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Associativity
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# Horizontal tensor product of Temperley–Lieb diagrams

Two Temperley–Lieb diagrams `f : n₁ → m₁` and `g : n₂ → m₂` are tensored horizontally by placing
`g` to the right of `f`, yielding `TauCeti.TLDiagram.tensor f g : TLDiagram (n₁ + n₂) (m₁ + m₂)`.
In the counterclockwise boundary numbering (`0, …, n - 1` along the bottom from left to right and
`n, …, n + m - 1` along the top from right to left), placing `g` to the right of `f` inserts the
entire boundary of `g` as a contiguous interval `[n₁, n₁ + n₂ + m₂)` between the bottom and top
boundaries of `f`, shifting the top points of `f` by `n₂ + m₂`. On matchings this is the insertion
operation `TauCeti.PlanarMatching.insert`; on circles it adds the circle counts.

The interchange law `TauCeti.TLDiagram.tensor_comp` says that horizontal tensoring commutes with
vertical gluing:
`(f₁.tensor g₁).comp (f₂.tensor g₂) = (f₁.comp f₂).tensor (g₁.comp g₂)`.
In the juxtaposition of `f₁ ⊗ g₁` and `f₂ ⊗ g₂`, the `m₁` glued pairs of `f₁` and `f₂` lie
strictly between the inserted blocks `g₁` and `g₂`; contracting them first leaves `f₁ ≫ f₂` and
brings `g₁` and `g₂` together into a single contiguous block, after which the remaining `m₂`
contractions glue `g₁` and `g₂` inside that block without disturbing `f₁ ≫ f₂`.

## Main definitions

* `TauCeti.PlanarMatching.insert`: inserting a planar matching as a contiguous block inside another.
* `TauCeti.TLDiagram.cast`: transporting a diagram along equalities of its bottom and top sizes.
* `TauCeti.TLDiagram.tensor`: horizontal juxtaposition of Temperley–Lieb diagrams.

## Main results

* `TauCeti.TLDiagram.tensor_id_id`: tensoring identity diagrams gives an identity diagram.
* `TauCeti.TLDiagram.tensor_comp`: the interchange law between tensoring and composition.
* `TauCeti.TLDiagram.tensor_assoc`: associativity of horizontal tensoring up to `cast`.
* `TauCeti.TLDiagram.mk_nested_zero_tensor`, `TauCeti.TLDiagram.tensor_mk_nested_zero`: tensoring
  with empty diagrams adds their circle counts on either side, giving left and right unit laws
  `TauCeti.TLDiagram.id_zero_tensor` and `TauCeti.TLDiagram.tensor_id_zero`.

## Implementation notes

As in `TauCeti.Combinatorics.PlanarMatching.Associativity`, the interchange and associativity
proofs work on the `ℕ → ℕ` partner functions `pv` and the contraction recursion `glueFn` /
`glueCircles`, using `import all` on `Glue` and `Associativity`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open Equiv

namespace TauCeti

namespace PlanarMatching

/-! ### Inserting a planar matching into another -/

section Insert

variable {k l : ℕ}

/-- The bijection `Fin k ⊕ Fin l ≃ Fin (k + l)` inserting `Fin l` as the contiguous block
`[c, c + l)` inside `Fin k`. -/
private def insertEquiv (c : ℕ) (hc : c ≤ k) (l : ℕ) : Fin k ⊕ Fin l ≃ Fin (k + l) where
  toFun
    | .inl i => if (i : ℕ) < c then ⟨i, by omega⟩ else ⟨i + l, by omega⟩
    | .inr j => ⟨c + j, by omega⟩
  invFun a :=
    if h₁ : (a : ℕ) < c then .inl ⟨a, by omega⟩
    else if h₂ : (a : ℕ) < c + l then .inr ⟨a - c, by omega⟩
    else .inl ⟨a - l, by omega⟩
  left_inv
    | .inl i => by
      dsimp only
      by_cases h : (i : ℕ) < c
      · rw [ite_eq_left h, dite_eq_left h]
      · rw [ite_eq_right h, dite_eq_right (by dsimp only; omega),
          dite_eq_right (by dsimp only; omega)]
        congr 1; exact Fin.ext (by dsimp only; omega)
    | .inr j => by
      dsimp only
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1; exact Fin.ext (by dsimp only; omega)
  right_inv a := by
    dsimp only
    by_cases h₁ : (a : ℕ) < c
    · rw [dite_eq_left h₁]; dsimp only; rw [ite_eq_left h₁]
    by_cases h₂ : (a : ℕ) < c + l
    · rw [dite_eq_right h₁, dite_eq_left h₂]; exact Fin.ext (by dsimp only; omega)
    · rw [dite_eq_right h₁, dite_eq_right h₂]; dsimp only
      rw [ite_eq_right (by omega)]
      exact Fin.ext (by dsimp only; omega)

private theorem insertEquiv_inl_lt {c : ℕ} {hc : c ≤ k} (i : Fin k) (hi : (i : ℕ) < c) :
    (insertEquiv c hc l (.inl i) : ℕ) = i := by
  simp [insertEquiv, hi]

private theorem insertEquiv_inl_ge {c : ℕ} {hc : c ≤ k} (i : Fin k) (hi : c ≤ (i : ℕ)) :
    (insertEquiv c hc l (.inl i) : ℕ) = i + l := by
  simp [insertEquiv, Nat.not_lt.mpr hi]

private theorem insertEquiv_inr {c : ℕ} {hc : c ≤ k} (j : Fin l) :
    (insertEquiv c hc l (.inr j) : ℕ) = c + j := (rfl)

private theorem insertEquiv_inl_lt_inl_iff {c : ℕ} {hc : c ≤ k} (i₁ i₂ : Fin k) :
    insertEquiv c hc l (.inl i₁) < insertEquiv c hc l (.inl i₂) ↔ i₁ < i₂ := by
  simp only [Fin.lt_def, insertEquiv, Equiv.coe_fn_mk]
  split_ifs <;> dsimp only <;> omega

private theorem insertEquiv_inr_lt_inr_iff {c : ℕ} {hc : c ≤ k} (j₁ j₂ : Fin l) :
    insertEquiv c hc l (.inr j₁) < insertEquiv c hc l (.inr j₂) ↔ j₁ < j₂ := by
  simp only [Fin.lt_def, insertEquiv_inr]
  omega

/-- The involution obtained by inserting the arcs of `y` at position `c` inside `x`. -/
private def insertPerm (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l) :
    Perm (Fin (k + l)) :=
  (insertEquiv c hc l).permCongr (x.1.val.sumCongr y.1.val)

private theorem insertPerm_inl (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l)
    (i : Fin k) :
    insertPerm c hc x y (insertEquiv c hc l (.inl i)) = insertEquiv c hc l (.inl (x.1.val i)) := by
  simp [insertPerm]

private theorem insertPerm_inr (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l)
    (j : Fin l) :
    insertPerm c hc x y (insertEquiv c hc l (.inr j)) = insertEquiv c hc l (.inr (y.1.val j)) := by
  simp [insertPerm]

private theorem isPerfectMatching_insertPerm (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) : IsPerfectMatching (insertPerm c hc x y) := by
  refine isPerfectMatching_iff.mpr ⟨fun a => ?_, fun a => ?_⟩
  · obtain ⟨s, rfl⟩ := (insertEquiv c hc l).surjective a
    cases s with
    | inl i => rw [insertPerm_inl, insertPerm_inl, x.1.apply_apply]
    | inr j => rw [insertPerm_inr, insertPerm_inr, y.1.apply_apply]
  · obtain ⟨s, rfl⟩ := (insertEquiv c hc l).surjective a
    cases s with
    | inl i =>
      rw [insertPerm_inl]
      intro h
      exact x.1.apply_ne i (Sum.inl.inj ((insertEquiv c hc l).injective h))
    | inr j =>
      rw [insertPerm_inr]
      intro h
      exact y.1.apply_ne j (Sum.inr.inj ((insertEquiv c hc l).injective h))

private theorem isNoncrossingMatching_insertPerm (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) : (insertPerm c hc x y).IsNoncrossingMatching := by
  rw [Equiv.Perm.isNoncrossingMatching_iff]
  intro a b hab hb hlt
  obtain ⟨sa, rfl⟩ := (insertEquiv c hc l).surjective a
  obtain ⟨sb, rfl⟩ := (insertEquiv c hc l).surjective b
  cases sa with
  | inl i =>
    cases sb with
    | inl i' =>
      rw [insertPerm_inl] at hb
      rw [insertPerm_inl, insertPerm_inl] at hlt
      rw [insertEquiv_inl_lt_inl_iff] at hab hb hlt
      exact Equiv.Perm.isNoncrossingMatching_iff.mp x.2 hab hb hlt
    | inr j' =>
      rw [insertPerm_inl] at hb
      rw [insertPerm_inl, insertPerm_inr] at hlt
      simp only [Fin.lt_def, insertEquiv, Equiv.coe_fn_mk] at hab hb hlt
      split_ifs at hab hb hlt <;> dsimp only at hab hb hlt <;> omega
  | inr j =>
    cases sb with
    | inl i' =>
      rw [insertPerm_inr] at hb
      rw [insertPerm_inr, insertPerm_inl] at hlt
      simp only [Fin.lt_def, insertEquiv, Equiv.coe_fn_mk] at hab hb hlt
      split_ifs at hab hb hlt <;> dsimp only at hab hb hlt <;> omega
    | inr j' =>
      rw [insertPerm_inr] at hb
      rw [insertPerm_inr, insertPerm_inr] at hlt
      rw [insertEquiv_inr_lt_inr_iff] at hab hb hlt
      exact Equiv.Perm.isNoncrossingMatching_iff.mp y.2 hab hb hlt

/-- **Insertion** of planar matchings: `insert c hc x y` places the arcs of `y` on the contiguous
block `c, …, c + l - 1`, and keeps the arcs of `x` on the remaining points `0, …, c - 1` and
`c + l, …, k + l - 1`. -/
def insert (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l) :
    PlanarMatching (k + l) :=
  ⟨⟨insertPerm c hc x y, isPerfectMatching_insertPerm c hc x y⟩,
    isNoncrossingMatching_insertPerm c hc x y⟩

/-- On the inserted block `c, …, c + l - 1`, `insert c hc x y` acts as `y`, shifted by `c`. -/
theorem insert_val_block (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l)
    (j : Fin l) :
    (insert c hc x y).1.val ⟨c + j, by omega⟩ = ⟨c + y.1.val j, by omega⟩ :=
  insertPerm_inr c hc x y j

/-- On a point before the insertion position `c`, `insert c hc x y` keeps the partner in `x`,
shifting it up by `l` if it lies at or past `c`. -/
theorem coe_insert_val_of_lt (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l)
    {q : ℕ} (hq : q < c) :
    ((insert c hc x y).1.val ⟨q, by omega⟩ : ℕ) =
      if (x.1.val ⟨q, by omega⟩ : ℕ) < c then (x.1.val ⟨q, by omega⟩ : ℕ)
      else (x.1.val ⟨q, by omega⟩ : ℕ) + l := by
  have harg : (⟨q, by omega⟩ : Fin (k + l)) = insertEquiv c hc l (.inl ⟨q, by omega⟩) :=
    Fin.ext (by rw [insertEquiv_inl_lt ⟨q, by omega⟩ hq])
  -- Expose the underlying `insertPerm` definition to rewrite with `insertPerm_inl`.
  change (insertPerm c hc x y ⟨q, by omega⟩ : ℕ) = _
  rw [harg, insertPerm_inl]
  split_ifs with h
  · exact insertEquiv_inl_lt _ h
  · exact insertEquiv_inl_ge _ (Nat.le_of_not_lt h)

/-- On a point inside the inserted block `[c, c + l)`, `insert c hc x y` shifts the partner in `y`
by `c`. -/
theorem coe_insert_val_of_le_of_lt (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) {q : ℕ} (h₁ : c ≤ q) (h₂ : q < c + l) :
    ((insert c hc x y).1.val ⟨q, by omega⟩ : ℕ) = c + (y.1.val ⟨q - c, by omega⟩ : ℕ) := by
  have harg : (⟨q, by omega⟩ : Fin (k + l)) = ⟨c + (⟨q - c, by omega⟩ : Fin l), by omega⟩ :=
    Fin.ext (by dsimp only; omega)
  rw [harg, insert_val_block]

/-- On a point past the inserted block, `insert c hc x y` shifts the point down by `l`, takes its
partner in `x`, and shifts it back up by `l` if it lies at or past `c`. -/
theorem coe_insert_val_of_le (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching l)
    {q : ℕ} (h₁ : c + l ≤ q) (h₂ : q < k + l) :
    ((insert c hc x y).1.val ⟨q, by omega⟩ : ℕ) =
      if (x.1.val ⟨q - l, by omega⟩ : ℕ) < c then (x.1.val ⟨q - l, by omega⟩ : ℕ)
      else (x.1.val ⟨q - l, by omega⟩ : ℕ) + l := by
  have harg : (⟨q, by omega⟩ : Fin (k + l)) = insertEquiv c hc l (.inl ⟨q - l, by omega⟩) :=
    Fin.ext (by rw [insertEquiv_inl_ge ⟨q - l, by omega⟩ (by dsimp only; omega)]; dsimp only; omega)
  -- Expose the underlying `insertPerm` definition to rewrite with `insertPerm_inl`.
  change (insertPerm c hc x y ⟨q, by omega⟩ : ℕ) = _
  rw [harg, insertPerm_inl]
  split_ifs with h
  · exact insertEquiv_inl_lt _ h
  · exact insertEquiv_inl_ge _ (Nat.le_of_not_lt h)

/-- Inserting `y` at the very end of `x` is the juxtaposition `x.append y`. -/
theorem insert_self_eq_append (x : PlanarMatching k) (y : PlanarMatching l) :
    insert k le_rfl x y = x.append y := by
  refine ext_pv fun q hq => ?_
  rw [pv_of_lt _ hq]
  by_cases h₁ : q < k
  · rw [coe_insert_val_of_lt _ _ _ _ h₁, ite_eq_left (x.1.val ⟨q, h₁⟩).isLt, pv_append_left _ _ h₁,
      pv_of_lt _ h₁]
  · rw [coe_insert_val_of_le_of_lt _ _ _ _ (by omega) (by omega),
      pv_append_right _ _ (by omega) hq, pv_of_lt _ (by omega)]

/-- Inserting `y` at the start of `x` is the juxtaposition `y.append x`, cast to `k + l`. -/
theorem insert_zero_eq_append (x : PlanarMatching k) (y : PlanarMatching l) :
    insert 0 (Nat.zero_le k) x y = cast (Nat.add_comm l k) (y.append x) := by
  refine ext_pv fun q hq => ?_
  rw [pv_of_lt _ hq, pv_cast]
  by_cases h₁ : q < l
  · rw [coe_insert_val_of_le_of_lt _ _ _ _ (Nat.zero_le q) (by omega), Nat.zero_add,
      pv_append_left _ _ h₁, pv_of_lt _ h₁]
    congr 2
  · rw [coe_insert_val_of_le _ _ _ _ (by omega) hq, ite_eq_right (Nat.not_lt_zero _),
      pv_append_right _ _ (by omega) (by omega), pv_of_lt _ (by omega), Nat.add_comm]

/-- Inserting an empty matching leaves `x` unchanged. -/
@[simp]
theorem insert_zero_right (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k) (y : PlanarMatching 0) :
    insert c hc x y = x := by
  refine ext_pv fun q hq => ?_
  rw [pv_of_lt _ hq, pv_of_lt _ hq]
  by_cases h₁ : q < c
  · rw [coe_insert_val_of_lt _ _ _ _ h₁]; split_ifs <;> omega
  · rw [coe_insert_val_of_le _ _ _ _ (by omega) (by omega)]
    simp only [Nat.sub_zero, Nat.add_zero, ite_self]

/-- Inserting `y` into an empty matching returns `y`, cast along `0 + l = l`. -/
@[simp]
theorem insert_zero_left (x : PlanarMatching 0) (y : PlanarMatching l) :
    insert 0 le_rfl x y = cast (Nat.zero_add l).symm y := by
  refine ext_pv fun q hq => ?_
  rw [pv_of_lt _ hq, pv_cast, pv_of_lt _ (by omega),
    coe_insert_val_of_le_of_lt _ _ _ _ (Nat.zero_le q) (by omega), Nat.zero_add]
  congr 2

/-- Inserting the nested matching on `2m` points into the middle of the nested matching on `2n`
points yields the nested matching on `2(n + m)` points. -/
theorem insert_nested_nested (n m : ℕ) :
    insert n (Nat.le_add_right n n) (nested n) (nested m) =
      cast (by omega) (nested (n + m)) := by
  refine ext_pv fun q hq => ?_
  rw [pv_of_lt _ hq, pv_cast, pv_nested _ (by omega)]
  by_cases h₁ : q < n
  · rw [coe_insert_val_of_lt _ _ _ _ h₁]
    simp only [nested_val, Fin.revPerm_apply, Fin.val_rev]
    split_ifs <;> omega
  by_cases h₂ : q < n + (m + m)
  · rw [coe_insert_val_of_le_of_lt _ _ _ _ (by omega) h₂]
    simp only [nested_val, Fin.revPerm_apply, Fin.val_rev]
    omega
  · rw [coe_insert_val_of_le _ _ _ _ (by omega) hq]
    simp only [nested_val, Fin.revPerm_apply, Fin.val_rev]
    split_ifs <;> omega

end Insert

/-! ### Partner-function arithmetic for insertion and contractions -/

section PartnerOps

/-- Shifting a boundary point of an outer matching past an inserted block of length `l` at `c`. -/
private def shiftIns (c l q : ℕ) : ℕ :=
  if q < c then q else q + l

/-- Inserting a partner function `ψ` of size `l` at position `c ≤ k` inside `φ` of size `k`. -/
private def insertFn (c k l : ℕ) (φ ψ : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < c then shiftIns c l (φ q)
  else if q < c + l then c + ψ (q - c)
  else if q < k + l then shiftIns c l (φ (q - l))
  else q

private theorem insertFn_of_lt {c k l q : ℕ} (φ ψ : ℕ → ℕ) (h : q < c) :
    insertFn c k l φ ψ q = shiftIns c l (φ q) := by
  simp [insertFn, h]

private theorem insertFn_of_le_of_lt {c k l q : ℕ} (φ ψ : ℕ → ℕ) (h₁ : c ≤ q) (h₂ : q < c + l) :
    insertFn c k l φ ψ q = c + ψ (q - c) := by
  simp [insertFn, Nat.not_lt.mpr h₁, h₂]

private theorem insertFn_of_le_of_lt' {c k l q : ℕ} (φ ψ : ℕ → ℕ) (h₁ : c + l ≤ q)
    (h₂ : q < k + l) :
    insertFn c k l φ ψ q = shiftIns c l (φ (q - l)) := by
  simp [insertFn, show ¬q < c by omega, Nat.not_lt.mpr h₁, h₂]

private theorem insertFn_of_ge {c k l q : ℕ} (hc : c ≤ k) (φ ψ : ℕ → ℕ) (h : k + l ≤ q) :
    insertFn c k l φ ψ q = q := by
  simp [insertFn, show ¬q < c by omega, show ¬q < c + l by omega, Nat.not_lt.mpr h]

private theorem pv_insert_eq {k l : ℕ} (c : ℕ) (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) :
    pv (insert c hc x y) = insertFn c k l (pv x) (pv y) := by
  funext q
  by_cases h₁ : q < c
  · rw [insertFn_of_lt _ _ h₁, pv_of_lt _ (by omega), coe_insert_val_of_lt _ _ _ _ h₁,
      pv_of_lt _ (by omega), shiftIns]
  by_cases h₂ : q < c + l
  · rw [insertFn_of_le_of_lt _ _ (by omega) h₂, pv_of_lt _ (by omega),
      coe_insert_val_of_le_of_lt _ _ _ _ (by omega) h₂, pv_of_lt _ (by omega)]
  by_cases h₃ : q < k + l
  · rw [insertFn_of_le_of_lt' _ _ (by omega) h₃, pv_of_lt _ h₃,
      coe_insert_val_of_le _ _ _ _ (by omega) h₃, pv_of_lt _ (by omega), shiftIns]
  · rw [insertFn_of_ge hc _ _ (by omega), pv_of_le _ (by omega)]

/-- Splitting a block of `j₁ + j₂` nested contractions into its inner `j₂` contractions followed by
its outer `j₁` contractions. -/
private theorem glueFn_add (n j₁ j₂ : ℕ) (φ : ℕ → ℕ) :
    glueFn n (j₁ + j₂) φ = glueFn n j₁ (glueFn (n + j₁) j₂ φ) := by
  induction j₂ generalizing φ with
  | zero => rfl
  | succ j₂ ih =>
    rw [← Nat.add_assoc, glueFn, glueFn, Nat.add_assoc, ih]

/-- Splitting the circle count of `j₁ + j₂` nested contractions into the inner `j₂` and outer `j₁`
contractions. -/
private theorem glueCircles_add (n j₁ j₂ : ℕ) (φ : ℕ → ℕ) :
    glueCircles n (j₁ + j₂) φ =
      glueCircles n j₁ (glueFn (n + j₁) j₂ φ) + glueCircles (n + j₁) j₂ φ := by
  induction j₂ generalizing φ with
  | zero => simp [glueFn, glueCircles]
  | succ j₂ ih =>
    rw [← Nat.add_assoc, glueCircles, glueFn, glueCircles, Nat.add_assoc, ih]
    omega

private theorem shiftIns_unskipN_of_lt {c l a w : ℕ} (ha : a + 1 < c) (hw₁ : w ≠ a)
    (hw₂ : w ≠ a + 1) :
    unskipN a (shiftIns c l w) = shiftIns (c - 2) l (unskipN a w) := by
  simp only [unskipN, shiftIns]
  split_ifs <;> omega

private theorem shiftIns_unskipN_of_ge {c l a w : ℕ} (hca : c ≤ a) (hw₁ : w ≠ a)
    (hw₂ : w ≠ a + 1) :
    unskipN (a + l) (shiftIns c l w) = shiftIns c l (unskipN a w) := by
  simp only [unskipN, shiftIns]
  split_ifs <;> omega

private theorem rejoin_insertFn_of_lt {c k l a w : ℕ} (φ ψ : ℕ → ℕ) (ha : a + 1 < c) :
    rejoin (insertFn c k l φ ψ) a (shiftIns c l w) = shiftIns c l (rejoin φ a w) := by
  have e₁ : insertFn c k l φ ψ a = shiftIns c l (φ a) := insertFn_of_lt _ _ (by omega)
  have e₂ : insertFn c k l φ ψ (a + 1) = shiftIns c l (φ (a + 1)) := insertFn_of_lt _ _ ha
  unfold rejoin
  rw [e₁, e₂]
  by_cases h₁ : w = a
  · subst h₁; simp [shiftIns, show w < c by omega]
  by_cases h₂ : w = a + 1
  · subst h₂; simp [shiftIns, ha]
  · have hne₁ : shiftIns c l w ≠ a := by simp only [shiftIns]; split_ifs <;> omega
    have hne₂ : shiftIns c l w ≠ a + 1 := by simp only [shiftIns]; split_ifs <;> omega
    simp [h₁, h₂, hne₁, hne₂]

private theorem rejoin_insertFn_of_ge {c k l a w : ℕ} (φ ψ : ℕ → ℕ) (hca : c ≤ a)
    (ha : a + 1 < k) :
    rejoin (insertFn c k l φ ψ) (a + l) (shiftIns c l w) = shiftIns c l (rejoin φ a w) := by
  have e₁ : insertFn c k l φ ψ (a + l) = shiftIns c l (φ a) := by
    rw [insertFn_of_le_of_lt' _ _ (by omega) (by omega), Nat.add_sub_cancel]
  have e₂ : insertFn c k l φ ψ (a + l + 1) = shiftIns c l (φ (a + 1)) := by
    rw [insertFn_of_le_of_lt' _ _ (by omega) (by omega), show a + l + 1 - l = a + 1 by omega]
  unfold rejoin
  rw [e₁, e₂]
  by_cases h₁ : w = a
  · subst h₁; simp [shiftIns, Nat.not_lt.mpr hca]
  by_cases h₂ : w = a + 1
  · subst h₂
    simp only [shiftIns, show ¬a + 1 < c by omega, ite_false, show a + 1 ≠ a by omega,
      show a + 1 + l = a + l + 1 by omega, show a + l + 1 ≠ a + l by omega, ite_true]
  · have hne₁ : shiftIns c l w ≠ a + l := by simp only [shiftIns]; split_ifs <;> omega
    have hne₂ : shiftIns c l w ≠ a + l + 1 := by simp only [shiftIns]; split_ifs <;> omega
    simp [h₁, h₂, hne₁, hne₂]

/-- Contracting a pair strictly before an inserted block commutes with insertion. -/
private theorem contractFn_insertFn_left {c k l : ℕ} (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) {a : ℕ} (ha : a + 1 < c) :
    contractFn a (insertFn c k l (pv x) (pv y)) =
      insertFn (c - 2) (k - 2) l (contractFn a (pv x)) (pv y) := by
  funext q
  have hs : skipN a q ≠ a ∧ skipN a q ≠ a + 1 := by simp only [skipN]; split_ifs <;> omega
  simp only [contractFn, erasePair_apply, splice_of_ne _ hs.1 hs.2]
  by_cases h₁ : q < c - 2
  · have hsk : skipN a q < c := by simp only [skipN]; split_ifs <;> omega
    have hne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : a < k))
      (pv_ne x (by omega : a + 1 < k)) hs.1 hs.2
    rw [splice_of_ne _ hs.1 hs.2] at hne
    rw [insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ hsk, erasePair_apply,
      splice_of_ne _ hs.1 hs.2, rejoin_insertFn_of_lt _ _ ha,
      shiftIns_unskipN_of_lt ha hne.1 hne.2]
  by_cases h₂ : q < c - 2 + l
  · have hsk : skipN a q = q + 2 := skipN_of_le (by omega)
    have hsub : q - (c - 2) = q + 2 - c := by omega
    rw [hsk, insertFn_of_le_of_lt _ _ (by omega) h₂,
      insertFn_of_le_of_lt _ _ (by omega) (by omega), hsub,
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega
  by_cases h₃ : q < k - 2 + l
  · have hsk : skipN a q = q + 2 := skipN_of_le (by omega)
    have hsk' : skipN a (q - l) = q + 2 - l := by simp only [skipN]; split_ifs <;> omega
    have hneq : q + 2 - l ≠ a ∧ q + 2 - l ≠ a + 1 := by omega
    have hne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : a < k))
      (pv_ne x (by omega : a + 1 < k)) hneq.1 hneq.2
    rw [splice_of_ne _ hneq.1 hneq.2] at hne
    rw [hsk, insertFn_of_le_of_lt' _ _ (by omega) h₃,
      insertFn_of_le_of_lt' _ _ (by omega) (by omega), erasePair_apply, hsk',
      splice_of_ne _ hneq.1 hneq.2, rejoin_insertFn_of_lt _ _ ha,
      shiftIns_unskipN_of_lt ha hne.1 hne.2]
  · have hsk : skipN a q = q + 2 := skipN_of_le (by omega)
    rw [hsk, insertFn_of_ge hc _ _ (by omega), insertFn_of_ge (by omega) _ _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem circleInd_insertFn_left {c k l : ℕ} (φ ψ : ℕ → ℕ) {a : ℕ} (ha : a + 1 < c) :
    circleInd a (insertFn c k l φ ψ) = circleInd a φ := by
  rw [circleInd, insertFn_of_lt _ _ (by omega), circleInd]
  simp only [shiftIns]
  split_ifs <;> omega

/-- Contracting a pair strictly after an inserted block commutes with insertion. -/
private theorem contractFn_insertFn_right {c k l : ℕ} (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) {a : ℕ} (hca : c ≤ a) (ha : a + 1 < k) :
    contractFn (a + l) (insertFn c k l (pv x) (pv y)) =
      insertFn c (k - 2) l (contractFn a (pv x)) (pv y) := by
  funext q
  have hs : skipN (a + l) q ≠ a + l ∧ skipN (a + l) q ≠ a + l + 1 := by
    simp only [skipN]; split_ifs <;> omega
  simp only [contractFn, erasePair_apply, splice_of_ne _ hs.1 hs.2]
  by_cases h₁ : q < c
  · have hsk : skipN (a + l) q = q := skipN_of_lt (by omega)
    have hsk' : skipN a q = q := skipN_of_lt (by omega)
    have hneq : q ≠ a ∧ q ≠ a + 1 := by omega
    have hne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : a < k))
      (pv_ne x (by omega : a + 1 < k)) hneq.1 hneq.2
    rw [splice_of_ne _ hneq.1 hneq.2] at hne
    rw [hsk, insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ h₁, erasePair_apply, hsk',
      splice_of_ne _ hneq.1 hneq.2, rejoin_insertFn_of_ge _ _ hca ha,
      shiftIns_unskipN_of_ge hca hne.1 hne.2]
  by_cases h₂ : q < c + l
  · have hsk : skipN (a + l) q = q := skipN_of_lt (by omega)
    have hyv := pv_lt y (by omega : q - c < l)
    rw [hsk, insertFn_of_le_of_lt _ _ (by omega) h₂, insertFn_of_le_of_lt _ _ (by omega) h₂,
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
  by_cases h₃ : q < k - 2 + l
  · have hsk : skipN (a + l) q = skipN a (q - l) + l := by
      simp only [skipN]; split_ifs <;> omega
    have hsk_ge : c ≤ skipN a (q - l) := by simp only [skipN]; split_ifs <;> omega
    have hsk_lt : skipN a (q - l) < k := by simp only [skipN]; split_ifs <;> omega
    have hneq : skipN a (q - l) ≠ a ∧ skipN a (q - l) ≠ a + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : a < k))
      (pv_ne x (by omega : a + 1 < k)) hneq.1 hneq.2
    rw [splice_of_ne _ hneq.1 hneq.2] at hne
    rw [hsk, insertFn_of_le_of_lt' _ _ (by omega) h₃,
      insertFn_of_le_of_lt' _ _ (by omega) (by omega), Nat.add_sub_cancel, erasePair_apply,
      splice_of_ne _ hneq.1 hneq.2, rejoin_insertFn_of_ge _ _ hca ha,
      shiftIns_unskipN_of_ge hca hne.1 hne.2]
  · have hsk : skipN (a + l) q = q + 2 := skipN_of_le (by omega)
    rw [hsk, insertFn_of_ge hc _ _ (by omega), insertFn_of_ge (by omega) _ _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem circleInd_insertFn_right {c k l : ℕ} (φ ψ : ℕ → ℕ) {a : ℕ} (hca : c ≤ a)
    (ha : a + 1 < k) :
    circleInd (a + l) (insertFn c k l φ ψ) = circleInd a φ := by
  rw [circleInd, insertFn_of_le_of_lt' _ _ (by omega) (by omega), Nat.add_sub_cancel, circleInd]
  simp only [shiftIns]
  split_ifs <;> omega

private theorem splice_insertFn_inner {c k l : ℕ} (φ : ℕ → ℕ) (y : PlanarMatching l) {a z : ℕ}
    (ha : a + 1 < l) (hz : z < l) :
    splice (c + a) (insertFn c k l φ (pv y)) (c + z) = c + splice a (pv y) z := by
  by_cases hza : z = a
  · rw [splice_of_eq_left _ (by omega), splice_of_eq_left _ hza, Nat.add_assoc]
  by_cases hza' : z = a + 1
  · rw [splice_of_eq_right _ (by omega), splice_of_eq_right _ hza']
  have e₀ : insertFn c k l φ (pv y) (c + z) = c + pv y z := by
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
  have e₁ : insertFn c k l φ (pv y) (c + a) = c + pv y a := by
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
  have e₂ : insertFn c k l φ (pv y) (c + a + 1) = c + pv y (a + 1) := by
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), show c + a + 1 - c = a + 1 by omega]
  rw [splice_of_ne _ (by omega) (by omega), splice_of_ne _ hza hza', e₀]
  unfold rejoin
  rw [e₁, e₂]
  split_ifs <;> omega

/-- Contracting a pair inside an inserted block commutes with insertion. -/
private theorem contractFn_insertFn_inner {c k l : ℕ} (hc : c ≤ k) (x : PlanarMatching k)
    (y : PlanarMatching l) {a : ℕ} (ha : a + 1 < l) :
    contractFn (c + a) (insertFn c k l (pv x) (pv y)) =
      insertFn c k (l - 2) (pv x) (contractFn a (pv y)) := by
  funext q
  simp only [contractFn, erasePair_apply]
  by_cases h₁ : q < c
  · have hsk : skipN (c + a) q = q := skipN_of_lt (by omega)
    rw [hsk, splice_of_ne _ (by omega) (by omega), insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ h₁]
    have hne : shiftIns c l (pv x q) ≠ c + a ∧ shiftIns c l (pv x q) ≠ c + a + 1 := by
      simp only [shiftIns]; split_ifs <;> omega
    rw [rejoin_of_ne _ hne.1 hne.2]
    simp only [shiftIns, unskipN]
    split_ifs <;> omega
  by_cases h₂ : q < c + (l - 2)
  · have hsk : skipN (c + a) q = c + skipN a (q - c) := by
      simp only [skipN]; split_ifs <;> omega
    have hs₁ : skipN a (q - c) < l := by simp only [skipN]; split_ifs <;> omega
    have hs₂ : skipN a (q - c) ≠ a ∧ skipN a (q - c) ≠ a + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hw := splice_ne (pv_pv_eq y) (pv_ne y (by omega : a < l)) (pv_ne y (by omega : a + 1 < l))
      hs₂.1 hs₂.2
    rw [hsk, splice_insertFn_inner _ _ ha hs₁, insertFn_of_le_of_lt _ _ (by omega) h₂,
      erasePair_apply]
    generalize splice a (pv y) (skipN a (q - c)) = w at hw
    simp only [unskipN]
    split_ifs <;> omega
  by_cases h₃ : q < k + (l - 2)
  · have hsk : skipN (c + a) q = q + 2 := skipN_of_le (by omega)
    have hsub : q + 2 - l = q - (l - 2) := by omega
    rw [hsk, splice_of_ne _ (by omega) (by omega), insertFn_of_le_of_lt' _ _ (by omega) h₃,
      insertFn_of_le_of_lt' _ _ (by omega) (by omega), hsub]
    have hne : shiftIns c l (pv x (q - (l - 2))) ≠ c + a ∧
        shiftIns c l (pv x (q - (l - 2))) ≠ c + a + 1 := by
      simp only [shiftIns]; split_ifs <;> omega
    rw [rejoin_of_ne _ hne.1 hne.2]
    simp only [shiftIns, unskipN]
    split_ifs <;> omega
  · have hsk : skipN (c + a) q = q + 2 := skipN_of_le (by omega)
    rw [hsk, splice_of_ne _ (by omega) (by omega), insertFn_of_ge hc _ _ (by omega),
      insertFn_of_ge hc _ _ (by omega), rejoin_of_ne _ (by omega) (by omega),
      unskipN_of_le (by omega)]
    omega

private theorem circleInd_insertFn_inner {c k l : ℕ} (φ ψ : ℕ → ℕ) {a : ℕ} (ha : a + 1 < l) :
    circleInd (c + a) (insertFn c k l φ ψ) = circleInd a ψ := by
  rw [circleInd, insertFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left,
    circleInd]
  simp only [Nat.add_assoc, Nat.add_left_cancel_iff]

private theorem glueFn_insertFn_left {n l : ℕ} (y : PlanarMatching l) :
    ∀ (m c K : ℕ) (x : PlanarMatching K), n + 2 * m ≤ c → c ≤ K →
      glueFn n m (insertFn c K l (pv x) (pv y)) =
        insertFn (c - 2 * m) (K - 2 * m) l (glueFn n m (pv x)) (pv y) ∧
      glueCircles n m (insertFn c K l (pv x) (pv y)) = glueCircles n m (pv x)
  | 0, c, K, x, _, _ => ⟨rfl, rfl⟩
  | m + 1, c, K, x, hnc, hcK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insertFn_left (n := n) y m (c - 2) (K - 2) x' (by omega) (by omega)
    have hc' : c - 2 - 2 * m = c - 2 * (m + 1) := by omega
    have hK' : K - 2 - 2 * m = K - 2 * (m + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [contractFn_insertFn_left hcK x y (by omega), ← hx', ih₁, ih₂,
      circleInd_insertFn_left _ _ (by omega), hc', hK']
    exact ⟨rfl, rfl⟩

private theorem glueFn_insertFn_right {c l : ℕ} (y : PlanarMatching l) :
    ∀ (m n K : ℕ) (x : PlanarMatching K), c ≤ n → n + 2 * m ≤ K →
      glueFn (n + l) m (insertFn c K l (pv x) (pv y)) =
        insertFn c (K - 2 * m) l (glueFn n m (pv x)) (pv y) ∧
      glueCircles (n + l) m (insertFn c K l (pv x) (pv y)) = glueCircles n m (pv x)
  | 0, n, K, x, _, _ => ⟨rfl, rfl⟩
  | m + 1, n, K, x, hcn, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insertFn_right (c := c) y m n (K - 2) x' hcn (by omega)
    have hK' : K - 2 - 2 * m = K - 2 * (m + 1) := by omega
    have ha : n + l + m = n + m + l := by omega
    simp only [glueFn, glueCircles]
    rw [ha, contractFn_insertFn_right (by omega) x y (by omega) (by omega), ← hx', ih₁, ih₂,
      circleInd_insertFn_right _ _ (by omega) (by omega), hK']
    exact ⟨rfl, rfl⟩

private theorem glueFn_insertFn_inner {c K : ℕ} (hc : c ≤ K) (x : PlanarMatching K) :
    ∀ (m n L : ℕ) (y : PlanarMatching L), n + 2 * m ≤ L →
      glueFn (c + n) m (insertFn c K L (pv x) (pv y)) =
        insertFn c K (L - 2 * m) (pv x) (glueFn n m (pv y)) ∧
      glueCircles (c + n) m (insertFn c K L (pv x) (pv y)) = glueCircles n m (pv y)
  | 0, n, L, y, _ => ⟨rfl, rfl⟩
  | m + 1, n, L, y, hL => by
    obtain ⟨y', hy'⟩ := exists_pv_eq_contractFn y (a := n + m) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insertFn_inner hc x m n (L - 2) y' (by omega)
    have hL' : L - 2 - 2 * m = L - 2 * (m + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [Nat.add_assoc c n m, contractFn_insertFn_inner hc x y (by omega), ← hy', ih₁, ih₂,
      circleInd_insertFn_inner _ _ (by omega), hL']
    exact ⟨rfl, rfl⟩

/-- Juxtaposing two inserted partner functions inserts the first block into the juxtaposed outer
functions and then inserts the second block. -/
private theorem appendFn_insertFn_insertFn {c₁ k₁ l₁ c₂ k₂ l₂ : ℕ} (h₁ : c₁ ≤ k₁) (h₂ : c₂ ≤ k₂)
    {φ₁ φ₂ ψ₁ ψ₂ : ℕ → ℕ} (hφ₁ : ∀ q < k₁, φ₁ q < k₁) (hφ₂ : ∀ q < k₂, φ₂ q < k₂)
    (hψ₁ : ∀ q < l₁, ψ₁ q < l₁) (hψ₂ : ∀ q < l₂, ψ₂ q < l₂) :
    appendFn (k₁ + l₁) (k₂ + l₂) (insertFn c₁ k₁ l₁ φ₁ ψ₁) (insertFn c₂ k₂ l₂ φ₂ ψ₂) =
      insertFn (k₁ + l₁ + c₂) (k₁ + k₂ + l₁) l₂
        (insertFn c₁ (k₁ + k₂) l₁ (appendFn k₁ k₂ φ₁ φ₂) ψ₁) ψ₂ := by
  funext q
  by_cases ha : q < c₁
  · have := hφ₁ q (by omega)
    rw [appendFn_of_lt _ _ (by omega), insertFn_of_lt _ _ ha, insertFn_of_lt _ _ (by omega),
      insertFn_of_lt _ _ ha, appendFn_of_lt _ _ (by omega)]
    simp only [shiftIns]; split_ifs <;> omega
  by_cases hb : q < c₁ + l₁
  · have := hψ₁ (q - c₁) (by omega)
    rw [appendFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) hb,
      insertFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) hb]
    simp only [shiftIns]; split_ifs <;> omega
  by_cases hc : q < k₁ + l₁
  · have := hφ₁ (q - l₁) (by omega)
    rw [appendFn_of_lt _ _ hc, insertFn_of_le_of_lt' _ _ (by omega) hc,
      insertFn_of_lt _ _ (by omega), insertFn_of_le_of_lt' _ _ (by omega) (by omega),
      appendFn_of_lt _ _ (by omega)]
    simp only [shiftIns]; split_ifs <;> omega
  by_cases hd : q < k₁ + l₁ + c₂
  · have := hφ₂ (q - (k₁ + l₁)) (by omega)
    have hsub : q - l₁ - k₁ = q - (k₁ + l₁) := by omega
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega),
      insertFn_of_lt _ _ hd, insertFn_of_le_of_lt' _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    simp only [shiftIns]; split_ifs <;> omega
  by_cases he : q < k₁ + l₁ + c₂ + l₂
  · have := hψ₂ (q - (k₁ + l₁ + c₂)) (by omega)
    have hsub : q - (k₁ + l₁) - c₂ = q - (k₁ + l₁ + c₂) := by omega
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) he, hsub]
    omega
  by_cases hf : q < k₁ + l₁ + (k₂ + l₂)
  · have := hφ₂ (q - (k₁ + l₁) - l₂) (by omega)
    have hsub : q - l₂ - l₁ - k₁ = q - (k₁ + l₁) - l₂ := by omega
    rw [appendFn_of_le_of_lt _ _ (by omega) hf,
      insertFn_of_le_of_lt' _ _ (by omega) (by omega),
      insertFn_of_le_of_lt' _ _ (by omega) (by omega),
      insertFn_of_le_of_lt' _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    simp only [shiftIns]; split_ifs <;> omega
  · rw [appendFn_of_le _ _ (by omega), insertFn_of_ge (by omega) _ _ (by omega)]

/-- Inserting two blocks side by side at `c` and `c + l₁` is the same as inserting their
juxtaposition at `c`. -/
private theorem insertFn_insertFn_adjacent {c k l₁ l₂ : ℕ} (hc : c ≤ k)
    {φ ψ₁ ψ₂ : ℕ → ℕ} (hφ : ∀ q < k, φ q < k) (hψ₁ : ∀ q < l₁, ψ₁ q < l₁)
    (hψ₂ : ∀ q < l₂, ψ₂ q < l₂) :
    insertFn (c + l₁) (k + l₁) l₂ (insertFn c k l₁ φ ψ₁) ψ₂ =
      insertFn c k (l₁ + l₂) φ (appendFn l₁ l₂ ψ₁ ψ₂) := by
  funext q
  by_cases ha : q < c
  · have := hφ q (by omega)
    rw [insertFn_of_lt _ _ (by omega), insertFn_of_lt _ _ ha, insertFn_of_lt _ _ ha]
    simp only [shiftIns]; split_ifs <;> omega
  by_cases hb : q < c + l₁
  · have := hψ₁ (q - c) (by omega)
    rw [insertFn_of_lt _ _ hb, insertFn_of_le_of_lt _ _ (by omega) hb,
      insertFn_of_le_of_lt _ _ (by omega) (by omega), appendFn_of_lt _ _ (by omega)]
    simp only [shiftIns]; split_ifs <;> omega
  by_cases hc' : q < c + l₁ + l₂
  · have := hψ₂ (q - (c + l₁)) (by omega)
    have hsub : q - c - l₁ = q - (c + l₁) := by omega
    rw [insertFn_of_le_of_lt _ _ (by omega) hc',
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    omega
  by_cases hd : q < k + l₁ + l₂
  · have := hφ (q - (l₁ + l₂)) (by omega)
    have hsub : q - l₂ - l₁ = q - (l₁ + l₂) := by omega
    rw [insertFn_of_le_of_lt' _ _ (by omega) hd,
      insertFn_of_le_of_lt' _ _ (by omega) (by omega),
      insertFn_of_le_of_lt' _ _ (by omega) (by omega), hsub]
    simp only [shiftIns]; split_ifs <;> omega
  · rw [insertFn_of_ge (by omega) _ _ (by omega), insertFn_of_ge hc _ _ (by omega)]

end PartnerOps

end PlanarMatching

/-! ### Casting and horizontal tensoring of Temperley–Lieb diagrams -/

namespace TLDiagram

section Cast

variable {n m n' m' n'' m'' : ℕ}

/-- Transport of Temperley–Lieb diagrams along equalities `n = n'` and `m = m'` of the numbers of
bottom and top boundary points. -/
def cast (hn : n = n') (hm : m = m') : TLDiagram n m ≃ TLDiagram n' m' where
  toFun f := ⟨PlanarMatching.cast (congrArg₂ (· + ·) hn hm) f.matching, f.circles⟩
  invFun f := ⟨PlanarMatching.cast (congrArg₂ (· + ·) hn.symm hm.symm) f.matching, f.circles⟩
  left_inv f := by subst hn hm; simp
  right_inv f := by subst hn hm; simp

@[simp]
theorem matching_cast (hn : n = n') (hm : m = m') (f : TLDiagram n m) :
    (cast hn hm f).matching = PlanarMatching.cast (congrArg₂ (· + ·) hn hm) f.matching := (rfl)

@[simp]
theorem circles_cast (hn : n = n') (hm : m = m') (f : TLDiagram n m) :
    (cast hn hm f).circles = f.circles := (rfl)

@[simp]
theorem cast_refl (hn : n = n) (hm : m = m) : cast hn hm = Equiv.refl (TLDiagram n m) := by
  ext f <;> simp

@[simp]
theorem cast_symm (hn : n = n') (hm : m = m') : (cast hn hm).symm = cast hn.symm hm.symm := by
  subst hn hm; simp

@[simp]
theorem cast_cast (hn : n = n') (hm : m = m') (hn' : n' = n'') (hm' : m' = m'')
    (f : TLDiagram n m) :
    cast hn' hm' (cast hn hm f) = cast (hn.trans hn') (hm.trans hm') f := by
  subst hn hm hn' hm'; simp

@[simp]
theorem cast_id (hn : n = n') : cast hn hn (id n) = id n' := by
  subst hn; simp

theorem cast_comp (hn : n = n') (hp : m' = m'') (f : TLDiagram n m) (g : TLDiagram m m') :
    cast hn hp (f.comp g) = (cast hn rfl f).comp (cast rfl hp g) := by
  subst hn hp; simp

theorem comp_cast_mid (hm : m = m') (f : TLDiagram n m) (g : TLDiagram m' n') :
    (cast rfl hm f).comp g = f.comp (cast hm.symm rfl g) := by
  subst hm; simp

theorem cast_verticalReflect (hn : n = n') (hm : m = m') (f : TLDiagram n m) :
    cast hm hn (verticalReflect n m f) = verticalReflect n' m' (cast hn hm f) := by
  subst hn hm; simp

theorem cast_reflect (hn : n = n') (hm : m = m') (f : TLDiagram n m) :
    cast hn hm (reflect n m f) = reflect n' m' (cast hn hm f) := by
  subst hn hm; simp

end Cast

section Tensor

variable {n₁ m₁ n₂ m₂ n₃ m₃ p₁ p₂ : ℕ}

/-- **Horizontal tensor product of Temperley–Lieb diagrams**: `f.tensor g` places `g : n₂ → m₂`
to the right of `f : n₁ → m₁`. In the counterclockwise boundary numbering, the boundary of `g` is
inserted as a contiguous block between the bottom and top boundaries of `f`, and the circle counts
are added. -/
def tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) : TLDiagram (n₁ + n₂) (m₁ + m₂) where
  matching := PlanarMatching.cast (by omega)
    (PlanarMatching.insert n₁ (Nat.le_add_right n₁ m₁) f.matching g.matching)
  circles := f.circles + g.circles

@[simp]
theorem matching_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    (f.tensor g).matching = PlanarMatching.cast (by omega)
      (PlanarMatching.insert n₁ (Nat.le_add_right n₁ m₁) f.matching g.matching) := (rfl)

@[simp]
theorem circles_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    (f.tensor g).circles = f.circles + g.circles := (rfl)

open PlanarMatching in
private theorem pv_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    pv (f.tensor g).matching =
      insertFn n₁ (n₁ + m₁) (n₂ + m₂) (pv f.matching) (pv g.matching) := by
  rw [matching_tensor, pv_cast_eq, pv_insert_eq]

/-- Tensoring two identity diagrams gives the identity diagram on the combined strands. -/
@[simp]
theorem tensor_id_id (n₁ n₂ : ℕ) : (id n₁).tensor (id n₂) = id (n₁ + n₂) := by
  ext : 1
  · simp only [matching_tensor, matching_id, PlanarMatching.insert_nested_nested,
      PlanarMatching.cast_cast, PlanarMatching.cast_refl, Equiv.refl_apply]
  · simp

open PlanarMatching in
/-- **The interchange law** for Temperley–Lieb diagrams: horizontal tensoring commutes with
vertical composition, for both the matchings and the circle counts. -/
theorem tensor_comp (f₁ : TLDiagram n₁ m₁) (g₁ : TLDiagram n₂ m₂)
    (f₂ : TLDiagram m₁ p₁) (g₂ : TLDiagram m₂ p₂) :
    (f₁.tensor g₁).comp (f₂.tensor g₂) = (f₁.comp f₂).tensor (g₁.comp g₂) := by
  have happ := appendFn_insertFn_insertFn (Nat.le_add_right n₁ m₁) (Nat.le_add_right m₁ p₁)
    (fun q hq => pv_lt f₁.matching hq) (fun q hq => pv_lt f₂.matching hq)
    (fun q hq => pv_lt g₁.matching hq) (fun q hq => pv_lt g₂.matching hq)
  set F : PlanarMatching (n₁ + m₁ + (m₁ + p₁)) := f₁.matching.append f₂.matching
  set G : PlanarMatching (n₂ + m₂ + (m₂ + p₂)) := g₁.matching.append g₂.matching
  set Fg₁ : PlanarMatching (n₁ + m₁ + (m₁ + p₁) + (n₂ + m₂)) :=
    insert n₁ (by omega) F g₁.matching
  have hFg₁ : pv Fg₁ = insertFn n₁ (n₁ + m₁ + (m₁ + p₁)) (n₂ + m₂) (pv F) (pv g₁.matching) := by
    rw [pv_insert_eq]
  have hL := glueFn_insertFn_left (n := n₁ + (n₂ + m₂)) g₂.matching m₁
    (n₁ + m₁ + (n₂ + m₂) + m₁) (n₁ + m₁ + (m₁ + p₁) + (n₂ + m₂)) Fg₁ (by omega) (by omega)
  have hR := glueFn_insertFn_right (c := n₁) g₁.matching m₁ n₁ (n₁ + m₁ + (m₁ + p₁)) F
    le_rfl (by omega)
  have hI := glueFn_insertFn_inner (c := n₁) (Nat.le_add_right n₁ p₁) (f₁.comp f₂).matching m₂ n₂
    (n₂ + m₂ + (m₂ + p₂)) G (by omega)
  have hadj := insertFn_insertFn_adjacent (c := n₁) (Nat.le_add_right n₁ p₁)
    (fun q hq => pv_lt (f₁.comp f₂).matching hq)
    (fun q hq => pv_lt g₁.matching hq) (fun q hq => pv_lt g₂.matching hq)
  have hstart : pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching) =
      insertFn (n₁ + m₁ + (n₂ + m₂) + m₁) (n₁ + m₁ + (m₁ + p₁) + (n₂ + m₂)) (m₂ + p₂)
        (pv Fg₁) (pv g₂.matching) := by
    rw [pv_append_eq, pv_tensor, pv_tensor, hFg₁, pv_append_eq]
    have e₁ : n₁ + n₂ + (m₁ + m₂) = n₁ + m₁ + (n₂ + m₂) := by omega
    have e₂ : m₁ + m₂ + (p₁ + p₂) = m₁ + p₁ + (m₂ + p₂) := by omega
    rw [e₁, e₂, happ]
  have hmid_fn : glueFn (n₁ + (n₂ + m₂)) m₁
      (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching)) =
      insertFn n₁ (n₁ + p₁) (n₂ + m₂ + (m₂ + p₂)) (pv (f₁.comp f₂).matching) (pv G) := by
    rw [hstart, hL.1, hFg₁, hR.1]
    have e₁ : n₁ + m₁ + (n₂ + m₂) + m₁ - 2 * m₁ = n₁ + (n₂ + m₂) := by omega
    have e₂ : n₁ + m₁ + (m₁ + p₁) + (n₂ + m₂) - 2 * m₁ = n₁ + p₁ + (n₂ + m₂) := by omega
    have e₃ : n₁ + m₁ + (m₁ + p₁) - 2 * m₁ = n₁ + p₁ := by omega
    rw [e₁, e₂, e₃, ← pv_glueMiddle m₁ F, ← matching_comp, hadj, ← pv_append_eq]
  have hmid_c : glueCircles (n₁ + (n₂ + m₂)) m₁
      (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching)) =
      glueCircles n₁ m₁ (pv F) := by
    rw [hstart, hL.2, hFg₁, hR.2]
  have hsplit_fn : glueFn (n₁ + n₂) (m₁ + m₂)
      (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching)) =
      insertFn n₁ (n₁ + p₁) (n₂ + p₂) (pv (f₁.comp f₂).matching) (pv (g₁.comp g₂).matching) := by
    rw [show glueFn (n₁ + n₂) (m₁ + m₂) = glueFn (n₁ + n₂) (m₂ + m₁) by rw [Nat.add_comm m₁ m₂],
      glueFn_add, show n₁ + n₂ + m₂ = n₁ + (n₂ + m₂) by omega, hmid_fn, hI.1,
      show n₂ + m₂ + (m₂ + p₂) - 2 * m₂ = n₂ + p₂ by omega, ← pv_glueMiddle m₂ G, ← matching_comp]
  have hsplit_c : glueCircles (n₁ + n₂) (m₁ + m₂)
      (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching)) =
      glueCircles n₂ m₂ (pv G) + glueCircles n₁ m₁ (pv F) := by
    rw [show glueCircles (n₁ + n₂) (m₁ + m₂) = glueCircles (n₁ + n₂) (m₂ + m₁) by
        rw [Nat.add_comm m₁ m₂],
      glueCircles_add, show n₁ + n₂ + m₂ = n₁ + (n₂ + m₂) by omega, hmid_fn, hmid_c, hI.2]
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, pv_tensor, hsplit_fn]
  · simp only [circles_comp, circles_tensor, glueMiddleCircles_eq]
    rw [hsplit_c]
    dsimp only [F, G]
    omega

open PlanarMatching in
/-- Horizontal tensoring is associative, up to casting along `Nat.add_assoc`. -/
theorem tensor_assoc (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) (h : TLDiagram n₃ m₃) :
    cast (Nat.add_assoc n₁ n₂ n₃) (Nat.add_assoc m₁ m₂ m₃) ((f.tensor g).tensor h) =
      f.tensor (g.tensor h) := by
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_cast, pv_cast_eq, pv_tensor, pv_tensor, pv_tensor, pv_tensor]
    funext q
    by_cases h₁ : q < n₁
    · have := pv_lt f.matching (by omega : q < n₁ + m₁)
      rw [insertFn_of_lt _ _ (by omega), insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ h₁]
      simp only [shiftIns]; split_ifs <;> omega
    by_cases h₂ : q < n₁ + n₂
    · have := pv_lt g.matching (by omega : q - n₁ < n₂ + m₂)
      rw [insertFn_of_lt _ _ h₂, insertFn_of_le_of_lt _ _ (by omega) (by omega),
        insertFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega)]
      simp only [shiftIns]; split_ifs <;> omega
    by_cases h₃ : q < n₁ + n₂ + (n₃ + m₃)
    · have := pv_lt h.matching (by omega : q - (n₁ + n₂) < n₃ + m₃)
      have hsub : q - n₁ - n₂ = q - (n₁ + n₂) := by omega
      rw [insertFn_of_le_of_lt _ _ (by omega) h₃,
        insertFn_of_le_of_lt _ _ (by omega) (by omega),
        insertFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
      omega
    by_cases h₄ : q < n₁ + n₂ + (n₃ + m₃) + m₂
    · have := pv_lt g.matching (by omega : q - (n₃ + m₃) - n₁ < n₂ + m₂)
      have hsub : q - n₁ - (n₃ + m₃) = q - (n₃ + m₃) - n₁ := by omega
      rw [insertFn_of_le_of_lt' _ _ (by omega) (by omega),
        insertFn_of_le_of_lt _ _ (by omega) (by omega),
        insertFn_of_le_of_lt _ _ (by omega) (by omega),
        insertFn_of_le_of_lt' _ _ (by omega) (by omega), hsub]
      simp only [shiftIns]; split_ifs <;> omega
    by_cases h₅ : q < n₁ + n₂ + (n₃ + m₃) + m₂ + m₁
    · have := pv_lt f.matching (by omega : q - (n₃ + m₃) - (n₂ + m₂) < n₁ + m₁)
      have hsub : q - (n₃ + m₃) - (n₂ + m₂) = q - (n₂ + n₃ + (m₂ + m₃)) := by omega
      rw [insertFn_of_le_of_lt' _ _ (by omega) (by omega),
        insertFn_of_le_of_lt' _ _ (by omega) (by omega),
        insertFn_of_le_of_lt' _ _ (by omega) (by omega), hsub]
      simp only [shiftIns]; split_ifs <;> omega
    · rw [insertFn_of_ge (by omega) _ _ (by omega), insertFn_of_ge (by omega) _ _ (by omega)]
  · simp [Nat.add_assoc]

/-- Tensoring a diagram on the left with `k` closed circles keeps the matching and adds `k`
circles. -/
theorem mk_nested_zero_tensor (k : ℕ) (f : TLDiagram n₁ m₁) :
    cast (Nat.zero_add n₁) (Nat.zero_add m₁)
      ((⟨PlanarMatching.nested 0, k⟩ : TLDiagram 0 0).tensor f) =
      ⟨f.matching, k + f.circles⟩ := by
  ext : 1
  · simp only [matching_cast, matching_tensor, PlanarMatching.insert_zero_left,
      PlanarMatching.cast_cast, PlanarMatching.cast_refl, Equiv.refl_apply]
  · simp

/-- Tensoring a diagram on the right with `k` closed circles keeps the matching and adds `k`
circles. -/
theorem tensor_mk_nested_zero (f : TLDiagram n₁ m₁) (k : ℕ) :
    f.tensor (⟨PlanarMatching.nested 0, k⟩ : TLDiagram 0 0) =
      ⟨f.matching, f.circles + k⟩ := by
  ext : 1
  · simp only [matching_tensor, PlanarMatching.insert_zero_right,
      PlanarMatching.cast_refl, Equiv.refl_apply]
  · simp

/-- The empty identity diagram `id 0` is a left unit for horizontal tensoring. -/
@[simp]
theorem id_zero_tensor (f : TLDiagram n₁ m₁) :
    cast (Nat.zero_add n₁) (Nat.zero_add m₁) ((id 0).tensor f) = f := by
  have h0 : id 0 = ⟨PlanarMatching.nested 0, 0⟩ := TLDiagram.ext (matching_id 0) (circles_id 0)
  rw [h0, mk_nested_zero_tensor]
  exact TLDiagram.ext rfl (Nat.zero_add _)

/-- The empty identity diagram `id 0` is a right unit for horizontal tensoring. -/
@[simp]
theorem tensor_id_zero (f : TLDiagram n₁ m₁) : f.tensor (id 0) = f := by
  have h0 : id 0 = ⟨PlanarMatching.nested 0, 0⟩ := TLDiagram.ext (matching_id 0) (circles_id 0)
  rw [h0, tensor_mk_nested_zero]
  exact TLDiagram.ext rfl (Nat.add_zero _)

/-- Casting commutes with horizontal tensoring. -/
theorem cast_tensor {n₁' m₁' n₂' m₂' : ℕ} (hn₁ : n₁ = n₁') (hm₁ : m₁ = m₁')
    (hn₂ : n₂ = n₂') (hm₂ : m₂ = m₂') (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    cast (congrArg₂ (· + ·) hn₁ hn₂) (congrArg₂ (· + ·) hm₁ hm₂) (f.tensor g) =
      (cast hn₁ hm₁ f).tensor (cast hn₂ hm₂ g) := by
  subst hn₁ hm₁ hn₂ hm₂; simp

end Tensor

end TLDiagram

/-- Horizontal tensoring is noncommutative: `cap ⊗ id 1` (joining bottom points `0` and `1`) is
distinct from `id 1 ⊗ cap` (joining bottom points `1` and `2`). -/
example :
    TLDiagram.cast rfl (Nat.zero_add 1) (TLDiagram.cap.tensor (TLDiagram.id 1)) ≠
      TLDiagram.cast (Nat.add_comm 1 2) (Nat.add_zero 1)
        ((TLDiagram.id 1).tensor TLDiagram.cap) := by
  intro h
  have h0 := congrArg (fun D : TLDiagram 3 1 => PlanarMatching.pv D.matching 0) h
  rw [TLDiagram.matching_cast, TLDiagram.matching_cast, PlanarMatching.pv_cast,
    PlanarMatching.pv_cast, TLDiagram.pv_tensor, TLDiagram.pv_tensor,
    PlanarMatching.insertFn_of_lt _ _ (by omega), PlanarMatching.insertFn_of_lt _ _ (by omega),
    TLDiagram.matching_id, PlanarMatching.pv_nested _ (by omega),
    PlanarMatching.pv_of_lt _ (by omega), TLDiagram.cap_matching_val] at h0
  simp only [PlanarMatching.shiftIns] at h0
  exact absurd h0 (by decide)

end TauCeti
