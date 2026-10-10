/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTime.Nat
public import TauCeti.GroupTheory.Perm.WordsAndCycles
public import Mathlib.Data.List.Find
public import Mathlib.Data.List.FinRange

/-!
# Uniform polynomial-time permutation tables

The degree is a unary input to these machines. All tables are ordinary lists of
unary naturals; the alphabet and finite control do not depend on the degree.
Clipping makes every intermediate table bounded even on invalid inputs.
On permutation tables clipping is inert.
-/

@[expose] public section

namespace TauCeti.PermutationTables

open Equiv Computability BitEncoding Turing

/-- A permutation represented by its list of point images. -/
abbrev Table := List ℕ
/-- A generator-index word with a Boolean inverse flag on each letter. -/
abbrev Word := List (ℕ × Bool)

/-- A forward-image table in increasing point order. -/
def ofPerm {n : ℕ} (g : Perm (Fin n)) : Table := List.ofFn fun x => (g x).val

/-- Total table access, clipped to the point set. -/
def lookup (n : ℕ) (t : Table) (x : ℕ) : ℕ := min (n - 1) (t[x]?.getD 0)

/-- Multiply tables, with the right factor acting first. -/
def mul (n : ℕ) (t u : Table) : Table :=
  (List.range n).map fun x => lookup n t (lookup n u x)

/-- Compute an inverse by a bounded search over points. -/
def inv (n : ℕ) (t : Table) : Table :=
  (List.range n).map fun x =>
    ((List.range n).find? fun y => decide (lookup n t y = x)).getD 0

/-- Interpret one signed generator index. -/
def letter (n : ℕ) (gs : List Table) (l : ℕ × Bool) : Table :=
  bif l.2 then inv n (gs[l.1]?.getD []) else gs[l.1]?.getD []

/-- Evaluate a word by the specified left fold. -/
def word (n : ℕ) (gs : List Table) (w : Word) : Table :=
  w.foldl (fun t l => mul n t (letter n gs l)) (List.range n)

@[fun_prop] theorem polyTime_lookup :
    PolyTime (fun p : ℕ × Table × ℕ => lookup p.1 p.2.1 p.2.2) := by
  unfold lookup
  fun_prop

@[fun_prop] theorem polyTime_mul :
    PolyTime (fun p : ℕ × Table × Table => mul p.1 p.2.1 p.2.2) := by
  unfold mul
  fun_prop

@[fun_prop] theorem polyTime_inv :
    PolyTime (fun p : ℕ × Table => inv p.1 p.2) := by
  unfold inv
  fun_prop

@[fun_prop] theorem polyTime_letter :
    PolyTime (fun p : (ℕ × List Table) × (ℕ × Bool) => letter p.1.1 p.1.2 p.2) := by
  unfold letter
  fun_prop

theorem lookup_le (n : ℕ) (t : Table) (x : ℕ) : lookup n t x ≤ n :=
  (Nat.min_le_left _ _).trans (Nat.sub_le _ _)

theorem length_mul (n : ℕ) (t u : Table) : (mul n t u).length = n := by
  simp [mul]

theorem mul_entry_le (n : ℕ) (t u : Table) :
    ∀ x ∈ mul n t u, x ≤ n := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact lookup_le ..

theorem length_enc_table_le {t : Table} {n : ℕ}
    (hl : t.length ≤ n) (he : ∀ x ∈ t, x ≤ n) :
    (enc t).length ≤ (n + 2) ^ 3 := by
  have h := length_enc_list_le t (B := n)
    (fun x hx => by simpa only [length_enc_nat] using he x hx)
  have hm := Nat.mul_le_mul_right (2 * n + 2) hl
  simp only [pow_succ, pow_zero]
  nlinarith

@[fun_prop] theorem polyTime_word :
    PolyTime (fun p : (ℕ × List Table) × Word => word p.1.1 p.1.2 p.2) := by
  have hl : PolyTime (fun p : (ℕ × List Table) × Table × (ℕ × Bool) =>
      letter p.1.1 p.1.2 p.2.2) :=
    PolyTime.comp (f := fun p : (ℕ × List Table) × Table × (ℕ × Bool) =>
      (p.1, p.2.2)) polyTime_letter (by fun_prop)
  have hs : PolyTime (fun p : (ℕ × List Table) × Table × (ℕ × Bool) =>
      mul p.1.1 p.2.1 (letter p.1.1 p.1.2 p.2.2)) :=
    PolyTime.comp (f := fun p : (ℕ × List Table) × Table × (ℕ × Bool) =>
      (p.1.1, p.2.1, letter p.1.1 p.1.2 p.2.2)) polyTime_mul
      (PolyTime.pair (by fun_prop) (PolyTime.pair (by fun_prop) hl))
  have hf := PolyTime.foldl
    (g := fun p : ℕ × List Table => fun t l => mul p.1 t (letter p.1 p.2 l))
    hs 3 fun p t l => by
      have h := length_enc_table_le (le_of_eq (length_mul p.1 t (letter p.1 p.2 l)))
        (mul_entry_le p.1 t (letter p.1 p.2 l))
      have hn : p.1 ≤ (enc p).length := by rw [length_enc_prod, length_enc_nat]; omega
      have hh := Nat.pow_le_pow_left (by omega : p.1 + 2 ≤ (enc p).length + 2) 3
      omega
  have hw : PolyTime (fun p : (ℕ × List Table) × Word =>
      (p.1, List.range p.1.1, p.2)) := by fun_prop
  exact PolyTime.comp hf hw

@[simp] theorem length_ofPerm {n : ℕ} (g : Perm (Fin n)) : (ofPerm g).length = n := by
  simp [ofPerm]

theorem lookup_ofPerm {n : ℕ} (g : Perm (Fin n)) (x : Fin n) :
    lookup n (ofPerm g) x.val = (g x).val := by
  simp [lookup, ofPerm, x.isLt, Nat.min_eq_right
    (show (g x).val ≤ n - 1 from by have := (g x).isLt; omega)]

theorem lookup_ofFn {n : ℕ} (f : Fin n → Fin n) (x : Fin n) :
    lookup n (List.ofFn fun y => (f y).val) x.val = (f x).val := by
  simp [lookup, x.isLt, Nat.min_eq_right
    (show (f x).val ≤ n - 1 from by have := (f x).isLt; omega)]

theorem range_eq_ofFn (n : ℕ) :
    List.range n = List.ofFn (fun x : Fin n => x.val) := by
  rw [List.ofFn_eq_map, List.map_coe_finRange_eq_range]

theorem mul_ofPerm {n : ℕ} (g h : Perm (Fin n)) :
    mul n (ofPerm g) (ofPerm h) = ofPerm (g * h) := by
  rw [mul, range_eq_ofFn, List.map_ofFn]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [lookup_ofPerm, lookup_ofPerm]
  rfl

theorem find_inverse {n : ℕ} (g : Perm (Fin n)) (x : Fin n) :
    ((List.range n).find? fun y => decide (lookup n (ofPerm g) y = x.val)) =
      some (g⁻¹ x).val := by
  rw [range_eq_ofFn, List.find?_ofFn_eq_some_of_injective Fin.val_injective]
  constructor
  · simp [lookup_ofPerm]
  · intro y hy he
    have h : g y = x := Fin.ext (by simpa [lookup_ofPerm] using he)
    have : y = g⁻¹ x := g.injective (h.trans (g.apply_symm_apply x).symm)
    subst y
    exact (lt_irrefl _ hy)

theorem inv_ofPerm {n : ℕ} (g : Perm (Fin n)) : inv n (ofPerm g) = ofPerm g⁻¹ := by
  rw [inv, range_eq_ofFn, List.map_ofFn]
  congr 1
  funext x
  simp only [Function.comp_apply, ← range_eq_ofFn]
  rw [find_inverse]
  rfl

/-- Erase only the proofs attached to signed indices. -/
def eraseWord {size : ℕ} (w : FinitePermutation.Word size) : Word :=
  w.map fun l => (l.1.val, l.2)

theorem letter_ofPerm {n : ℕ} (gs : List (Perm (Fin n))) (l : Fin gs.length × Bool) :
    letter n (gs.map ofPerm) (l.1.val, l.2) = ofPerm (FinitePermutation.letterValue gs l) := by
  cases l with
  | mk i b =>
    cases b <;> simp [letter, FinitePermutation.letterValue, inv_ofPerm]

theorem word_ofPerm {n : ℕ} (gs : List (Perm (Fin n))) (w : FinitePermutation.Word gs.length) :
    word n (gs.map ofPerm) (eraseWord w) = ofPerm (FinitePermutation.wordValue gs w) := by
  have h : ∀ (w : FinitePermutation.Word gs.length) (g : Perm (Fin n)),
      (eraseWord w).foldl (fun t l => mul n t (letter n (gs.map ofPerm) l)) (ofPerm g) =
        ofPerm (w.foldl (fun g l => g * FinitePermutation.letterValue gs l) g) := by
    intro w
    induction w with
    | nil => intro; rfl
    | cons l w ih =>
      intro g
      simp only [eraseWord, List.map_cons, List.foldl_cons]
      rw [letter_ofPerm, mul_ofPerm]
      exact ih _
  have hunit : ofPerm (1 : Perm (Fin n)) = List.range n := by
    simp [ofPerm, range_eq_ofFn]
  rw [word, ← hunit, h, FinitePermutation.wordValue_foldl]

end TauCeti.PermutationTables
