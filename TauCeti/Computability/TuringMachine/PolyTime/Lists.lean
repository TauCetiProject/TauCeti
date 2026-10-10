/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTime.Iteration

/-!
# Polynomial-time list searches

These machines enumerate only the supplied list or a bounded range of natural numbers.
Their running times include the cost of copying the self-delimiting encodings.
-/

@[expose] public section

namespace Turing.PolyTime

open Computability BitEncoding

variable {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Primcodable γ] [BitEncoding γ]

omit [Primcodable α] [BitEncoding α] in
theorem foldl_append_eq_flatten : ∀ (L : List (List α)) (acc : List α),
    L.foldl (fun acc u => acc ++ u) acc = acc ++ L.flatten
  | [], acc => by simp
  | u :: L, acc => by
    rw [List.foldl_cons, foldl_append_eq_flatten L, List.flatten_cons, List.append_assoc]

@[fun_prop] theorem flatten : PolyTime (List.flatten : List (List α) → List α) := by
  have hF := foldl (g := fun (_ : Unit) (acc u : List α) => acc ++ u)
    (by fun_prop) 0 fun _ acc u => by
      have := length_enc_append acc u
      omega
  have hw : PolyTime (fun L : List (List α) => ((), ([] : List α), L)) := by fun_prop
  exact of_eq (comp hF hw) fun L => by
    rw [foldl_append_eq_flatten, List.nil_append]

omit [Primcodable α] [BitEncoding α] in
theorem filter_eq_flatten (p : α → Bool) (l : List α) :
    l.filter p = (l.map fun a => bif p a then [a] else []).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

@[fun_prop] theorem filter {p : α → β → Bool} {l : α → List β}
    (hp : PolyTime fun q : α × β => p q.1 q.2) (hl : PolyTime l) :
    PolyTime fun a => (l a).filter (p a) := by
  have hm : PolyTime (fun a => (l a).map fun b => bif p a b then [b] else []) := by
    fun_prop
  exact of_eq (comp flatten hm) fun a => (filter_eq_flatten (p a) (l a)).symm

@[fun_prop] theorem find? {p : α → β → Bool} {l : α → List β}
    (hp : PolyTime fun q : α × β => p q.1 q.2) (hl : PolyTime l) :
    PolyTime fun a => (l a).find? (p a) := by
  exact of_eq (comp head? (filter hp hl)) fun a => List.head?_filter ..

@[fun_prop] theorem countP {p : α → β → Bool} {l : α → List β}
    (hp : PolyTime fun q : α × β => p q.1 q.2) (hl : PolyTime l) :
    PolyTime fun a => (l a).countP (p a) := by
  exact of_eq (comp length (filter hp hl)) fun a => (List.countP_eq_length_filter ..).symm

@[fun_prop] theorem any {p : α → β → Bool} {l : α → List β}
    (hp : PolyTime fun q : α × β => p q.1 q.2) (hl : PolyTime l) :
    PolyTime fun a => (l a).any (p a) := by
  have h : PolyTime fun a => !(l a).all (fun b => !p a b) := by fun_prop
  exact of_eq h fun a => List.any_eq_not_all_not.symm

@[fun_prop] theorem replicate : PolyTime (fun p : ℕ × α => List.replicate p.1 p.2) := by
  have h : PolyTime (fun p : ℕ × α => (enc p.1).map fun _ => p.2) := by fun_prop
  exact of_eq h fun _ => List.map_replicate

@[fun_prop] theorem option_bind [Inhabited β] {f : α → β → Option γ}
    {o : α → Option β} (hf : PolyTime fun q : α × β => f q.1 q.2) (ho : PolyTime o) :
    PolyTime fun a => (o a).bind (f a) := by
  have h : PolyTime (fun a => bif (o a).isSome then f a ((o a).getD default) else none) := by
    fun_prop
  exact of_eq h fun a => by cases o a <;> rfl

/-- The cap bounds every step, even on arbitrary intermediate lists. -/
def rangeStep (N : ℕ) (l : List ℕ) : List ℕ := l ++ [(l.take N).length]

theorem iterate_rangeStep (N : ℕ) : ∀ i ≤ N, (rangeStep N)^[i] [] = List.range i := by
  intro i
  induction i with
  | zero => intro; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), rangeStep, List.range_succ,
      List.length_take, List.length_range, Nat.min_eq_right (by omega)]

@[fun_prop] theorem range : PolyTime List.range := by
  have hI := iterate₂ (g := rangeStep) (by unfold rangeStep; fun_prop) 2 fun N l => by
    have h := length_enc_append l [(l.take N).length]
    rw [length_enc_cons, length_enc_nil, length_enc_nat, List.length_take] at h
    rw [rangeStep, length_enc_nat, List.length_take]
    have hm : min N l.length ≤ N := Nat.min_le_left _ _
    have h2 : 2 * N + 2 ≤ (N + 2) ^ 2 := by nlinarith
    omega
  have hw : PolyTime (fun N : ℕ => (N, N, ([] : List ℕ))) := by fun_prop
  exact of_eq (comp hI hw) fun N => iterate_rangeStep N N le_rfl

@[fun_prop] theorem lt {f g : α → ℕ} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun a => decide (f a < g a)) :=
  of_eq (f := fun a => decide (f a + 1 ≤ g a)) (by fun_prop) fun a => by
    simp only [Nat.add_one_le_iff]

@[fun_prop] theorem min : PolyTime (fun p : ℕ × ℕ => min p.1 p.2) := by
  have h : PolyTime (fun p : ℕ × ℕ => bif decide (p.1 ≤ p.2) then p.1 else p.2) := by
    fun_prop
  exact of_eq h fun p => by simp [Nat.min_def]

@[fun_prop] theorem max : PolyTime (fun p : ℕ × ℕ => max p.1 p.2) := by
  have h : PolyTime (fun p : ℕ × ℕ => bif decide (p.1 ≤ p.2) then p.2 else p.1) := by
    fun_prop
  exact of_eq h fun p => by simp [Nat.max_def]

end Turing.PolyTime
