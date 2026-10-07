/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTime

/-!
# Polynomially bounded folds and iterations

The list traversal has a unary clock stored separately from the accumulator.
Each traversal theorem constructs a TM2 machine using `PolyTime.iterate`;
the hypotheses bound the size of intermediate data, not the running time of an
abstract operation.
-/

@[expose] public section

namespace Turing

open Computability BitEncoding

namespace PolyTime

variable {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Primcodable γ] [BitEncoding γ]

theorem iterate₂ {g : α → β → β} (hg : PolyTime (fun p : α × β => g p.1 p.2)) (c : ℕ)
    (hb : ∀ a s, (enc (g a s)).length ≤ (enc s).length + ((enc a).length + 2) ^ c) :
    PolyTime (fun p : α × ℕ × β => (g p.1)^[p.2.1] p.2.2) := by
  have hh : PolyTime (fun p : α × β => (p.1, g p.1 p.2)) := by fun_prop
  have hit : ∀ (a : α) (s : β) (j : ℕ),
      (fun p : α × β => (p.1, g p.1 p.2))^[j] (a, s) = (a, (g a)^[j] s) := by
    intro a s j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
  have hlen : ∀ (a : α) (s : β) (j : ℕ),
      (enc ((g a)^[j] s)).length ≤ (enc s).length + j * ((enc a).length + 2) ^ c := by
    intro a s j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', Nat.succ_mul]
      have := hb a ((g a)^[j] s)
      omega
  have hi := iterate hh
    (Polynomial.X + Polynomial.X * (Polynomial.X + Polynomial.C 2) ^ c) fun N z i hi => by
    obtain ⟨a, s⟩ := z
    have hn : (enc (N, (a, s))).length =
        2 * N + 1 + (2 * (enc a).length + 1 + (enc s).length) := by
      rw [length_enc_prod, length_enc_nat, length_enc_prod]
    have h2 : ((enc a).length + 2) ^ c ≤ ((enc (N, (a, s))).length + 2) ^ c :=
      Nat.pow_le_pow_left (by omega) c
    have h3 := Nat.mul_le_mul (show i ≤ (enc (N, (a, s))).length by omega) h2
    have := hlen a s i
    rw [hit, length_enc_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_C]
    omega
  refine of_eq (f := fun p : α × ℕ × β =>
    ((fun q : α × β => (q.1, g q.1 q.2))^[p.2.1] (p.1, p.2.2)).2) (by fun_prop) ?_
  intro p
  rw [hit]

/-- Pop one list entry and update the accumulator, leaving an empty list unchanged. -/
def foldStep (g : α → β → γ → β) (a : α) (q : List γ × β) : List γ × β :=
  (q.1.drop 1, (((q.1.take 1).map fun y => Option.some (g a q.2 y)).headD none).getD q.2)

omit [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Primcodable γ] [BitEncoding γ] in
theorem iterate_foldStep (g : α → β → γ → β) (a : α) :
    ∀ (l : List γ) (s : β), (foldStep g a)^[l.length] (l, s) = ([], l.foldl (g a) s)
  | [], _ => rfl
  | y :: l, s => by
    rw [List.length_cons, Function.iterate_succ_apply,
      show foldStep g a (y :: l, s) = (l, g a s y) from rfl, iterate_foldStep g a l]
    rfl

/-- A fold is polynomial-time when each step grows the accumulator by at most the
consumed entry's encoding and a polynomial in the fixed parameter. -/
theorem foldl {g : α → β → γ → β}
    (hg : PolyTime (fun p : α × β × γ => g p.1 p.2.1 p.2.2)) (c : ℕ)
    (hb : ∀ a s y, (enc (g a s y)).length ≤
      (enc s).length + 2 * (enc y).length + ((enc a).length + 2) ^ c) :
    PolyTime (fun p : α × β × List γ => p.2.2.foldl (g p.1) p.2.1) := by
  have hG : PolyTime (fun p : α × (List γ × β) => foldStep g p.1 p.2) := by
    unfold foldStep
    fun_prop
  have hGb : ∀ a q, (enc (foldStep g a q)).length ≤
      (enc q).length + ((enc a).length + 2) ^ c := by
    rintro a ⟨l, s⟩
    cases l with
    | nil => exact Nat.le_add_right _ _
    | cons y l =>
      rw [show foldStep g a (y :: l, s) = (l, g a s y) from rfl,
        length_enc_prod, length_enc_prod, length_enc_cons]
      have := hb a s y
      omega
  have hI := iterate₂ hG c hGb
  have hw : PolyTime (fun p : α × β × List γ =>
      (p.1, p.2.2.length, (p.2.2, p.2.1))) := by fun_prop
  refine of_eq (f := fun p : α × β × List γ =>
    ((foldStep g p.1)^[p.2.2.length] (p.2.2, p.2.1)).2)
    (comp snd (comp hI hw)) ?_
  intro p
  rw [iterate_foldStep]

@[fun_prop] theorem option_map [Inhabited β] {f : α → β → γ}
    {o : α → Option β} (hf : PolyTime fun q : α × β => f q.1 q.2) (ho : PolyTime o) :
    PolyTime fun a => (o a).map (f a) :=
  of_eq (f := fun a => bif (o a).isSome then Option.some (f a ((o a).getD default)) else none)
    (by fun_prop) fun a => by cases o a <;> rfl

@[fun_prop] theorem all {f : α → β → Bool} {l : α → List β}
    (hf : PolyTime fun q : α × β => f q.1 q.2) (hl : PolyTime l) :
    PolyTime (fun a => (l a).all (f a)) := by
  have hfold := foldl
    (g := fun a (b : Bool) y => b && f a y) (by fun_prop) 0
    (fun a b y => by simp only [enc_bool, List.length_singleton, pow_zero]; omega)
  have hw : PolyTime (fun a => (a, true, l a)) := by fun_prop
  refine of_eq (f := fun a => (l a).foldl (fun b y => b && f a y) true)
    (comp hfold hw) ?_
  intro a
  have h : ∀ (xs : List β) (b : Bool),
      xs.foldl (fun b y => b && f a y) b = (b && xs.all (f a)) := by
    intro xs
    induction xs with
    | nil => intro b; simp
    | cons y xs ih =>
      intro b
      rw [List.foldl_cons, ih]
      simp [Bool.and_assoc]
  simpa using h (l a) true

end PolyTime

end Turing
