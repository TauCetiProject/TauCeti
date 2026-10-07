/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.BitLists
public import Mathlib.Tactic.FunProp

/-!
# Polynomial-time bit machines

`PolyTime f` is the existence of a finite-control TM2 machine computing `f` on
self-delimiting bit encodings, with a polynomial bound on its actual transitions.
The closure rules below are consequences of the explicit machine constructions.
-/

@[expose] public section

namespace Turing

open Computability BitEncoding BitMachines

/-- A finite-control TM2 computes `f` on bit encodings within a polynomial transition bound. -/
@[fun_prop]
def PolyTime {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime enc enc f)

namespace PolyTime

variable {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Primcodable γ] [BitEncoding γ]

@[fun_prop] theorem id : PolyTime (fun a : α => a) :=
  ⟨idComputableInPolyTime enc⟩

@[fun_prop] theorem const (b : β) : PolyTime (fun _ : α => b) :=
  tm_const b

@[fun_prop] theorem comp {g : β → γ} {f : α → β} (hg : PolyTime g) (hf : PolyTime f) :
    PolyTime (fun a => g (f a)) := by
  obtain ⟨mg⟩ := hg
  obtain ⟨mf⟩ := hf
  exact ⟨mg.comp mf⟩

@[fun_prop] theorem pair {f : α → β} {g : α → γ} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun a => (f a, g a)) := by
  obtain ⟨mf⟩ := hf
  obtain ⟨mg⟩ := hg
  exact tm_pair mf mg

@[fun_prop] theorem fst : PolyTime (fun p : α × β => p.1) := tm_fst
@[fun_prop] theorem snd : PolyTime (fun p : α × β => p.2) := tm_snd
@[fun_prop] theorem add : PolyTime (fun p : ℕ × ℕ => p.1 + p.2) := tm_add
@[fun_prop] theorem mul : PolyTime (fun p : ℕ × ℕ => p.1 * p.2) := tm_mul
@[fun_prop] theorem take : PolyTime (fun p : ℕ × List α => p.2.take p.1) := tm_take
@[fun_prop] theorem drop : PolyTime (fun p : ℕ × List α => p.2.drop p.1) := tm_drop
@[fun_prop] theorem headD (d : α) : PolyTime (fun l : List α => l.headD d) := tm_headD d
@[fun_prop] theorem tail : PolyTime (List.tail : List α → List α) := tm_tail
@[fun_prop] theorem some : PolyTime (fun a : α => Option.some a) := tm_some
@[fun_prop] theorem getD : PolyTime (fun p : Option α × α => p.1.getD p.2) := tm_getD
@[fun_prop] theorem cond :
    PolyTime (fun p : Bool × α × α => bif p.1 then p.2.1 else p.2.2) := tm_cond
@[fun_prop] theorem length : PolyTime (List.length : List α → ℕ) := tm_length
@[fun_prop] theorem append : PolyTime (fun p : List α × List α => p.1 ++ p.2) := tm_append
@[fun_prop] theorem reverse : PolyTime (List.reverse : List α → List α) := tm_reverse
@[fun_prop] theorem encode : PolyTime (enc : α → List Bool) := tm_enc
@[fun_prop] theorem cons : PolyTime (fun p : α × List α => p.1 :: p.2) := tm_cons

@[fun_prop] theorem beq [DecidableEq β] {f₁ f₂ : α → β} (h₁ : PolyTime f₁)
    (h₂ : PolyTime f₂) : PolyTime (fun a => decide (f₁ a = f₂ a)) := by
  obtain ⟨m⟩ := pair h₁ h₂
  exact tm_comp tm_beq.some m

@[fun_prop] theorem map₂ {f : α → β → γ} {l : α → List β}
    (hf : PolyTime fun p : α × β => f p.1 p.2) (hl : PolyTime l) :
    PolyTime fun a => (l a).map (f a) := by
  obtain ⟨m⟩ := hf
  exact comp (tm_map₂ m) (pair id hl)

@[fun_prop] theorem map {f : α → β} (hf : PolyTime f) : PolyTime (List.map f) :=
  map₂ (comp hf snd) id

@[fun_prop] theorem le {f g : α → ℕ} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun a => decide (f a ≤ g a)) := by
  have hd : PolyTime (fun p : ℕ × ℕ => decide ((enc p.1).drop p.2 = [])) := by
    fun_prop
  have he : (fun p : ℕ × ℕ => decide ((enc p.1).drop p.2 = [])) =
      (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
    funext p
    simp [enc_nat, Nat.sub_eq_zero_iff_le]
  exact comp (he ▸ hd) (pair hf hg)

@[fun_prop] theorem pow (c : ℕ) : PolyTime (fun n : ℕ => n ^ c) := by
  induction c with
  | zero => exact const 1
  | succ c ih => exact comp mul (pair ih id)

theorem iterate {g : α → α} (hg : PolyTime g) (Q : Polynomial ℕ)
    (hQ : ∀ (N : ℕ) (s : α), ∀ i ≤ N,
      (enc (g^[i] s)).length ≤ Q.eval (enc (N, s)).length) :
    PolyTime (fun p : ℕ × α => g^[p.1] p.2) := by
  obtain ⟨m⟩ := hg
  exact tm_iterate m Q hQ

end PolyTime

attribute [irreducible] PolyTime

namespace PolyTime

variable {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]

theorem of_eq {f g : α → β} (hf : PolyTime f) (h : ∀ a, f a = g a) : PolyTime g :=
  funext h ▸ hf

@[fun_prop] theorem and : PolyTime (fun p : Bool × Bool => p.1 && p.2) :=
  of_eq (f := fun p : Bool × Bool => bif p.1 then p.2 else false) (by fun_prop)
    fun p => by cases p.1 <;> rfl

@[fun_prop] theorem or : PolyTime (fun p : Bool × Bool => p.1 || p.2) :=
  of_eq (f := fun p : Bool × Bool => bif p.1 then true else p.2) (by fun_prop)
    fun p => by cases p.1 <;> rfl

@[fun_prop] theorem not : PolyTime (fun b : Bool => !b) :=
  of_eq (f := fun b : Bool => bif b then false else true) (by fun_prop)
    fun b => by cases b <;> rfl

@[fun_prop] theorem xor : PolyTime (fun p : Bool × Bool => xor p.1 p.2) :=
  of_eq (f := fun p : Bool × Bool => bif p.1 then !p.2 else p.2) (by fun_prop)
    fun p => by cases p.1 <;> cases p.2 <;> rfl

@[fun_prop] theorem isSome : PolyTime (fun o : Option α => o.isSome) := by
  classical
  exact of_eq (f := fun o : Option α => bif decide (o = none) then false else true)
    (by fun_prop) fun o => by cases o <;> rfl

@[fun_prop] theorem head? : PolyTime (List.head? : List α → Option α) :=
  of_eq (f := fun l : List α => (l.take 1).map Option.some |>.headD none) (by fun_prop)
    fun l => by cases l <;> rfl

@[fun_prop] theorem getElem? : PolyTime (fun p : List α × ℕ => p.1[p.2]?) :=
  of_eq (f := fun p : List α × ℕ => (p.1.drop p.2).head?) (by fun_prop)
    fun p => by simp

@[fun_prop] theorem sub : PolyTime (fun p : ℕ × ℕ => p.1 - p.2) :=
  of_eq (f := fun p : ℕ × ℕ => ((enc p.1).drop p.2).length) (by fun_prop)
    fun p => by simp [length_enc_nat]

end PolyTime

end Turing
