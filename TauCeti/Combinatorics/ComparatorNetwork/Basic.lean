/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Order.Fin.Basic
import Mathlib.Basic.Nontrivial.Basic
import Mathlib.Order.MinMax

/-!
# Comparator networks and the zero-one principle

A comparator network on `n` wires is a list of comparators, each a pair `(i, j)` of wires. The
comparator `(i, j)` puts the smaller of the values on the wires `i` and `j` on the wire `i` and
the larger on the wire `j`, and leaves the other wires unchanged. A network acts on an input
`x : Fin n → β` with values in a linear order `β` by applying its comparators in the order of the
list, and it sorts `β` when its output on every such input is monotone.

A monotone map `f : β → γ` commutes with `min` and `max`, hence with every comparator and with
every network. This gives the zero-one principle: if the output `y` of a network on `x` has
`y j < y i` for wires `i ≤ j`, then the monotone map `β → Bool` that is `true` exactly on the
values at least `y i` turns `x` into an input of zeros and ones whose output is not monotone
either. Conversely, a strictly monotone map `Bool → β` shows that a network that sorts a linear
order with two different elements sorts `Bool`.

## Main definitions

* `TauCeti.ComparatorNetwork n`: comparator networks on `n` wires.
* `TauCeti.comparator`: the action of one comparator on an input.
* `TauCeti.ComparatorNetwork.apply`: the output of a network on an input.
* `TauCeti.ComparatorNetwork.Sorts`: the outputs of a network on all inputs from a linear order
  are monotone.

## Main results

* `TauCeti.ComparatorNetwork.apply_append`: the output of a concatenation.
* `TauCeti.ComparatorNetwork.apply_comp_of_monotone`: a monotone map commutes with a network.
* `TauCeti.ComparatorNetwork.sorts_of_sorts_bool`: the zero-one principle.
* `TauCeti.ComparatorNetwork.sorts_iff_sorts_bool`: a network sorts a linear order with two
  different elements if and only if it sorts `Bool`.

## References

* Hans Werner Lang, web pages *Sorting networks* and *The 0-1-principle*, at
  `hwlang.de/algorithmen/sortieren/networks`.
-/

public section

namespace TauCeti

/-- A comparator network on `n` wires: a list of comparators, each a pair of wires. -/
abbrev ComparatorNetwork (n : ℕ) : Type := List (Fin n × Fin n)

variable {n : ℕ} {β γ : Type*} [LinearOrder β] [LinearOrder γ]

/-- The comparator `p` puts the smaller of the values of `x` on the wires `p.1` and `p.2` on the
wire `p.1` and the larger on the wire `p.2`, and leaves the other wires unchanged. When
`p.1 = p.2` it changes nothing. -/
def comparator (p : Fin n × Fin n) (x : Fin n → β) : Fin n → β :=
  fun k => if k = p.1 then min (x p.1) (x p.2) else if k = p.2 then max (x p.1) (x p.2) else x k

/-- The value of `comparator p x` on the wire `k`. -/
theorem comparator_apply (p : Fin n × Fin n) (x : Fin n → β) (k : Fin n) :
    comparator p x k =
      if k = p.1 then min (x p.1) (x p.2) else if k = p.2 then max (x p.1) (x p.2) else x k :=
  (rfl)

/-- The comparator `p` puts the smaller of its two values on the wire `p.1`. -/
@[simp]
theorem comparator_apply_fst (p : Fin n × Fin n) (x : Fin n → β) :
    comparator p x p.1 = min (x p.1) (x p.2) := by
  simp [comparator_apply]

/-- The comparator `p` puts the larger of its two values on the wire `p.2`. When `p.1 = p.2`
both values are the same. -/
@[simp]
theorem comparator_apply_snd (p : Fin n × Fin n) (x : Fin n → β) :
    comparator p x p.2 = max (x p.1) (x p.2) := by
  obtain ⟨i, j⟩ := p
  by_cases h : j = i
  · subst h
    simp [comparator_apply]
  · simp [comparator_apply, h]

/-- The comparator `p` leaves the wires other than `p.1` and `p.2` unchanged. -/
theorem comparator_apply_of_ne {p : Fin n × Fin n} {k : Fin n} (h₁ : k ≠ p.1) (h₂ : k ≠ p.2)
    (x : Fin n → β) : comparator p x k = x k := by
  simp [comparator_apply, h₁, h₂]

/-- A comparator that joins a wire to itself changes nothing. -/
@[simp]
theorem comparator_self (i : Fin n) (x : Fin n → β) : comparator (i, i) x = x := by
  funext k
  by_cases hk : k = i <;> simp [comparator_apply, hk]

/-- A monotone map commutes with every comparator. -/
theorem comparator_comp_of_monotone {f : β → γ} (hf : Monotone f) (p : Fin n × Fin n)
    (x : Fin n → β) : comparator p (f ∘ x) = f ∘ comparator p x := by
  funext k
  simp only [comparator_apply, Function.comp_apply]
  split_ifs <;> simp [hf.map_min, hf.map_max]

namespace ComparatorNetwork

/-- The output of the network `c` on the input `x`: the comparators of `c` act in the order of
the list. -/
def apply : ComparatorNetwork n → (Fin n → β) → Fin n → β
  | [], x => x
  | p :: c, x => apply c (comparator p x)

/-- The empty network changes nothing. -/
@[simp]
theorem apply_nil (x : Fin n → β) : apply ([] : ComparatorNetwork n) x = x :=
  (rfl)

/-- The network `p :: c` applies the comparator `p` first and then the network `c`. -/
@[simp]
theorem apply_cons (p : Fin n × Fin n) (c : ComparatorNetwork n) (x : Fin n → β) :
    apply (p :: c) x = c.apply (comparator p x) :=
  (rfl)

/-- The output of a network is the left fold of its comparators over the input. -/
theorem apply_eq_foldl (c : ComparatorNetwork n) (x : Fin n → β) :
    c.apply x = c.foldl (fun y p => comparator p y) x := by
  induction c generalizing x with
  | nil => rfl
  | cons p c ih => rw [apply_cons, List.foldl_cons, ih]

/-- The output of the concatenation `c ++ c'` on `x` is the output of `c'` on the output of `c`
on `x`. -/
@[simp]
theorem apply_append (c c' : ComparatorNetwork n) (x : Fin n → β) :
    (c ++ c').apply x = c'.apply (c.apply x) := by
  induction c generalizing x with
  | nil => rfl
  | cons p c ih => rw [List.cons_append, apply_cons, apply_cons, ih]

/-- A monotone map commutes with every network. -/
theorem apply_comp_of_monotone {f : β → γ} (hf : Monotone f) (c : ComparatorNetwork n)
    (x : Fin n → β) : c.apply (f ∘ x) = f ∘ c.apply x := by
  induction c generalizing x with
  | nil => rfl
  | cons p c ih => rw [apply_cons, apply_cons, comparator_comp_of_monotone hf, ih]

/-- The network `c` sorts the linear order `β` when its output on every input
`x : Fin n → β` is monotone. -/
def Sorts (c : ComparatorNetwork n) (β : Type*) [LinearOrder β] : Prop :=
  ∀ x : Fin n → β, Monotone (c.apply x)

/-- The definition of `Sorts` as a statement. -/
theorem sorts_iff {c : ComparatorNetwork n} : c.Sorts β ↔ ∀ x : Fin n → β, Monotone (c.apply x) :=
  Iff.rfl

/-- Every network sorts a linear order with at most one element. -/
theorem sorts_of_subsingleton [Subsingleton β] (c : ComparatorNetwork n) : c.Sorts β :=
  sorts_iff.2 fun _ _ _ _ => (Subsingleton.elim _ _).le

/-- **The zero-one principle.** A network that sorts all inputs of zeros and ones sorts all inputs
from every linear order. -/
theorem sorts_of_sorts_bool (c : ComparatorNetwork n) (h : c.Sorts Bool) (β : Type*)
    [LinearOrder β] : c.Sorts β := by
  refine sorts_iff.2 fun x i j hij => ?_
  by_contra hlt
  -- The map that is `true` exactly on the values at least `c.apply x i` is monotone.
  let f : β → Bool := fun b => decide (c.apply x i ≤ b)
  have hf : Monotone f := fun a b hab => Bool.le_iff_imp.2 fun ha =>
    decide_eq_true ((of_decide_eq_true ha).trans hab)
  have := sorts_iff.1 h (f ∘ x) hij
  rw [apply_comp_of_monotone hf] at this
  exact hlt (of_decide_eq_true (Bool.le_iff_imp.1 this (decide_eq_true le_rfl)))

/-- A network that sorts a linear order with two different elements sorts `Bool`. -/
theorem Sorts.sorts_bool [Nontrivial β] {c : ComparatorNetwork n} (h : c.Sorts β) :
    c.Sorts Bool := by
  obtain ⟨a, b, hab⟩ := exists_pair_lt β
  -- The map `Bool → β` that sends `false` to `a` and `true` to `b` is strictly monotone.
  let f : Bool → β := fun t => if t then b else a
  have hf : StrictMono f := by
    intro s t hst
    obtain ⟨rfl, rfl⟩ := Bool.lt_iff.1 hst
    exact hab
  refine sorts_iff.2 fun x i j hij => ?_
  have := sorts_iff.1 h (f ∘ x) hij
  rw [apply_comp_of_monotone hf.monotone] at this
  exact hf.le_iff_le.1 this

/-- A network sorts a linear order with two different elements if and only if it sorts
`Bool`. -/
theorem sorts_iff_sorts_bool [Nontrivial β] {c : ComparatorNetwork n} :
    c.Sorts β ↔ c.Sorts Bool :=
  ⟨Sorts.sorts_bool, fun h => sorts_of_sorts_bool c h β⟩

end ComparatorNetwork

end TauCeti
