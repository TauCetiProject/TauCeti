/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.ZMod.Defs

/-!
# Deterministic finite automata with output

A deterministic automaton with output (DFAO) with input alphabet `α`, states `σ` and output
alphabet `Δ` consists of a transition function `step : σ → α → σ`, an initial state `start` and
an output function `output : σ → Δ`. Where Mathlib's `DFA` only accepts or rejects a word, a
DFAO attaches an arbitrary output to the state it reaches. These automata are the machines that
compute automatic sequences, the objects of the theorems of Christol and Cobham.

As for Mathlib's `DFA`, words are read from the head of the list, and the structure does not
require finitely many states; finiteness is imposed where it is used.

## Main definitions and results

* `TauCeti.DFAO`: a deterministic automaton with output.
* `TauCeti.DFAO.evalFrom`, `TauCeti.DFAO.eval`: the state reached on a word, from a given state
  or from the initial state.
* `TauCeti.DFAO.evalFrom_append`: running on `x ++ y` runs on `x` and then on `y`.
* `TauCeti.DFAO.toDFA`: the Mathlib `DFA` accepting the words whose output lies in a set `S`;
  `TauCeti.DFAO.mem_accepts_toDFA` describes its language.
* `TauCeti.DFAO.mapOutput`, `TauCeti.DFAO.prod`: post-composition of the output, and the
  product automaton running two automata in parallel.

## References

* Andrew Bridy, *Automatic sequences and curves over finite fields*, Algebra & Number Theory
  11 (2017), Section 2.1.
* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Section 4.
-/

public section

universe u v w x y z

namespace TauCeti

/-- A **deterministic automaton with output** (DFAO) with input alphabet `α`, states `σ` and
output alphabet `Δ`: a transition function, an initial state and an output function. No
finiteness is assumed. -/
@[ext]
structure DFAO (α : Type u) (σ : Type v) (Δ : Type w) where
  /-- The transition from a state on one input letter. -/
  step : σ → α → σ
  /-- The initial state. -/
  start : σ
  /-- The output attached to a state. -/
  output : σ → Δ

namespace DFAO

variable {α : Type u} {σ : Type v} {Δ : Type w} (M : DFAO α σ Δ)

/-- `M.evalFrom s x` is the state reached by running `M` on the word `x` from the state `s`,
reading `x` from its head. -/
def evalFrom (s : σ) (x : List α) : σ :=
  x.foldl M.step s

/-- `M.eval x` is the state reached by running `M` on the word `x` from its initial state. -/
def eval (x : List α) : σ :=
  M.evalFrom M.start x

@[simp]
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s :=
  (rfl)

@[simp]
theorem evalFrom_cons (s : σ) (a : α) (x : List α) :
    M.evalFrom s (a :: x) = M.evalFrom (M.step s a) x :=
  (rfl)

theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  (rfl)

@[simp]
theorem evalFrom_append (s : σ) (x y : List α) :
    M.evalFrom s (x ++ y) = M.evalFrom (M.evalFrom s x) y :=
  List.foldl_append

theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp

theorem eval_eq_evalFrom (x : List α) : M.eval x = M.evalFrom M.start x :=
  (rfl)

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  (rfl)

@[simp]
theorem eval_cons (a : α) (x : List α) : M.eval (a :: x) = M.evalFrom (M.step M.start a) x :=
  (rfl)

theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  (rfl)

theorem eval_append (x y : List α) : M.eval (x ++ y) = M.evalFrom (M.eval x) y :=
  M.evalFrom_append M.start x y

@[simp]
theorem eval_append_singleton (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.step (M.eval x) a :=
  M.evalFrom_append_singleton M.start x a

/-! ### The acceptor of a set of outputs -/

/-- The Mathlib `DFA` with the transitions of `M` whose accepting states are those with output in
`S`. It accepts exactly the words on which `M` outputs an element of `S`
(`TauCeti.DFAO.mem_accepts_toDFA`). -/
def toDFA (S : Set Δ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.output ⁻¹' S

@[simp]
theorem toDFA_step (S : Set Δ) : (M.toDFA S).step = M.step :=
  (rfl)

@[simp]
theorem toDFA_start (S : Set Δ) : (M.toDFA S).start = M.start :=
  (rfl)

@[simp]
theorem toDFA_accept (S : Set Δ) : (M.toDFA S).accept = M.output ⁻¹' S :=
  (rfl)

@[simp]
theorem evalFrom_toDFA (S : Set Δ) (s : σ) (x : List α) :
    (M.toDFA S).evalFrom s x = M.evalFrom s x :=
  (rfl)

@[simp]
theorem eval_toDFA (S : Set Δ) (x : List α) : (M.toDFA S).eval x = M.eval x :=
  (rfl)

/-- A word is accepted by `M.toDFA S` exactly when `M` outputs an element of `S` on it. -/
@[simp]
theorem mem_accepts_toDFA {S : Set Δ} {x : List α} :
    x ∈ (M.toDFA S).accepts ↔ M.output (M.eval x) ∈ S := by
  rw [DFA.mem_accepts, eval_toDFA, toDFA_accept, Set.mem_preimage]

/-! ### Changing the output and running two automata in parallel -/

/-- Change the output alphabet of `M` along `f`: the same transitions, with output `f ∘ output`. -/
def mapOutput {Δ' : Type x} (f : Δ → Δ') : DFAO α σ Δ' where
  step := M.step
  start := M.start
  output := f ∘ M.output

@[simp]
theorem mapOutput_step {Δ' : Type x} (f : Δ → Δ') : (M.mapOutput f).step = M.step :=
  (rfl)

@[simp]
theorem mapOutput_start {Δ' : Type x} (f : Δ → Δ') : (M.mapOutput f).start = M.start :=
  (rfl)

@[simp]
theorem mapOutput_output {Δ' : Type x} (f : Δ → Δ') (q : σ) :
    (M.mapOutput f).output q = f (M.output q) :=
  (rfl)

@[simp]
theorem evalFrom_mapOutput {Δ' : Type x} (f : Δ → Δ') (s : σ) (x : List α) :
    (M.mapOutput f).evalFrom s x = M.evalFrom s x :=
  (rfl)

/-- Changing the output does not change the state reached; with
`TauCeti.DFAO.mapOutput_output`, the output on a word is `f` applied to the original output. -/
@[simp]
theorem eval_mapOutput {Δ' : Type x} (f : Δ → Δ') (x : List α) :
    (M.mapOutput f).eval x = M.eval x :=
  (rfl)

@[simp]
theorem mapOutput_id : M.mapOutput id = M :=
  (rfl)

@[simp]
theorem mapOutput_mapOutput {Δ' : Type x} {Δ'' : Type z} (f : Δ → Δ') (g : Δ' → Δ'') :
    (M.mapOutput f).mapOutput g = M.mapOutput (g ∘ f) :=
  (rfl)

/-- The product automaton, running `M` and `N` in parallel on the same input and outputting the
pair of their outputs. -/
def prod {τ : Type x} {Δ' : Type y} (N : DFAO α τ Δ') : DFAO α (σ × τ) (Δ × Δ') where
  step q a := (M.step q.1 a, N.step q.2 a)
  start := (M.start, N.start)
  output q := (M.output q.1, N.output q.2)

@[simp]
theorem prod_step {τ : Type x} {Δ' : Type y} (N : DFAO α τ Δ') (q : σ × τ) (a : α) :
    (M.prod N).step q a = (M.step q.1 a, N.step q.2 a) :=
  (rfl)

@[simp]
theorem prod_start {τ : Type x} {Δ' : Type y} (N : DFAO α τ Δ') :
    (M.prod N).start = (M.start, N.start) :=
  (rfl)

@[simp]
theorem prod_output {τ : Type x} {Δ' : Type y} (N : DFAO α τ Δ') (q : σ × τ) :
    (M.prod N).output q = (M.output q.1, N.output q.2) :=
  (rfl)

@[simp]
theorem evalFrom_prod {τ : Type x} {Δ' : Type y} (N : DFAO α τ Δ') (q : σ × τ) (x : List α) :
    (M.prod N).evalFrom q x = (M.evalFrom q.1 x, N.evalFrom q.2 x) := by
  induction x generalizing q with
  | nil => simp
  | cons a x ih => simp [ih]

/-- The product automaton reaches the pair of the states reached by the two factors. -/
@[simp]
theorem eval_prod {τ : Type x} {Δ' : Type y} (N : DFAO α τ Δ') (x : List α) :
    (M.prod N).eval x = (M.eval x, N.eval x) :=
  M.evalFrom_prod N _ x

end DFAO

/-- The parity automaton on `Fin 2`, adding the letters in `ZMod 2`. -/
def parityDFAO : DFAO (Fin 2) (ZMod 2) (ZMod 2) := ⟨fun s a => s + (a : ℕ), 0, id⟩

@[simp]
theorem parityDFAO_step (q : ZMod 2) (d : Fin 2) : parityDFAO.step q d = q + d.val := by
  simp only [parityDFAO]

@[simp]
theorem parityDFAO_start : parityDFAO.start = 0 := by
  simp only [parityDFAO]

@[simp]
theorem parityDFAO_output (q : ZMod 2) : parityDFAO.output q = q := by
  simp only [parityDFAO]
  rfl

/-! ### Checks -/

/-- The parity automaton outputs the parity of the number of ones of a word. -/
example : parityDFAO.output (parityDFAO.eval [1, 0, 1, 1]) = 1 := by decide

/-- With accepting outputs `{0}`, the acceptor of the parity automaton accepts `[1, 1]` and
rejects `[1]`. -/
example : [1, 1] ∈ (parityDFAO.toDFA {0}).accepts ∧ [1] ∉ (parityDFAO.toDFA {0}).accepts := by
  simp only [DFAO.mem_accepts_toDFA, Set.mem_singleton_iff]
  decide

/-- Noncommuting transitions detect the reading direction: words are read from their head. -/
example :
    (⟨fun q b => if b then 2 * q else q + 1, 0, id⟩ : DFAO Bool (ZMod 3) (ZMod 3)).eval
      [false, true] = 2 ∧
    (⟨fun q b => if b then 2 * q else q + 1, 0, id⟩ : DFAO Bool (ZMod 3) (ZMod 3)).eval
      [true, false] = 1 := by
  decide

end TauCeti
