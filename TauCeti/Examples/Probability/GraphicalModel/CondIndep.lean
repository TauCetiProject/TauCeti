/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.GraphicalModel.CondIndep
import Mathlib.Tactic.NormNum

/-!
# Examples: conditional independence of fair bits

Worked values of `TauCeti.GraphicalModel.CondIndep` for laws of fair bits. A fair bit takes the
values `false` and `true` with mass `1/2` each.

* Three independent fair bits (`threeBits`, margins in `margin_threeBits`): at every
  configuration `p(x_2) p(x_{0,1,2}) = 1/2 · 1/8` and `p(x_{0,2}) p(x_{1,2}) = 1/4 · 1/4`, so
  `{0} ⊥ {1} | {2}`. The identity without the factor `p(x_S)` compares `1/8` with `1/16` and
  fails.
* Two copies of one fair bit (`twoCopies`): at `x = (false, false)`,
  `p(x_∅) p(x_{0,1}) = 1/2` but `p(x_0) p(x_1) = 1/4`, so `{0} ⊥ {1} | ∅` fails, while
  `{0} ⊥ {1} | {0}` holds.
* One fair bit (`oneBit`) is not independent of itself, since `{0} ⊥ {0} | ∅` asks that each
  value has mass `0` or the total mass `1`.
-/

public section

noncomputable section

open Finset TauCeti.GraphicalModel
open scoped NNReal

namespace TauCeti.Examples.GraphicalModel

/-- The law of three independent fair bits: each configuration has mass `1/8`. -/
def threeBits : (Fin 3 → Bool) → ℝ≥0 := fun _ => 1 / 8

/-- The law of two copies of one fair bit: `(false, false)` and `(true, true)` have mass `1/2`. -/
def twoCopies : (Fin 2 → Bool) → ℝ≥0 := fun y => if y 0 = y 1 then 1 / 2 else 0

/-- The law of one fair bit. -/
def oneBit : (Fin 1 → Bool) → ℝ≥0 := fun _ => 1 / 2

section Count

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {A : Finset V} {x : ∀ v, X v} {c : ℝ≥0} {n : ℕ}

/-- A margin of a law of constant mass, from the number of configurations that agree with `x` on
`A`. The hypothesis uses the decidability instance of `margin_const`, so that `decide` proves it
for concrete sets; a count written out by hand elaborates with a different instance. -/
private theorem margin_const_of_card
    (h : #(univ.filter fun y : ∀ v, X v => ∀ v ∈ A, y v = x v) = n) :
    margin (fun _ => c) A x = n * c := by
  rw [margin_const, h]

/-- A margin of a law of mass `c` on the configurations where `P` holds and `0` elsewhere, from
the number of configurations that satisfy `P` and agree with `x` on `A`. -/
private theorem margin_ite_of_card {P : (∀ v, X v) → Prop} [DecidablePred P]
    (h : #((univ.filter fun y : ∀ v, X v => ∀ v ∈ A, y v = x v).filter P) = n) :
    margin (fun y => if P y then c else 0) A x = n * c := by
  rw [margin_def, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, h]

end Count

/-- The margins of `threeBits` on the sets that appear in `{0} ⊥ {1} | {2}`. -/
theorem margin_threeBits (x : Fin 3 → Bool) :
    margin threeBits {2} x = 1 / 2 ∧ margin threeBits ({0} ∪ {1} ∪ {2}) x = 1 / 8 ∧
      margin threeBits ({0} ∪ {2}) x = 1 / 4 ∧ margin threeBits ({1} ∪ {2}) x = 1 / 4 := by
  rw [threeBits.eq_unfold, margin_const_of_card (n := 4) (by revert x; decide),
    margin_const_of_card (n := 1) (by revert x; decide),
    margin_const_of_card (n := 2) (by revert x; decide),
    margin_const_of_card (n := 2) (by revert x; decide)]
  norm_num

-- Three independent fair bits: `{0} ⊥ {1} | {2}`.
example : CondIndep threeBits {0} {1} {2} := by
  refine condIndep_iff.2 fun x => ?_
  obtain ⟨h₁, h₂, h₃, h₄⟩ := margin_threeBits x
  rw [h₁, h₂, h₃, h₄]
  norm_num

-- Three independent fair bits: the identity without the factor `p(x_S)` fails.
example (x : Fin 3 → Bool) : margin threeBits ({0} ∪ {1} ∪ {2}) x ≠
    margin threeBits ({0} ∪ {2}) x * margin threeBits ({1} ∪ {2}) x := by
  obtain ⟨-, h₂, h₃, h₄⟩ := margin_threeBits x
  rw [h₂, h₃, h₄]
  norm_num

-- Two copies of one fair bit: `{0} ⊥ {1} | ∅` fails at `x = (false, false)`.
example : ¬CondIndep twoCopies {0} {1} ∅ := by
  intro h
  have := condIndep_iff.1 h fun _ => false
  rw [twoCopies.eq_unfold, margin_ite_of_card (n := 2) (by decide),
    margin_ite_of_card (n := 1) (by decide), margin_ite_of_card (n := 1) (by decide),
    margin_ite_of_card (n := 1) (by decide)] at this
  norm_num at this

-- Two copies of one fair bit: `{0} ⊥ {1} | {0}` holds.
example : CondIndep twoCopies {0} {1} {0} :=
  condIndep_of_subset subset_rfl

-- One fair bit is not independent of itself: `false` has mass `1/2`, neither `0` nor `1`.
example : ¬CondIndep oneBit {0} {0} ∅ := by
  rw [condIndep_self_iff]
  intro h
  have := h fun _ => false
  rw [oneBit.eq_unfold, margin_const_of_card (n := 1) (by decide),
    margin_const_of_card (n := 2) (by decide)] at this
  norm_num at this

end TauCeti.Examples.GraphicalModel
