/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.Setoid.Isolation
import Mathlib.Order.Setoid.Basic

/-!
# Regression examples: isolation is a genuine hypothesis

On Cantor space `ℕ → Bool`, let `E n` relate two points that agree on their first `n`
coordinates. These examples check, through public statements only:

* each `E n` has countably many classes (there are at most `2 ^ n` of them);
* the intersection of the `E n` is equality;
* equality is not isolated by the `E n`: changing the coordinate `n` of a point keeps it
  `E n`-equivalent to the original one. Equality has continuum many classes, so countably many
  classes at every `E n` do not bound the classes of their intersection without isolation.
-/

-- Each relation `E n` has countably many classes: a class is determined by the first `n`
-- coordinates.
example (n : ℕ) :
    Countable (Quotient (Setoid.ker fun x : ℕ → Bool => fun i : Fin n => x i)) :=
  (Setoid.kerLift_injective _).countable

-- The intersection of the relations `E n` is equality.
example (x y : ℕ → Bool) :
    (∀ n, Setoid.ker (fun x : ℕ → Bool => fun i : Fin n => x i) x y) ↔ x = y := by
  refine ⟨fun h => funext fun i => ?_, fun h n => h ▸ Setoid.refl' _ x⟩
  exact congrFun (h (i + 1)) ⟨i, Nat.lt_succ_self i⟩

-- Equality is not isolated by the relations `E n`.
example : ¬ (⊥ : Setoid (ℕ → Bool)).IsolatedBy
    fun n => Setoid.ker fun x : ℕ → Bool => fun i : Fin n => x i := by
  intro h
  obtain ⟨n, hn⟩ := Setoid.isolatedBy_iff.1 h fun _ => false
  have hE : Setoid.ker (fun x : ℕ → Bool => fun i : Fin n => x i) (fun _ => false)
      (Function.update (fun _ => false) n true) := by
    funext i
    simp [Function.update_of_ne (Nat.ne_of_lt i.2)]
  have := hn _ hE
  simpa [Setoid.bot_def] using congrFun this n
