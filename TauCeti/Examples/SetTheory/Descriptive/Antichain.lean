/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.Antichain

/-!
# Regression examples: Cantor antichains

These examples exercise the antichain API from a downstream module, through public statements
only:

* equality on Cantor space has a Cantor antichain on the whole space, the identity map;
* the universal relation has no Cantor antichain on any set;
* the subtype bridge bounds the quotient of a specified subset: equality restricted to the
  points of Cantor space starting with `true` has at least continuum many classes.
-/

open Cardinal

-- Equality on Cantor space: the identity is a Cantor antichain on the whole space.
example : (⊥ : Setoid (ℕ → Bool)).HasCantorAntichainOn Set.univ :=
  Setoid.hasCantorAntichainOn_iff.2
    ⟨id, continuous_id, fun _ => trivial, fun _ _ hab h => hab (by simpa [Setoid.bot_def] using h)⟩

-- The universal relation relates any two images, so it has no Cantor antichain.
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    ¬ (⊤ : Setoid X).HasCantorAntichainOn A := by
  intro h
  obtain ⟨f, -, -, hf⟩ := Setoid.hasCantorAntichainOn_iff.1 h
  exact hf (fun _ => false) (fun _ => true) (fun h => by simpa using congrFun h 0) trivial

-- Restricted to the points starting with `true`, equality still has at least continuum many
-- classes: prepending `true` is a Cantor antichain on that set.
example : 𝔠 ≤ #(Quotient ((⊥ : Setoid (ℕ → Bool)).comap
    ((↑) : {x : ℕ → Bool | x 0 = true} → ℕ → Bool))) := by
  refine Setoid.HasCantorAntichainOn.continuum_le_mk_quotient_comap
    (Setoid.hasCantorAntichainOn_iff.2 ⟨fun a n => Nat.casesOn n true a, ?_, fun _ => rfl, ?_⟩)
  · exact continuous_pi fun n => by cases n <;> fun_prop
  · intro a b hab h
    have h' : (fun n => Nat.casesOn n true a : ℕ → Bool) = fun n => Nat.casesOn n true b := by
      simpa [Setoid.bot_def] using h
    exact hab (funext fun n => congrFun h' (n + 1))
