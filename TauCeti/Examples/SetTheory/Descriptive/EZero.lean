/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.EZero
import TauCeti.Topology.Baire.Mycielski
import TauCeti.Topology.Perfect

/-!
# Open splitting and limit avoidance for E₀

Although E₀ is meagre in the square, every pair of nonempty open sets contains related
points, since every class is dense. Thus an open Cantor scheme cannot have nonempty,
E₀-inequivalent siblings. In contrast, Mycielski's theorem produces a continuous Cantor
antichain by avoiding E₀ only at the limit. These examples distinguish the hypotheses
of finite-stage antichain extraction from the limit-avoidance theorem.

See A. S. Kechris, *Classical Descriptive Set Theory*, Theorem 19.1 (Mycielski's theorem).
-/

open Set TauCeti

-- Even disjoint nonempty open sets cannot be separated by E₀-inequivalence.
example {U V : Set (ℕ → Bool)} (hU : U.Nonempty) (hV : V.Nonempty) (hoV : IsOpen V) :
    ∃ x ∈ U, ∃ y ∈ V, eZero x y := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hxy, hyV⟩ := (dense_setOf_eZero x).exists_mem_open hoV hV
  exact ⟨x, hx, y, hyV, hxy⟩

-- In particular, no open scheme with nonempty pieces has inequivalent siblings, even
-- without imposing nesting, vanishing diameters, or branch-intersection conditions.
example (A : List Bool → Set (ℕ → Bool)) (ho : ∀ l, IsOpen (A l))
    (hne : ∀ l, (A l).Nonempty) :
    ¬ (∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ eZero x y) := by
  intro hcross
  obtain ⟨x, hx⟩ := hne [false]
  obtain ⟨y, hxy, hy⟩ := (dense_setOf_eZero x).exists_mem_open (ho [true]) (hne [true])
  exact hcross [] x hx y hy hxy

-- Mycielski nevertheless gives a Cantor antichain, independently of the explicit
-- coordinate-repetition witness in `hasCantorAntichainOn_eZero`.
example : eZero.HasCantorAntichainOn univ :=
  eZero.hasCantorAntichainOn_univ_of_isMeagre isMeagre_eZero
