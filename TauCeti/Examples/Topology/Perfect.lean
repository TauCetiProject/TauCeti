/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Perfect

/-!
# Regression examples: perfect products

These examples check from a downstream module that instance search finds the perfect-space
structure of infinite products:

* Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` are perfect;
* with finitely many coordinates the conclusion fails: the discrete space `Fin 2 → Bool` is not
  perfect, so the infinitude of the index type is needed.
-/

-- Cantor space is perfect.
example : PerfectSpace (ℕ → Bool) := inferInstance

-- Baire space is perfect.
example : PerfectSpace (ℕ → ℕ) := inferInstance

-- A finite product of discrete spaces is discrete, so it is not perfect.
example : ¬ PerfectSpace (Fin 2 → Bool) := by
  intro h
  exact ((perfectSpace_iff_forall_not_isolated.1 h) fun _ => true).ne
    ((isOpen_singleton_iff_punctured_nhds _).1 (isOpen_discrete _))
