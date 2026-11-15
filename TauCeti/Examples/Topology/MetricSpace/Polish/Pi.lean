/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.MetricSpace.Perfect
import TauCeti.Topology.MetricSpace.Polish.Pi
import TauCeti.Topology.Perfect

/-!
# Regression examples: Cantor space is Polish

These examples check from a downstream module that instance search finds the Polish structure of
Cantor space and of the spaces built from it:

* `ℕ → Bool`, `ℕ → Fin 3`, the square `(ℕ → Bool) × (ℕ → Bool)` and the power
  `Fin 3 → ℕ → Bool` are Polish;
* consequently Cantor space, being perfect and Polish, has cardinality continuum by the
  perfect-set cardinality theorem.
-/

open Set Cardinal

-- Cantor space is Polish.
example : PolishSpace (ℕ → Bool) := inferInstance

-- So are the spaces of sequences in a finite alphabet.
example : PolishSpace (ℕ → Fin 3) := inferInstance

-- The square of Cantor space is Polish.
example : PolishSpace ((ℕ → Bool) × (ℕ → Bool)) := inferInstance

-- Finite powers of Cantor space are Polish.
example : PolishSpace (Fin 3 → ℕ → Bool) := inferInstance

-- Cantor space is perfect and Polish, so it has cardinality continuum.
example : #(univ : Set (ℕ → Bool)) = 𝔠 :=
  (PerfectSpace.univ_perfect (α := ℕ → Bool)).mk_eq_continuum univ_nonempty
