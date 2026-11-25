/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.ModelTheory.Graph
import TauCeti.ModelTheory.RelationalConfiguration.IncidenceGraph

/-!
# Examples of incidence graphs

In the language of graphs, a configuration in which `adj(0, 1)` holds and `adj(1, 0)` fails joins
the tuple vertex of `adj(0, 1)` to its truth vertex and leaves that of `adj(1, 0)` without one. A
language with no relation symbols has incidence graphs with no edges. Two configurations that
differ at a nullary atom have no colour-preserving isomorphism of incidence graphs, although the
tuple vertex of a nullary atom has no position neighbours.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration IncidenceVertex

-- In a configuration of the language of graphs where `adj(0, 1)` holds and `adj(1, 0)` fails,
-- the tuple vertex of `adj(0, 1)` is joined to its two position vertices and its truth vertex,
-- and that of `adj(1, 0)` to its two position vertices only.
example (c : RelationalConfiguration Language.graph ℕ) (h01 : c.eval (atom adj ![0, 1]) = true)
    (h10 : c.eval (atom adj ![1, 0]) = false) (j : Fin 2) :
    c.incidenceGraph.Adj (tuple (atom adj ![0, 1])) (position adj ![0, 1] j) ∧
      c.incidenceGraph.Adj (tuple (atom adj ![0, 1])) (truth (atom adj ![0, 1])) ∧
      c.incidenceGraph.Adj (tuple (atom adj ![1, 0])) (position adj ![1, 0] j) ∧
      ¬c.incidenceGraph.Adj (tuple (atom adj ![1, 0])) (truth (atom adj ![1, 0])) := by
  simp [h01, h10]

-- The vertex of position `1` of `adj(1, 0)` is joined to the point `0`, whatever the
-- configuration.
example (c : RelationalConfiguration Language.graph ℕ) :
    c.incidenceGraph.Adj (position adj ![1, 0] 1) (point 0) := by
  simp

-- With no relation symbols there are no atoms, so the incidence graph has no edges.
example (c : RelationalConfiguration Language.empty ℕ) : c.incidenceGraph = ⊥ := by
  ext x y
  rcases x with _ | ⟨_, R, _⟩ | ⟨R, _, _⟩ | ⟨_, R, _⟩ <;>
    first | exact isEmptyElim R | rcases y with _ | ⟨_, R, _⟩ | ⟨R, _, _⟩ | ⟨_, R, _⟩ <;>
      first | exact isEmptyElim R | simp

-- Two configurations that differ at a nullary atom are not relabellings of one another, so no
-- isomorphism of their incidence graphs preserves the colours.
example {L : Language} {ι : (Σ n, L.Relations n) → ℕ} (hι : Function.Injective ι)
    (R : L.Relations 0) {c d : RelationalConfiguration L ℕ}
    (h : c.eval (atom R ![]) ≠ d.eval (atom R ![])) :
    ¬∃ f : c.incidenceGraph ≃g d.incidenceGraph, ∀ x, color ι (f x) = color ι x := by
  rw [← exists_perm_smul_eq_iff_exists_iso_incidenceGraph hι]
  rintro ⟨σ, rfl⟩
  exact h (by simp [Matrix.empty_eq])
