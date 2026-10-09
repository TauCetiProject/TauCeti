/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Multiplication
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# Corners at nonadjacent zigzag vertices

For distinct nonadjacent vertices `i, j` of a finite simple graph, the corner
`e_i Z e_j` of the componentwise zigzag algebra is zero, including when either
vertex is isolated. These corners enter the calculation of tensor products
of the vertex projective bimodules.

See Huerfano--Khovanov, *A category for the adjoint representation*.
-/

public section

namespace TauCeti

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

/-- Each vertex basis element of the componentwise zigzag algebra is idempotent. -/
theorem isIdempotentElem_zigzagAlgebraBasis_inl (i : V) :
    IsIdempotentElem (zigzagAlgebraBasis k G (Sum.inl i)) := by
  simp [IsIdempotentElem]

/-- Distinct nonadjacent vertex idempotents cut out a zero corner of the public
zigzag algebra, including its isolated-vertex dual-number factors. -/
theorem cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) : cornerSubmodule k (e i) (e j) = ⊥ := by
  classical
  have hzero : LinearMap.mulLeftRight k (e i, e j) = 0 := by
    apply (zigzagAlgebraBasis k G).ext
    intro b
    simp only [LinearMap.mulLeftRight_apply, LinearMap.zero_apply]
    rcases b with v | d | v
    · by_cases h : i = v
      · subst v
        simp [hij]
      · simp [h]
    · by_cases h : i = d.snd
      · by_cases h' : d.fst = j
        · have ha : G.Adj i j := by simpa only [h, ← h'] using d.adj.symm
          exact (hadj ha).elim
        · simp [h, Ne.symm h']
      · simp [h]
    · by_cases h : i = v
      · subst v
        simp [hij]
      · simp [h]
  rw [cornerSubmodule_def]
  exact LinearMap.range_eq_bot.mpr hzero

end TauCeti
