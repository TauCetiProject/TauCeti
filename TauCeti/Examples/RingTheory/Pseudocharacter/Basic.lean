/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Pseudocharacter.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Examples: cycle products, cycle terms and pseudocharacters

* `cycleProduct`: the identity permutation returns the chosen entry; the transposition starting
  at `0` gives `x₀x₁`, starting at `1` gives `x₁x₀`.
* `cycleTerm`: the empty tuple gives `1`; the identity on two entries gives `T(x₀)T(x₁)`; the
  transposition gives `T(x₀x₁)`, with one cycle factor.
* `id : ℚ → ℚ` is a `1`-dimensional pseudocharacter.
* The trace on `M₂(ℚ)` is not `1`-dimensional: `T(1) = 2 ≠ 1`, and the `S₂` identity
  `T(x)T(y) − T(xy) = 0` fails at `x = y = 1`.
-/

open TauCeti Equiv

variable {A : Type*} [CommRing A] {R : Type*} [Ring R] [Module A R]

-- The identity permutation returns the chosen entry.
example {n : ℕ} (x : Fin n → R) (i : Fin n) : cycleProduct 1 x i = x i :=
  cycleProduct_one x i

-- The transposition starting at `0` gives `x₀x₁` ...
example (x : Fin 2 → R) : cycleProduct (swap 0 1) x 0 = x 0 * x 1 :=
  cycleProduct_swap x (by decide)

-- ... and starting at `1` gives `x₁x₀`.
example (x : Fin 2 → R) : cycleProduct (swap 0 1) x 1 = x 1 * x 0 := by
  rw [swap_comm, cycleProduct_swap x (by decide)]

-- The empty tuple has cycle term `1`.
example (T : R →ₗ[A] A) (x : Fin 0 → R) : cycleTerm T 1 x = 1 :=
  cycleTerm_fin_zero T 1 x

-- The identity on two entries gives `T(x₀)T(x₁)`.
example (T : R →ₗ[A] A) (x : Fin 2 → R) : cycleTerm T 1 x = T (x 0) * T (x 1) := by
  simp [Fin.prod_univ_two]

-- The transposition gives `T(x₀x₁)`, with one cycle factor.
example (T : R →ₗ[A] A) (x : Fin 2 → R) : cycleTerm T (swap 0 1) x = T (x 0 * x 1) :=
  cycleTerm_swap_fin_two T x

-- `id : ℚ → ℚ` is a `1`-dimensional pseudocharacter.
example : IsPseudocharacter (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 1 :=
  (isPseudocharacter_one_iff _).mpr ⟨rfl, fun _ _ ↦ rfl⟩

-- The trace on `M₂(ℚ)` is not a `1`-dimensional pseudocharacter: `T(1) = 2 ≠ 1`.
example : ¬ IsPseudocharacter (Matrix.traceLinearMap (Fin 2) ℚ ℚ) 1 := fun h ↦ by
  have := h.map_one
  norm_num [Matrix.trace_one] at this

-- The `S₂` identity `T(x)T(y) − T(xy) = 0` fails for the trace on `M₂(ℚ)` at `x = y = 1`.
example : cycleSum (Matrix.traceLinearMap (Fin 2) ℚ ℚ) ![1, 1] ≠ 0 := by
  rw [cycleSum_fin_two]
  norm_num [Matrix.trace_one]
