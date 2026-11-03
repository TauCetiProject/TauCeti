/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Basic

/-!
# Abstract Markov traces

An unnormalized Markov trace on the Temperley–Lieb tower takes the value `δ ^ n` on the
identity on `n` strands. Adding a strand multiplies the trace by `δ`, whereas capping that
strand with the last generator recovers the trace one level down.

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` and proves the trace reduction for
a last generator sandwiched between two included elements. This reduction is used for the
capped terms in the tower's normal form and for quantum-dimension calculations.

This does not assert existence of a Markov trace at every loop parameter, or uniqueness of
Markov traces.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
-/

public section

namespace TauCeti.TemperleyLieb

/-- An **unnormalized Markov trace** on the Temperley–Lieb tower: a family of linear forms
with `tr n 1 = δ ^ n`, traciality, strand-inclusion compatibility, and the Markov property.
The normalization is specified in every degree, including degrees zero and one, since
`strandIncl` starts at one strand. -/
structure IsMarkovTrace (R : Type*) [CommRing R] (δ : R)
    (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n, tr n 1 = δ ^ n
  map_mul_comm : ∀ n (x y : TemperleyLieb R δ n), tr n (x * y) = tr n (y * x)
  map_strandIncl : ∀ n (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) (strandIncl x) = δ * tr (n + 1) x
  map_strandIncl_mul_e_last : ∀ n (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) (strandIncl x * e δ (Fin.last n)) = tr (n + 1) x

variable {R : Type*} [CommRing R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

namespace IsMarkovTrace

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

end IsMarkovTrace

end TauCeti.TemperleyLieb
