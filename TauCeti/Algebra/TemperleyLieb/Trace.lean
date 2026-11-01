/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.JonesWenzl
import Mathlib.Tactic.LinearCombination

/-!
# Markov traces and quantum dimensions

An unnormalized Markov trace on the Temperley–Lieb tower takes the value `δ ^ n` on the
identity on `n` strands. Adding a strand multiplies the trace by `δ`, whereas capping that
strand with the last generator recovers the trace one level down.

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` and proves that every such trace
takes the value `qInt R δ (n + 1)` on the Jones–Wenzl projection on `n` strands, whenever
`[1], …, [n]` are units. In particular the next quantum integer may vanish: this is the
quantum-dimension calculation used to detect negligible projections. The result also applies
to any normalized element annihilated by the generators, by uniqueness of the projection.

This does not assert existence of a Markov trace at every loop parameter, or uniqueness of
Markov traces.

## References

* H. Wenzl, *On sequences of projections*, C. R. Math. Rep. Acad. Sci. Canada 9 (1987), 5–9.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.

The calculation uses `TauCeti.TemperleyLieb.jonesWenzl_add_two` and its idempotence theorem.
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

/-- Every Markov trace takes the value `[n + 1]` on the Jones–Wenzl projection on `n`
strands, provided `[1], …, [n]` are units. No assumption on `[n + 1]` is needed. -/
@[simp]
theorem map_jonesWenzl (htr : IsMarkovTrace R δ tr) :
    ∀ n, (∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) →
      tr n (jonesWenzl δ n) = qInt R δ (n + 1)
  | 0, _ => by simp [htr.map_one]
  | 1, _ => by simp [htr.map_one]
  | m + 2, h => by
    have hprev : ∀ k ∈ Finset.Icc 1 (m + 1), IsUnit (qInt R δ k) :=
      fun k hk ↦ h k (Finset.Icc_subset_Icc le_rfl (by omega) hk)
    have hid := (isIdempotentElem_jonesWenzl hprev).eq
    rw [jonesWenzl_add_two, map_sub, map_smul, htr.map_strandIncl,
      htr.map_strandIncl_mul_e_last_mul, hid, htr.map_jonesWenzl (m + 1) hprev,
      smul_eq_mul, qInt_add_two δ (m + 1)]
    linear_combination -(qInt R δ (m + 1)) *
      Ring.inverse_mul_cancel _ (h (m + 2) (by simp))

/-- The quantum-dimension formula for any element of augmentation `1` annihilated on the
left by the generators. One-sided annihilation already characterizes the Jones–Wenzl projection.
-/
theorem apply_jonesWenzl (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) (f : TemperleyLieb R δ n)
    (hf : aug f = 1)
    (hfe : ∀ i : Fin (n - 1), e δ i * f = 0) :
    tr n f = qInt R δ (n + 1) := by
  rw [eq_jonesWenzl_of_e_mul_eq_zero h hf hfe]
  exact htr.map_jonesWenzl n h

end IsMarkovTrace

end TauCeti.TemperleyLieb
