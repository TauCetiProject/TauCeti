/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Tower

/-!
# Abstract Markov traces

An unnormalized Markov trace on the Temperley–Lieb tower takes the value `δ ^ n` on the
identity on `n` strands. Adding a strand multiplies the trace by `δ`, whereas capping that
strand with the last generator recovers the trace one level down.

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` and proves the trace reduction for
a last generator sandwiched between two included elements. This reduction is used for the
capped terms in the tower's normal form and for quantum-dimension calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `n + 2` strands from its values on `n + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So there is at most one Markov trace at each loop parameter
(`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), over every commutative semiring. This file does
not assert the existence of a Markov trace at every loop parameter. The same induction stops at
any level: a family of linear forms satisfying the conditions of a Markov trace on at most `N`
strands agrees there with every Markov trace (`TauCeti.TemperleyLieb.IsMarkovTrace.eq_of_le`).

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.eq_of_le`: uniqueness of the Markov trace up to a level.
* `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of the Markov trace.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

/-- An **unnormalized Markov trace** on the Temperley–Lieb tower: a family of linear forms
with `tr n 1 = δ ^ n`, traciality, strand-inclusion compatibility, and the Markov property.
The normalization is specified in every degree, including degrees zero and one, since
`strandIncl` starts at one strand. -/
structure IsMarkovTrace (R : Type*) [CommSemiring R] (δ : R)
    (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n, tr n 1 = δ ^ n
  map_mul_comm : ∀ n (x y : TemperleyLieb R δ n), tr n (x * y) = tr n (y * x)
  map_strandIncl : ∀ n (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) (strandIncl x) = δ * tr (n + 1) x
  map_strandIncl_mul_e_last : ∀ n (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) (strandIncl x * e δ (Fin.last n)) = tr (n + 1) x

variable {R : Type*} [CommSemiring R] {δ : R}
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

/-- On at most one strand the algebra is the base ring, so a Markov trace is determined there by
its normalization `tr n 1 = δ ^ n`. -/
private theorem eq_of_le_one {n : ℕ} {tr' : TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (h' : tr' 1 = δ ^ n) (hn : n ≤ 1) : tr n = tr' := by
  ext x
  rw [← (algEquivOfLeOne δ hn).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, h']

/-- **Uniqueness of the Markov trace up to a level.** If a family of linear forms satisfies the
conditions of an unnormalized Markov trace on at most `N` strands, then it agrees with every
Markov trace on at most `N` strands: on `n + 2` strands both are determined on the spanning
elements `strandIncl a` and `strandIncl a * e δ (Fin.last n) * strandIncl b` by their values on
`n + 1` strands. -/
theorem eq_of_le {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} {N : ℕ}
    (htr : IsMarkovTrace R δ tr) (map_one : ∀ n ≤ N, tr' n 1 = δ ^ n)
    (map_mul_comm : ∀ n ≤ N, ∀ x y : TemperleyLieb R δ n, tr' n (x * y) = tr' n (y * x))
    (map_strandIncl : ∀ n, n + 2 ≤ N → ∀ x : TemperleyLieb R δ (n + 1),
      tr' (n + 2) (strandIncl x) = δ * tr' (n + 1) x)
    (map_strandIncl_mul_e_last : ∀ n, n + 2 ≤ N → ∀ x : TemperleyLieb R δ (n + 1),
      tr' (n + 2) (strandIncl x * e δ (Fin.last n)) = tr' (n + 1) x)
    {n : ℕ} (hn : n ≤ N) : tr n = tr' n := by
  obtain _ | n := n
  · exact htr.eq_of_le_one (map_one 0 hn) (by omega)
  induction n with
  | zero => exact htr.eq_of_le_one (map_one 1 hn) le_rfl
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, map_strandIncl n hn, ih (by omega)]
    · rw [htr.map_strandIncl_mul_e_last_mul, ih (by omega), map_mul_comm _ hn, ← mul_assoc,
        ← map_mul, map_strandIncl_mul_e_last n hn, map_mul_comm _ (by omega)]

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' :=
  funext fun n ↦ htr.eq_of_le (N := n) (fun m _ ↦ htr'.map_one m)
    (fun m _ ↦ htr'.map_mul_comm m) (fun m _ ↦ htr'.map_strandIncl m)
    (fun m _ ↦ htr'.map_strandIncl_mul_e_last m) le_rfl

end IsMarkovTrace

end TauCeti.TemperleyLieb
