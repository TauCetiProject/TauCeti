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
not assert the existence of a Markov trace at every loop parameter.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
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
private theorem eq_of_le_one {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ tr') {n : ℕ} (hn : n ≤ 1) :
    tr n = tr' n := by
  ext x
  rw [← (algEquivOfLeOne δ hn).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, htr'.map_one]

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' := by
  funext n
  obtain _ | n := n
  · exact eq_of_le_one htr htr' (by omega)
  induction n with
  | zero => exact eq_of_le_one htr htr' le_rfl
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, htr'.map_strandIncl, ih]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr'.map_strandIncl_mul_e_last_mul, ih]

end IsMarkovTrace

end TauCeti.TemperleyLieb
