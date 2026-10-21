/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.GeomSum
public import TauCeti.Combinatorics.Young.Addable

/-!
# Split semisimplicity separates the Jucys–Murphy eigenvalues

On the semisimple Hecke algebra `Hₙ(q)` with `Q = q²` the Jucys–Murphy elements act on the new box
of a one-box branching `μ ⊂ μ + c` by the eigenvalue `Q ^ content c`, and
`YoungDiagram.injOn_zpow_cellContent_iff` says that these eigenvalues separate the addable cells of
every diagram of size less than `n` exactly when `Q ^ d ≠ 1` for `2 ≤ d ≤ n`. This file derives
that condition from the split-semisimplicity criterion: over a commutative ring without zero
divisors, it holds whenever `Q ≠ 1` and the product `∏_{d=1}^{n} [d]_Q` of `Q`-integers is
nonzero.

## Main results

* `YoungDiagram.injOn_zpow_cellContent_of_prod_geom_sum_ne_zero`: without zero divisors, the
  split-semisimplicity criterion `∏_{d=1}^{n} [d]_Q ≠ 0` together with `Q ≠ 1` makes the powers
  `Q ^ content c` separate the addable cells of every diagram of size less than `n`.

## References

* A. Ram, *Seminormal representations of Weyl groups and Iwahori-Hecke algebras*, Proc. London
  Math. Soc. 75 (1997), 99–133, for the Hecke eigenvalues `Q ^ content`.
-/

public section

namespace YoungDiagram

/-- **Split semisimplicity separates the Jucys–Murphy eigenvalues.** Over a commutative ring
without zero divisors, if the unit `Q` is not `1` and the product `∏_{d=1}^{n} [d]_Q` of the
`Q`-integers `[d]_Q = 1 + Q + ⋯ + Q ^ (d - 1)` is nonzero, then on every Young diagram of size
less than `n` the powers `Q ^ content c` of distinct addable cells are distinct. -/
theorem injOn_zpow_cellContent_of_prod_geom_sum_ne_zero {μ : YoungDiagram} {R : Type*}
    [CommRing R] [NoZeroDivisors R] {Q : Rˣ} {n : ℕ} (hQ : (Q : R) ≠ 1)
    (hprod : ∏ d ∈ Finset.Icc 1 n, ∑ i ∈ Finset.range d, (Q : R) ^ i ≠ 0) (hμ : μ.card < n) :
    Set.InjOn (fun c ↦ ((Q ^ cellContent c : Rˣ) : R)) {c | IsAddable μ c} := by
  refine Units.val_injective.comp_injOn (injOn_zpow_cellContent (fun d hd hdn hQd ↦ ?_) hμ)
  refine (TauCeti.prod_geom_sum_ne_zero_iff hQ _).mp hprod d
    (Finset.mem_Icc.mpr ⟨by omega, hdn⟩) ?_
  rw [← Units.val_pow_eq_pow_val, hQd, Units.val_one]

end YoungDiagram
