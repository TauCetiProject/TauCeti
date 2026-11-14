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

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` and its bounded counterpart
`TauCeti.TemperleyLieb.IsMarkovTraceUpTo` on `0, …, N` strands, and proves the trace reduction
for a last generator sandwiched between two included elements. This reduction is used for the
capped terms in the tower's normal form and for quantum-dimension calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `m + 2` strands from its values on `m + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So up to any number `N` of strands (`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), and hence
on the full tower (`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), there is at most one Markov
trace at each loop parameter over every commutative semiring. Bounded uniqueness lets a path model
defined only up to depth `N` identify and control the global Markov trace up to `N` strands. This
file does not assert the existence of a Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on the full Temperley–Lieb
  tower.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace on `0, …, N` strands.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of Markov traces up to `N` strands and
  on the full tower.
* `TauCeti.TemperleyLieb.IsMarkovTrace.eq_of_isMarkovTraceUpTo`: a global Markov trace agrees up
  to `N` strands with any Markov trace defined up to `N` strands.
* `TauCeti.TemperleyLieb.IsMarkovTrace.succ_eq_zero`: at loop parameter `0`, every Markov trace
  vanishes on one or more strands.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

/-- An **unnormalized Markov trace up to `N` strands**: a family of linear forms on `0, …, N`
strands with `tr m hm 1 = δ ^ m`, traciality, strand-inclusion compatibility, and the Markov
property whenever all strand counts involved are at most `N`. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ m ≤ N, TemperleyLieb R δ m →ₗ[R] R) : Prop where
  map_one : ∀ m (hm : m ≤ N), tr m hm 1 = δ ^ m
  map_mul_comm : ∀ m (hm : m ≤ N) (x y : TemperleyLieb R δ m),
    tr m hm (x * y) = tr m hm (y * x)
  map_strandIncl : ∀ m (hm : m + 2 ≤ N) (x : TemperleyLieb R δ (m + 1)),
    tr (m + 2) hm (strandIncl x) = δ * tr (m + 1) (by omega) x
  map_strandIncl_mul_e_last : ∀ m (hm : m + 2 ≤ N) (x : TemperleyLieb R δ (m + 1)),
    tr (m + 2) hm (strandIncl x * e δ (Fin.last m)) = tr (m + 1) (by omega) x

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

namespace IsMarkovTraceUpTo

variable {N : ℕ} {tr : ∀ m ≤ N, TemperleyLieb R δ m →ₗ[R] R}

/-- Restricting a Markov trace up to `N` strands to `M ≤ N` strands gives a Markov trace up to
`M` strands. -/
theorem mono (htr : IsMarkovTraceUpTo R δ N tr) {M : ℕ} (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M (fun m hm ↦ tr m (hm.trans hMN)) :=
  ⟨fun m hm ↦ htr.map_one m (hm.trans hMN),
    fun m hm ↦ htr.map_mul_comm m (hm.trans hMN),
    fun m hm ↦ htr.map_strandIncl m (hm.trans hMN),
    fun m hm ↦ htr.map_strandIncl_mul_e_last m (hm.trans hMN)⟩

/-- The Markov property up to `N` strands for a last generator sandwiched between two included
elements. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTraceUpTo R δ N tr) {m : ℕ}
    (hm : m + 2 ≤ N) (a b : TemperleyLieb R δ (m + 1)) :
    tr (m + 2) hm (strandIncl a * e δ (Fin.last m) * strandIncl b) =
      tr (m + 1) (by omega) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

/-- On at most one strand the algebra is the base ring, so a Markov trace is `aug x * δ ^ m`. -/
theorem apply_of_le_one (htr : IsMarkovTraceUpTo R δ N tr) {m : ℕ} (hm : m ≤ N) (hm1 : m ≤ 1)
    (x : TemperleyLieb R δ m) : tr m hm x = aug x * δ ^ m := by
  conv_lhs => rw [← (algEquivOfLeOne δ hm1).symm_apply_apply x]
  rw [algEquivOfLeOne_apply, algEquivOfLeOne_symm_apply, Algebra.algebraMap_eq_smul_one,
    map_smul, htr.map_one, smul_eq_mul]

/-- **Uniqueness of Markov traces up to `N` strands.** Over every commutative semiring and at
every loop parameter there is at most one unnormalized Markov trace on `0, …, N` strands: on at
most one strand it is determined by its normalization, and on `m + 2 ≤ N` strands it is
determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last m) * strandIncl b` by its values on `m + 1` strands. -/
theorem unique {tr' : ∀ m ≤ N, TemperleyLieb R δ m →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') : tr = tr' := by
  funext m hm
  obtain _ | m := m
  · ext x
    rw [htr.apply_of_le_one hm (by omega), htr'.apply_of_le_one hm (by omega)]
  induction m with
  | zero =>
    ext x
    rw [htr.apply_of_le_one hm le_rfl, htr'.apply_of_le_one hm le_rfl]
  | succ m ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top m) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, htr'.map_strandIncl, ih (by omega)]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr'.map_strandIncl_mul_e_last_mul, ih (by omega)]

end IsMarkovTraceUpTo

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- Restricting a Markov trace on the full tower to `0, …, N` strands gives a Markov trace up to
`N` strands. -/
theorem isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) (N : ℕ) :
    IsMarkovTraceUpTo R δ N (fun m _ ↦ tr m) :=
  ⟨fun m _ ↦ htr.map_one m, fun m _ ↦ htr.map_mul_comm m,
    fun m _ ↦ htr.map_strandIncl m, fun m _ ↦ htr.map_strandIncl_mul_e_last m⟩

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) :=
  (htr.isMarkovTraceUpTo (n + 2)).map_strandIncl_mul_e_last_mul le_rfl a b

/-- On at most one strand the algebra is the base ring, so a Markov trace is `aug x * δ ^ n`. -/
theorem apply_of_le_one (htr : IsMarkovTrace R δ tr) {n : ℕ} (hn : n ≤ 1)
    (x : TemperleyLieb R δ n) : tr n x = aug x * δ ^ n :=
  (htr.isMarkovTraceUpTo n).apply_of_le_one le_rfl hn x

/-- On zero strands, every Markov trace is the augmentation. -/
theorem apply_zero (htr : IsMarkovTrace R δ tr) (x : TemperleyLieb R δ 0) :
    tr 0 x = aug x := by
  rw [htr.apply_of_le_one (Nat.zero_le 1), pow_zero, mul_one]

/-- On one strand, every Markov trace is `δ` times the augmentation. -/
theorem apply_one (htr : IsMarkovTrace R δ tr) (x : TemperleyLieb R δ 1) :
    tr 1 x = δ * aug x := by
  rw [htr.apply_of_le_one le_rfl, pow_one, mul_comm]

/-- A Markov trace on the full tower agrees on `m ≤ N` strands with any Markov trace defined up to
`N` strands. -/
theorem eq_of_isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) {N : ℕ}
    {tr' : ∀ m ≤ N, TemperleyLieb R δ m →ₗ[R] R} (htr' : IsMarkovTraceUpTo R δ N tr')
    {m : ℕ} (hm : m ≤ N) : tr m = tr' m hm :=
  congrFun₂ ((htr.isMarkovTraceUpTo N).unique htr') m hm

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' :=
  funext fun n ↦ htr.eq_of_isMarkovTraceUpTo (htr'.isMarkovTraceUpTo n) le_rfl

/-- At loop parameter `0`, every Markov trace vanishes on one or more strands: closing any diagram
on at least one strand creates at least one loop. -/
theorem succ_eq_zero {tr : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTrace R 0 tr) (n : ℕ) : tr (n + 1) = 0 := by
  induction n with
  | zero =>
    ext x
    simp [htr.apply_one]
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · simp [htr.map_strandIncl]
    · simp [htr.map_strandIncl_mul_e_last_mul, ih]

end IsMarkovTrace

end TauCeti.TemperleyLieb
