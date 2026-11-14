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

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` and its bounded-level counterpart
`TauCeti.TemperleyLieb.IsMarkovTraceUpTo` (for families defined on at most `N` strands), and
proves the trace reduction for a last generator sandwiched between two included elements. This
reduction is used for the capped terms in the tower's normal form and for quantum-dimension
calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `n + 2` strands from its values on `n + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So there is at most one Markov trace up to any given level
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), and hence at most one global Markov trace at
each loop parameter (`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), over every commutative
semiring. Bounded-level uniqueness identifies the trace on `n` strands with finite path models
whose adjacency eigenvector equation holds only up to distance `n`. This file does not assert the
existence of a Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace defined on at most `N`
  strands.
* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on the full Temperley–Lieb
  tower.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_strandIncl_mul_e_last_mul`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of bounded-level and global Markov
  traces.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.eq_pow_smul_aug_of_le_one`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.eq_pow_smul_aug_of_le_one`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.eq_aug_zero`: on at most one strand a Markov trace is
  `δ ^ n • aug.toLinearMap`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.eq_zero_of_pos`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.eq_zero_of_pos`: at loop parameter `0`, every Markov trace
  vanishes on any positive number of strands.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

/-- An **unnormalized Markov trace up to `N` strands** on the Temperley–Lieb tower: a family of
linear forms defined on at most `N` strands with `tr n hn 1 = δ ^ n`, traciality, strand-inclusion
compatibility, and the Markov property up to level `N`. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n (hn : n ≤ N), tr n hn 1 = δ ^ n
  map_mul_comm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n),
    tr n hn (x * y) = tr n hn (y * x)
  map_strandIncl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x) = δ * tr (n + 1) (Nat.le_of_succ_le hn) x
  map_strandIncl_mul_e_last : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x * e δ (Fin.last n)) =
      tr (n + 1) (Nat.le_of_succ_le hn) x

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

variable {R : Type*} [CommSemiring R]

namespace IsMarkovTraceUpTo

section Semiring

variable {δ : R} {N : ℕ} {tr : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}

/-- Restricting a Markov trace up to `N` strands to a smaller bound `M ≤ N` gives a Markov trace up
to `M` strands. -/
theorem mono (htr : IsMarkovTraceUpTo R δ N tr) {M : ℕ} (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M (fun n hn ↦ tr n (hn.trans hMN)) :=
  ⟨fun n hn ↦ htr.map_one n (hn.trans hMN),
    fun n hn x y ↦ htr.map_mul_comm n (hn.trans hMN) x y,
    fun n hn x ↦ htr.map_strandIncl n (hn.trans hMN) x,
    fun n hn x ↦ htr.map_strandIncl_mul_e_last n (hn.trans hMN) x⟩

/-- The Markov property up to `N` strands for a last generator sandwiched between two included
elements. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ}
    (hn : n + 2 ≤ N) (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) hn (strandIncl a * e δ (Fin.last n) * strandIncl b) =
      tr (n + 1) (Nat.le_of_succ_le hn) (a * b) := by
  rw [htr.map_mul_comm (n + 2) hn, ← mul_assoc, ← map_mul,
    htr.map_strandIncl_mul_e_last n hn, htr.map_mul_comm (n + 1)]

/-- On at most one strand the algebra is the base ring via `aug`, so any Markov trace up to `N`
strands equals `δ ^ n • aug.toLinearMap`. -/
theorem eq_pow_smul_aug_of_le_one (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn₁ : n ≤ 1)
    (hn : n ≤ N) : tr n hn = δ ^ n • aug.toLinearMap := by
  ext x
  conv_lhs => rw [← (algEquivOfLeOne δ hn₁).symm_apply_apply x]
  rw [algEquivOfLeOne_symm_apply, Algebra.algebraMap_eq_smul_one, map_smul, htr.map_one,
    algEquivOfLeOne_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  simp only [smul_eq_mul, mul_comm]

/-- **Uniqueness of bounded-level Markov traces.** Over every commutative semiring and at every
loop parameter there is at most one unnormalized Markov trace up to `N` strands. -/
theorem unique {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') :
    tr = tr' := by
  funext n hn
  obtain _ | n := n
  · rw [htr.eq_pow_smul_aug_of_le_one (Nat.zero_le 1) hn,
      htr'.eq_pow_smul_aug_of_le_one (Nat.zero_le 1) hn]
  induction n with
  | zero =>
    rw [htr.eq_pow_smul_aug_of_le_one le_rfl hn, htr'.eq_pow_smul_aug_of_le_one le_rfl hn]
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl n hn, htr'.map_strandIncl n hn, ih (Nat.le_of_succ_le hn)]
    · rw [htr.map_strandIncl_mul_e_last_mul hn, htr'.map_strandIncl_mul_e_last_mul hn,
        ih (Nat.le_of_succ_le hn)]

end Semiring

/-- At loop parameter `0`, every Markov trace up to `N` strands vanishes on any positive number of
strands `n ≤ N`. -/
theorem eq_zero_of_pos {N : ℕ} {tr : ∀ n ≤ N, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R 0 N tr) {n : ℕ} (hn₀ : 0 < n) (hn : n ≤ N) :
    tr n hn = 0 := by
  obtain _ | m := n
  · omega
  induction m with
  | zero => simp [htr.eq_pow_smul_aug_of_le_one le_rfl hn]
  | succ m ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top m) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl m hn, zero_mul, LinearMap.zero_apply]
    · rw [htr.map_strandIncl_mul_e_last_mul hn,
        ih (Nat.succ_pos m) (Nat.le_of_succ_le hn), LinearMap.zero_apply, LinearMap.zero_apply]

end IsMarkovTraceUpTo

namespace IsMarkovTrace

section Semiring

variable {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- Restricting a global Markov trace to at most `N` strands gives a Markov trace up to `N`
strands. -/
theorem upTo (htr : IsMarkovTrace R δ tr) (N : ℕ) :
    IsMarkovTraceUpTo R δ N (fun n _ ↦ tr n) :=
  ⟨fun n _ ↦ htr.map_one n, fun n _ ↦ htr.map_mul_comm n,
    fun n _ ↦ htr.map_strandIncl n, fun n _ ↦ htr.map_strandIncl_mul_e_last n⟩

/-- On at most one strand the algebra is the base ring via `aug`, so any Markov trace equals
`δ ^ n • aug.toLinearMap`. -/
theorem eq_pow_smul_aug_of_le_one (htr : IsMarkovTrace R δ tr) {n : ℕ} (hn : n ≤ 1) :
    tr n = δ ^ n • aug.toLinearMap :=
  (htr.upTo n).eq_pow_smul_aug_of_le_one hn le_rfl

/-- On zero strands any Markov trace is the augmentation `aug.toLinearMap`. -/
theorem eq_aug_zero (htr : IsMarkovTrace R δ tr) : tr 0 = aug.toLinearMap := by
  simpa using htr.eq_pow_smul_aug_of_le_one (Nat.zero_le 1)

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) :=
  (htr.upTo (n + 2)).map_strandIncl_mul_e_last_mul le_rfl a b

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' := by
  funext n
  exact congrFun (congrFun ((htr.upTo n).unique (htr'.upTo n)) n) le_rfl

end Semiring

/-- At loop parameter `0`, every Markov trace vanishes on any positive number of strands. -/
theorem eq_zero_of_pos {tr : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTrace R 0 tr) {n : ℕ} (hn : 0 < n) : tr n = 0 :=
  (htr.upTo n).eq_zero_of_pos hn le_rfl

end IsMarkovTrace

end TauCeti.TemperleyLieb
