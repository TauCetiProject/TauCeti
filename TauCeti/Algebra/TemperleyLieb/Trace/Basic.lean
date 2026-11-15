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

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` together with its bounded-level
counterpart `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`, and proves the trace reduction for a last
generator sandwiched between two included elements. This reduction is used for the capped terms in
the tower's normal form and for quantum-dimension calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `n + 2` strands from its values on `n + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So a Markov trace up to `N` strands is unique (`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`),
and hence there is at most one Markov trace on the full tower at each loop parameter
(`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), over every commutative semiring. This file does
not assert the existence of a Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on the Temperley–Lieb tower.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace defined up to `N`
  strands.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`,
  `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of bounded and full Markov traces.
* `TauCeti.TemperleyLieb.IsMarkovTrace.eq_of_isMarkovTraceUpTo`: a full Markov trace agrees up to
  level `N` with any Markov trace defined up to `N` strands.
* `TauCeti.TemperleyLieb.IsMarkovTrace.eq_zero_of_succ`: when the loop parameter vanishes, every
  Markov trace vanishes on one or more strands.

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

/-- An **unnormalized Markov trace up to `N` strands** on the Temperley–Lieb tower: a family of
linear forms defined on at most `N` strands with `tr n hn 1 = δ ^ n`, traciality, strand-inclusion
compatibility, and the Markov property whenever `n + 2 ≤ N`. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n (hn : n ≤ N), tr n hn 1 = δ ^ n
  map_mul_comm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n),
    tr n hn (x * y) = tr n hn (y * x)
  map_strandIncl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x) = δ * tr (n + 1) (by omega) x
  map_strandIncl_mul_e_last : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x * e δ (Fin.last n)) = tr (n + 1) (by omega) x

variable {R : Type*} [CommSemiring R] {δ : R}

namespace IsMarkovTraceUpTo

variable {N : ℕ} {tr : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}

/-- The Markov property up to `N` strands for a last generator sandwiched between two included
elements. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn : n + 2 ≤ N)
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) hn (strandIncl a * e δ (Fin.last n) * strandIncl b) =
      tr (n + 1) (by omega) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

/-- Restricting a Markov trace up to `N` strands to `M ≤ N` strands gives a Markov trace up to `M`
strands. -/
theorem mono {M : ℕ} (htr : IsMarkovTraceUpTo R δ N tr) (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M (fun n hn ↦ tr n (hn.trans hMN)) where
  map_one n hn := htr.map_one n (hn.trans hMN)
  map_mul_comm n hn := htr.map_mul_comm n (hn.trans hMN)
  map_strandIncl n hn := htr.map_strandIncl n (hn.trans hMN)
  map_strandIncl_mul_e_last n hn := htr.map_strandIncl_mul_e_last n (hn.trans hMN)

/-- On at most one strand the algebra is the base ring, so a bounded Markov trace is determined
there by its normalization `tr n hn 1 = δ ^ n`. -/
private theorem eq_of_le_one {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr')
    {n : ℕ} (hn : n ≤ N) (hn1 : n ≤ 1) :
    tr n hn = tr' n hn := by
  ext x
  rw [← (algEquivOfLeOne δ hn1).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, htr'.map_one]

/-- **Uniqueness of Markov traces up to `N` strands.** Over every commutative semiring and at every
loop parameter there is at most one unnormalized Markov trace defined up to `N` strands. -/
theorem unique {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') :
    tr = tr' := by
  funext n hn
  obtain _ | n := n
  · exact eq_of_le_one htr htr' hn (by omega)
  induction n with
  | zero => exact eq_of_le_one htr htr' hn le_rfl
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, htr'.map_strandIncl, ih (by omega)]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr'.map_strandIncl_mul_e_last_mul, ih (by omega)]

end IsMarkovTraceUpTo

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

/-- Every Markov trace on the full tower restricts to a Markov trace up to `N` strands. -/
theorem isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) (N : ℕ) :
    IsMarkovTraceUpTo R δ N (fun n _ ↦ tr n) where
  map_one n _ := htr.map_one n
  map_mul_comm n _ := htr.map_mul_comm n
  map_strandIncl n _ := htr.map_strandIncl n
  map_strandIncl_mul_e_last n _ := htr.map_strandIncl_mul_e_last n

/-- A full Markov trace agrees on at most `N` strands with any Markov trace defined up to `N`
strands. -/
theorem eq_of_isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) {N : ℕ}
    {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R} (htr' : IsMarkovTraceUpTo R δ N tr')
    {n : ℕ} (hn : n ≤ N) : tr n = tr' n hn :=
  congr_fun₂ ((htr.isMarkovTraceUpTo N).unique htr') n hn

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' := by
  funext n
  exact htr.eq_of_isMarkovTraceUpTo (htr'.isMarkovTraceUpTo n) le_rfl

/-- When the loop parameter vanishes, every unnormalized Markov trace vanishes on one or more
strands. -/
theorem eq_zero_of_succ {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (hδ : δ = 0) (n : ℕ) : tr (n + 1) = 0 := by
  subst hδ
  let tr' : ∀ m : ℕ, TemperleyLieb R 0 m →ₗ[R] R := fun
    | 0 => tr 0
    | _ + 1 => 0
  have htr' : IsMarkovTrace R 0 tr' :=
    { map_one := fun | 0 => htr.map_one 0 | _ + 1 => by simp [tr']
      map_mul_comm := fun | 0 => htr.map_mul_comm 0 | _ + 1 => fun _ _ ↦ rfl
      map_strandIncl := fun _ _ ↦ by simp [tr']
      map_strandIncl_mul_e_last := fun _ _ ↦ rfl }
  exact congr_fun (htr.unique htr') (n + 1)

end IsMarkovTrace

end TauCeti.TemperleyLieb
