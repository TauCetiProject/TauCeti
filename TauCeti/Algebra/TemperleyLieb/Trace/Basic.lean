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

This file defines both global Markov traces (`TauCeti.TemperleyLieb.IsMarkovTrace`) and truncated
Markov traces defined up to a finite strand bound `N` (`TauCeti.TemperleyLieb.IsMarkovTraceUpTo`),
and proves the trace reduction for a last generator sandwiched between two included elements. This
reduction is used for the capped terms in the tower's normal form and for quantum-dimension
calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `n + 2` strands from its values on `n + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So there is at most one Markov trace up to any level `N`
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), and hence at most one global Markov trace at
each loop parameter (`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), over every commutative
semiring. This file does not assert the existence of a Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on all strand levels.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace defined up to a finite
  number of strands `N`.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_strandIncl_mul_e_last_mul`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.eq_of_isMarkovTraceUpTo`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of truncated and global Markov traces.

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

/-- An **unnormalized Markov trace up to level `N`**: a family of linear forms on
`TemperleyLieb R δ n` for `n ≤ N` satisfying the normalization, traciality, strand-inclusion
compatibility, and Markov property up to `N` strands. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n (hn : n ≤ N), tr n hn 1 = δ ^ n
  map_mul_comm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n),
    tr n hn (x * y) = tr n hn (y * x)
  map_strandIncl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x) = δ * tr (n + 1) (Nat.le_of_succ_le hn) x
  map_strandIncl_mul_e_last : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x * e δ (Fin.last n)) = tr (n + 1) (Nat.le_of_succ_le hn) x

variable {R : Type*} [CommSemiring R] {δ : R}

namespace IsMarkovTraceUpTo

variable {N : ℕ} {tr : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}

/-- The Markov property for a last generator sandwiched between two included elements, up to
level `N`. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ}
    (hn : n + 2 ≤ N) (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) hn (strandIncl a * e δ (Fin.last n) * strandIncl b) =
      tr (n + 1) (Nat.le_of_succ_le hn) (a * b) := by
  rw [htr.map_mul_comm _ hn, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last _ hn,
    htr.map_mul_comm]

/-- A truncated Markov trace up to level `N` restricts to any smaller level `M ≤ N`. -/
theorem mono (htr : IsMarkovTraceUpTo R δ N tr) {M : ℕ} (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M fun n hn ↦ tr n (hn.trans hMN) where
  map_one n hn := htr.map_one n (hn.trans hMN)
  map_mul_comm n hn := htr.map_mul_comm n (hn.trans hMN)
  map_strandIncl n hn := htr.map_strandIncl n (hn.trans hMN)
  map_strandIncl_mul_e_last n hn := htr.map_strandIncl_mul_e_last n (hn.trans hMN)

/-- On at most one strand the algebra is the base ring, so a truncated Markov trace is determined
there by its normalization `tr n hn 1 = δ ^ n`. -/
private theorem eq_of_le_one {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr')
    {n : ℕ} (hnN : n ≤ N) (hn : n ≤ 1) : tr n hnN = tr' n hnN := by
  ext x
  rw [← (algEquivOfLeOne δ hn).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, htr'.map_one]

/-- **Uniqueness of truncated Markov traces.** Over every commutative semiring and at every loop
parameter there is at most one unnormalized Markov trace up to level `N`: on `n + 2` strands it is
determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') : tr = tr' := by
  funext n hn
  obtain _ | n := n
  · exact eq_of_le_one htr htr' hn (by omega)
  induction n with
  | zero => exact eq_of_le_one htr htr' hn le_rfl
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl _ hn, htr'.map_strandIncl _ hn, ih (by omega)]
    · rw [htr.map_strandIncl_mul_e_last_mul hn, htr'.map_strandIncl_mul_e_last_mul hn,
        ih (by omega)]

/-- Any two truncated Markov traces agree at every common strand level. -/
theorem eq_of_le {N₁ N₂ : ℕ} {tr₁ : ∀ n ≤ N₁, TemperleyLieb R δ n →ₗ[R] R}
    {tr₂ : ∀ n ≤ N₂, TemperleyLieb R δ n →ₗ[R] R}
    (htr₁ : IsMarkovTraceUpTo R δ N₁ tr₁) (htr₂ : IsMarkovTraceUpTo R δ N₂ tr₂)
    {n : ℕ} (hn₁ : n ≤ N₁) (hn₂ : n ≤ N₂) : tr₁ n hn₁ = tr₂ n hn₂ :=
  congrFun (congrFun ((htr₁.mono hn₁).unique (htr₂.mono hn₂)) n) le_rfl

end IsMarkovTraceUpTo

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- A family of linear forms on all strand levels is a global Markov trace exactly when its
truncation up to every finite level `N` is a truncated Markov trace. -/
theorem isMarkovTrace_iff_forall_isMarkovTraceUpTo :
    IsMarkovTrace R δ tr ↔ ∀ N, IsMarkovTraceUpTo R δ N (fun n _ ↦ tr n) :=
  ⟨fun h _ ↦ ⟨fun n _ ↦ h.map_one n, fun n _ ↦ h.map_mul_comm n, fun n _ ↦ h.map_strandIncl n,
      fun n _ ↦ h.map_strandIncl_mul_e_last n⟩,
    fun h ↦ ⟨fun n ↦ (h n).map_one n le_rfl, fun n ↦ (h n).map_mul_comm n le_rfl,
      fun n ↦ (h (n + 2)).map_strandIncl n le_rfl,
      fun n ↦ (h (n + 2)).map_strandIncl_mul_e_last n le_rfl⟩⟩

namespace IsMarkovTrace

/-- A global Markov trace restricts to a truncated Markov trace up to every level `N`. -/
theorem isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) (N : ℕ) :
    IsMarkovTraceUpTo R δ N (fun n _ ↦ tr n) :=
  isMarkovTrace_iff_forall_isMarkovTraceUpTo.1 htr N

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) :=
  (htr.isMarkovTraceUpTo (n + 2)).map_strandIncl_mul_e_last_mul le_rfl a b

/-- A global Markov trace agrees with any truncated Markov trace up to level `N` on every level
`n ≤ N`. -/
theorem eq_of_isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) {N : ℕ}
    {tr' : ∀ n ≤ N, TemperleyLieb R δ n →ₗ[R] R} (htr' : IsMarkovTraceUpTo R δ N tr')
    {n : ℕ} (hn : n ≤ N) : tr n = tr' n hn :=
  congrFun (congrFun ((htr.isMarkovTraceUpTo N).unique htr') n) hn

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' :=
  funext fun n ↦ htr.eq_of_isMarkovTraceUpTo (htr'.isMarkovTraceUpTo n) le_rfl

end IsMarkovTrace

end TauCeti.TemperleyLieb
