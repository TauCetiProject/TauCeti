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
So there is at most one Markov trace at each loop parameter, both on the whole tower
(`TauCeti.TemperleyLieb.IsMarkovTrace.unique`) and on any finite initial segment up to `N` strands
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), over every commutative semiring. This file does
not assert the existence of a Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace defined up to `N` strands.
* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on the full tower.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_strandIncl_mul_e_last_mul`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of the Markov trace, up to `N` strands
  and on the full tower.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.eq_zero_of_loop_eq_zero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.eq_zero_of_loop_eq_zero`: at loop parameter `0`, a Markov
  trace vanishes on every positive number of strands.
* `TauCeti.TemperleyLieb.isMarkovTraceUpTo_smul_pow`,
  `TauCeti.TemperleyLieb.isMarkovTrace_smul_pow`: scaling a normalized Markov family by `δ ^ n`
  produces an unnormalized Markov trace.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

/-- An **unnormalized Markov trace up to `N` strands**: a family of linear forms defined for
`n ≤ N` with `tr n hn 1 = δ ^ n`, traciality, strand-inclusion compatibility, and the Markov
property within that range. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n (hn : n ≤ N), tr n hn 1 = δ ^ n
  map_mul_comm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n),
    tr n hn (x * y) = tr n hn (y * x)
  map_strandIncl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x) = δ * tr (n + 1) (by omega) x
  map_strandIncl_mul_e_last : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x * e δ (Fin.last n)) = tr (n + 1) (by omega) x

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

variable {N : ℕ} {tr : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}

/-- The Markov property for a last generator sandwiched between two included elements, within a
truncated Markov trace. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ}
    (hn : n + 2 ≤ N) (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) hn (strandIncl a * e δ (Fin.last n) * strandIncl b) =
      tr (n + 1) (by omega) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

/-- Restricting a truncated Markov trace to a smaller bound `M ≤ N` gives a truncated Markov trace
up to `M` strands. -/
theorem mono (htr : IsMarkovTraceUpTo R δ N tr) {M : ℕ} (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M fun n hn ↦ tr n (hn.trans hMN) where
  map_one n hn := htr.map_one n (hn.trans hMN)
  map_mul_comm n hn x y := htr.map_mul_comm n (hn.trans hMN) x y
  map_strandIncl n hn x := htr.map_strandIncl n (hn.trans hMN) x
  map_strandIncl_mul_e_last n hn x := htr.map_strandIncl_mul_e_last n (hn.trans hMN) x

/-- On at most one strand the algebra is the base ring, so a truncated Markov trace is determined
there by its normalization `tr n hn 1 = δ ^ n`. -/
private theorem eq_of_le_one {tr' : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') {n : ℕ}
    (hn : n ≤ N) (hn₁ : n ≤ 1) : tr n hn = tr' n hn := by
  ext x
  rw [← (algEquivOfLeOne δ hn₁).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, htr'.map_one]

/-- **Uniqueness of the truncated Markov trace.** Over every commutative semiring and at every loop
parameter there is at most one unnormalized Markov trace up to `N` strands: on `n + 2 ≤ N` strands
it is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') : tr = tr' := by
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

/-- At loop parameter `0`, a truncated Markov trace vanishes on every positive number of strands. -/
theorem eq_zero_of_loop_eq_zero (htr : IsMarkovTraceUpTo R δ N tr) (hδ : δ = 0) {n : ℕ}
    (hn₀ : 0 < n) (hn : n ≤ N) : tr n hn = 0 := by
  subst hδ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    ext x
    rw [← (algEquivOfLeOne (0 : R) le_rfl).symm_apply_apply x, algEquivOfLeOne_symm_apply,
      Algebra.algebraMap_eq_smul_one, map_smul, htr.map_one, pow_one, smul_zero,
      LinearMap.zero_apply]
  | succ m ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top m) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · simp [htr.map_strandIncl]
    · simp [htr.map_strandIncl_mul_e_last_mul, ih (by omega)]

end IsMarkovTraceUpTo

/-- Scaling a normalized Markov family defined up to `N` strands by `δ ^ n` produces an
unnormalized truncated Markov trace. -/
theorem isMarkovTraceUpTo_smul_pow {N : ℕ}
    {σ : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (h1 : ∀ n (hn : n ≤ N), σ n hn 1 = 1)
    (hcomm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n), σ n hn (x * y) = σ n hn (y * x))
    (hincl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) hn (strandIncl x) = σ (n + 1) (by omega) x)
    (hmarkov : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
      δ * σ (n + 2) hn (strandIncl x * e δ (Fin.last n)) = σ (n + 1) (by omega) x) :
    IsMarkovTraceUpTo R δ N fun n hn ↦ δ ^ n • σ n hn where
  map_one n hn := by simp [h1 n hn]
  map_mul_comm n hn x y := by simp [hcomm n hn x y]
  map_strandIncl n hn x := by
    simp only [LinearMap.smul_apply, smul_eq_mul, hincl n hn x, pow_succ', mul_assoc]
  map_strandIncl_mul_e_last n hn x := by
    simp only [LinearMap.smul_apply, smul_eq_mul, pow_succ, mul_assoc, hmarkov n hn x]

/-- Scaling a normalized Markov family on the full tower by `δ ^ n` produces an unnormalized Markov
trace. -/
theorem isMarkovTrace_smul_pow {σ : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (h1 : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb R δ n), σ n (x * y) = σ n (y * x))
    (hincl : ∀ n (x : TemperleyLieb R δ (n + 1)), σ (n + 2) (strandIncl x) = σ (n + 1) x)
    (hmarkov : ∀ n (x : TemperleyLieb R δ (n + 1)),
      δ * σ (n + 2) (strandIncl x * e δ (Fin.last n)) = σ (n + 1) x) :
    IsMarkovTrace R δ fun n ↦ δ ^ n • σ n where
  map_one n := by simp [h1 n]
  map_mul_comm n x y := by simp [hcomm n x y]
  map_strandIncl n x := by
    simp only [LinearMap.smul_apply, smul_eq_mul, hincl n x, pow_succ', mul_assoc]
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, smul_eq_mul, pow_succ, mul_assoc, hmarkov n x]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- Restricting a full Markov trace to degrees `n ≤ N` gives a truncated Markov trace up to `N`
strands. -/
theorem isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) (N : ℕ) :
    IsMarkovTraceUpTo R δ N fun n _ ↦ tr n where
  map_one n _ := htr.map_one n
  map_mul_comm n _ x y := htr.map_mul_comm n x y
  map_strandIncl n _ x := htr.map_strandIncl n x
  map_strandIncl_mul_e_last n _ x := htr.map_strandIncl_mul_e_last n x

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) :=
  (htr.isMarkovTraceUpTo (n + 2)).map_strandIncl_mul_e_last_mul le_rfl a b

/-- A full Markov trace agrees with any truncated Markov trace up to `N` strands on every degree
`n ≤ N`. -/
theorem eq_of_isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) {N : ℕ}
    {tr' : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr' : IsMarkovTraceUpTo R δ N tr') {n : ℕ} (hn : n ≤ N) :
    tr n = tr' n hn :=
  congrFun (congrFun ((htr.isMarkovTraceUpTo N).unique htr') n) hn

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' :=
  funext fun n ↦ htr.eq_of_isMarkovTraceUpTo (htr'.isMarkovTraceUpTo n) le_rfl

/-- At loop parameter `0`, a Markov trace vanishes on every positive number of strands. -/
theorem eq_zero_of_loop_eq_zero (htr : IsMarkovTrace R δ tr) (hδ : δ = 0) {n : ℕ}
    (hn : 0 < n) : tr n = 0 :=
  (htr.isMarkovTraceUpTo n).eq_zero_of_loop_eq_zero hδ hn le_rfl

end IsMarkovTrace

end TauCeti.TemperleyLieb
