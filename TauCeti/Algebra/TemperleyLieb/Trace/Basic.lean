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
Because this recursion up to `N` strands never inspects higher levels, Markov traces defined only
up to `N` strands (`TauCeti.TemperleyLieb.IsMarkovTraceUpTo`) are already unique
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), which implies uniqueness of all-level Markov
traces (`TauCeti.TemperleyLieb.IsMarkovTrace.unique`) over every commutative semiring. Conversely,
rescaling normalized functionals pulled back along a tower of algebra maps gives a Markov trace
(`TauCeti.TemperleyLieb.isMarkovTrace_of_pullback`). This file does not assert the existence of a
Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace defined on `0, …, N`
  strands.
* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on the full Temperley–Lieb
  tower.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_strandIncl_mul_e_last_mul` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of bounded-level and all-level Markov
  traces.
* `TauCeti.TemperleyLieb.isMarkovTrace_of_pullback` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.pullback_eq`: constructing and identifying Markov traces
  from normalized functionals on a target tower.

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
linear forms on `0, …, N` strands satisfying `tr n hn 1 = δ ^ n`, traciality, strand-inclusion
compatibility, and the Markov property whenever the strand counts are at most `N`. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n (hn : n ≤ N), tr n hn 1 = δ ^ n
  map_mul_comm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n),
    tr n hn (x * y) = tr n hn (y * x)
  map_strandIncl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x) = δ * tr (n + 1) (Nat.le_of_succ_le hn) x
  map_strandIncl_mul_e_last : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x * e δ (Fin.last n)) = tr (n + 1) (Nat.le_of_succ_le hn) x

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

variable {N : ℕ} {tr : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}

/-- Restricting a Markov trace up to `N` strands to `M ≤ N` strands gives a Markov trace up to
`M` strands. -/
theorem mono {M : ℕ} (htr : IsMarkovTraceUpTo R δ N tr) (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M (fun n hn ↦ tr n (hn.trans hMN)) where
  map_one n hn := htr.map_one n (hn.trans hMN)
  map_mul_comm n hn := htr.map_mul_comm n (hn.trans hMN)
  map_strandIncl n hn := htr.map_strandIncl n (hn.trans hMN)
  map_strandIncl_mul_e_last n hn := htr.map_strandIncl_mul_e_last n (hn.trans hMN)

/-- The Markov property up to `N` strands for a last generator sandwiched between two included
elements. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ}
    (hn : n + 2 ≤ N) (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) hn (strandIncl a * e δ (Fin.last n) * strandIncl b) =
      tr (n + 1) (Nat.le_of_succ_le hn) (a * b) := by
  rw [htr.map_mul_comm (n + 2) hn, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last n hn,
    htr.map_mul_comm (n + 1)]

/-- On at most one strand the algebra is the base ring, so a bounded-level Markov trace is
determined there by its normalization `tr n hn 1 = δ ^ n`. -/
private theorem eq_of_le_one {tr' : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') {n : ℕ}
    (hn : n ≤ N) (hn1 : n ≤ 1) : tr n hn = tr' n hn := by
  ext x
  rw [← (algEquivOfLeOne δ hn1).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, htr'.map_one]

/-- **Uniqueness of bounded-level Markov traces.** Over every commutative semiring and at every
loop parameter, there is at most one unnormalized Markov trace up to `N` strands. -/
theorem unique {tr' : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr') :
    tr = tr' := by
  funext n hn
  obtain _ | n := n
  · exact eq_of_le_one htr htr' hn (Nat.zero_le _)
  induction n with
  | zero => exact eq_of_le_one htr htr' hn le_rfl
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, htr'.map_strandIncl, ih (Nat.le_of_succ_le hn)]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr'.map_strandIncl_mul_e_last_mul,
        ih (Nat.le_of_succ_le hn)]

end IsMarkovTraceUpTo

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- Restricting an all-level Markov trace to `0, …, N` strands gives a Markov trace up to `N`
strands. -/
theorem isMarkovTraceUpTo (htr : IsMarkovTrace R δ tr) (N : ℕ) :
    IsMarkovTraceUpTo R δ N (fun n _ ↦ tr n) where
  map_one n _ := htr.map_one n
  map_mul_comm n _ := htr.map_mul_comm n
  map_strandIncl n _ := htr.map_strandIncl n
  map_strandIncl_mul_e_last n _ := htr.map_strandIncl_mul_e_last n

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) :=
  (htr.isMarkovTraceUpTo (n + 2)).map_strandIncl_mul_e_last_mul le_rfl a b

/-- An all-level Markov trace agrees on `n ≤ N` strands with any Markov trace defined up to `N`
strands. -/
theorem eq_of_isMarkovTraceUpTo {N : ℕ} {tr' : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTraceUpTo R δ N tr') {n : ℕ} (hn : n ≤ N) :
    tr n = tr' n hn :=
  congrFun₂ ((htr.isMarkovTraceUpTo N).unique htr') n hn

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' := by
  funext n
  exact htr.eq_of_isMarkovTraceUpTo (htr'.isMarkovTraceUpTo n) le_rfl

end IsMarkovTrace

section Pullback

variable {dinv : R} {B : ℕ → Type*} [∀ n, Semiring (B n)] [∀ n, Algebra R (B n)]
  (ρ : ∀ n, TemperleyLieb R δ n →ₐ[R] B n) (σ : ∀ n, B n →ₗ[R] R)

/-- Pulling normalized linear forms `σ n` back along algebra maps `ρ n` and rescaling by `δ ^ n`
produces an unnormalized Markov trace whenever `δ * dinv = 1`, `σ 0 1 = 1`, `σ 1 1 = 1`, each
`σ n` is tracial on the image of `ρ n`, strand inclusion preserves `σ`, and capping with the last
generator multiplies `σ` by `dinv`. Neither injectivity of `ρ n` nor traciality of `σ n` outside
the image of `ρ n` is required. -/
theorem isMarkovTrace_of_pullback (hδ : δ * dinv = 1)
    (hone : ∀ n, n ≤ 1 → σ n 1 = 1)
    (hmul : ∀ n (x y : TemperleyLieb R δ n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hstrand : ∀ n (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x * e δ (Fin.last n))) =
        dinv * σ (n + 1) (ρ (n + 1) x)) :
    IsMarkovTrace R δ (fun n ↦ (δ ^ n) • (σ n ∘ₗ (ρ n).toLinearMap)) where
  map_one := by
    have hone_all : ∀ n, σ n 1 = 1 := by
      intro n
      obtain _ | n := n
      · exact hone 0 (Nat.zero_le _)
      induction n with
      | zero => exact hone 1 le_rfl
      | succ n ih =>
        simpa using (hstrand n 1).trans (by simpa using ih)
    intro n
    simp [hone_all]
  map_mul_comm n x y := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      smul_eq_mul, hmul]
  map_strandIncl n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      hstrand, pow_succ', mul_assoc]
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      hmarkov]
    calc
      δ ^ (n + 2) * (dinv * σ (n + 1) (ρ (n + 1) x)) =
          δ ^ (n + 1) * (δ * dinv) * σ (n + 1) (ρ (n + 1) x) := by
        rw [pow_succ]
        ring
      _ = δ ^ (n + 1) * σ (n + 1) (ρ (n + 1) x) := by rw [hδ, mul_one]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- Under the normalized tower pullback hypotheses, every Markov trace equals `δ ^ n` times the
pulled-back functional at level `n`. -/
theorem eq_mul_of_pullback (htr : IsMarkovTrace R δ tr) (hδ : δ * dinv = 1)
    (hone : ∀ n, n ≤ 1 → σ n 1 = 1)
    (hmul : ∀ n (x y : TemperleyLieb R δ n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hstrand : ∀ n (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x * e δ (Fin.last n))) =
        dinv * σ (n + 1) (ρ (n + 1) x))
    (n : ℕ) (x : TemperleyLieb R δ n) :
    tr n x = δ ^ n * σ n (ρ n x) := by
  have heq := htr.unique (isMarkovTrace_of_pullback ρ σ hδ hone hmul hstrand hmarkov)
  exact LinearMap.congr_fun (congrFun heq n) x

/-- Under the normalized tower pullback hypotheses, the pulled-back functional `σ n ∘ ρ n` equals
`dinv ^ n` times any Markov trace `tr n`. -/
theorem pullback_eq (htr : IsMarkovTrace R δ tr) (hδ : δ * dinv = 1)
    (hone : ∀ n, n ≤ 1 → σ n 1 = 1)
    (hmul : ∀ n (x y : TemperleyLieb R δ n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hstrand : ∀ n (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb R δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x * e δ (Fin.last n))) =
        dinv * σ (n + 1) (ρ (n + 1) x))
    (n : ℕ) (x : TemperleyLieb R δ n) :
    σ n (ρ n x) = dinv ^ n * tr n x := by
  rw [htr.eq_mul_of_pullback ρ σ hδ hone hmul hstrand hmarkov, ← mul_assoc, ← mul_pow,
    mul_comm dinv δ, hδ, one_pow, one_mul]

end IsMarkovTrace

end Pullback

end TauCeti.TemperleyLieb
