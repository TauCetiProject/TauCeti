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
`TauCeti.TemperleyLieb.IsMarkovTraceUpTo`, and proves the trace reduction for a last generator
sandwiched between two included elements. This reduction is used for the capped terms in the
tower's normal form and for quantum-dimension calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `n + 2` strands from its values on `n + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So there is at most one Markov trace up to `N` strands
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`) and hence at most one Markov trace on the full
tower (`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), over every commutative semiring. Truncated
path models on finite prefixes of the half-line define a Markov trace only up to `N` strands, and
`TauCeti.TemperleyLieb.IsMarkovTrace.eq_of_isMarkovTraceUpTo` identifies those values with any
global Markov trace. Likewise, rescaling a normalized strand-preserving tracial family `σ` by
`δ ^ n` gives an unnormalized Markov trace (`TauCeti.TemperleyLieb.isMarkovTrace_pow_smul`). This
file does not assert the existence of a Markov trace at every loop parameter.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace`: an unnormalized Markov trace on the full tower.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo`: an unnormalized Markov trace on `0, …, N` strands.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`,
  `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: bounded-level and global uniqueness of the Markov
  trace.
* `TauCeti.TemperleyLieb.isMarkovTrace_pow_smul`: rescaling a normalized tower trace by `δ ^ n`
  gives an unnormalized Markov trace.

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

/-- An **unnormalized Markov trace up to `N` strands** on the Temperley–Lieb tower: a family
of linear forms on `0, …, N` strands satisfying the normalization `tr n hn 1 = δ ^ n`,
traciality, strand-inclusion compatibility, and the Markov property as far as defined. -/
structure IsMarkovTraceUpTo (R : Type*) [CommSemiring R] (δ : R) (N : ℕ)
    (tr : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R) : Prop where
  /-- Normalization on the identity at each level `n ≤ N`. -/
  map_one : ∀ n (hn : n ≤ N), tr n hn 1 = δ ^ n
  /-- Traciality at each level `n ≤ N`. -/
  map_mul_comm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb R δ n),
    tr n hn (x * y) = tr n hn (y * x)
  /-- Adding a straight strand multiplies the trace by `δ`. -/
  map_strandIncl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x) = δ * tr (n + 1) (Nat.le_of_succ_le hn) x
  /-- Capping the added last strand with the last generator recovers the trace one level down. -/
  map_strandIncl_mul_e_last : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) hn (strandIncl x * e δ (Fin.last n)) = tr (n + 1) (Nat.le_of_succ_le hn) x

variable {R : Type*} [CommSemiring R] {δ : R}

namespace IsMarkovTraceUpTo

/-- Restricting a Markov trace up to `N` strands to `M ≤ N` strands gives a Markov trace up to
`M` strands. -/
theorem mono {M N : ℕ} {tr : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (hMN : M ≤ N) :
    IsMarkovTraceUpTo R δ M (fun n hn ↦ tr n (hn.trans hMN)) where
  map_one n hn := htr.map_one n (hn.trans hMN)
  map_mul_comm n hn := htr.map_mul_comm n (hn.trans hMN)
  map_strandIncl n hn := htr.map_strandIncl n (hn.trans hMN)
  map_strandIncl_mul_e_last n hn := htr.map_strandIncl_mul_e_last n (hn.trans hMN)

/-- The Markov property up to `N` strands for a last generator sandwiched between two included
elements. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul {N : ℕ}
    {tr : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn : n + 2 ≤ N)
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) hn (strandIncl a * e δ (Fin.last n) * strandIncl b) =
      tr (n + 1) (Nat.le_of_succ_le hn) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

/-- On at most one strand the algebra is the base ring, so a Markov trace up to `N` strands is
determined there by its normalization `tr n hn 1 = δ ^ n`. -/
private theorem eq_of_le_one {N : ℕ}
    {tr tr' : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTraceUpTo R δ N tr) (htr' : IsMarkovTraceUpTo R δ N tr')
    {n : ℕ} (hn : n ≤ N) (hn1 : n ≤ 1) :
    tr n hn = tr' n hn := by
  ext x
  rw [← (algEquivOfLeOne δ hn1).symm_apply_apply x, algEquivOfLeOne_symm_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, map_smul, htr.map_one, htr'.map_one]

/-- **Bounded-level uniqueness of the Markov trace.** Over every commutative semiring and at every
loop parameter, there is at most one unnormalized Markov trace up to `N` strands: on `n + 2 ≤ N`
strands it is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {N : ℕ} {tr tr' : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
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
    · rw [htr.map_strandIncl, htr'.map_strandIncl, ih (Nat.le_of_succ_le hn)]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr'.map_strandIncl_mul_e_last_mul,
        ih (Nat.le_of_succ_le hn)]

end IsMarkovTraceUpTo

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

namespace IsMarkovTrace

/-- Forgetting levels above `N` restricts a Markov trace to a Markov trace up to `N` strands. -/
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

/-- Any Markov trace agrees on `n ≤ N` strands with any Markov trace defined up to `N` strands. -/
theorem eq_of_isMarkovTraceUpTo {N : ℕ}
    {tr' : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTraceUpTo R δ N tr')
    {n : ℕ} (hn : n ≤ N) :
    tr n = tr' n hn :=
  congrFun (congrFun ((htr.isMarkovTraceUpTo N).unique htr') n) hn

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' := by
  funext n
  exact htr.eq_of_isMarkovTraceUpTo (htr'.isMarkovTraceUpTo n) le_rfl

end IsMarkovTrace

/-- A family of linear forms on the Temperley–Lieb tower is a Markov trace exactly when its
restriction to `0, …, N` strands is a Markov trace up to `N` strands for every `N`. -/
theorem isMarkovTrace_iff_forall_isMarkovTraceUpTo :
    IsMarkovTrace R δ tr ↔ ∀ N, IsMarkovTraceUpTo R δ N (fun n _ ↦ tr n) :=
  ⟨fun htr ↦ htr.isMarkovTraceUpTo, fun h ↦
    { map_one := fun n ↦ (h n).map_one n le_rfl
      map_mul_comm := fun n ↦ (h n).map_mul_comm n le_rfl
      map_strandIncl := fun n ↦ (h (n + 2)).map_strandIncl n le_rfl
      map_strandIncl_mul_e_last := fun n ↦ (h (n + 2)).map_strandIncl_mul_e_last n le_rfl }⟩

/-- Rescaling a family of normalized (`σ n 1 = 1`), strand-preserving tracial forms by `δ ^ n`
produces an unnormalized Markov trace whenever `δ * σ (n + 2) (strandIncl x * e δ (Fin.last n)) =
σ (n + 1) x`. In the Jones tower, where `e δ i` acts as `δ` times a Jones projection `p_i`, this
identity is the normalized Markov formula `tr (x * p_n) = δ⁻² * tr x` multiplied by `δ ^ 2`,
stated without assuming `δ` invertible. -/
theorem isMarkovTrace_pow_smul {σ : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (hone : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb R δ n), σ n (x * y) = σ n (y * x))
    (hincl : ∀ n (x : TemperleyLieb R δ (n + 1)), σ (n + 2) (strandIncl x) = σ (n + 1) x)
    (hmarkov : ∀ n (x : TemperleyLieb R δ (n + 1)),
      δ * σ (n + 2) (strandIncl x * e δ (Fin.last n)) = σ (n + 1) x) :
    IsMarkovTrace R δ (fun n ↦ (δ ^ n) • σ n) where
  map_one n := by simp [hone]
  map_mul_comm n x y := by simp [hcomm]
  map_strandIncl n x := by
    simp only [LinearMap.smul_apply, smul_eq_mul, hincl, pow_succ', mul_assoc]
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [pow_succ, mul_assoc, hmarkov]

/-- Every unnormalized Markov trace agrees with `δ ^ n • σ n` for any normalized,
strand-preserving tracial family `σ` satisfying `δ * σ (n + 2) (strandIncl x * e δ (Fin.last n)) =
σ (n + 1) x`. -/
theorem IsMarkovTrace.eq_pow_smul (htr : IsMarkovTrace R δ tr)
    {σ : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (hone : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb R δ n), σ n (x * y) = σ n (y * x))
    (hincl : ∀ n (x : TemperleyLieb R δ (n + 1)), σ (n + 2) (strandIncl x) = σ (n + 1) x)
    (hmarkov : ∀ n (x : TemperleyLieb R δ (n + 1)),
      δ * σ (n + 2) (strandIncl x * e δ (Fin.last n)) = σ (n + 1) x) :
    tr = fun n ↦ (δ ^ n) • σ n :=
  htr.unique (isMarkovTrace_pow_smul hone hcomm hincl hmarkov)

end TauCeti.TemperleyLieb
