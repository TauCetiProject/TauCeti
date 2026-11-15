/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.RingTheory.TraceFunctional.Positive
import TauCeti.Analysis.StarAlgebra.CauchySchwarz

/-!
# Positive Markov traces and their trace radicals

When a bounded-level or all-level Markov trace `tr` on the complex Temperley–Lieb tower at a
self-adjoint loop parameter `δ` is positive semidefinite at level `n` (`0 ≤ tr n (star x * x)` for
every `x`), its level-`n` component is a `TauCeti.StarPositiveFunctional`. Specializing the general
star-algebra Cauchy–Schwarz and trace-radical theory to `TemperleyLieb ℂ δ n` yields:

* the Cauchy–Schwarz inequality for `tr n (star x * y)`;
* the equality between the null vectors `{x | tr n (star x * x) = 0}` and the two-sided trace
  radical `(tr n).traceRadical`;
* the faithful positive trace `positiveQuotientTrace` directly on
  `TemperleyLieb ℂ δ n ⧸ (tr n).traceRadical` and its compatibility with `htr.quotientStrandIncl`.

These results apply at a single strand count `n`, so they cover both all-level admissible loop
parameters and levels `n < ⌊π / arccos (δ / 2)⌋₊` below the first bad level at inadmissible loop
parameters.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

section Bounded

variable {δ : ℂ} [Fact (IsSelfAdjoint δ)] {N : ℕ}
  {tr : ∀ n, n ≤ N → TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ}

namespace IsMarkovTraceUpTo

/-- Level `n ≤ N` of a bounded-level Markov trace bundled as a `StarPositiveFunctional` when its
Hermitian form is positive semidefinite at level `n`. -/
def starPositiveFunctional (_htr : IsMarkovTraceUpTo ℂ δ N tr) {n : ℕ} (hn : n ≤ N)
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n hn (star x * x)) :
    StarPositiveFunctional (TemperleyLieb ℂ δ n) where
  toLinearMap := tr n hn
  square_nonneg := hpos

/-- Forgetting positivity recovers the linear map `tr n hn`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTraceUpTo ℂ δ N tr) {n : ℕ}
    (hn : n ≤ N) (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n hn (star x * x)) :
    (htr.starPositiveFunctional hn hpos).toLinearMap = tr n hn := (rfl)

/-- Evaluating `starPositiveFunctional` evaluates `tr n hn`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTraceUpTo ℂ δ N tr) {n : ℕ} (hn : n ≤ N)
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n hn (star x * x))
    (x : TemperleyLieb ℂ δ n) :
    htr.starPositiveFunctional hn hpos x = tr n hn x := (rfl)

/-- **Cauchy–Schwarz inequality** for a bounded-level Markov trace at a positive semidefinite level
`n ≤ N`. -/
theorem norm_map_star_mul_sq_le (_htr : IsMarkovTraceUpTo ℂ δ N tr) {n : ℕ} (hn : n ≤ N)
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n hn (star x * x))
    (x y : TemperleyLieb ℂ δ n) :
    ‖tr n hn (star x * y)‖ ^ 2 ≤ ‖tr n hn (star x * x)‖ * ‖tr n hn (star y * y)‖ :=
  (tr n hn).norm_map_star_mul_sq_le hpos x y

/-- At a positive semidefinite level `n ≤ N` of a bounded-level Markov trace, the null vectors of
`x ↦ tr n hn (star x * x)` are precisely the two-sided trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical (htr : IsMarkovTraceUpTo ℂ δ N tr)
    {n : ℕ} (hn : n ≤ N) (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n hn (star x * x))
    {x : TemperleyLieb ℂ δ n} :
    tr n hn (star x * x) = 0 ↔ x ∈ (tr n hn).traceRadical (htr.map_mul_comm n hn) :=
  ((htr.starPositiveFunctional hn hpos).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n hn) x).symm

/-- At a positive semidefinite level `n ≤ N` of a bounded-level Markov trace,
`tr n hn (star x * x)` is strictly positive precisely when `x` does not lie in the trace
radical. -/
theorem map_star_mul_self_pos_iff_notMem_traceRadical (htr : IsMarkovTraceUpTo ℂ δ N tr)
    {n : ℕ} (hn : n ≤ N) (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n hn (star x * x))
    {x : TemperleyLieb ℂ δ n} :
    0 < tr n hn (star x * x) ↔ x ∉ (tr n hn).traceRadical (htr.map_mul_comm n hn) := by
  rw [← htr.map_star_mul_self_eq_zero_iff_mem_traceRadical hn hpos]
  exact ⟨fun h hz ↦ h.ne' hz, fun h ↦ (hpos x).lt_of_ne' h⟩

end IsMarkovTraceUpTo

end Bounded

namespace IsMarkovTrace

variable {δ : ℂ} [Fact (IsSelfAdjoint δ)]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ}

/-- Level `n` of a Markov trace bundled as a `StarPositiveFunctional` when its Hermitian form is
positive semidefinite at level `n`. -/
def starPositiveFunctional (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x)) :
    StarPositiveFunctional (TemperleyLieb ℂ δ n) :=
  (htr.isMarkovTraceUpTo n).starPositiveFunctional le_rfl hpos

/-- Forgetting positivity recovers the linear map `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x)) :
    (htr.starPositiveFunctional hpos).toLinearMap = tr n := (rfl)

/-- Evaluating `starPositiveFunctional` evaluates `tr n`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    (x : TemperleyLieb ℂ δ n) :
    htr.starPositiveFunctional hpos x = tr n x := (rfl)

/-- **Cauchy–Schwarz inequality** for a Markov trace at any positive semidefinite level `n`. -/
theorem norm_map_star_mul_sq_le (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    (x y : TemperleyLieb ℂ δ n) :
    ‖tr n (star x * y)‖ ^ 2 ≤ ‖tr n (star x * x)‖ * ‖tr n (star y * y)‖ :=
  (htr.isMarkovTraceUpTo n).norm_map_star_mul_sq_le le_rfl hpos x y

/-- At a positive semidefinite level `n`, the null vectors of `x ↦ tr n (star x * x)` are
precisely the two-sided trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    {x : TemperleyLieb ℂ δ n} :
    tr n (star x * x) = 0 ↔ x ∈ (tr n).traceRadical (htr.map_mul_comm n) :=
  (htr.isMarkovTraceUpTo n).map_star_mul_self_eq_zero_iff_mem_traceRadical le_rfl hpos

/-- At a positive semidefinite level `n`, `tr n (star x * x)` is strictly positive precisely when
`x` does not lie in the trace radical. -/
theorem map_star_mul_self_pos_iff_notMem_traceRadical (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    {x : TemperleyLieb ℂ δ n} :
    0 < tr n (star x * x) ↔ x ∉ (tr n).traceRadical (htr.map_mul_comm n) :=
  (htr.isMarkovTraceUpTo n).map_star_mul_self_pos_iff_notMem_traceRadical le_rfl hpos

/-- The faithful positive tracial functional induced on the trace-radical quotient
`TemperleyLieb ℂ δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)` at a positive semidefinite level
`n`. -/
def positiveQuotientTrace (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x)) :
    StarPositiveFunctional
      (TemperleyLieb ℂ δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) where
  toLinearMap := (tr n).quotientTrace (htr.map_mul_comm n)
  square_nonneg q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simpa only [Ideal.Quotient.star_mk, ← map_mul, LinearMap.quotientTrace_mk] using hpos x

/-- Forgetting positivity of `positiveQuotientTrace` recovers `(tr n).quotientTrace`. -/
@[simp]
theorem toLinearMap_positiveQuotientTrace (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x)) :
    (htr.positiveQuotientTrace hpos).toLinearMap = (tr n).quotientTrace (htr.map_mul_comm n) :=
  (rfl)

/-- Evaluating `positiveQuotientTrace` on a quotient class evaluates `tr n` on its
representative. -/
@[simp]
theorem positiveQuotientTrace_mk (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    (x : TemperleyLieb ℂ δ n) :
    htr.positiveQuotientTrace hpos
        (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
      tr n x :=
  (tr n).quotientTrace_mk (htr.map_mul_comm n) x

/-- Value of `positiveQuotientTrace` on the identity of the quotient algebra. -/
@[simp]
theorem positiveQuotientTrace_one (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x)) :
    htr.positiveQuotientTrace hpos 1 = δ ^ n :=
  ((tr n).quotientTrace_one (htr.map_mul_comm n)).trans (htr.map_one n)

/-- Traciality of `positiveQuotientTrace` on the trace-radical quotient. -/
theorem positiveQuotientTrace_mul_comm (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    (x y : TemperleyLieb ℂ δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.positiveQuotientTrace hpos (x * y) = htr.positiveQuotientTrace hpos (y * x) :=
  (tr n).quotientTrace_mul_comm (htr.map_mul_comm n) x y

/-- When levels `n + 1` and `n + 2` are positive semidefinite, `positiveQuotientTrace` scales by
`δ` along `htr.quotientStrandIncl`. -/
@[simp]
theorem positiveQuotientTrace_quotientStrandIncl (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (hpos₁ : ∀ x : TemperleyLieb ℂ δ (n + 1), 0 ≤ tr (n + 1) (star x * x))
    (hpos₂ : ∀ x : TemperleyLieb ℂ δ (n + 2), 0 ≤ tr (n + 2) (star x * x))
    (q : TemperleyLieb ℂ δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.positiveQuotientTrace hpos₂ (htr.quotientStrandIncl n q) =
      δ * htr.positiveQuotientTrace hpos₁ q :=
  htr.quotientTrace_quotientStrandIncl n q

/-- Faithfulness of `positiveQuotientTrace` on squares in the trace-radical quotient. -/
@[simp]
theorem positiveQuotientTrace_star_mul_self_eq_zero_iff (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x))
    (q : TemperleyLieb ℂ δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.positiveQuotientTrace hpos (star q * q) = 0 ↔ q = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.star_mk, ← map_mul, htr.positiveQuotientTrace_mk,
    htr.map_star_mul_self_eq_zero_iff_mem_traceRadical hpos, Ideal.Quotient.eq_zero_iff_mem]

/-- The positive quotient trace has trivial GNS null space. -/
theorem nullSubmodule_positiveQuotientTrace (htr : IsMarkovTrace ℂ δ tr) {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (hpos : ∀ x : TemperleyLieb ℂ δ n, 0 ≤ tr n (star x * x)) :
    (htr.positiveQuotientTrace hpos).nullSubmodule = ⊥ := by
  ext q
  simp only [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    htr.positiveQuotientTrace_star_mul_self_eq_zero_iff hpos, Submodule.mem_bot]

end IsMarkovTrace

end TauCeti.TemperleyLieb
