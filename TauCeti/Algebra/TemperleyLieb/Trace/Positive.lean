/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.Analysis.StarAlgebra.CauchySchwarz
public import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# Positive Markov traces, Jones quotients, and the pullback criterion

At a real loop parameter `δ`, `TauCeti.Algebra.TemperleyLieb.Positivity` determines when the
Hermitian forms `H_n(x, y) = tr n (x⋆ * y)` of a Markov trace on `TemperleyLieb ℂ (δ : ℂ) n` are
positive semidefinite: on all numbers of strands for `δ ∈ jonesLoopParameters`, and below the
first bad level `n < ⌊π / arccos (δ / 2)⌋` for inadmissible `δ > 0`. This file packages those
positive forms as `TauCeti.StarPositiveFunctional`s and derives their consequences for the trace
radicals, the positive Jones quotients, and star representations into operator or tower algebras:

1. **Cauchy–Schwarz and radical characterization.** Whenever the level-`n` form is positive
   semidefinite (for `δ ∈ jonesLoopParameters`, or for `0 < δ ∉ jonesLoopParameters` and
   `n < ⌊π / arccos (δ / 2)⌋`), `tr n` satisfies Cauchy–Schwarz and its trace radical equals the
   null cone `{x : tr n (x⋆ * x) = 0}`.
2. **Positive and normalized traces on the Jones quotients.** For `δ ∈ jonesLoopParameters`, the
   quotient `Q_n = TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical` carries both the unnormalized
   positive trace `positiveQuotientTrace` and the normalized faithful tracial state
   `normalizedPositiveQuotientTrace` (`= δ⁻ⁿ • positiveQuotientTrace`), which is preserved on the
   nose by the injective `⋆`-homomorphisms `quotientStrandInclStarAlgHom` and satisfies the
   normalized Markov identity with factor `(δ ^ 2)⁻¹` on the Jones projection
   `δ⁻¹ • e (Fin.last n)`.
3. **Pullback criteria and representation kernels.** If `δ > 0` and compatible `⋆`-homomorphisms
   `ρ_n : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B_n` pull positive functionals `σ_n` back to
   `δ⁻ⁿ • tr n` (or satisfy the normalized tower Markov identities directly, without assuming an
   ambient `tr` or injectivity of `ρ_n`), then `δ ∈ jonesLoopParameters`. When `σ_n` has trivial
   GNS null space, `RingHom.ker ρ_n` equals the trace radical `(tr n).traceRadical`.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctional`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctionalOfLtFloor`: `tr n` bundled as a
  `StarPositiveFunctional` at admissible `δ` or below `⌊π / arccos (δ / 2)⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.positiveQuotientTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedPositiveQuotientTrace`: the unnormalized and
  normalized faithful positive traces on the Jones quotients `TemperleyLieb ℂ (δ : ℂ) n ⧸ R_n`.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_traceRadical_iff_map_star_mul_self_eq_zero_of_mem`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.mem_traceRadical_iff_map_star_mul_self_eq_zero_of_lt_floor`:
  `{x : tr n (x⋆ * x) = 0} = (tr n).traceRadical`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedPositiveQuotientTrace_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedPositiveQuotientTrace_mul_jonesProj`: strand
  invariance and the `(δ ^ 2)⁻¹` Markov formula on the positive Jones quotients.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_pullback`,
  `TauCeti.TemperleyLieb.mem_jonesLoopParameters_of_tower_pullback`: the pullback criteria forcing
  `δ ∈ jonesLoopParameters` without injectivity of `ρ_n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.ker_eq_traceRadical_of_pullback`: `ker ρ_n = R_n` for a
  faithful target functional.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones and V. S. Sunder, *Introduction to Subfactors*, LMS Lecture Note Series 234,
  Cambridge University Press, 1997, Theorem 2.3.8.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.3–4.5.
-/

public section

noncomputable section

open Real
open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

section PositiveForm

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

namespace IsMarkovTrace

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Markov trace on `n` strands as
a `TauCeti.StarPositiveFunctional`. -/
def starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters)
    (n : ℕ) : StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg x :=
    (htr.forall_map_star_mul_self_nonneg_iff (pos_of_mem_jonesLoopParameters hδ)).2 hδ n x

/-- Evaluating `starPositiveFunctional` gives `tr n`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctional hδ n x = tr n x :=
  (rfl)

/-- Forgetting positivity recovers `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.starPositiveFunctional hδ n).toLinearMap = tr n :=
  (rfl)

/-- Below the first bad level `n < ⌊π / arccos (δ / 2)⌋` at an inadmissible loop parameter
`δ > 0`, the Markov trace on `n` strands as a `TauCeti.StarPositiveFunctional`. -/
def starPositiveFunctionalOfLtFloor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg x := htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ hn x

/-- Evaluating `starPositiveFunctionalOfLtFloor` gives `tr n`. -/
@[simp]
theorem starPositiveFunctionalOfLtFloor_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctionalOfLtFloor hδ hδJ hn x = tr n x :=
  (rfl)

/-- Forgetting positivity recovers `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctionalOfLtFloor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊) :
    (htr.starPositiveFunctionalOfLtFloor hδ hδJ hn).toLinearMap = tr n :=
  (rfl)

/-- **Cauchy–Schwarz** for the Hermitian form of a Markov trace at an admissible loop parameter. -/
theorem norm_map_star_mul_sq_le_of_mem (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖tr n (star x * y)‖ ^ 2 ≤ ‖tr n (star x * x)‖ * ‖tr n (star y * y)‖ :=
  (tr n).norm_map_star_mul_sq_le (htr.starPositiveFunctional hδ n).square_nonneg x y

/-- **Cauchy–Schwarz** for the Hermitian form of a Markov trace below the first bad level
`⌊π / arccos (δ / 2)⌋`. -/
theorem norm_map_star_mul_sq_le_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖tr n (star x * y)‖ ^ 2 ≤ ‖tr n (star x * x)‖ * ‖tr n (star y * y)‖ :=
  (tr n).norm_map_star_mul_sq_le
    (htr.starPositiveFunctionalOfLtFloor hδ hδJ hn).square_nonneg x y

/-- At an admissible loop parameter, the trace radical on `n` strands is precisely the null cone
`{x : tr n (x⋆ * x) = 0}` of the Hermitian Markov trace form. -/
theorem mem_traceRadical_iff_map_star_mul_self_eq_zero_of_mem (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ tr n (star x * x) = 0 :=
  (htr.starPositiveFunctional hδ n).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n) x

/-- Below the first bad level `⌊π / arccos (δ / 2)⌋` at an inadmissible loop parameter `δ > 0`,
the trace radical on `n` strands is precisely `{x : tr n (x⋆ * x) = 0}`. -/
theorem mem_traceRadical_iff_map_star_mul_self_eq_zero_of_lt_floor
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : n < ⌊π / arccos (δ / 2)⌋₊) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ tr n (star x * x) = 0 :=
  (htr.starPositiveFunctionalOfLtFloor hδ hδJ hn).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n) x

section Quotient

/-- At an admissible loop parameter, the unnormalized faithful positive trace induced on the
Jones quotient `TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical`. -/
def positiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters)
    (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    StarPositiveFunctional
      (TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :=
  (htr.starPositiveFunctional hδ n).quotientTrace (htr.map_mul_comm n)

/-- Forgetting positivity recovers the algebraic quotient trace. -/
@[simp]
theorem toLinearMap_positiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.positiveQuotientTrace hδ n).toLinearMap = (tr n).quotientTrace (htr.map_mul_comm n) :=
  (htr.starPositiveFunctional hδ n).toLinearMap_quotientTrace (htr.map_mul_comm n)

/-- Evaluating `positiveQuotientTrace` on a quotient class evaluates `tr n` on its
representative. -/
@[simp]
theorem positiveQuotientTrace_mk (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters)
    (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] (a : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.positiveQuotientTrace hδ n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) a) = tr n a :=
  (htr.starPositiveFunctional hδ n).quotientTrace_mk (htr.map_mul_comm n) a

/-- A square in the positive Jones quotient has zero trace if and only if its argument vanishes. -/
@[simp]
theorem positiveQuotientTrace_star_mul_self_eq_zero_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.positiveQuotientTrace hδ n (star x * x) = 0 ↔ x = 0 :=
  (htr.starPositiveFunctional hδ n).quotientTrace_star_mul_self_eq_zero_iff
    (htr.map_mul_comm n) x

/-- The unnormalized positive quotient trace has trivial GNS null space. -/
theorem nullSubmodule_positiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.positiveQuotientTrace hδ n).nullSubmodule = ⊥ :=
  (htr.starPositiveFunctional hδ n).nullSubmodule_quotientTrace (htr.map_mul_comm n)

/-- At an admissible loop parameter, the normalized faithful positive trace `δ⁻ⁿ • tr n` on the
Jones quotient `TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical`. Unlike the unnormalized trace,
it takes the value `1` at the identity and is preserved on the nose by strand inclusion. -/
def normalizedPositiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    StarPositiveFunctional
      (TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) where
  toLinearMap := ((δ : ℂ)⁻¹ ^ n) • (htr.positiveQuotientTrace hδ n).toLinearMap
  square_nonneg x := by
    have hδ0 : 0 ≤ (((δ⁻¹) ^ n : ℝ) : ℂ) :=
      Complex.zero_le_real.2 (pow_nonneg (inv_nonneg.2 (pos_of_mem_jonesLoopParameters hδ).le) n)
    have hcast : ((δ : ℂ)⁻¹) ^ n = (((δ⁻¹) ^ n : ℝ) : ℂ) := by simp
    simpa only [LinearMap.smul_apply, smul_eq_mul, hcast] using
      mul_nonneg hδ0 ((htr.positiveQuotientTrace hδ n).square_nonneg x)

/-- Evaluating `normalizedPositiveQuotientTrace` rescales `positiveQuotientTrace` by `δ⁻ⁿ`. -/
theorem normalizedPositiveQuotientTrace_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.normalizedPositiveQuotientTrace hδ n x =
      ((δ : ℂ)⁻¹) ^ n * htr.positiveQuotientTrace hδ n x :=
  (rfl)

/-- Evaluating `normalizedPositiveQuotientTrace` on a quotient class rescales `tr n` by `δ⁻ⁿ`. -/
@[simp]
theorem normalizedPositiveQuotientTrace_mk (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (a : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.normalizedPositiveQuotientTrace hδ n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) a) =
      ((δ : ℂ)⁻¹) ^ n * tr n a := by
  rw [htr.normalizedPositiveQuotientTrace_apply, htr.positiveQuotientTrace_mk]

/-- The normalized positive quotient trace takes the value `1` at the identity. -/
@[simp]
theorem normalizedPositiveQuotientTrace_one (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    htr.normalizedPositiveQuotientTrace hδ n 1 = 1 := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne'
  rw [htr.normalizedPositiveQuotientTrace_apply, ← StarPositiveFunctional.toLinearMap_apply,
    htr.toLinearMap_positiveQuotientTrace, LinearMap.quotientTrace_one, htr.map_one, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero n hδ0)]

/-- The normalized positive quotient trace is tracial. -/
theorem normalizedPositiveQuotientTrace_mul_comm (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x y : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.normalizedPositiveQuotientTrace hδ n (x * y) =
      htr.normalizedPositiveQuotientTrace hδ n (y * x) := by
  simp only [htr.normalizedPositiveQuotientTrace_apply, htr.toLinearMap_positiveQuotientTrace,
    ← StarPositiveFunctional.toLinearMap_apply, LinearMap.quotientTrace_mul_comm]

/-- The normalized positive quotient trace has trivial GNS null space. -/
theorem nullSubmodule_normalizedPositiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.normalizedPositiveQuotientTrace hδ n).nullSubmodule = ⊥ := by
  have hδ0 : (δ : ℂ)⁻¹ ^ n ≠ 0 :=
    pow_ne_zero n (inv_ne_zero (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne'))
  ext x
  simp only [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    htr.normalizedPositiveQuotientTrace_apply, mul_eq_zero, hδ0, false_or,
    htr.positiveQuotientTrace_star_mul_self_eq_zero_iff hδ n, Submodule.mem_bot]

/-- The normalized positive quotient trace is preserved by the strand inclusion between Jones
quotients. -/
@[simp]
theorem normalizedPositiveQuotientTrace_quotientStrandIncl (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.normalizedPositiveQuotientTrace hδ (n + 2) (htr.quotientStrandIncl n x) =
      htr.normalizedPositiveQuotientTrace hδ (n + 1) x := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne'
  rw [htr.normalizedPositiveQuotientTrace_apply, htr.normalizedPositiveQuotientTrace_apply,
    ← StarPositiveFunctional.toLinearMap_apply, ← StarPositiveFunctional.toLinearMap_apply,
    htr.toLinearMap_positiveQuotientTrace, htr.toLinearMap_positiveQuotientTrace,
    htr.quotientTrace_quotientStrandIncl, pow_succ ((δ : ℂ)⁻¹) (n + 1), mul_assoc,
    inv_mul_cancel_left₀ hδ0]

/-- Pulling `normalizedPositiveQuotientTrace` back along `quotientStrandInclStarAlgHom` recovers
`normalizedPositiveQuotientTrace` one strand lower. -/
@[simp]
theorem normalizedPositiveQuotientTrace_comp_quotientStrandInclStarAlgHom
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar] :
    (htr.normalizedPositiveQuotientTrace hδ (n + 2)).comp (htr.quotientStrandInclStarAlgHom n) =
      htr.normalizedPositiveQuotientTrace hδ (n + 1) := by
  ext x
  simp

/-- The **normalized Markov formula** on the positive Jones quotients: multiplying an included
element by the Jones projection `δ⁻¹ • e (Fin.last n)` scales the normalized trace by
`(δ ^ 2)⁻¹`. -/
theorem normalizedPositiveQuotientTrace_mul_jonesProj (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.normalizedPositiveQuotientTrace hδ (n + 2)
      (htr.quotientStrandIncl n x *
        Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          ((δ : ℂ)⁻¹ • e (δ : ℂ) (Fin.last n))) =
      ((δ : ℂ) ^ 2)⁻¹ * htr.normalizedPositiveQuotientTrace hδ (n + 1) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [htr.quotientStrandIncl_mk, ← map_mul, htr.normalizedPositiveQuotientTrace_apply,
    htr.positiveQuotientTrace_mk, mul_smul_comm, map_smul, smul_eq_mul,
    htr.map_strandIncl_mul_e_last]
  ring

end Quotient

/-- **Pullback criterion for admissibility.** Let `δ > 0`, and suppose that for every `n` there is
a `⋆`-homomorphism `ρ n` from `TemperleyLieb ℂ (δ : ℂ) n` into a complex `⋆`-algebra `B n`
carrying a positive functional `σ n` such that `σ n (ρ n x) = δ⁻ⁿ * tr n x`. Then
`δ ∈ jonesLoopParameters`. Neither injectivity of `ρ n` nor traciality of `σ n` on `B n` is
required. -/
theorem mem_jonesLoopParameters_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    {B : ℕ → Type*} [∀ n, NonUnitalRing (B n)] [∀ n, Module ℂ (B n)] [∀ n, StarRing (B n)]
    {F : ℕ → Type*} [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, NonUnitalAlgHomClass (F n) ℂ (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n)) (ρ : ∀ n, F n)
    (hpull : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x) = ((δ : ℂ)⁻¹) ^ n * tr n x) :
    δ ∈ jonesLoopParameters := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  refine htr.mem_jonesLoopParameters_of_forall_nonneg hδ fun n x ↦ ?_
  have hval : tr n (star x * x) = (((δ ^ n : ℝ) : ℂ)) * ((σ n).comp (ρ n)) (star x * x) := by
    rw [StarPositiveFunctional.comp_apply, hpull, Complex.ofReal_pow, ← mul_assoc, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero n hδ0), one_mul]
  rw [hval]
  exact mul_nonneg (Complex.zero_le_real.2 (pow_nonneg hδ.le n))
    (((σ n).comp (ρ n)).square_nonneg x)

/-- If `δ > 0` and a `⋆`-algebra homomorphism `ρ : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B` pulls back
a positive functional `σ` with trivial GNS null space to `δ⁻ⁿ • tr n`, then `RingHom.ker ρ` equals
the trace radical of `tr n`. Surjectivity of `ρ` and traciality of `σ` on `B` are not required. -/
theorem ker_eq_traceRadical_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) {n : ℕ}
    {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (σ : StarPositiveFunctional B) (hσ : σ.nullSubmodule = ⊥)
    (ρ : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B)
    (hpull : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, σ (ρ x) = ((δ : ℂ)⁻¹) ^ n * tr n x) :
    RingHom.ker ρ = (tr n).traceRadical (htr.map_mul_comm n) := by
  have hcomm (x y : TemperleyLieb ℂ (δ : ℂ) n) :
      ((((δ : ℂ)⁻¹) ^ n) • tr n) (x * y) = ((((δ : ℂ)⁻¹) ^ n) • tr n) (y * x) := by
    simp [htr.map_mul_comm n x y]
  rw [← ((((δ : ℂ)⁻¹) ^ n) • tr n).traceRadical_eq_ker_of_nullSubmodule_eq_bot hcomm σ hσ ρ hpull]
  ext x
  simp [hδ.ne']

end IsMarkovTrace

end PositiveForm

section TowerPullback

/-- Given `⋆`-algebra homomorphisms `ρ n : TemperleyLieb ℂ δ n →⋆ₐ[ℂ] B n` and normalized
(`σ n 1 = 1`) functionals `σ n` that are tracial on the image of `ρ n`, preserve strand inclusion,
and satisfy the rescaled Markov identity `δ * σ (n + 2) (ρ (n + 2) (strandIncl x * e δ (last n)))
= σ (n + 1) (ρ (n + 1) x)`, the rescaled pullbacks `δ ^ n • (σ n ∘ ρ n)` form an unnormalized
Markov trace. -/
theorem isMarkovTrace_pow_smul_comp {δ : ℂ} [Fact (IsSelfAdjoint δ)] {B : ℕ → Type*}
    [∀ n, Ring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, StarRing (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n)) (ρ : ∀ n, TemperleyLieb ℂ δ n →⋆ₐ[ℂ] B n)
    (hone : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb ℂ δ n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hincl : ∀ n (x : TemperleyLieb ℂ δ (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb ℂ δ (n + 1)),
      δ * σ (n + 2) (ρ (n + 2) (strandIncl x * e δ (Fin.last n))) = σ (n + 1) (ρ (n + 1) x)) :
    IsMarkovTrace ℂ δ (fun n ↦ (δ ^ n) • ((σ n).comp (ρ n)).toLinearMap) :=
  isMarkovTrace_pow_smul (fun n ↦ by simp [hone]) (fun n x y ↦ by simp [hcomm])
    (fun n x ↦ by simp [hincl])
    (fun n x ↦ by
      simpa only [StarPositiveFunctional.toLinearMap_apply, StarPositiveFunctional.comp_apply] using
        hmarkov n x)

/-- **Tower pullback criterion.** Let `δ > 0`, and let `ρ n : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B n`
be `⋆`-homomorphisms into complex `⋆`-algebras carrying normalized positive functionals `σ n`
(`σ n 1 = 1`) that are tracial on the image of `ρ n`, compatible with `strandIncl`, and satisfy
`δ * σ (n + 2) (ρ (n + 2) (strandIncl x * e _ (Fin.last n))) = σ (n + 1) (ρ (n + 1) x)`. Then
`δ ∈ jonesLoopParameters`, so `δ ^ 2` lies in the Jones index set
`{4 cos² (π / m) : m ≥ 3} ∪ [4, ∞)`. Injectivity of `ρ n` is not required. -/
theorem mem_jonesLoopParameters_of_tower_pullback {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
    (hδ : 0 < δ) {B : ℕ → Type*} [∀ n, Ring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, StarRing (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n))
    (ρ : ∀ n, TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B n) (hone : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hincl : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      (δ : ℂ) * σ (n + 2) (ρ (n + 2) (strandIncl x * e (δ : ℂ) (Fin.last n))) =
        σ (n + 1) (ρ (n + 1) x)) :
    δ ∈ jonesLoopParameters := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  have htr := isMarkovTrace_pow_smul_comp σ ρ hone hcomm hincl hmarkov
  refine htr.mem_jonesLoopParameters_of_pullback hδ σ ρ fun n x ↦ ?_
  simp only [LinearMap.smul_apply, StarPositiveFunctional.toLinearMap_apply,
    StarPositiveFunctional.comp_apply, smul_eq_mul, ← mul_assoc, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero n hδ0), one_mul]

end TowerPullback

end TauCeti.TemperleyLieb
