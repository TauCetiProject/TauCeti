/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation
import TauCeti.RingTheory.LaurentSeries.Puiseux.AlgClosure

/-!
# Newton slopes over `K⸨X⸩` and the orders of Puiseux roots

For a field `K`, the Newton polygon of a polynomial `P = ∑ aₙ Yⁿ` over the Laurent-series field
`K⸨X⸩` is taken at the real order valuation `LaurentSeries.realAddVal K`, with heights
`ord(aₙ)`. Its finite slopes are read here through the roots of `P` in the Puiseux field
`TauCeti.puiseuxField K`: a face of slope `σ` accounts for the roots of order `-σ`.

The Puiseux order `TauCeti.puiseuxField.addVal K`, with values in `WithTop ℚ`, is read through
the real additive valuation `TauCeti.puiseuxField.realAddVal K`, which on `K⸨X⸩` is
`LaurentSeries.realAddVal K` (`TauCeti.puiseuxField.realAddVal_algebraMap`). So extending the
coefficients of `P` to the Puiseux field changes neither its Newton polygon nor its slopes, and
the slope-root dictionary of `Polynomial.newtonSlopes_eq_map_roots_map` applies.

In every characteristic, the negated order of a nonzero Puiseux root of a nonzero `P` is a finite
slope of `P`, and if all finite slopes of `P` equal `q`, every nonzero Puiseux root of `P` has
order `-q`. If `P` splits over the Puiseux field, its finite slopes are exactly the negated orders
of its nonzero Puiseux roots, counted with multiplicity. For a finite face of slope `σ` running
from `l` to `u`, the roots of order greater than `-σ` then number `l`, those of order at least `-σ`
number `u`, and those of order exactly `-σ` number `u - l`, counted with multiplicity and, in the
first two counts, including the root zero. If `K` is algebraically closed of characteristic zero,
every polynomial splits over the Puiseux field (the Newton–Puiseux theorem,
`TauCeti.puiseuxField.instIsAlgClosed`), so these hold for every `P`.

For example `Y² - t` has the single slope `-1/2`, and its two roots `± t ^ (1/2)` have order `1/2`.

## Main results

* `Polynomial.newtonSlopes_map_puiseuxField`: extending coefficients to the Puiseux field preserves
  the finite slopes.
* `Polynomial.neg_untop₀_addVal_mem_newtonSlopes_of_aeval_eq_zero`: the negated order of a nonzero
  Puiseux root is a finite slope, in every characteristic.
* `Polynomial.addVal_eq_neg_of_forall_mem_newtonSlopes_eq`: if every finite slope equals `q`,
  every nonzero Puiseux root has order `-q`.
* `Polynomial.newtonSlopes_eq_map_roots_puiseuxField`: if `P` splits over the Puiseux field, its
  finite slopes are the negated orders of its nonzero Puiseux roots;
  `Polynomial.newtonSlopes_eq_map_roots_puiseuxField_of_isAlgClosed` is the form over an
  algebraically closed `K` of characteristic zero.
* `Polynomial.exists_aeval_eq_zero_addVal_eq_of_mem_newtonSlopes`: for such `P`, every finite
  slope `σ` is attained by a Puiseux root of order `-σ`;
  `Polynomial.exists_aeval_eq_zero_addVal_eq_of_mem_newtonSlopes_of_isAlgClosed` is the form over
  an algebraically closed `K` of characteristic zero.
* `Polynomial.card_filter_roots_map_lt_realAddVal`, `Polynomial.card_filter_roots_map_le_realAddVal`
  and `Polynomial.card_filter_roots_map_realAddVal_eq`: for such `P`, the endpoints and the width
  of a finite face of slope `σ` count the Puiseux roots of order above `-σ`, at least `-σ` and
  exactly `-σ`.
-/

public section

open Polynomial
open scoped LaurentSeries

namespace Polynomial

open TauCeti TauCeti.puiseuxField

variable {K : Type*} [Field K]

/-- Extending the coefficients of a polynomial from `K⸨X⸩` to the Puiseux field preserves its
Newton polygon. -/
@[simp]
theorem newtonPolygon_map_puiseuxField (P : K⸨X⸩[X]) :
    (P.map (algebraMap K⸨X⸩ (puiseuxField K))).newtonPolygon (realAddVal K) =
      P.newtonPolygon (LaurentSeries.realAddVal K) :=
  P.newtonPolygon_map _ _ realAddVal_algebraMap

/-- Extending the coefficients of a polynomial from `K⸨X⸩` to the Puiseux field preserves its
finite slopes. -/
@[simp]
theorem newtonSlopes_map_puiseuxField (P : K⸨X⸩[X]) :
    (P.map (algebraMap K⸨X⸩ (puiseuxField K))).newtonSlopes (realAddVal K) =
      P.newtonSlopes (LaurentSeries.realAddVal K) :=
  P.newtonSlopes_map _ _ realAddVal_algebraMap

/-- The negated order `-ord α` of a nonzero Puiseux root `α` of a nonzero polynomial over `K⸨X⸩`
is one of its finite slopes. This holds over every field `K`, and the polynomial need not split
over the Puiseux field. -/
theorem neg_untop₀_addVal_mem_newtonSlopes_of_aeval_eq_zero {P : K⸨X⸩[X]} (hP : P ≠ 0)
    {α : puiseuxField K} (hα : α ≠ 0) (hroot : aeval α P = 0) :
    -((addVal K α).untop₀ : ℝ) ∈ P.newtonSlopes (LaurentSeries.realAddVal K) := by
  have hmem := neg_untop₀_mem_newtonSlopes_of_isRoot (fun _ => realAddVal_eq_top_iff.mp)
    (Polynomial.map_ne_zero hP) hα (by rwa [IsRoot, eval_map_algebraMap])
  rwa [newtonSlopes_map_puiseuxField, untop₀_realAddVal] at hmem

/-- If every finite slope of a nonzero polynomial over `K⸨X⸩` equals the rational number `q`, then
every nonzero Puiseux root of the polynomial has order `-q`. This holds over every field `K`, and
the polynomial need not split over the Puiseux field. -/
theorem addVal_eq_neg_of_forall_mem_newtonSlopes_eq {P : K⸨X⸩[X]} (hP : P ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ P.newtonSlopes (LaurentSeries.realAddVal K), m = q) {α : puiseuxField K}
    (hα : α ≠ 0) (hroot : aeval α P = 0) : addVal K α = ((-q : ℚ) : WithTop ℚ) := by
  rw [← realAddVal_eq_ratCast_iff, Rat.cast_neg]
  exact addValuation_eq_neg_of_forall_mem_newtonSlopes_eq (fun _ => realAddVal_eq_top_iff.mp)
    (algebraMap K⸨X⸩ (puiseuxField K)) realAddVal_algebraMap
    (Polynomial.map_ne_zero hP) hq hα
    (by rwa [IsRoot, eval_map_algebraMap])

/-- **Newton slopes are the orders of the Puiseux roots.** If a polynomial over `K⸨X⸩` splits over
the Puiseux field, its finite slopes are the negated orders `-ord α` of its nonzero roots `α` in
the Puiseux field, counted with multiplicity. -/
theorem newtonSlopes_eq_map_roots_puiseuxField [DecidableEq (puiseuxField K)] {P : K⸨X⸩[X]}
    (hP : (P.map (algebraMap K⸨X⸩ (puiseuxField K))).Splits) :
    P.newtonSlopes (LaurentSeries.realAddVal K) =
      ((P.map (algebraMap K⸨X⸩ (puiseuxField K))).roots.filter (· ≠ 0)).map
        fun α ↦ -((addVal K α).untop₀ : ℝ) := by
  rw [newtonSlopes_eq_map_roots_map (fun _ => realAddVal_eq_top_iff.mp) _ realAddVal_algebraMap hP]
  simp only [untop₀_realAddVal]

/-- If a polynomial over `K⸨X⸩` splits over the Puiseux field, every finite slope `σ` of it is
attained: the polynomial has a nonzero root of order `-σ` in the Puiseux field. -/
theorem exists_aeval_eq_zero_addVal_eq_of_mem_newtonSlopes {P : K⸨X⸩[X]}
    (hP : (P.map (algebraMap K⸨X⸩ (puiseuxField K))).Splits) {σ : ℝ}
    (hσ : σ ∈ P.newtonSlopes (LaurentSeries.realAddVal K)) :
    ∃ α : puiseuxField K, α ≠ 0 ∧ aeval α P = 0 ∧ ((addVal K α).untop₀ : ℝ) = -σ := by
  classical
  rw [newtonSlopes_eq_map_roots_puiseuxField hP, Multiset.mem_map] at hσ
  obtain ⟨α, hα, rfl⟩ := hσ
  rw [Multiset.mem_filter] at hα
  refine ⟨α, hα.2, ?_, (neg_neg _).symm⟩
  rw [aeval_def, ← eval_map]
  exact (mem_roots'.mp hα.1).2

/-- If a polynomial over `K⸨X⸩` splits over the Puiseux field, the left endpoint `l` of its finite
face of slope `σ` is the number of its roots in the Puiseux field of order greater than `-σ`,
counted with multiplicity and including the root zero. -/
theorem card_filter_roots_map_lt_realAddVal {P : K⸨X⸩[X]}
    (hP : (P.map (algebraMap K⸨X⸩ (puiseuxField K))).Splits) {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (P.newtonPolygon (LaurentSeries.realAddVal K)) σ l u) :
    ((P.map (algebraMap K⸨X⸩ (puiseuxField K))).roots.filter
      fun α ↦ ((-σ : ℝ) : WithTop ℝ) < realAddVal K α).card = l :=
  card_filter_roots_lt_addValuation (fun _ => realAddVal_eq_top_iff.mp) hP
    (by rwa [newtonPolygon_map_puiseuxField])

/-- If a polynomial over `K⸨X⸩` splits over the Puiseux field, the right endpoint `u` of its finite
face of slope `σ` is the number of its roots in the Puiseux field of order at least `-σ`, counted
with multiplicity and including the root zero. -/
theorem card_filter_roots_map_le_realAddVal {P : K⸨X⸩[X]}
    (hP : (P.map (algebraMap K⸨X⸩ (puiseuxField K))).Splits) {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (P.newtonPolygon (LaurentSeries.realAddVal K)) σ l u) :
    ((P.map (algebraMap K⸨X⸩ (puiseuxField K))).roots.filter
      fun α ↦ ((-σ : ℝ) : WithTop ℝ) ≤ realAddVal K α).card = u :=
  card_filter_roots_le_addValuation (fun _ => realAddVal_eq_top_iff.mp) hP
    (by rwa [newtonPolygon_map_puiseuxField])

/-- If a polynomial over `K⸨X⸩` splits over the Puiseux field, the width `u - l` of its finite face
of slope `σ` is the number of its roots in the Puiseux field of order exactly `-σ`, counted with
multiplicity. -/
theorem card_filter_roots_map_realAddVal_eq {P : K⸨X⸩[X]}
    (hP : (P.map (algebraMap K⸨X⸩ (puiseuxField K))).Splits) {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (P.newtonPolygon (LaurentSeries.realAddVal K)) σ l u) :
    ((P.map (algebraMap K⸨X⸩ (puiseuxField K))).roots.filter
      fun α ↦ realAddVal K α = ((-σ : ℝ) : WithTop ℝ)).card = u - l :=
  card_filter_roots_addValuation_eq (fun _ => realAddVal_eq_top_iff.mp) hP
    (by rwa [newtonPolygon_map_puiseuxField])

section AlgClosed

variable [IsAlgClosed K] [CharZero K]

/-- **Newton slopes are the orders of the Puiseux roots.** Over an algebraically closed field `K`
of characteristic zero, the finite slopes of any polynomial over `K⸨X⸩` are the negated orders
`-ord α` of its nonzero roots `α` in the Puiseux field, counted with multiplicity, with no
splitting assumption. -/
theorem newtonSlopes_eq_map_roots_puiseuxField_of_isAlgClosed [DecidableEq (puiseuxField K)]
    (P : K⸨X⸩[X]) :
    P.newtonSlopes (LaurentSeries.realAddVal K) =
      ((P.map (algebraMap K⸨X⸩ (puiseuxField K))).roots.filter (· ≠ 0)).map
        fun α ↦ -((addVal K α).untop₀ : ℝ) :=
  newtonSlopes_eq_map_roots_puiseuxField (IsAlgClosed.splits _)

/-- Over an algebraically closed field `K` of characteristic zero, every finite slope `σ` of any
polynomial over `K⸨X⸩` is attained: the polynomial has a nonzero root of order `-σ` in the
Puiseux field. -/
theorem exists_aeval_eq_zero_addVal_eq_of_mem_newtonSlopes_of_isAlgClosed {P : K⸨X⸩[X]} {σ : ℝ}
    (hσ : σ ∈ P.newtonSlopes (LaurentSeries.realAddVal K)) :
    ∃ α : puiseuxField K, α ≠ 0 ∧ aeval α P = 0 ∧ ((addVal K α).untop₀ : ℝ) = -σ :=
  exists_aeval_eq_zero_addVal_eq_of_mem_newtonSlopes (IsAlgClosed.splits _) hσ

end AlgClosed

end Polynomial
