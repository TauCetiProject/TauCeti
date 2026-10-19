/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Polynomial reducta

The reductum `p.reductum k` retains exactly the terms of `p` of degree strictly below `k`.
The finite set `p.reducta` contains the reducta at every cutoff through `p.natDegree + 1`, so it
includes both zero and `p` itself.  After any coefficient specialization, one member of this set
maps to the specialized polynomial: take the cutoff immediately above its new degree.  This is
the finite degree-case decomposition needed when polynomial degrees can drop under specialization.

The reductum is `PowerSeries.trunc` applied to `p` viewed as a power series.  Reducta also agree
with repeatedly deleting leading terms, connecting the fixed cutoffs used for specialization to
Mathlib's `eraseLead` API.

## Main results

* `Polynomial.coeff_reductum`: a reductum keeps precisely the coefficients below its cutoff.
* `Polynomial.reductum_reductum`: nested reducta reduce to the smaller cutoff.
* `Polynomial.derivative_reductum`: differentiation lowers the cutoff by one.
* `Polynomial.reductum_natDegree`: the cutoff at the degree deletes the leading term.
* `Polynomial.reducta_map`: coefficient maps carry the reducta onto the reducta of the mapped
  polynomial, with no injectivity or degree-preservation hypothesis.
* `Polynomial.exists_mem_reducta_map_eq`: every coefficient specialization is the image of a
  reductum of the original polynomial.
* `Polynomial.reducta_eq_eraseLeadOrbit`: the bounded cutoffs give exactly the finite orbit under
  repeated deletion of leading terms.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 4 and 11.
-/

public section

namespace Polynomial

open Polynomial

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The part of `p` of degree strictly below `k`. -/
noncomputable def reductum (p : R[X]) (k : ℕ) : R[X] :=
  PowerSeries.trunc k (p : PowerSeries R)

/-- A reductum is the truncation of `p`, viewed as a power series, at the same cutoff. -/
theorem reductum_eq_trunc (p : R[X]) (k : ℕ) :
    p.reductum k = PowerSeries.trunc k (p : PowerSeries R) := by
  rw [reductum]

/-- A reductum keeps the coefficients strictly below its cutoff and discards the rest. -/
@[simp, grind =]
theorem coeff_reductum (p : R[X]) (k i : ℕ) :
    (p.reductum k).coeff i = if i < k then p.coeff i else 0 := by
  simp [reductum, PowerSeries.coeff_trunc]

/-- A reductum is the sum of the monomials of `p` below its cutoff. -/
theorem reductum_eq_sum (p : R[X]) (k : ℕ) :
    p.reductum k = ∑ i ∈ Finset.range k, monomial i (p.coeff i) := by
  ext i
  simp [coeff_monomial]

/-- The reductum at cutoff zero is zero. -/
@[simp]
theorem reductum_zero (p : R[X]) : p.reductum 0 = 0 := by
  ext
  simp

/-- Every reductum of the zero polynomial is zero. -/
@[simp]
theorem zero_reductum (k : ℕ) :
    (0 : R[X]).reductum k = 0 := by
  ext
  simp

/-- Increasing the cutoff by one adjoins the coefficient at the old cutoff. -/
theorem reductum_succ (p : R[X]) (k : ℕ) :
    p.reductum (k + 1) = p.reductum k + monomial k (p.coeff k) := by
  simpa [reductum] using PowerSeries.trunc_succ (p : PowerSeries R) k

/-- The degree of a reductum is strictly below its cutoff. -/
theorem degree_reductum_lt (p : R[X]) (k : ℕ) :
    (p.reductum k).degree < k := by
  exact PowerSeries.degree_trunc_lt (p : PowerSeries R) k

/-- The natural degree of a reductum at a positive cutoff is strictly below that cutoff. -/
theorem natDegree_reductum_lt (p : R[X]) (k : ℕ) :
    (p.reductum (k + 1)).natDegree < k + 1 := by
  exact PowerSeries.natDegree_trunc_lt (p : PowerSeries R) k

/-- A cutoff strictly above the degree does not change a polynomial. -/
theorem reductum_eq_self {p : R[X]} {k : ℕ} (h : p.natDegree < k) :
    p.reductum k = p := by
  ext i
  rw [coeff_reductum, ite_eq_left_iff]
  intro hi
  exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Cutting off immediately above the degree returns the original polynomial, including for zero. -/
@[simp]
theorem reductum_natDegree_add_one (p : R[X]) :
    p.reductum (p.natDegree + 1) = p := by
  exact p.reductum_eq_self (Nat.lt_succ_self _)

/-- Nested reducta use the minimum of their cutoffs. -/
@[simp]
theorem reductum_reductum (p : R[X]) (k l : ℕ) :
    (p.reductum l).reductum k = p.reductum (min k l) := by
  ext i
  simp only [coeff_reductum, lt_min_iff]
  by_cases hk : i < k <;> by_cases hl : i < l <;> simp [hk, hl]

/-- Taking a smaller reductum after a larger one is the same as taking the smaller reductum
directly. -/
theorem reductum_reductum_of_le (p : R[X]) {k l : ℕ} (h : k ≤ l) :
    (p.reductum l).reductum k = p.reductum k := by
  rw [reductum_reductum, min_eq_left h]

/-- Reducta commute with coefficient maps, with no degree-preservation hypothesis. -/
@[simp]
theorem reductum_map (f : R →+* S) (p : R[X]) (k : ℕ) :
    (p.map f).reductum k = (p.reductum k).map f := by
  ext i
  simp [apply_ite f]

/-- Differentiating a reductum lowers its cutoff by one. -/
theorem derivative_reductum (p : R[X]) (k : ℕ) :
    (p.reductum (k + 1)).derivative = p.derivative.reductum k := by
  ext i
  simp only [coeff_derivative, coeff_reductum]
  by_cases hi : i < k <;> simp [hi]

/-- The reductum at the degree is Mathlib's operation deleting the leading term. -/
theorem reductum_natDegree (p : R[X]) :
    p.reductum p.natDegree = p.eraseLead := by
  ext i
  rw [coeff_reductum, eraseLead_coeff]
  by_cases hi : i < p.natDegree
  · simp [hi, hi.ne]
  · by_cases hieq : i = p.natDegree
    · simp [hieq]
    · have hlt : p.natDegree < i := lt_of_le_of_ne (Nat.le_of_not_gt hi) (Ne.symm hieq)
      simp [hi, hieq, coeff_eq_zero_of_natDegree_lt hlt]

/-- Below the degree of `p`, taking a reductum is unaffected by first deleting the leading term. -/
theorem reductum_eraseLead (p : R[X]) {k : ℕ} (h : k ≤ p.natDegree) :
    p.eraseLead.reductum k = p.reductum k := by
  ext i
  simp only [coeff_reductum, eraseLead_coeff]
  by_cases hi : i < k
  · have hine : i ≠ p.natDegree := (hi.trans_le h).ne
    simp [hi, hine]
  · simp [hi]

/-- A cutoff above the degree of `p.eraseLead` but not above the degree of `p` deletes exactly
the leading term. -/
theorem reductum_eq_eraseLead_of_lt_of_le {p : R[X]} {k : ℕ}
    (h₁ : p.eraseLead.natDegree < k) (h₂ : k ≤ p.natDegree) :
    p.reductum k = p.eraseLead := by
  rw [← p.reductum_eraseLead h₂, p.eraseLead.reductum_eq_self h₁]

/-- The finite set of all reducta at cutoffs from zero through one above the degree. -/
noncomputable def reducta (p : R[X]) : Finset R[X] := by
  classical
  exact (Finset.range (p.natDegree + 2)).image p.reductum

/-- Membership in `reducta` is membership at one of its bounded cutoffs. -/
theorem mem_reducta {p q : R[X]} :
    q ∈ p.reducta ↔ ∃ k < p.natDegree + 2, p.reductum k = q := by
  classical
  simp [reducta]

/-- Zero belongs to the reducta of every polynomial. -/
@[simp]
theorem zero_mem_reducta (p : R[X]) : 0 ∈ p.reducta := by
  rw [mem_reducta]
  exact ⟨0, by omega, p.reductum_zero⟩

/-- Every polynomial belongs to its own reducta. -/
@[simp]
theorem self_mem_reducta (p : R[X]) : p ∈ p.reducta := by
  rw [mem_reducta]
  exact ⟨p.natDegree + 1, by omega, p.reductum_natDegree_add_one⟩

/-- The reductum at every cutoff belongs to the reducta, including cutoffs past the degree. -/
@[simp]
theorem reductum_mem_reducta (p : R[X]) (k : ℕ) : p.reductum k ∈ p.reducta := by
  by_cases hk : k < p.natDegree + 2
  · exact mem_reducta.2 ⟨k, hk, rfl⟩
  · rw [p.reductum_eq_self (by omega)]
    exact p.self_mem_reducta

/-- Deleting the leading term produces a member of the reducta. -/
theorem eraseLead_mem_reducta (p : R[X]) :
    p.eraseLead ∈ p.reducta := by
  rw [mem_reducta]
  exact ⟨p.natDegree, by omega, p.reductum_natDegree⟩

/-- The only reductum of the zero polynomial is zero. -/
@[simp]
theorem reducta_zero : (0 : R[X]).reducta = {0} := by
  ext q
  rw [mem_reducta, Finset.mem_singleton]
  constructor
  · rintro ⟨k, _, hq⟩
    simpa using hq.symm
  · intro hq
    exact ⟨0, by omega, by simp [hq]⟩

open scoped Classical in
/-- The reducta consist of `p` together with the reducta after deleting its leading term. -/
theorem reducta_eq_insert_eraseLead_reducta (p : R[X]) :
    p.reducta = insert p p.eraseLead.reducta := by
  classical
  ext q
  constructor
  · intro hq
    rw [mem_reducta] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    rw [Finset.mem_insert]
    by_cases hkp : k ≤ p.natDegree
    · right
      by_cases hke : k < p.eraseLead.natDegree + 2
      · rw [mem_reducta]
        exact ⟨k, hke, p.reductum_eraseLead hkp⟩
      · rw [reductum_eq_eraseLead_of_lt_of_le (by omega) hkp]
        exact p.eraseLead.self_mem_reducta
    · left
      have hk' : k = p.natDegree + 1 := by omega
      simp [hk']
  · intro hq
    rw [Finset.mem_insert] at hq
    rcases hq with hqp | hq
    · subst q
      exact p.self_mem_reducta
    · rw [mem_reducta] at hq
      obtain ⟨k, _, rfl⟩ := hq
      by_cases hkp : k ≤ p.natDegree
      · rw [mem_reducta]
        exact ⟨k, by omega, (p.reductum_eraseLead hkp).symm⟩
      · have hdeg : p.eraseLead.natDegree < k :=
          p.eraseLead_natDegree_le_aux.trans_lt (Nat.lt_of_not_ge hkp)
        rw [p.eraseLead.reductum_eq_self hdeg]
        exact p.eraseLead_mem_reducta

/-- The finite orbit obtained by repeatedly deleting leading terms, including the zero polynomial
at the end. -/
noncomputable def eraseLeadOrbit (p : R[X]) : Finset R[X] := by
  classical
  exact (Finset.range (p.support.card + 1)).image fun k ↦ (eraseLead^[k]) p

/-- Membership in the `eraseLead` orbit is being one of the first `p.support.card + 1` iterates
of `eraseLead` on `p`. -/
theorem mem_eraseLeadOrbit {p q : R[X]} :
    q ∈ p.eraseLeadOrbit ↔ ∃ k ≤ p.support.card, (eraseLead^[k]) p = q := by
  classical
  simp [eraseLeadOrbit]

/-- The orbit of zero under `eraseLead` is the singleton containing zero. -/
@[simp]
theorem eraseLeadOrbit_zero :
    eraseLeadOrbit (0 : R[X]) = {0} := by
  classical
  simp [eraseLeadOrbit]

open scoped Classical in
/-- The `eraseLead` orbit of a polynomial is the polynomial together with the orbit of the
polynomial with its leading term deleted. -/
theorem eraseLeadOrbit_eq_insert (p : R[X]) :
    p.eraseLeadOrbit = insert p p.eraseLead.eraseLeadOrbit := by
  classical
  by_cases hp : p = 0
  · subst hp
    simp
  ext q
  simp only [eraseLeadOrbit, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨k, hk, rfl⟩
    cases k with
    | zero => simp
    | succ k =>
        right
        refine ⟨k, ?_, ?_⟩
        · have hcard := card_support_eraseLead_add_one hp
          omega
        · exact Function.iterate_succ_apply eraseLead k p
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨k + 1, ?_, ?_⟩
      · have hcard := card_support_eraseLead_add_one hp
        omega
      · exact (Function.iterate_succ_apply eraseLead k p).symm

/-- The finite set of reducta at bounded cutoffs is exactly the finite orbit under deletion of
leading terms. -/
theorem reducta_eq_eraseLeadOrbit (p : R[X]) :
    p.reducta = p.eraseLeadOrbit := by
  classical
  induction hn : p.support.card using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp : p = 0
      · subst p
        rw [reducta_zero, eraseLeadOrbit_zero]
      · have hcard : p.eraseLead.support.card < n := by
          have := card_support_eraseLead_add_one hp
          omega
        rw [p.reducta_eq_insert_eraseLead_reducta, p.eraseLeadOrbit_eq_insert,
          ih _ hcard p.eraseLead rfl]

/-- Every iterate of `eraseLead` on `p` lies in its `eraseLead` orbit, including the iterates past
the point where the orbit reaches zero. -/
theorem iterate_eraseLead_mem_eraseLeadOrbit (p : R[X]) (k : ℕ) :
    (eraseLead^[k]) p ∈ p.eraseLeadOrbit := by
  classical
  rw [← reducta_eq_eraseLeadOrbit]
  induction k generalizing p with
  | zero => exact p.self_mem_reducta
  | succ k ih =>
      rw [Function.iterate_succ_apply, reducta_eq_insert_eraseLead_reducta]
      exact Finset.mem_insert_of_mem (ih _)

open scoped Classical in
/-- Coefficient maps carry all reducta exactly to the reducta of the mapped polynomial, with no
injectivity or degree-preservation hypothesis. -/
theorem reducta_map (f : R →+* S) (p : R[X]) :
    (p.map f).reducta = p.reducta.image (Polynomial.map f) := by
  classical
  have hdeg : (p.map f).natDegree ≤ p.natDegree := natDegree_map_le
  ext q
  rw [Finset.mem_image]
  constructor
  · rw [mem_reducta]
    rintro ⟨k, hk, rfl⟩
    exact ⟨p.reductum k, mem_reducta.2 ⟨k, by omega, rfl⟩, (p.reductum_map f k).symm⟩
  · rintro ⟨_, hq, rfl⟩
    obtain ⟨k, -, rfl⟩ := mem_reducta.1 hq
    rw [← reductum_map]
    by_cases hk : k < (p.map f).natDegree + 2
    · exact mem_reducta.2 ⟨k, hk, rfl⟩
    · rw [reductum_eq_self (by omega)]
      exact (p.map f).self_mem_reducta

/-- Cutting off immediately above the degree after specialization maps back to the specialized
polynomial.  This gives an explicit member of `p.reducta` witnessing
`exists_mem_reducta_map_eq`. -/
theorem map_reductum_natDegree_map_add_one (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).map f = p.map f := by
  rw [← reductum_map, reductum_natDegree_add_one]

/-- Cutting off immediately above the degree after specialization gives a reductum whose own
degree is the specialized degree, so formal degree bounds taken at this reductum are the actual
degrees after specialization. -/
theorem natDegree_reductum_natDegree_map_add_one (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).natDegree = (p.map f).natDegree := by
  refine Nat.le_antisymm (Nat.lt_succ_iff.mp (p.natDegree_reductum_lt _)) ?_
  conv_lhs => rw [← map_reductum_natDegree_map_add_one f p]
  exact natDegree_map_le

/-- Every coefficient specialization is the image of a member of the original polynomial's finite
set of reducta. -/
theorem exists_mem_reducta_map_eq (f : R →+* S) (p : R[X]) :
    ∃ q ∈ p.reducta, q.map f = p.map f := by
  classical
  have h := (p.map f).self_mem_reducta
  rw [reducta_map, Finset.mem_image] at h
  exact h

end Polynomial
