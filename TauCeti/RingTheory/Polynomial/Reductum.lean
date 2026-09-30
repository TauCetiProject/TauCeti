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

The construction uses `PowerSeries.trunc`, whose coefficient, derivative, and coefficient-map
theorems provide the corresponding polynomial laws.  Reducta also agree with repeatedly deleting
leading terms, connecting the fixed cutoffs used for specialization to Mathlib's `eraseLead` API.

## Main results

* `Polynomial.coeff_reductum`: a reductum keeps precisely the coefficients below its cutoff.
* `Polynomial.reductum_reductum`: nested reducta reduce to the smaller cutoff.
* `Polynomial.derivative_reductum`: differentiation lowers the cutoff by one.
* `Polynomial.reductum_natDegree`: the cutoff at the degree deletes the leading term.
* `Polynomial.exists_mem_reducta_map_eq`: every coefficient specialization is the image of a
  reductum of the original polynomial.
* `Polynomial.reducta_eq_eraseLeadOrbit`: the bounded cutoffs give exactly the finite orbit under
  repeated deletion of leading terms.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 4 and 11.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The part of `p` of degree strictly below `k`. -/
noncomputable def _root_.Polynomial.reductum [CommSemiring R] (p : R[X]) (k : ℕ) : R[X] :=
  PowerSeries.trunc k (p : PowerSeries R)

/-- A reductum keeps the coefficients strictly below its cutoff and discards the rest. -/
@[simp]
theorem _root_.Polynomial.coeff_reductum [CommSemiring R] (p : R[X]) (k i : ℕ) :
    (p.reductum k).coeff i = if i < k then p.coeff i else 0 := by
  simp [reductum, PowerSeries.coeff_trunc]

/-- The reductum at cutoff zero is zero. -/
@[simp]
theorem _root_.Polynomial.reductum_zero [CommSemiring R] (p : R[X]) : p.reductum 0 = 0 := by
  ext
  simp

/-- Every reductum of the zero polynomial is zero. -/
@[simp]
theorem _root_.Polynomial.zero_reductum [CommSemiring R] (k : ℕ) :
    (0 : R[X]).reductum k = 0 := by
  ext
  simp

/-- Increasing the cutoff by one adjoins the coefficient at the old cutoff. -/
theorem _root_.Polynomial.reductum_succ [CommSemiring R] (p : R[X]) (k : ℕ) :
    p.reductum (k + 1) = p.reductum k + monomial k (p.coeff k) := by
  simpa [reductum] using PowerSeries.trunc_succ (p : PowerSeries R) k

/-- The degree of a reductum is strictly below its cutoff. -/
theorem _root_.Polynomial.degree_reductum_lt [CommSemiring R] (p : R[X]) (k : ℕ) :
    (p.reductum k).degree < k := by
  exact PowerSeries.degree_trunc_lt (p : PowerSeries R) k

/-- A cutoff strictly above the degree does not change a polynomial. -/
theorem _root_.Polynomial.reductum_eq_self [CommSemiring R] {p : R[X]} {k : ℕ}
    (h : p.natDegree < k) :
    p.reductum k = p := by
  exact PowerSeries.trunc_coe_eq_self h

/-- Cutting off immediately above the degree returns the original polynomial, including for zero. -/
@[simp]
theorem _root_.Polynomial.reductum_natDegree_add_one [CommSemiring R] (p : R[X]) :
    p.reductum (p.natDegree + 1) = p := by
  exact p.reductum_eq_self (Nat.lt_succ_self _)

/-- Taking a smaller reductum after a larger one is the same as taking the smaller reductum
directly. -/
theorem _root_.Polynomial.reductum_reductum_of_le [CommSemiring R] (p : R[X]) {k l : ℕ}
    (h : k ≤ l) :
    (p.reductum l).reductum k = p.reductum k := by
  exact PowerSeries.trunc_trunc_of_le (p : PowerSeries R) h

/-- Nested reducta use the minimum of their cutoffs. -/
@[simp]
theorem _root_.Polynomial.reductum_reductum [CommSemiring R] (p : R[X]) (k l : ℕ) :
    (p.reductum l).reductum k = p.reductum (min k l) := by
  rcases le_total k l with h | h
  · simpa [min_eq_left h] using p.reductum_reductum_of_le h
  · rw [min_eq_right h]
    apply Polynomial.ext
    intro i
    simp only [coeff_reductum]
    by_cases hi : i < l
    · have hik : i < k := hi.trans_le h
      simp [hi, hik]
    · simp [hi]

/-- Reducta commute with coefficient maps, with no degree-preservation hypothesis. -/
@[simp]
theorem _root_.Polynomial.reductum_map [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : R[X]) (k : ℕ) :
    (p.map f).reductum k = (p.reductum k).map f := by
  ext i
  simp [apply_ite f]

/-- Differentiating a reductum lowers its cutoff by one. -/
theorem _root_.Polynomial.derivative_reductum [CommSemiring R] (p : R[X]) (k : ℕ) :
    (p.reductum (k + 1)).derivative = p.derivative.reductum k := by
  simpa [reductum, PowerSeries.derivative_coe] using
    (PowerSeries.trunc_derivative (p : PowerSeries R) k).symm

/-- The reductum at the degree is Mathlib's operation deleting the leading term. -/
theorem _root_.Polynomial.reductum_natDegree [CommSemiring R] (p : R[X]) :
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
theorem _root_.Polynomial.eraseLead_reductum [CommSemiring R] (p : R[X]) {k : ℕ}
    (h : k ≤ p.natDegree) :
    p.eraseLead.reductum k = p.reductum k := by
  ext i
  simp only [coeff_reductum, eraseLead_coeff]
  by_cases hi : i < k
  · have hine : i ≠ p.natDegree := (hi.trans_le h).ne
    simp [hi, hine]
  · simp [hi]

/-- The finite set of all reducta at cutoffs from zero through one above the degree. -/
noncomputable def _root_.Polynomial.reducta [CommSemiring R] (p : R[X]) : Finset R[X] := by
  classical
  exact (Finset.range (p.natDegree + 2)).image p.reductum

/-- Membership in `reducta` is membership at one of its bounded cutoffs. -/
theorem _root_.Polynomial.mem_reducta_iff [CommSemiring R] {p q : R[X]} :
    q ∈ p.reducta ↔ ∃ k < p.natDegree + 2, p.reductum k = q := by
  classical
  simp [reducta]

/-- Zero belongs to the reducta of every polynomial. -/
@[simp]
theorem _root_.Polynomial.zero_mem_reducta [CommSemiring R] (p : R[X]) : 0 ∈ p.reducta := by
  rw [mem_reducta_iff]
  exact ⟨0, by omega, p.reductum_zero⟩

/-- Every polynomial belongs to its own reducta. -/
@[simp]
theorem _root_.Polynomial.mem_reducta [CommSemiring R] (p : R[X]) : p ∈ p.reducta := by
  rw [mem_reducta_iff]
  exact ⟨p.natDegree + 1, by omega, p.reductum_natDegree_add_one⟩

/-- Deleting the leading term produces a member of the reducta. -/
theorem _root_.Polynomial.eraseLead_mem_reducta [CommSemiring R] (p : R[X]) :
    p.eraseLead ∈ p.reducta := by
  rw [mem_reducta_iff]
  exact ⟨p.natDegree, by omega, p.reductum_natDegree⟩

open scoped Classical in
/-- The reducta consist of `p` together with the reducta after deleting its leading term. -/
theorem _root_.Polynomial.reducta_eq_insert_eraseLead_reducta [CommSemiring R] (p : R[X]) :
    p.reducta = insert p p.eraseLead.reducta := by
  classical
  ext q
  constructor
  · intro hq
    rw [mem_reducta_iff] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    rw [Finset.mem_insert]
    by_cases hkp : k ≤ p.natDegree
    · right
      by_cases hke : k < p.eraseLead.natDegree + 2
      · rw [mem_reducta_iff]
        exact ⟨k, hke, p.eraseLead_reductum hkp⟩
      · have hdeg : p.eraseLead.natDegree < k := by omega
        simp [← p.eraseLead_reductum hkp, p.eraseLead.reductum_eq_self hdeg]
    · left
      have hk' : k = p.natDegree + 1 := by omega
      simp [hk']
  · intro hq
    rw [Finset.mem_insert] at hq
    rcases hq with hqp | hq
    · subst q
      exact p.mem_reducta
    · rw [mem_reducta_iff] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      by_cases hkp : k ≤ p.natDegree
      · rw [mem_reducta_iff]
        exact ⟨k, by omega, (p.eraseLead_reductum hkp).symm⟩
      · have hdeg : p.eraseLead.natDegree < k :=
          p.eraseLead_natDegree_le_aux.trans_lt (Nat.lt_of_not_ge hkp)
        rw [mem_reducta_iff]
        refine ⟨p.natDegree, by omega, ?_⟩
        rw [p.reductum_natDegree, p.eraseLead.reductum_eq_self hdeg]

/-- The finite orbit obtained by repeatedly deleting leading terms, including the zero polynomial
at the end. -/
noncomputable def _root_.Polynomial.eraseLeadOrbit [CommSemiring R] (p : R[X]) :
    Finset R[X] := by
  classical
  exact (Finset.range (p.support.card + 1)).image fun k ↦ (eraseLead^[k]) p

/-- The orbit of zero under `eraseLead` is the singleton containing zero. -/
@[simp]
theorem _root_.Polynomial.eraseLeadOrbit_zero [CommSemiring R] :
    eraseLeadOrbit (0 : R[X]) = {0} := by
  classical
  simp [eraseLeadOrbit]

open scoped Classical in
/-- For a nonzero polynomial, its `eraseLead` orbit is obtained by adjoining the polynomial to the
orbit of its first reductum. -/
theorem _root_.Polynomial.eraseLeadOrbit_eq_insert [CommSemiring R] {p : R[X]} (hp : p ≠ 0) :
    p.eraseLeadOrbit = insert p p.eraseLead.eraseLeadOrbit := by
  classical
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

/-- The finite set of degree cutoffs is exactly the finite orbit under deletion of leading terms. -/
theorem _root_.Polynomial.reducta_eq_eraseLeadOrbit [CommSemiring R] (p : R[X]) :
    p.reducta = p.eraseLeadOrbit := by
  classical
  induction hn : p.support.card using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp : p = 0
      · subst p
        rw [eraseLeadOrbit_zero]
        ext q
        rw [mem_reducta_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨k, _, hq⟩
          simpa using hq.symm
        · intro hq
          exact ⟨0, by omega, by simp [hq]⟩
      · have hcard : p.eraseLead.support.card < n := by
          have := card_support_eraseLead_add_one hp
          omega
        rw [p.reducta_eq_insert_eraseLead_reducta, eraseLeadOrbit_eq_insert hp,
          ih _ hcard p.eraseLead rfl]

open scoped Classical in
/-- Injective coefficient maps carry all reducta exactly to the reducta of the mapped polynomial. -/
theorem _root_.Polynomial.reducta_map [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reducta = p.reducta.image (Polynomial.map f) := by
  classical
  simp only [reducta, natDegree_map_eq_of_injective hf]
  rw [Finset.image_image]
  apply Finset.image_congr
  intro k hk
  exact p.reductum_map f k

/-- Cutting off immediately above the degree after specialization maps back to the specialized
polynomial.  This is the degree-drop formula behind the finite reducta construction. -/
theorem _root_.Polynomial.map_reductum_natDegree_add_one [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).map f = p.map f := by
  ext i
  rw [coeff_map, coeff_reductum, apply_ite f, map_zero, coeff_map]
  split_ifs with hi
  · rfl
  · have hz : (p.map f).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simpa only [coeff_map] using hz.symm

/-- Every coefficient specialization is the image of a member of the original polynomial's finite
set of reducta. -/
theorem _root_.Polynomial.exists_mem_reducta_map_eq [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : R[X]) :
    ∃ q ∈ p.reducta, q.map f = p.map f := by
  refine ⟨p.reductum ((p.map f).natDegree + 1), ?_, p.map_reductum_natDegree_add_one f⟩
  rw [mem_reducta_iff]
  have hdeg : (p.map f).natDegree ≤ p.natDegree := natDegree_map_le
  exact ⟨(p.map f).natDegree + 1, by omega, rfl⟩

end TauCeti
