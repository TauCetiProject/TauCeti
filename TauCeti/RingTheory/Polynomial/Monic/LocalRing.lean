/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Lowering the degree of a monic polynomial in an ideal over a local ring

Let `R` be a local ring, `p : R[X]` monic of degree `d`, and `q : R[X]` of degree less than `d`
with at least one unit coefficient. Then the ideal `(p, q)` contains a monic polynomial of
degree `d - 1` (`Polynomial.exists_monic_mem_span_pair`).

If the coefficient of `q` at `d - 1` is a unit, a unit multiple of `q` itself is such a
polynomial. Otherwise, let `n` be the largest index at which `q` has a unit coefficient. Then
`X * q - c p`, with `c` the coefficient of `q` at `d - 1`, still lies in `(p, q)` and has degree
less than `d`. Its coefficient at `n + 1` is a unit, and its coefficients above `n + 1` are not:
they differ from coefficients of `q` above `n` by multiples of the nonunit `c`. Repeating this
step moves the top unit coefficient up to index `d - 1`.

This is the degree-lowering step in Horrocks' theorem on unimodular vectors over a polynomial
ring over a local ring (`TauCeti.unimodularEquiv_single_of_isUnit_leadingCoeff`).

## References

* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter XXI, §3.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- An index at which `q` has a unit coefficient lies below the degree of `p` when `q` has
smaller degree than `p`. -/
private theorem lt_natDegree_of_isUnit_coeff {p q : R[X]} (hq : q.degree < p.degree) {n : ℕ}
    (hn : IsUnit (q.coeff n)) : n < p.natDegree := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hn
  exact (le_natDegree_of_ne_zero hn.ne_zero).trans_lt (natDegree_lt_natDegree hq0 hq)

/-- **Lowering the degree of a monic polynomial.** Over a local ring, if `p` is monic and `q` has
smaller degree than `p` and some unit coefficient, then the ideal `(p, q)` contains a monic
polynomial of degree one less than that of `p`. -/
theorem exists_monic_mem_span_pair {p q : R[X]} (hp : p.Monic) (hq : q.degree < p.degree)
    {n : ℕ} (hn : IsUnit (q.coeff n)) :
    ∃ h ∈ Ideal.span {p, q}, h.Monic ∧ h.natDegree + 1 = p.natDegree := by
  -- Strong induction on the distance from the unit coefficient to the top degree of `p`, with
  -- `q` varying in the fixed ideal `(p, q)`.
  suffices H : ∀ m, ∀ r ∈ Ideal.span {p, q}, r.degree < p.degree → ∀ n, IsUnit (r.coeff n) →
      p.natDegree - n = m → ∃ h ∈ Ideal.span {p, q}, h.Monic ∧ h.natDegree + 1 = p.natDegree from
    H _ q (Ideal.subset_span (by simp)) hq n hn rfl
  intro m
  induction m using Nat.strong_induction_on with | _ m ih => ?_
  intro r hrI hr n hn hm
  have hnd := lt_natDegree_of_isUnit_coeff hr hn
  -- If `r` has a unit coefficient above `n`, move to it.
  by_cases hmax : ∃ k, n < k ∧ IsUnit (r.coeff k)
  · obtain ⟨k, hnk, hk⟩ := hmax
    have hkd := lt_natDegree_of_isUnit_coeff hr hk
    exact ih _ (by omega) r hrI hr k hk rfl
  push Not at hmax
  obtain ⟨e, he⟩ : ∃ e, p.natDegree = e + 1 := ⟨p.natDegree - 1, by omega⟩
  have hrdeg : r.degree < ↑(e + 1) := by rwa [degree_eq_natDegree hp.ne_zero, he] at hr
  rcases (show n ≤ e by omega).lt_or_eq with hne | rfl
  · -- The coefficient `c` of `r` at `e` is not a unit; pass to `X * r - c p`.
    set c := r.coeff e
    have hc : ¬IsUnit c := hmax e hne
    have hpI : p ∈ Ideal.span {p, q} := Ideal.subset_span (by simp)
    refine ih (p.natDegree - (n + 1)) (by omega) (X * r - C c * p)
      (sub_mem (Ideal.mul_mem_left _ _ hrI) (Ideal.mul_mem_left _ _ hpI)) ?_ (n + 1) ?_ rfl
    · rw [degree_eq_natDegree hp.ne_zero, degree_lt_iff_coeff_zero]
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      rcases (show e ≤ k by omega).eq_or_lt with rfl | hlt
      · rw [← he, hp.coeff_natDegree, mul_one, sub_self]
      · rw [coeff_eq_zero_of_degree_lt (hrdeg.trans_le (by exact_mod_cast hlt)),
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, sub_zero]
    · rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      -- `r.coeff n` is a unit and `c * p.coeff (n + 1)` is not, so their difference is a unit.
      refine (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (by rwa [sub_add_cancel])).resolve_right
        fun h ↦ hc (isUnit_of_mul_isUnit_left h)
  · -- The coefficient of `r` at `e` is a unit, so `r` is a unit multiple of a monic polynomial.
    have hrp := natDegree_lt_natDegree (fun h ↦ by simp [h] at hn) hr
    have hrn : r.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero (by omega) hn.ne_zero
    refine ⟨C ↑hn.unit⁻¹ * r, Ideal.mul_mem_left _ _ hrI,
      monic_C_mul_of_mul_leadingCoeff_eq_one ?_, ?_⟩
    · rw [leadingCoeff, hrn]
      exact hn.val_inv_mul
    · rw [natDegree_C_mul_of_isUnit (Units.isUnit _), hrn, he]

end Polynomial
