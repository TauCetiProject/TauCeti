/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import TauCeti.RingTheory.Polynomial.Roots

/-!
# Counting roots of a monic polynomial by its factorizations

A monic polynomial `p` of degree `n` over a domain has at least `k` roots, counted with
multiplicity, exactly when it factors as `∏ j, (X - x j) * q` with `q` monic of degree `n - k`.
Writing `q` through its lower coefficients `b : Fin (n - k) → R` as
`TauCeti.Polynomial.monicOfCoeff b` turns the condition into the solvability of a polynomial
system in the finitely many unknowns `x` and `b`. This is how the root count is related to the
coefficients when one studies its dependence on them, for instance its measurability over a local
field (`TauCeti.isCompact_setOf_le_card_aroots`).

## Main results

* `Polynomial.Monic.le_card_roots_iff_exists_prod_mul_monicOfCoeff_eq`: a monic polynomial of
  degree `n` has at least `k` roots exactly when it is `∏ j, (X - x j)` times a monic
  polynomial of degree `n - k`.
* `Polynomial.Monic.prod_X_sub_C_eq_iff_forall_le_rootMultiplicity`: a split monic polynomial of
  degree `n` equals `∏ j, (X - C (x j))` if and only if each value `x j` occurs in `x` at most
  its root multiplicity times.
-/

public section

open Polynomial TauCeti.Polynomial

namespace Polynomial.Monic

/-- A monic polynomial `p` of degree `n` over a domain has at least `k` roots, counted with
multiplicity, exactly when `p = ∏ j, (X - x j) * monicOfCoeff b` for some `x : Fin k → R` and
`b : Fin (n - k) → R`, that is, with a monic cofactor of degree `n - k`. -/
theorem le_card_roots_iff_exists_prod_mul_monicOfCoeff_eq {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p.Monic) {n k : ℕ} (hdeg : p.natDegree = n) :
    k ≤ p.roots.card ↔ ∃ (x : Fin k → R) (b : Fin (n - k) → R),
      (∏ j, (X - C (x j))) * monicOfCoeff b = p := by
  rw [le_card_roots_iff_exists_prod_X_sub_C_dvd hp.ne_zero]
  refine exists_congr fun x ↦ ⟨fun ⟨q, hq⟩ ↦ ?_, fun ⟨b, hb⟩ ↦ ⟨_, hb.symm⟩⟩
  have hP : (∏ j, (X - C (x j))).Monic := monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (x j)
  have hq' : q.Monic := hP.of_mul_monic_left (hq ▸ hp)
  have hqdeg : q.natDegree = n - k := by
    have := congrArg natDegree hq
    rw [hP.natDegree_mul hq', natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (x j)] at this
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at this
    omega
  exact ⟨fun i ↦ q.coeff i, by rw [monicOfCoeff_coeff hq' hqdeg, hq]⟩

/-- A split monic polynomial `p` of degree `n` over a domain equals `∏ j, (X - C (x j))`
for a tuple `x : Fin n → R` if and only if each entry `x j` occurs in `x` at most
`p.rootMultiplicity (x j)` times. -/
theorem prod_X_sub_C_eq_iff_forall_le_rootMultiplicity {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] {p : R[X]} (hp : p.Monic) (hs : p.Splits) {n : ℕ} (hdeg : p.natDegree = n)
    (x : Fin n → R) :
    ∏ j, (X - C (x j)) = p ↔
      ∀ j, (Finset.univ.filter fun l ↦ x l = x j).card ≤ p.rootMultiplicity (x j) := by
  have hcount (a : R) :
      (Finset.univ.val.map x).count a = (Finset.univ.filter fun l ↦ x l = a).card := by
    simp [eq_comm]
  refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, ← count_roots, roots_prod_X_sub_C_map, hcount]
  · have hle : Finset.univ.val.map x ≤ p.roots := by
      rw [Multiset.le_iff_count]
      intro a
      by_cases ha : a ∈ Finset.univ.val.map x
      · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
        rw [hcount, count_roots]
        exact h j
      · rw [Multiset.count_eq_zero_of_notMem ha]
        exact Nat.zero_le _
    have hcard : p.roots.card ≤ (Finset.univ.val.map x).card := by
      simp [← hs.natDegree_eq_card_roots, hdeg]
    exact (eq_prod_X_sub_C_of_monic_of_roots_eq hp (by simp [hdeg])
      (Multiset.eq_of_le_of_card_le hle hcard).symm).symm

end Polynomial.Monic
