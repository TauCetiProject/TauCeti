/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Taylor

/-!
# Counting and characterizing roots of a monic polynomial

A monic polynomial `p` of degree `n` over a domain has at least `k` roots, counted with
multiplicity, exactly when it factors as `∏ j, (X - x j) * q` with `q` monic of degree `n - k`.
Writing `q` through its lower coefficients `b : Fin (n - k) → R` as
`TauCeti.Polynomial.monicOfCoeff b` turns the condition into the solvability of a polynomial
system in the finitely many unknowns `x` and `b`. This is how the root count is related to the
coefficients when one studies its dependence on them, for instance its measurability over a local
field (`TauCeti.isCompact_setOf_le_card_aroots`).

When `monicOfCoeff` polynomials split over the domain and all of their roots lie in a set `s`,
matching vanishing of Hasse derivatives on `s` forces equality of their coefficient tuples, and
matching Hasse jets up to each root multiplicity forces equality of degree-`< d` remainders.

## Main results

* `Polynomial.Monic.le_card_roots_iff_exists_prod_mul_monicOfCoeff_eq`: a monic polynomial of
  degree `n` has at least `k` roots exactly when it is `∏ j, (X - x j)` times a monic
  polynomial of degree `n - k`.
* `TauCeti.Polynomial.eq_of_monicOfCoeff_forall_hasseDeriv_iff`: two split `monicOfCoeff`
  polynomials whose roots lie in `s` agree whenever their Hasse jets vanish together on `s`.
* `TauCeti.Polynomial.eq_of_sum_monomial_forall_hasseDeriv_eq`: if `monicOfCoeff c` splits with all
  roots in `s`, two degree-`< d` polynomials agree whenever their Hasse derivatives agree up to the
  multiplicity of `monicOfCoeff c` on `s`.
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

end Polynomial.Monic

namespace TauCeti.Polynomial

/-- Over an integral domain, two split monic polynomials `monicOfCoeff a` and `monicOfCoeff c` of
degree `d` whose roots all lie in `s` agree whenever, at every `w ∈ s` and for every `k ≤ d`,
their Hasse derivatives of order `< k` vanish together. -/
theorem eq_of_monicOfCoeff_forall_hasseDeriv_iff {R : Type*} [CommRing R] [IsDomain R]
    {d : ℕ} {a c : Fin d → R} {s : Set R}
    (ha_split : (monicOfCoeff a).Splits) (hc_split : (monicOfCoeff c).Splits)
    (ha : ∀ w, (monicOfCoeff a).IsRoot w → w ∈ s)
    (hc : ∀ w, (monicOfCoeff c).IsRoot w → w ∈ s)
    (hderiv : ∀ w ∈ s, ∀ k ≤ d,
      (∀ j < k, (hasseDeriv j (monicOfCoeff a)).eval w = 0) ↔
        (∀ j < k, (hasseDeriv j (monicOfCoeff c)).eval w = 0)) :
    a = c := by
  set P := monicOfCoeff a
  set Q := monicOfCoeff c
  have hPm : P.Monic := monic_monicOfCoeff a
  have hQm : Q.Monic := monic_monicOfCoeff c
  have hroots : P.roots = Q.roots := by
    classical
    ext w
    rw [count_roots, count_roots]
    by_cases hw : w ∈ s
    · have hmP : P.rootMultiplicity w ≤ d := by
        rw [← count_roots, ← natDegree_monicOfCoeff a]
        exact (Multiset.count_le_card w _).trans P.card_roots'
      have hmQ : Q.rootMultiplicity w ≤ d := by
        rw [← count_roots, ← natDegree_monicOfCoeff c]
        exact (Multiset.count_le_card w _).trans Q.card_roots'
      refine le_antisymm ?_ ?_
      · exact (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hQm.ne_zero).2
          ((hderiv w hw _ hmP).1
            ((le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hPm.ne_zero).1 le_rfl))
      · exact (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hPm.ne_zero).2
          ((hderiv w hw _ hmQ).2
            ((le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hQm.ne_zero).1 le_rfl))
    · rw [rootMultiplicity_eq_zero (mt (ha w) hw), rootMultiplicity_eq_zero (mt (hc w) hw)]
  have hPQ : P = Q := by
    rw [ha_split.eq_prod_roots_of_monic hPm, hc_split.eq_prod_roots_of_monic hQm, hroots]
  exact (monicOfCoeff_inj a c).1 hPQ

/-- Over an integral domain, if `P = monicOfCoeff c` splits and every root of `P` lies in `s`,
then two degree-`< d` polynomials `∑ i, monomial i (b i)` and `∑ i, monomial i (r i)` agree
whenever their Hasse derivatives agree up to the multiplicity of `P` at every point of `s`. -/
theorem eq_of_sum_monomial_forall_hasseDeriv_eq {R : Type*} [CommRing R] [IsDomain R]
    {d : ℕ} {c b r : Fin d → R} {s : Set R}
    (hc_split : (monicOfCoeff c).Splits)
    (hc : ∀ w, (monicOfCoeff c).IsRoot w → w ∈ s)
    (hderiv : ∀ w ∈ s, ∀ k ≤ d,
      (∀ j < k, (hasseDeriv j (monicOfCoeff c)).eval w = 0) →
        ∀ j < k,
          (hasseDeriv j (∑ i : Fin d, monomial (i : ℕ) (b i))).eval w =
            (hasseDeriv j (∑ i : Fin d, monomial (i : ℕ) (r i))).eval w) :
    b = r := by
  set P := monicOfCoeff c
  let B := ∑ i : Fin d, monomial (i : ℕ) (b i)
  let Q := ∑ i : Fin d, monomial (i : ℕ) (r i)
  have hPm : P.Monic := monic_monicOfCoeff c
  have hBQ : B - Q = 0 := by
    by_contra hne
    have hle : P.roots ≤ (B - Q).roots := by
      classical
      rw [Multiset.le_iff_count]
      intro w
      rw [count_roots, count_roots]
      by_cases hw : P.IsRoot w
      · have hm : P.rootMultiplicity w ≤ d := by
          rw [← count_roots, ← natDegree_monicOfCoeff c]
          exact (Multiset.count_le_card w _).trans P.card_roots'
        have hP0 :=
          (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hPm.ne_zero).1
            (le_rfl : P.rootMultiplicity w ≤ P.rootMultiplicity w)
        have hBQ0 := hderiv w (hc w hw) _ hm hP0
        rw [le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hne]
        intro j hj
        rw [map_sub, eval_sub, sub_eq_zero]
        exact hBQ0 j hj
      · simp [rootMultiplicity_eq_zero hw]
    have hdvd : P ∣ B - Q := by
      rw [hc_split.eq_prod_roots_of_monic hPm]
      exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans
        (prod_multiset_X_sub_C_dvd _)
    have hdeg_ge : d ≤ (B - Q).natDegree := by
      simpa only [P, natDegree_monicOfCoeff] using natDegree_le_of_dvd hdvd hne
    have hsub_eq : B - Q = ∑ i : Fin d, monomial (i : ℕ) (b i - r i) := by
      simp [B, Q, ← Finset.sum_sub_distrib, monomial_sub]
    have hdeg_lt : (B - Q).degree < (d : WithBot ℕ) := by
      rw [hsub_eq]
      simpa only [C_mul_X_pow_eq_monomial] using degree_sum_fin_lt (fun i ↦ b i - r i)
    rw [degree_eq_natDegree hne, Nat.cast_lt] at hdeg_lt
    omega
  have heq : B = Q := sub_eq_zero.1 hBQ
  funext i
  simpa [B, Q, finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Fin.val_eq_val] using
    congrArg (fun p : R[X] ↦ p.coeff (i : ℕ)) heq

end TauCeti.Polynomial
