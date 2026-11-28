/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
public import TauCeti.RingTheory.Polynomial.Roots
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Counting roots of a monic polynomial by its factorizations

A monic polynomial `p` of degree `n` over a domain has at least `k` roots, counted with
multiplicity, exactly when it factors as `∏ j, (X - x j) * q` with `q` monic of degree `n - k`.
Writing `q` through its lower coefficients `b : Fin (n - k) → R` as
`TauCeti.Polynomial.monicOfCoeff b` turns the condition into the solvability of a polynomial
system in the finitely many unknowns `x` and `b`. This is how the root count is related to the
coefficients when one studies its dependence on them, for instance its measurability over a local
field (`TauCeti.isCompact_setOf_le_card_aroots`).

When `p` splits, grouping its roots by distinct value expresses `p` as a product
`∏ l, (X - C (z l)) ^ m l` indexed by distinct roots `z l` with positive multiplicities `m l`
summing to `p.natDegree`; conversely, over a field any such distinct-root multiplicity bound
summing to at least `p.natDegree` forces `p` to equal the corresponding product.

## Main results

* `Polynomial.Monic.le_card_roots_iff_exists_prod_mul_monicOfCoeff_eq`: a monic polynomial of
  degree `n` has at least `k` roots exactly when it is `∏ j, (X - x j)` times a monic
  polynomial of degree `n - k`.
* `Polynomial.Monic.exists_eq_prod_X_sub_C_pow_rootMultiplicity`: a split monic polynomial over
  an integral domain factors as a product of powers of distinct linear factors weighted by its
  root multiplicities.
* `Polynomial.Monic.eq_prod_X_sub_C_pow_of_le_rootMultiplicity`: a monic polynomial over a field
  is determined by distinct roots whose multiplicity lower bounds sum to at least its degree.
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

/-- A split monic polynomial `p` over an integral domain factors as a product of powers of distinct
linear factors `X - C (z l)` with positive exponents `m l` equal to the root multiplicities of `p`
and summing to `p.natDegree`. -/
theorem exists_eq_prod_X_sub_C_pow_rootMultiplicity {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p.Monic) (hsplit : p.Splits) :
    ∃ (r : ℕ) (z : Fin r → R) (m : Fin r → ℕ),
      (∀ l, 0 < m l) ∧ ∑ l, m l = p.natDegree ∧ (∀ l, p.IsRoot (z l)) ∧
      Function.Injective z ∧ (∀ l, p.rootMultiplicity (z l) = m l) ∧
      (∏ l, (X - C (z l)) ^ m l) = p := by
  classical
  let e : Fin p.roots.toFinset.card ≃ p.roots.toFinset :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe p.roots.toFinset)).symm
  refine ⟨p.roots.toFinset.card, fun l ↦ (e l : R), fun l ↦ p.roots.count (e l : R),
    fun l ↦ Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (e l).property), ?_, fun l ↦ ?_,
    fun _ _ h ↦ e.injective (Subtype.ext h), fun l ↦ (count_roots p).symm, ?_⟩
  · calc ∑ l, p.roots.count (e l : R)
        = ∑ x : p.roots.toFinset, p.roots.count (x : R) :=
          e.sum_comp (fun x : p.roots.toFinset ↦ p.roots.count (x : R))
      _ = ∑ a ∈ p.roots.toFinset, p.roots.count a :=
          Finset.sum_coe_sort p.roots.toFinset (fun a ↦ p.roots.count a)
      _ = p.natDegree := by rw [Multiset.toFinset_sum_count_eq, ← hsplit.natDegree_eq_card_roots]
  · exact (mem_roots hp.ne_zero).mp (Multiset.mem_toFinset.mp (e l).property)
  · calc (∏ l, (X - C (e l : R)) ^ p.roots.count (e l : R))
        = ∏ x : p.roots.toFinset, (X - C (x : R)) ^ p.roots.count (x : R) :=
          e.prod_comp (fun x : p.roots.toFinset ↦ (X - C (x : R)) ^ p.roots.count (x : R))
      _ = ∏ a ∈ p.roots.toFinset, (X - C a) ^ p.roots.count a :=
          Finset.prod_coe_sort p.roots.toFinset (fun a ↦ (X - C a) ^ p.roots.count a)
      _ = (p.roots.map fun a ↦ X - C a).prod := (Finset.prod_multiset_map_count p.roots _).symm
      _ = p := (hsplit.eq_prod_roots_of_monic hp).symm

/-- A monic polynomial `p` over a field whose root multiplicities at distinct points `z l` are at
least `m l`, with `p.natDegree ≤ ∑ l, m l`, equals `∏ l, (X - C (z l)) ^ m l`. -/
theorem eq_prod_X_sub_C_pow_of_le_rootMultiplicity {K ι : Type*} [Field K] [Fintype ι]
    {p : K[X]} (hp : p.Monic) {z : ι → K} {m : ι → ℕ}
    (hm : p.natDegree ≤ ∑ l, m l) (hz : Function.Injective z)
    (hmult : ∀ l, m l ≤ p.rootMultiplicity (z l)) :
    p = ∏ l, (X - C (z l)) ^ m l := by
  let q : K[X] := ∏ l, (X - C (z l)) ^ m l
  have hqmon : q.Monic := monic_prod_of_monic _ _ fun l _ ↦ (monic_X_sub_C (z l)).pow _
  have hqdeg : q.natDegree = ∑ l, m l := by
    rw [natDegree_prod_of_monic _ _ fun l _ ↦ (monic_X_sub_C (z l)).pow _]
    simp
  have hcop : Pairwise (Function.onFun IsCoprime fun l ↦ (X - C (z l)) ^ m l) :=
    fun _ _ hne ↦ (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hz.ne hne)).isUnit).pow
  have hdvd : q ∣ p := Fintype.prod_dvd_of_coprime hcop fun l ↦
    (pow_dvd_pow _ (hmult l)).trans (pow_rootMultiplicity_dvd p (z l))
  exact eq_of_monic_of_dvd_of_natDegree_le hqmon hp hdvd (hqdeg ▸ hm)

end Polynomial.Monic
