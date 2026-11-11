/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# The monic polynomial with prescribed power sums

Let `M : ℕ → K` be a sequence in a field of characteristic zero, thought of as the power sums
`M j = ∑ tʲ` of some unknown points `t`. Newton's identities determine recursively the numbers

`b₀ = 1`,  `k b_k = ∑_{j=1}^{k} (-1)^(j-1) b_{k-j} M_j`  (`TauCeti.newtonCoeff`),

and hence the monic polynomial `P(X) = Xᵐ - b₁ Xᵐ⁻¹ + ⋯ + (-1)ᵐ bₘ`
(`TauCeti.newtonPolynomial M m`), built with `TauCeti.Polynomial.monicOfCoeff` from its lower
coefficients. When `M j` is the `j`-th power sum of a multiset `s`, the `b_k`
are the elementary symmetric functions of `s` and, for `m = card s`, `P = ∏_{t ∈ s} (X - t)`, so
the roots of `P` are exactly `s`. Conversely, over an algebraically closed field the roots of `P`,
counted with multiplicity, have power sums `M j` for `1 ≤ j ≤ m`, whatever `M` is. Thus
`newtonPolynomial · m` inverts the passage from a multiset of `m` points to its first `m` power
sums.

This is how a finite measure that should approximate `m` point masses is assigned its candidate
points: its first `m` moments are fed into `newtonPolynomial`, whose roots are the candidates.
Each `b_k` is a polynomial in `M₁, …, M_k`, so it depends continuously on `M`.

## Main definitions

* `TauCeti.newtonCoeff M k`: the `k`-th Newton coefficient `b_k` of the sequence `M`.
* `TauCeti.newtonPolynomial M m`: the monic polynomial `∑_{j ≤ m} (-1)ʲ b_j Xᵐ⁻ʲ`.

## Main results

* `TauCeti.mul_newtonCoeff_eq_sum`: the defining recursion, in the form of
  `Multiset.mul_esymm_eq_sum`.
* `TauCeti.newtonCoeff_sum_map_pow`: the Newton coefficients of the power sums of a multiset are
  its elementary symmetric functions.
* `TauCeti.continuous_newtonCoeff`: `b_k` depends continuously on `M`.
* `TauCeti.newtonPolynomial_eq_monicOfCoeff`: `newtonPolynomial M m` is the monic polynomial with
  lower coefficients `(-1)^(m-i) b_{m-i}`, so the `TauCeti.Polynomial.monicOfCoeff` API applies.
* `TauCeti.monic_newtonPolynomial`, `TauCeti.natDegree_newtonPolynomial`,
  `TauCeti.coeff_newtonPolynomial_sub`.
* `TauCeti.roots_newtonPolynomial_sum_map_pow`: the roots of the polynomial built from the power
  sums of a multiset `s` of cardinality `m` are `s`.
* `TauCeti.sum_map_pow_roots_newtonPolynomial`: over an algebraically closed field, the roots of
  `newtonPolynomial M m` have power sums `M k` for `1 ≤ k ≤ m`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2.
-/

public section

noncomputable section

open Finset Polynomial

namespace TauCeti

variable {K : Type*} [Field K]

/-- The **Newton coefficients** of a sequence `M`: `b₀ = 1` and, for `k ≥ 1`,
`b_k = k⁻¹ * ((-1)^(k+1) ∑_{(i, j) ∈ antidiagonal k, i < k} (-1)ⁱ b_i M_j)`. Whenever `(k : K) ≠ 0`,
in particular in characteristic zero (`TauCeti.mul_newtonCoeff_eq_sum`), this is the recursion
`k b_k = ∑_{j=1}^{k} (-1)^(j-1) b_{k-j} M_j`; when the characteristic divides `k`, the inverse is
`0` and so is `b_k`. When `M j` is the `j`-th power sum of a multiset in characteristic zero, `b_k`
is its `k`-th elementary symmetric function (`TauCeti.newtonCoeff_sum_map_pow`). The value `M 0`
is not used. -/
def newtonCoeff (M : ℕ → K) (k : ℕ) : K :=
  if k = 0 then 1 else
    (k : K)⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ ({a ∈ antidiagonal k | a.1 < k} : Finset (ℕ × ℕ)).attach,
        (-1) ^ a.1.1 * newtonCoeff M a.1.1 * M a.1.2)
termination_by k
decreasing_by exact (mem_filter.1 a.2).2

@[simp]
theorem newtonCoeff_zero (M : ℕ → K) : newtonCoeff M 0 = 1 := by
  simp [newtonCoeff]

theorem newtonCoeff_of_ne_zero (M : ℕ → K) {k : ℕ} (hk : k ≠ 0) :
    newtonCoeff M k = (k : K)⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * newtonCoeff M a.1 * M a.2) := by
  rw [newtonCoeff, ite_eq_right_of_eq_false _ _ (eq_false hk),
    sum_attach _ fun a : ℕ × ℕ => (-1) ^ a.1 * newtonCoeff M a.1 * M a.2]

/-- Each Newton coefficient is a continuous function of the sequence, for the product topology. -/
theorem continuous_newtonCoeff [TopologicalSpace K] [IsTopologicalRing K] (k : ℕ) :
    Continuous fun M : ℕ → K => newtonCoeff M k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using continuous_const
  simp_rw [newtonCoeff_of_ne_zero _ hk]
  refine continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun a ha => ?_))
  exact (continuous_const.mul (ih a.1 (mem_filter.1 ha).2)).mul (continuous_apply a.2)

/-- The polynomial `Xᵐ - b₁ Xᵐ⁻¹ + ⋯ + (-1)ᵐ bₘ` of the Newton coefficients `b_j` of `M`: the
monic polynomial `TauCeti.Polynomial.monicOfCoeff` of degree `m` whose coefficient of `Xⁱ`, for
`i < m`, is `(-1)^(m-i) b_{m-i}` (`TauCeti.newtonPolynomial_eq_monicOfCoeff`). -/
def newtonPolynomial (M : ℕ → K) (m : ℕ) : K[X] :=
  Polynomial.monicOfCoeff fun i : Fin m => (-1) ^ (m - i) * newtonCoeff M (m - i)

/-- `newtonPolynomial M m` is the monic polynomial of degree `m` whose coefficient of `Xⁱ`, for
`i < m`, is `(-1)^(m-i) b_{m-i}`, so the `TauCeti.Polynomial.monicOfCoeff` API applies to it. -/
theorem newtonPolynomial_eq_monicOfCoeff (M : ℕ → K) (m : ℕ) :
    newtonPolynomial M m =
      Polynomial.monicOfCoeff fun i : Fin m => (-1) ^ (m - i) * newtonCoeff M (m - i) :=
  (rfl)

@[simp]
theorem monic_newtonPolynomial (M : ℕ → K) (m : ℕ) : (newtonPolynomial M m).Monic := by
  rw [newtonPolynomial_eq_monicOfCoeff]
  exact Polynomial.monic_monicOfCoeff _

@[simp]
theorem natDegree_newtonPolynomial (M : ℕ → K) (m : ℕ) : (newtonPolynomial M m).natDegree = m := by
  rw [newtonPolynomial_eq_monicOfCoeff, Polynomial.natDegree_monicOfCoeff]

theorem coeff_newtonPolynomial_sub (M : ℕ → K) {m j : ℕ} (hj : j ≤ m) :
    (newtonPolynomial M m).coeff (m - j) = (-1) ^ j * newtonCoeff M j := by
  rw [newtonPolynomial_eq_monicOfCoeff]
  rcases eq_or_ne j 0 with rfl | hj₀
  · simp
  have h := Polynomial.coeff_monicOfCoeff
    (fun i : Fin m => (-1) ^ (m - i) * newtonCoeff M (m - i)) ⟨m - j, by omega⟩
  rwa [Nat.sub_sub_self hj] at h

section CharZero

variable [CharZero K]

/-- The defining recursion of the Newton coefficients, in the form of Newton's identities
`Multiset.mul_esymm_eq_sum`. -/
theorem mul_newtonCoeff_eq_sum (M : ℕ → K) (k : ℕ) :
    k * newtonCoeff M k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * newtonCoeff M a.1 * M a.2 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [newtonCoeff_of_ne_zero M hk, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk), one_mul]

/-- The Newton coefficients of the power sums of a multiset are its elementary symmetric
functions. -/
@[simp]
theorem newtonCoeff_sum_map_pow (s : Multiset K) (k : ℕ) :
    newtonCoeff (fun j => (s.map (· ^ j)).sum) k = s.esymm k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  apply mul_left_cancel₀ (Nat.cast_ne_zero.2 hk : (k : K) ≠ 0)
  rw [mul_newtonCoeff_eq_sum, Multiset.mul_esymm_eq_sum]
  congr 1
  exact sum_congr rfl fun a ha => by rw [ih a.1 (mem_filter.1 ha).2]

/-- The polynomial built from the power sums of a multiset `s`, of degree `card s`, is
`∏_{t ∈ s} (X - t)`. -/
@[simp]
theorem newtonPolynomial_sum_map_pow (s : Multiset K) :
    newtonPolynomial (fun j => (s.map (· ^ j)).sum) (Multiset.card s) =
      (s.map fun t => X - C t).prod := by
  have hmonic : (s.map fun t => X - C t).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  rw [newtonPolynomial_eq_monicOfCoeff, ← Polynomial.monicOfCoeff_coeff hmonic
    (natDegree_multiset_prod_X_sub_C_eq_card s)]
  congr 1
  funext i
  rw [Multiset.prod_X_sub_C_coeff s i.2.le, newtonCoeff_sum_map_pow]

/-- The roots of the polynomial built from the power sums of a multiset `s`, of degree `card s`,
are the elements of `s`, with their multiplicities. -/
theorem roots_newtonPolynomial_sum_map_pow (s : Multiset K) :
    (newtonPolynomial (fun j => (s.map (· ^ j)).sum) (Multiset.card s)).roots = s := by
  rw [newtonPolynomial_sum_map_pow, roots_multiset_prod_X_sub_C]

/-- The Newton coefficients `b₀, …, bₘ` determine `M₁, …, Mₘ`. -/
theorem eq_of_forall_newtonCoeff_eq {M M' : ℕ → K} {m : ℕ}
    (h : ∀ j ≤ m, newtonCoeff M j = newtonCoeff M' j) {k : ℕ} (hk₀ : 0 < k) (hk : k ≤ m) :
    M k = M' k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hmem : ((0, k) : ℕ × ℕ) ∈ ({a ∈ antidiagonal k | a.1 < k} : Finset (ℕ × ℕ)) :=
    mem_filter.2 ⟨mem_antidiagonal.2 (zero_add k), hk₀⟩
  -- Split the term `(0, k)`, the only one involving `M k`, off the recursion for `b_k`.
  have key (N : ℕ → K) : (k : K) * newtonCoeff N k = (-1) ^ (k + 1) * (N k +
      ∑ a ∈ ({a ∈ antidiagonal k | a.1 < k} : Finset (ℕ × ℕ)).erase (0, k),
        (-1) ^ a.1 * newtonCoeff N a.1 * N a.2) := by
    rw [mul_newtonCoeff_eq_sum, ← add_sum_erase _ _ hmem]
    simp
  have hsum : ∑ a ∈ ({a ∈ antidiagonal k | a.1 < k} : Finset (ℕ × ℕ)).erase (0, k),
        (-1) ^ a.1 * newtonCoeff M a.1 * M a.2 =
      ∑ a ∈ ({a ∈ antidiagonal k | a.1 < k} : Finset (ℕ × ℕ)).erase (0, k),
        (-1) ^ a.1 * newtonCoeff M' a.1 * M' a.2 := by
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨hne, ha⟩ := mem_erase.1 ha
    obtain ⟨hak, hlt⟩ := mem_filter.1 ha
    rw [mem_antidiagonal] at hak
    have ha₁ : 0 < a.1 := Nat.pos_of_ne_zero fun h0 => hne (Prod.ext h0 (by simp; omega))
    rw [h a.1 (by omega), ih a.2 (by omega) (by omega) (by omega)]
  have hM := key M
  rw [h k hk, hsum] at hM
  have hs : ((-1 : K)) ^ (k + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  exact add_right_cancel (mul_left_cancel₀ hs (hM.symm.trans (key M')))

section IsAlgClosed

variable [IsAlgClosed K]

omit [CharZero K] in
@[simp]
theorem card_roots_newtonPolynomial (M : ℕ → K) (m : ℕ) :
    Multiset.card (newtonPolynomial M m).roots = m := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_newtonPolynomial]

omit [CharZero K] in
/-- Over an algebraically closed field, the elementary symmetric functions of the roots of
`newtonPolynomial M m` are its Newton coefficients. -/
theorem esymm_roots_newtonPolynomial (M : ℕ → K) {m j : ℕ} (hj : j ≤ m) :
    (newtonPolynomial M m).roots.esymm j = newtonCoeff M j := by
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_newtonPolynomial M m)
    (by rw [card_roots_newtonPolynomial, natDegree_newtonPolynomial])
  have h := Multiset.prod_X_sub_C_coeff (newtonPolynomial M m).roots (k := m - j)
    (by rw [card_roots_newtonPolynomial]; omega)
  rw [hprod, coeff_newtonPolynomial_sub M hj, card_roots_newtonPolynomial,
    Nat.sub_sub_self hj] at h
  exact (mul_right_injective₀ (pow_ne_zero j (neg_ne_zero.2 one_ne_zero))) h.symm

/-- Over an algebraically closed field, the roots of `newtonPolynomial M m`, counted with
multiplicity, have power sums `M k` for `1 ≤ k ≤ m`. -/
theorem sum_map_pow_roots_newtonPolynomial (M : ℕ → K) {m k : ℕ} (hk₀ : 0 < k) (hk : k ≤ m) :
    ((newtonPolynomial M m).roots.map (· ^ k)).sum = M k :=
  eq_of_forall_newtonCoeff_eq (M := fun j => ((newtonPolynomial M m).roots.map (· ^ j)).sum)
    (fun j hj => by rw [newtonCoeff_sum_map_pow, esymm_roots_newtonPolynomial M hj]) hk₀ hk

end IsAlgClosed

end CharZero

end TauCeti
