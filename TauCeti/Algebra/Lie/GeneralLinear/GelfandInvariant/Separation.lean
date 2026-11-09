/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.GelfandInvariant.HighestWeight
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Data.Fintype.CardFilterOrder
import Mathlib.Data.Finset.Sort
import Mathlib.Order.WellFounded

/-!
# The Gelfand invariants separate dominant weights

For a weight `μ` of `gl n`, `TauCeti.gelfandEigenvalue μ r` is the scalar by which the Gelfand
invariant `Cᵣ = trace (𝔼 ^ r)` acts on a highest-weight vector of weight `μ`. This file shows that
these scalars determine an integral dominant weight: over a commutative ring of characteristic zero,
two weakly decreasing integer weights `μ`, `μ'` of `gl n` with the same eigenvalues `Cᵣ(μ) = Cᵣ(μ')`
for `1 ≤ r ≤ n` are equal. Applied at each corner `gl k` of the chain `gl 1 ⊆ ⋯ ⊆ gl n`, this is the
statement that the joint eigencharacter of the Gelfand-Tsetlin generators separates Gelfand-Tsetlin
patterns.

The proof goes through the generating function of the eigenvalues. Write
`lᵢ = μᵢ + #{j | i < j}` for the `ρ`-shifted weight. Then, as formal power series in `X`,

`(∏ᵢ (1 - lᵢ X)) * (1 - X * ∑ᵣ Cᵣ(μ) Xʳ) = ∏ᵢ (1 - (lᵢ + 1) X)`,

a form of the Perelomov-Popov formula for the eigenvalues of the Gelfand invariants
(`TauCeti.prod_mul_one_sub_X_mul_mk_gelfandEigenvalue`). It is proved by induction on `n`,
deleting the first index: the diagonal scalars at the later indices are those of the smaller
weight, and the scalar at the first index satisfies a first-order recurrence.

Reversing the polynomials, the formula says that the polynomial `Q(X) = ∏ᵢ (X - lᵢ)` satisfies
`Q(X) - Q(X - 1) = ∑ₖ qₖ ∑_{r < k} Cᵣ X^(k - 1 - r)`. If two weights `μ`, `μ'` have the same
eigenvalues in degrees at most `n`, compare the top coefficient of `D = Q - Q'`: if `D` has degree
`t < n` and leading coefficient `d`, the coefficient of `X^(t - 1)` in `D(X) - D(X - 1)` is `t d`,
while the formula computes it as `n d`. In characteristic zero this forces `d = 0`, so `Q = Q'`.
The roots of `Q` are the shifted weights, which are strictly decreasing for a weakly decreasing
`μ`, so the weights agree. The degrees `1, …, n - 1` alone do not suffice in general: for `gl 1`
there are none, and the invariant of degree zero is the rank, which does not see the weight.

## Main results

* `TauCeti.prod_mul_one_sub_X_mul_mk_gelfandEigenvalue`: the generating function of the
  highest-weight eigenvalues of the Gelfand invariants.
* `TauCeti.eq_of_forall_gelfandEigenvalue_eq`: the eigenvalues of the Gelfand invariants of degrees
  `1, …, n` separate the weakly decreasing integer weights of `gl n`.

## References

* A. M. Perelomov and V. S. Popov, *Casimir operators for semisimple Lie groups*, Izv. Akad. Nauk
  SSSR Ser. Mat. **32** (1968), 1368–1390.
* A. Molev, *Yangians and Classical Lie Algebras* (2007), Chapter 7.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {K : Type*} [CommRing K]

/-! ### The generating function -/

section GeneratingFunction

variable {m : ℕ}

private theorem gelfandEigenvalueEntry_comp_succ (μ : Fin (m + 1) → K) (r : ℕ) (i : Fin m) :
    gelfandEigenvalueEntry (μ ∘ Fin.succ) r i = gelfandEigenvalueEntry μ r i.succ := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [gelfandEigenvalueEntry_succ, gelfandEigenvalueEntry_succ, Fin.sum_univ_succ]
    simp [ih]

private theorem gelfandEigenvalueEntry_succ_zero (μ : Fin (m + 1) → K) (r : ℕ) :
    gelfandEigenvalueEntry μ (r + 1) 0 =
      (μ 0 + m) * gelfandEigenvalueEntry μ r 0 - gelfandEigenvalue (μ ∘ Fin.succ) r := by
  rw [gelfandEigenvalueEntry_succ, Fin.sum_univ_succ]
  simp [gelfandEigenvalue_def, gelfandEigenvalueEntry_comp_succ, sum_sub_distrib]
  ring

private theorem gelfandEigenvalue_eq_entry_zero_add (μ : Fin (m + 1) → K) (r : ℕ) :
    gelfandEigenvalue μ r = gelfandEigenvalueEntry μ r 0 + gelfandEigenvalue (μ ∘ Fin.succ) r := by
  simp [gelfandEigenvalue_def, Fin.sum_univ_succ, gelfandEigenvalueEntry_comp_succ]

private theorem prod_mul_one_sub_X_mul_mk_gelfandEigenvalue_fin :
    ∀ (m : ℕ) (μ : Fin m → K),
      (∏ i, (1 - PowerSeries.C (μ i + #{j | i < j}) * PowerSeries.X)) *
          (1 - PowerSeries.X * PowerSeries.mk (gelfandEigenvalue μ)) =
        ∏ i, (1 - PowerSeries.C (μ i + #{j | i < j} + 1) * PowerSeries.X)
  | 0, μ => by
    have h : PowerSeries.mk (gelfandEigenvalue μ) = 0 := by
      ext r
      simp [gelfandEigenvalue_def]
    simp [h]
  | m + 1, μ => by
    have ih := prod_mul_one_sub_X_mul_mk_gelfandEigenvalue_fin m (μ ∘ Fin.succ)
    set A := PowerSeries.mk fun r => gelfandEigenvalueEntry μ r 0
    set S := PowerSeries.mk (gelfandEigenvalue (μ ∘ Fin.succ))
    have hA : (1 - PowerSeries.C (μ 0 + m) * PowerSeries.X) * A = 1 - PowerSeries.X * S := by
      ext (_ | r)
      · simp [A]
      · rw [sub_mul, one_mul, mul_assoc, map_sub, map_sub, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
        simp [A, S, gelfandEigenvalueEntry_succ_zero]
    have hS : PowerSeries.mk (gelfandEigenvalue μ) = A + S := by
      ext r
      simp [A, S, gelfandEigenvalue_eq_entry_zero_add]
    have hcard (i : Fin m) : #{j : Fin (m + 1) | i.succ < j} = #{j : Fin m | i < j} := by
      simp only [filter_lt_eq_Ioi, Fin.card_Ioi, Fin.val_succ]
      omega
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, hS,
      show #{j : Fin (m + 1) | 0 < j} = m by simp [filter_lt_eq_Ioi]]
    simp only [hcard, Function.comp_apply] at ih ⊢
    simp only [map_add, map_one] at ih hA ⊢
    linear_combination
      (-PowerSeries.X * ∏ i : Fin m, (1 - (PowerSeries.C (μ i.succ) +
        PowerSeries.C (#{j | i < j} : K)) * PowerSeries.X)) * hA +
      (1 - (PowerSeries.C (μ 0) + PowerSeries.C (m : K) + 1) * PowerSeries.X) * ih

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **The generating function of the eigenvalues of the Gelfand invariants** (Perelomov-Popov).
For the `ρ`-shifted weight `lᵢ = μᵢ + #{j | i < j}`, the highest-weight eigenvalues `Cᵣ(μ)` of the
Gelfand invariants satisfy `(∏ᵢ (1 - lᵢ X)) * (1 - X * ∑ᵣ Cᵣ(μ) Xʳ) = ∏ᵢ (1 - (lᵢ + 1) X)`. -/
theorem prod_mul_one_sub_X_mul_mk_gelfandEigenvalue (μ : n → K) :
    (∏ i, (1 - PowerSeries.C (μ i + #{j | i < j}) * PowerSeries.X)) *
        (1 - PowerSeries.X * PowerSeries.mk (gelfandEigenvalue μ)) =
      ∏ i, (1 - PowerSeries.C (μ i + #{j | i < j} + 1) * PowerSeries.X) := by
  let e := Fintype.orderIsoFinOfCardEq n rfl
  have hcard (i : Fin (Fintype.card n)) : #{j | e i < j} = #{j | i < j} :=
    (card_equiv e.toEquiv fun j => by simp).symm
  have h := prod_mul_one_sub_X_mul_mk_gelfandEigenvalue_fin _ (μ ∘ e)
  rw [funext (gelfandEigenvalue_comp_orderIso e μ)] at h
  rw [← e.toEquiv.prod_comp, ← e.toEquiv.prod_comp]
  simpa [hcard] using h

end GeneratingFunction

/-! ### Separation of dominant weights -/

section Separation

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- The coefficients of the reversed generating-function identity, as a statement about
polynomials. -/
private theorem coeff_reflect_prod_X_sub_C_sub_sum (μ : n → K) (r : ℕ) :
    (reflect (Fintype.card n) (∏ i, (X - C (μ i + #{j | i < j})))).coeff (r + 1) -
        ∑ p ∈ antidiagonal r,
          (reflect (Fintype.card n) (∏ i, (X - C (μ i + #{j | i < j})))).coeff p.1 *
            gelfandEigenvalue μ p.2 =
      (reflect (Fintype.card n) ((∏ i, (X - C (μ i + #{j | i < j}))).comp (X - 1))).coeff
        (r + 1) := by
  have hcomp : (∏ i, (X - C (μ i + #{j | i < j}))).comp (X - 1) =
      ∏ i, (X - C (μ i + #{j | i < j} + 1)) := by
    rw [Polynomial.prod_comp]
    refine prod_congr rfl fun i _ => ?_
    rw [sub_comp, X_comp, C_comp, C_add (b := 1), C_1]
    ring
  have hcoe (c : n → K) : ((reflect (Fintype.card n) (∏ i, (X - C (c i))) : K[X]) :
      PowerSeries K) = ∏ i, (1 - PowerSeries.C (c i) * PowerSeries.X) := by
    rw [← card_univ, card_eq_sum_ones, reflect_prod _ _ _ fun i _ => natDegree_X_sub_C_le _,
      ← coeToPowerSeries.ringHom_apply, map_prod]
    simp [reflect_sub, reflect_C]
  have h := congrArg (PowerSeries.coeff (r + 1)) (prod_mul_one_sub_X_mul_mk_gelfandEigenvalue μ)
  rw [← hcoe, ← hcoe, mul_sub, mul_one, map_sub, mul_left_comm, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_mul] at h
  simp only [coeff_coe, PowerSeries.coeff_mk] at h
  rwa [hcomp]

/-- Two weights of `gl n` with the same Gelfand-invariant eigenvalues in degrees at most `n` have
the same `ρ`-shifted weights, up to order. -/
private theorem prod_X_sub_C_eq_of_gelfandEigenvalue_eq [IsDomain K] [CharZero K] {μ μ' : n → K}
    (h : ∀ r ≤ Fintype.card n, gelfandEigenvalue μ r = gelfandEigenvalue μ' r) :
    ∏ i, (X - C (μ i + #{j | i < j})) = ∏ i, (X - C (μ' i + #{j | i < j})) := by
  have h1 := coeff_reflect_prod_X_sub_C_sub_sum μ
  have h2 := coeff_reflect_prod_X_sub_C_sub_sum μ'
  set m := Fintype.card n
  set Q := ∏ i, (X - C (μ i + #{j | i < j}))
  set Q' := ∏ i, (X - C (μ' i + #{j | i < j}))
  have hmonic (ν : n → K) : (∏ i, (X - C (ν i + #{j | i < j}))).Monic :=
    monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hdeg (ν : n → K) : (∏ i, (X - C (ν i + #{j | i < j}))).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, sum_const, card_univ, smul_eq_mul, mul_one, m]
  by_contra hne
  set D := Q - Q' with hD
  have hD0 : D ≠ 0 := sub_ne_zero.mpr hne
  have hDm : D.natDegree < m := by
    refine (natDegree_lt_natDegree hD0 (degree_sub_lt_left ?_ (hmonic μ).ne_zero ?_)).trans_eq
      (hdeg μ)
    · rw [degree_eq_natDegree (hmonic μ).ne_zero, degree_eq_natDegree (hmonic μ').ne_zero,
        hdeg μ, hdeg μ']
    · rw [(hmonic μ).leadingCoeff, (hmonic μ').leadingCoeff]
  set t := D.natDegree with ht
  -- The convolution of the reversed difference with the eigenvalues only sees the leading term.
  have hsum : ∑ p ∈ antidiagonal (m - t), (reflect m D).coeff p.1 * gelfandEigenvalue μ p.2 =
      D.leadingCoeff * m := by
    rw [sum_eq_single_of_mem (m - t, 0) (mem_antidiagonal.mpr (add_zero _))]
    · rw [coeff_reflect, revAt_le (by omega), show m - (m - t) = t by omega, gelfandEigenvalue_zero,
        leadingCoeff]
    · rintro ⟨a, b⟩ hab hne'
      rw [mem_antidiagonal] at hab
      have hb : b ≠ 0 := by
        rintro rfl
        exact hne' (by simp_all)
      rw [coeff_reflect, revAt_le (by omega),
        coeff_eq_zero_of_natDegree_lt (show D.natDegree < m - a by omega), zero_mul]
  have hcomb : (reflect m (D - D.comp (X - 1))).coeff (m - t + 1) =
      ∑ p ∈ antidiagonal (m - t), (reflect m D).coeff p.1 * gelfandEigenvalue μ p.2 := by
    have hs : ∑ p ∈ antidiagonal (m - t), (reflect m Q').coeff p.1 * gelfandEigenvalue μ' p.2 =
        ∑ p ∈ antidiagonal (m - t), (reflect m Q').coeff p.1 * gelfandEigenvalue μ p.2 :=
      sum_congr rfl fun p hp => by
        rw [h p.2 (by have := mem_antidiagonal.mp hp; omega)]
    simp only [hD, sub_comp, reflect_sub, coeff_sub, sub_mul, sum_sub_distrib]
    linear_combination h1 (m - t) - h2 (m - t) - hs
  rw [← C_1, coeff_reflect_sub_comp_X_sub_C D hDm.le, mul_one, hsum] at hcomb
  have hzero : ((m - t : ℕ) : K) * D.leadingCoeff = 0 := by
    rw [Nat.cast_sub hDm.le]
    linear_combination -hcomb
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.mpr (by omega))
  · exact hD0 (leadingCoeff_eq_zero.mp h0)

private theorem eq_of_forall_gelfandEigenvalue_eq_of_isDomain [IsDomain K] [CharZero K]
    {μ μ' : n → ℤ}
    (hμ : Antitone μ) (hμ' : Antitone μ')
    (h : ∀ r ∈ Icc 1 (Fintype.card n),
      gelfandEigenvalue (fun i => (μ i : K)) r = gelfandEigenvalue (fun i => (μ' i : K)) r) :
    μ = μ' := by
  have h' : ∀ r ≤ Fintype.card n,
      gelfandEigenvalue (fun i => (μ i : K)) r = gelfandEigenvalue (fun i => (μ' i : K)) r := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp
    · exact h r (mem_Icc.mpr ⟨hr0, hr⟩)
  set L : n → ℤ := fun i => μ i + (#{j | i < j} : ℤ)
  set L' : n → ℤ := fun i => μ' i + (#{j | i < j} : ℤ)
  have hQ := congrArg roots (prod_X_sub_C_eq_of_gelfandEigenvalue_eq h')
  have hcast (ν : n → ℤ) : ∏ i, (X - C ((ν i : K) + #{j | i < j})) =
      ((univ.val.map fun i => ((ν i + (#{j | i < j} : ℤ) : ℤ) : K)).map fun a => X - C a).prod := by
    rw [prod_eq_multiset_prod, Multiset.map_map]
    push_cast
    rfl
  rw [hcast, hcast, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hQ
  have hmap : univ.val.map L = univ.val.map L' := by
    refine Multiset.map_injective (Int.cast_injective (α := K)) ?_
    rw [Multiset.map_map, Multiset.map_map]
    exact hQ
  have hrange : Set.range L = Set.range L' := by
    ext x
    simpa using congrArg (x ∈ ·) hmap
  have hLL := ((strictAnti_add_card_filter_lt hμ).range_inj_of_wellFoundedLT
    (strictAnti_add_card_filter_lt hμ')).mp hrange
  funext i
  simpa [L, L'] using congrFun hLL i

/-- **The Gelfand invariants separate dominant weights.** Over a commutative ring of characteristic
zero, two weakly decreasing integer weights of `gl n` on which the Gelfand invariants of degrees
`1, …, n` have the same highest-weight eigenvalues are equal. -/
theorem eq_of_forall_gelfandEigenvalue_eq [CharZero K] {μ μ' : n → ℤ}
    (hμ : Antitone μ) (hμ' : Antitone μ')
    (h : ∀ r ∈ Icc 1 (Fintype.card n),
      gelfandEigenvalue (fun i => (μ i : K)) r = gelfandEigenvalue (fun i => (μ' i : K)) r) :
    μ = μ' := by
  -- The eigenvalues of integer weights are integers, so it suffices to separate over `ℤ`.
  refine eq_of_forall_gelfandEigenvalue_eq_of_isDomain (K := ℤ) hμ hμ' fun r hr => ?_
  refine Int.cast_injective (α := K) ?_
  have hcast (ν : n → ℤ) : ((gelfandEigenvalue ν r : ℤ) : K) =
      gelfandEigenvalue (fun i => (ν i : K)) r :=
    map_gelfandEigenvalue (Int.castRingHom K) ν r
  simpa only [Int.cast_id, hcast] using h r hr

end Separation

end TauCeti
