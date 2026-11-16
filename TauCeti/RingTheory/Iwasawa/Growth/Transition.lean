/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.Polynomial.Distinguished

import TauCeti.RingTheory.Iwasawa.CyclotomicGrowth
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm

/-!
# Cyclotomic transition polynomials and power series

For a natural number `p`, a commutative ring `O`, and levels `n₀, n : ℕ`, the *cyclotomic
transition* from `n₀` to `n` is the product

```text
ν_{n,n₀} = ∏_{n₀ ≤ j ≤ n} ξ_j,
```

where `ξ_0 = X` and `ξ_j = ∑_{i < p} (1 + X) ^ (i p ^ (j - 1))` for `j ≥ 1`. Writing the
transition directly as a product avoids division in `O⟦X⟧`: with the convention `ω_{-1} = 1`, one
has `ν_{n,0} = ω_n = (1 + X) ^ p ^ n - 1` for every `p : ℕ`, and
`(∏_{j < n₀} ξ_j) * ν_{n,n₀} = ν_{n,0}` for `n₀ ≤ n + 1`.

For `0 < n₀`, the constant coefficient of `ν_{n,n₀}` is `p ^ (n + 1 - n₀)`, whereas
`ν_{n,0}` has constant coefficient `0` and annihilates `O⟦X⟧ ⧸ (X)`. Separating the cutoff level
`n₀` from `0` is what allows Iwasawa's growth theorem to apply to modules on which `ω_n` has
infinite cokernel because `charPoly` vanishes at `ζ - 1` for finitely many `p`-power roots of unity
`ζ` (equivalently, shares a factor with finitely many `ξ_j = Φ_{p ^ j}(X + 1)`).

For `p ≠ 0`, `ν_{n,n₀}` is monic of degree `p ^ n - (if n₀ = 0 then 0 else p ^ (n₀ - 1))` over any
nontrivial ring. When `p` is prime, each factor `ξ_j` is the shifted cyclotomic polynomial
`Φ_{p ^ j}(X + 1)`, so `ν_{n,n₀}` is distinguished at every ideal containing `p`. On an `I`-adically
complete ring `O`, combining multiplicativity of the resultant in its right argument with
`Polynomial.IsDistinguishedAt.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one` shows
that for prime `p` and `F` distinguished at `I` with `I ^ e ⊆ (p)` and `p` in the Jacobson radical
of `O`, `Res(F, ν_{k,n₀})` grows by an associate of `p ^ deg F` at every step starting at
`m ≥ max (n₀ - 1) (deg F * e + 1)` (i.e. `n₀ ≤ m + 1` and `deg F * e < m`).

## Main definitions

* `TauCeti.Iwasawa.growthTransitionPoly`: the transition polynomial `ν_{n,n₀} ∈ O[X]`.
* `TauCeti.Iwasawa.growthTransition`: the transition power series `ν_{n,n₀} ∈ O⟦X⟧`.

## Main results

* `TauCeti.Iwasawa.coeff_zero_growthTransitionPoly`,
  `TauCeti.Iwasawa.growthTransition_constantCoeff`: for `0 < n₀`, the constant coefficient of
  `ν_{n,n₀}` is `p ^ (n + 1 - n₀)`.
* `TauCeti.Iwasawa.growthTransitionPoly_zero_left`, `TauCeti.Iwasawa.growthTransition_zero_left`:
  `ν_{n,0} = (1 + X) ^ p ^ n - 1`.
* `TauCeti.Iwasawa.monic_growthTransitionPoly`, `TauCeti.Iwasawa.natDegree_growthTransitionPoly`:
  for `p ≠ 0`, `ν_{n,n₀}` is monic and over a nontrivial ring has degree
  `p ^ n - if n₀ = 0 then 0 else p ^ (n₀ - 1)`.
* `TauCeti.Iwasawa.isDistinguishedAt_growthTransitionPoly`: for prime `p` with `p ∈ I`,
  `ν_{n,n₀}` is distinguished at `I`.
* `TauCeti.Iwasawa.associated_resultant_growthTransitionPoly`: for `n₀ ≤ m + 1`,
  `deg F * e < m`, and `m ≤ k`, `Res(F, ν_{k,n₀})` is associated to
  `Res(F, ν_{m,n₀}) * p ^ (deg F * (k - m))`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, (5.3.17)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public noncomputable section

open PowerSeries
open scoped Polynomial PowerSeries

namespace TauCeti.Iwasawa

section General

/-- The cyclotomic transition polynomial `ν_{n,n₀} = ω_n / ω_{n₀ - 1} = ∏_{n₀ ≤ j ≤ n} ξ_j` in
`O[X]`, written without division (`ω_{-1} = 1`, so `n₀ = 0` gives `ω_n`). -/
def growthTransitionPoly (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ) : O[X] :=
  ∏ j ∈ Finset.Ico n₀ (n + 1),
    if j = 0 then Polynomial.X else ∑ i ∈ Finset.range p, (1 + Polynomial.X) ^ (i * p ^ (j - 1))

/-- The cyclotomic transition element `ν_{n,n₀} = ω_n / ω_{n₀ - 1} = ∏_{n₀ ≤ j ≤ n} ξ_j` in
`O⟦X⟧`, defined by coercing `growthTransitionPoly p O n₀ n`. -/
def growthTransition (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ) : O⟦X⟧ :=
  growthTransitionPoly p O n₀ n

/-- Unfolding `growthTransitionPoly`. -/
theorem growthTransitionPoly_def (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ) :
    growthTransitionPoly p O n₀ n =
      ∏ j ∈ Finset.Ico n₀ (n + 1), if j = 0 then Polynomial.X
        else ∑ i ∈ Finset.range p, (1 + Polynomial.X) ^ (i * p ^ (j - 1)) := (rfl)

/-- Coercing `growthTransitionPoly` from `O[X]` to `O⟦X⟧` gives `growthTransition`. -/
@[simp]
theorem coe_growthTransitionPoly (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ) :
    ((growthTransitionPoly p O n₀ n : O[X]) : O⟦X⟧) = growthTransition p O n₀ n := (rfl)

/-- Unfolding `growthTransition` as a product in `O⟦X⟧`. -/
theorem growthTransition_def (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ) :
    growthTransition p O n₀ n =
      ∏ j ∈ Finset.Ico n₀ (n + 1),
        if j = 0 then X else ∑ i ∈ Finset.range p, (1 + X) ^ (i * p ^ (j - 1)) := by
  rw [← coe_growthTransitionPoly, growthTransitionPoly_def,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp [Polynomial.coeToPowerSeries.ringHom_apply]

/-- Mapping `growthTransitionPoly` along a ring homomorphism changes the coefficient ring. -/
@[simp]
theorem map_growthTransitionPoly {O O' : Type*} [CommRing O] [CommRing O'] (f : O →+* O')
    (p n₀ n : ℕ) :
    (growthTransitionPoly p O n₀ n).map f = growthTransitionPoly p O' n₀ n := by
  rw [← Polynomial.coe_mapRingHom, growthTransitionPoly_def, growthTransitionPoly_def, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  split_ifs
  · simp
  · rw [map_sum]
    simp

/-- Mapping `growthTransition` along a ring homomorphism changes the coefficient ring. -/
@[simp]
theorem map_growthTransition {O O' : Type*} [CommRing O] [CommRing O'] (f : O →+* O')
    (p n₀ n : ℕ) :
    PowerSeries.map f (growthTransition p O n₀ n) = growthTransition p O' n₀ n := by
  ext k
  rw [coeff_map, ← coe_growthTransitionPoly, ← coe_growthTransitionPoly, Polynomial.coeff_coe,
    Polynomial.coeff_coe, ← map_growthTransitionPoly f, Polynomial.coeff_map]

/-- When `n < n₀`, the transition product is empty and equals `1`. -/
@[simp]
theorem growthTransitionPoly_of_lt (p : ℕ) (O : Type*) [CommRing O] {n₀ n : ℕ} (h : n < n₀) :
    growthTransitionPoly p O n₀ n = 1 := by
  rw [growthTransitionPoly_def, Finset.Ico_eq_empty (by omega), Finset.prod_empty]

/-- When `n < n₀`, the transition series is empty and equals `1`. -/
@[simp]
theorem growthTransition_of_lt (p : ℕ) (O : Type*) [CommRing O] {n₀ n : ℕ} (h : n < n₀) :
    growthTransition p O n₀ n = 1 := by
  rw [← coe_growthTransitionPoly, growthTransitionPoly_of_lt p O h, Polynomial.coe_one]

/-- At level `(0, 0)`, the transition polynomial is `X`. -/
theorem growthTransitionPoly_zero_zero (p : ℕ) (O : Type*) [CommRing O] :
    growthTransitionPoly p O 0 0 = Polynomial.X := by
  simp [growthTransitionPoly_def]

/-- At level `(0, 0)`, the transition series is `X`. -/
theorem growthTransition_zero_zero (p : ℕ) (O : Type*) [CommRing O] :
    growthTransition p O 0 0 = X := by
  rw [← coe_growthTransitionPoly, growthTransitionPoly_zero_zero, Polynomial.coe_X]

/-- At diagonal level `(n, n)` with `n > 0`, the transition polynomial is the single factor
`ξ_n`. -/
theorem growthTransitionPoly_self_of_pos (p : ℕ) (O : Type*) [CommRing O] {n : ℕ} (hn : 0 < n) :
    growthTransitionPoly p O n n =
      ∑ i ∈ Finset.range p, (1 + Polynomial.X) ^ (i * p ^ (n - 1)) := by
  rw [growthTransitionPoly_def, Nat.Ico_succ_singleton, Finset.prod_singleton, ite_eq_right hn.ne']

/-- Consecutive transition polynomials multiply: `ν_{m,n₀} * ν_{n,m+1} = ν_{n,n₀}`. -/
theorem growthTransitionPoly_mul_of_le (p : ℕ) (O : Type*) [CommRing O] {n₀ m n : ℕ}
    (h₁ : n₀ ≤ m + 1) (h₂ : m ≤ n) :
    growthTransitionPoly p O n₀ m * growthTransitionPoly p O (m + 1) n =
      growthTransitionPoly p O n₀ n :=
  Finset.prod_Ico_consecutive _ h₁ (Nat.succ_le_succ h₂)

/-- Consecutive transition series multiply: `ν_{m,n₀} * ν_{n,m+1} = ν_{n,n₀}`. -/
theorem growthTransition_mul_of_le (p : ℕ) (O : Type*) [CommRing O] {n₀ m n : ℕ}
    (h₁ : n₀ ≤ m + 1) (h₂ : m ≤ n) :
    growthTransition p O n₀ m * growthTransition p O (m + 1) n = growthTransition p O n₀ n := by
  rw [← coe_growthTransitionPoly, ← coe_growthTransitionPoly, ← Polynomial.coe_mul,
    growthTransitionPoly_mul_of_le p O h₁ h₂, coe_growthTransitionPoly]

/-- For `m ≤ n`, `ν_{m,n₀}` divides `ν_{n,n₀}` in `O[X]`. -/
theorem growthTransitionPoly_dvd_of_le (p : ℕ) (O : Type*) [CommRing O] (n₀ : ℕ) {m n : ℕ}
    (hmn : m ≤ n) : growthTransitionPoly p O n₀ m ∣ growthTransitionPoly p O n₀ n := by
  by_cases hm : n₀ ≤ m + 1
  · exact ⟨growthTransitionPoly p O (m + 1) n,
      (growthTransitionPoly_mul_of_le p O hm hmn).symm⟩
  · rw [growthTransitionPoly_of_lt p O (by omega)]
    exact one_dvd _

/-- For `m ≤ n`, `ν_{m,n₀}` divides `ν_{n,n₀}` in `O⟦X⟧`. -/
theorem growthTransition_dvd_of_le (p : ℕ) (O : Type*) [CommRing O] (n₀ : ℕ) {m n : ℕ}
    (hmn : m ≤ n) : growthTransition p O n₀ m ∣ growthTransition p O n₀ n :=
  _root_.map_dvd Polynomial.coeToPowerSeries.ringHom (growthTransitionPoly_dvd_of_le p O n₀ hmn)

/-- For `0 < n₀`, the product of the diagonal factors `ξ_j = ν_{j,j}` for `j < n₀` is
`ν_{n₀ - 1, 0}`. -/
theorem prod_range_growthTransitionPoly_eq (p : ℕ) (O : Type*) [CommRing O] {n₀ : ℕ}
    (h₀ : 0 < n₀) :
    ∏ j ∈ Finset.range n₀, growthTransitionPoly p O j j =
      growthTransitionPoly p O 0 (n₀ - 1) := by
  rw [growthTransitionPoly_def, Nat.sub_add_cancel h₀, Nat.Ico_zero_eq_range]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [growthTransitionPoly_def, Nat.Ico_succ_singleton, Finset.prod_singleton]

/-- In `O⟦X⟧`, for `0 < n₀`, the product of the diagonal factors `ξ_j = ν_{j,j}` for `j < n₀` is
`ν_{n₀ - 1, 0}`. -/
theorem prod_range_growthTransition_eq (p : ℕ) (O : Type*) [CommRing O] {n₀ : ℕ}
    (h₀ : 0 < n₀) :
    ∏ j ∈ Finset.range n₀, growthTransition p O j j =
      growthTransition p O 0 (n₀ - 1) := by
  have h := congr_arg (Polynomial.coeToPowerSeries.ringHom (R := O))
    (prod_range_growthTransitionPoly_eq p O h₀)
  simpa only [map_prod, Polynomial.coeToPowerSeries.ringHom_apply,
    coe_growthTransitionPoly] using h

/-- Multiplying the prefix `∏_{j < n₀} ν_{j,j}` by the transition `ν_{n,n₀}` recovers `ν_{n,0}`. -/
theorem prod_range_growthTransitionPoly_mul (p : ℕ) (O : Type*) [CommRing O] {n₀ n : ℕ}
    (hn : n₀ ≤ n + 1) :
    (∏ j ∈ Finset.range n₀, growthTransitionPoly p O j j) * growthTransitionPoly p O n₀ n =
      growthTransitionPoly p O 0 n := by
  rcases Nat.eq_zero_or_pos n₀ with rfl | h₀
  · simp
  · rw [prod_range_growthTransitionPoly_eq p O h₀]
    have hmul := growthTransitionPoly_mul_of_le p O (Nat.zero_le _) (n := n) (m := n₀ - 1)
    rw [Nat.sub_add_cancel h₀] at hmul
    exact hmul (by omega)

/-- In `O⟦X⟧`, multiplying `∏_{j < n₀} ν_{j,j}` by `ν_{n,n₀}` recovers `ν_{n,0}`. -/
theorem prod_range_growthTransition_mul (p : ℕ) (O : Type*) [CommRing O] {n₀ n : ℕ}
    (hn : n₀ ≤ n + 1) :
    (∏ j ∈ Finset.range n₀, growthTransition p O j j) * growthTransition p O n₀ n =
      growthTransition p O 0 n := by
  have h := congr_arg (Polynomial.coeToPowerSeries.ringHom (R := O))
    (prod_range_growthTransitionPoly_mul p O hn)
  simpa only [map_mul, map_prod, Polynomial.coeToPowerSeries.ringHom_apply,
    coe_growthTransitionPoly] using h

/-- For every `p` and `n`, `ν_{n,0} = (1 + X) ^ p ^ n - 1` in `O[X]`. -/
@[simp]
theorem growthTransitionPoly_zero_left (p : ℕ) (O : Type*) [CommRing O] (n : ℕ) :
    growthTransitionPoly p O 0 n = (1 + Polynomial.X) ^ p ^ n - 1 := by
  induction n with
  | zero => simp [growthTransitionPoly_zero_zero]
  | succ n ih =>
    rw [← growthTransitionPoly_mul_of_le p O (Nat.zero_le _) (Nat.le_succ n), ih,
      growthTransitionPoly_self_of_pos p O (Nat.succ_pos n), Nat.succ_sub_one]
    have hsum : ∑ i ∈ Finset.range p, (1 + Polynomial.X : O[X]) ^ (i * p ^ n) =
        ∑ i ∈ Finset.range p, ((1 + Polynomial.X : O[X]) ^ p ^ n) ^ i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← pow_mul, mul_comm]
    rw [hsum, mul_comm, geom_sum_mul, ← pow_mul, ← pow_succ]

/-- For every `p` and `n`, `ν_{n,0} = (1 + X) ^ p ^ n - 1` in `O⟦X⟧`. -/
@[simp]
theorem growthTransition_zero_left (p : ℕ) (O : Type*) [CommRing O] (n : ℕ) :
    growthTransition p O 0 n = (1 + X) ^ p ^ n - 1 := by
  rw [← coe_growthTransitionPoly, growthTransitionPoly_zero_left]
  simp

/-- For `0 < n₀`, the constant term of `ν_{n,n₀}` in `O[X]` is `p ^ (n + 1 - n₀)`. -/
@[simp]
theorem coeff_zero_growthTransitionPoly (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ)
    (h₀ : 0 < n₀) :
    (growthTransitionPoly p O n₀ n).coeff 0 = (p : O) ^ (n + 1 - n₀) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, growthTransitionPoly_def,
    map_prod]
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico n₀ (n + 1)) :
      Polynomial.evalRingHom 0 (if j = 0 then (Polynomial.X : O[X])
        else ∑ i ∈ Finset.range p, (1 + Polynomial.X : O[X]) ^ (i * p ^ (j - 1))) =
        (p : O) := by
    rw [ite_eq_right (by have := (Finset.mem_Ico.mp hj).1; omega), map_sum]
    simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_const, Nat.card_Ico]

/-- On `O⟦X⟧ ⧸ (X)`, the transition `ν_{n,n₀}` acts by `p ^ (n + 1 - n₀)` when `0 < n₀`,
whereas `ν_{n,0}` has constant coefficient `0`. -/
@[simp]
theorem growthTransition_constantCoeff (p : ℕ) (O : Type*) [CommRing O] (n₀ n : ℕ)
    (h₀ : 0 < n₀) :
    constantCoeff (growthTransition p O n₀ n) = (p : O) ^ (n + 1 - n₀) := by
  rw [← coe_growthTransitionPoly, Polynomial.constantCoeff_coe,
    coeff_zero_growthTransitionPoly p O n₀ n h₀]

/-- When `p ≠ 0`, every transition polynomial `ν_{n,n₀}` is monic. -/
theorem monic_growthTransitionPoly (p : ℕ) [NeZero p] (O : Type*) [CommRing O] (n₀ n : ℕ) :
    (growthTransitionPoly p O n₀ n).Monic := by
  have h0 (k : ℕ) : (growthTransitionPoly p O 0 k).Monic := by
    rw [growthTransitionPoly_zero_left]
    exact TauCeti.Polynomial.monic_one_add_X_pow_sub_one (pow_ne_zero k (NeZero.ne p))
  rcases lt_or_ge n n₀ with hlt | hle
  · rw [growthTransitionPoly_of_lt p O hlt]
    exact Polynomial.monic_one
  · rcases Nat.eq_zero_or_pos n₀ with rfl | h₀
    · exact h0 n
    · refine (h0 (n₀ - 1)).of_mul_monic_left ?_
      rw [← prod_range_growthTransitionPoly_eq p O h₀,
        prod_range_growthTransitionPoly_mul p O (by omega)]
      exact h0 n

/-- Over a nontrivial ring and for `p ≠ 0`, the degree of `ν_{n,n₀}` is
`p ^ n - if n₀ = 0 then 0 else p ^ (n₀ - 1)`. -/
theorem natDegree_growthTransitionPoly (p : ℕ) [NeZero p] (O : Type*) [CommRing O] [Nontrivial O]
    (n₀ n : ℕ) :
    (growthTransitionPoly p O n₀ n).natDegree =
      p ^ n - if n₀ = 0 then 0 else p ^ (n₀ - 1) := by
  rcases lt_or_ge n n₀ with hlt | hle
  · have h₀ : n₀ ≠ 0 := by omega
    have hpow : p ^ n ≤ p ^ (n₀ - 1) :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne p)) (by omega)
    rw [growthTransitionPoly_of_lt p O hlt, Polynomial.natDegree_one, ite_eq_right h₀,
      Nat.sub_eq_zero_of_le hpow]
  · rcases Nat.eq_zero_or_pos n₀ with rfl | h₀
    · simp [TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one]
    · rw [ite_eq_right h₀.ne']
      have hmul := prod_range_growthTransitionPoly_mul p O (n₀ := n₀) (n := n) (by omega)
      rw [prod_range_growthTransitionPoly_eq p O h₀] at hmul
      have hdeg := congr_arg Polynomial.natDegree hmul
      rw [(monic_growthTransitionPoly p O 0 (n₀ - 1)).natDegree_mul
        (monic_growthTransitionPoly p O n₀ n), growthTransitionPoly_zero_left,
        growthTransitionPoly_zero_left, TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one,
        TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one] at hdeg
      omega

end General

section Prime

variable (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]

/-- When `p` is prime, the transition polynomial `ν_{n,n₀}` is the product of the shifted
prime-power cyclotomic polynomials `Φ_{p ^ j}(X + 1)` for `n₀ ≤ j ≤ n`. -/
theorem growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one (n₀ n : ℕ) :
    growthTransitionPoly p O n₀ n =
      ∏ j ∈ Finset.Ico n₀ (n + 1), (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) := by
  rw [growthTransitionPoly_def]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rcases j with _ | j
  · simp
  · simp [Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_sum p j]

/-- When `p` is prime, the diagonal transition polynomial `ν_{j,j}` is `Φ_{p ^ j}(X + 1)`. -/
theorem growthTransitionPoly_self_eq_cyclotomic_comp_X_add_one (j : ℕ) :
    growthTransitionPoly p O j j = (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) := by
  rw [growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one, Nat.Ico_succ_singleton,
    Finset.prod_singleton]

/-- When `p` is prime and `(p : O) ∈ I`, every transition polynomial `ν_{n,n₀}` is distinguished
at `I`. -/
theorem isDistinguishedAt_growthTransitionPoly {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]
    {I : Ideal O} (hp : (p : O) ∈ I) (n₀ n : ℕ) :
    (growthTransitionPoly p O n₀ n).IsDistinguishedAt I := by
  rw [growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one]
  exact Polynomial.isDistinguishedAt_prod fun j _ ↦
    Polynomial.cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt p hp j

/-- **Resultant growth along cyclotomic transitions.** If `O` is `I`-adically complete, `F` is
distinguished at `I`, `I ^ e ⊆ (p)`, and `p` lies in the Jacobson radical of `O`, then for every
`m` with `n₀ ≤ m + 1` and `deg F * e < m` and every `k ≥ m`, `Res(F, ν_{k,n₀})` is associated to
`Res(F, ν_{m,n₀}) * p ^ (deg F * (k - m))`. -/
theorem associated_resultant_growthTransitionPoly {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]
    {I : Ideal O} [IsAdicComplete I O] {F : O[X]} (hF : F.IsDistinguishedAt I) {e : ℕ}
    (hI : I ^ e ≤ Ideal.span {(p : O)}) (hpO : (p : O) ∈ (⊥ : Ideal O).jacobson)
    {n₀ m k : ℕ} (hnm : n₀ ≤ m + 1) (hm : F.natDegree * e < m) (hmk : m ≤ k) :
    Associated (F.resultant (growthTransitionPoly p O n₀ k))
      (F.resultant (growthTransitionPoly p O n₀ m) * (p : O) ^ (F.natDegree * (k - m))) := by
  rw [← growthTransitionPoly_mul_of_le p O hnm hmk, hF.monic.resultant_mul_right]
  refine Associated.mul_left _ ?_
  have hprod : ((growthTransitionPoly p O (m + 1) k : O[X]) : O⟦X⟧) =
      ∏ j ∈ Finset.Ico m k,
        (((Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) : O[X]) : O⟦X⟧) := by
    rw [growthTransitionPoly_eq_prod_cyclotomic_comp_X_add_one, ← Finset.prod_Ico_add'
      (fun j ↦ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) m k 1,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply]
  rw [← hF.isWeierstrassFactorizationAt.norm_mk_coe_eq_resultant, hprod]
  exact hF.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one hI hpO hm k

end Prime

end TauCeti.Iwasawa
