/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Analysis.Asymptotics.Expansion.Basic
public import TauCeti.RingTheory.PowerSeries.ComplexPower

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Complex.Log
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Algebra of asymptotic power series

This file develops the algebraic operations on asymptotic power series in a small variable
`w : α → 𝕜` tending to `0` along a filter `l` (NIST DLMF §2.1(iii)): sums, differences, scalar
multiples, products, powers, reciprocals, composition, and reversion/inversion, together with
the rules for principal complex powers (via `PowerSeries.formalCpow`) and logarithms of asymptotic
power series.

An asymptotic power series `P : 𝕜⟦X⟧` of a function `f : α → 𝕜` in a small variable `w → 0` is
expressed via `Asymptotics.HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f`.
Poincaré expansions at infinity are the specialization `w z = z⁻¹`.

## Main results

* `Asymptotics.hasAsymptoticExpansion_pow_add`, `Asymptotics.hasAsymptoticExpansion_pow_mul`,
  `Asymptotics.hasAsymptoticExpansion_pow_pow`, `Asymptotics.hasAsymptoticExpansion_pow_inv`:
  closure of asymptotic power series under ring operations and reciprocals (when
  `constantCoeff P ≠ 0`).
* `Asymptotics.hasAsymptoticExpansion_pow_subst`: composition `H ∘ y ~ P.subst Q` when `H ~ P`
  in `σ`, `σ ∘ y ~ Q` in `w`, and `constantCoeff Q = 0`.
* `Asymptotics.hasAsymptoticExpansion_pow_substInv`: inversion `σ ∘ y ~ P.substInvOfIsUnit _`
  when `σ → 0`, `H ~ P` in `σ` with `constantCoeff P = 0` and `coeff 1 P ≠ 0`, and eventually
  `H (y x) = w x`.
* `Asymptotics.hasAsymptoticExpansion_pow_cpow` and
  `Asymptotics.hasAsymptoticExpansion_pow_log`: principal complex powers and logarithms of complex
  asymptotic power series whose constant coefficient lies in `Complex.slitPlane`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1(iii),
  <https://dlmf.nist.gov/2.1#iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1, §8.
-/

public section

open Filter Topology Finset PowerSeries

namespace Asymptotics

/-! ### Auxiliary lemmas on truncated power series -/

section Helpers

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

private lemma isBigO_partialSum_one (hw : Tendsto w l (𝓝 0)) (P : 𝕜⟦X⟧) (N : ℕ) :
    (fun x => ∑ i ∈ range N, w x ^ i * coeff i P) =O[l] fun _ => (1 : 𝕜) := by
  have hsum : (fun x => ∑ i ∈ range N, w x ^ i * coeff i P) =O[l] fun x => w x ^ 0 := by
    refine IsBigO.fun_sum fun i _ => ?_
    have h1 := ((isAsymptoticScale_pow hw).isBigO_of_le (Nat.zero_le i)).const_mul_left (coeff i P)
    exact h1.congr' (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
  simpa only [pow_zero] using hsum

private lemma isBigO_mul_partialSum_sub (hw : Tendsto w l (𝓝 0)) (P Q : 𝕜⟦X⟧) (N : ℕ) :
    (fun x => (∑ i ∈ range N, w x ^ i * coeff i P) * (∑ j ∈ range N, w x ^ j * coeff j Q) -
      ∑ k ∈ range N, w x ^ k * coeff k (P * Q)) =O[l] fun x => w x ^ N := by
  have hbi : (range N).biUnion antidiagonal =
      (range N ×ˢ range N).filter fun p => p.1 + p.2 < N := by
    ext ⟨i, j⟩
    simp only [mem_biUnion, mem_range, mem_antidiagonal, mem_filter, mem_product]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, hk⟩
    · rintro ⟨_, hlt⟩
      exact ⟨i + j, hlt, rfl⟩
  have hdisj : Set.PairwiseDisjoint (↑(range N) : Set ℕ) antidiagonal := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    rw [mem_antidiagonal] at hp₁ hp₂
    exact hne (hp₁.symm.trans hp₂)
  have hident : ∀ x : α,
      (∑ i ∈ range N, w x ^ i * coeff i P) * (∑ j ∈ range N, w x ^ j * coeff j Q) -
        ∑ k ∈ range N, w x ^ k * coeff k (P * Q) =
      ∑ p ∈ (range N ×ˢ range N).filter (fun p => ¬ p.1 + p.2 < N),
        w x ^ (p.1 + p.2) * (coeff p.1 P * coeff p.2 Q) := fun x => by
    have hprod : (∑ i ∈ range N, w x ^ i * coeff i P) * (∑ j ∈ range N, w x ^ j * coeff j Q) =
        ∑ p ∈ range N ×ˢ range N, w x ^ (p.1 + p.2) * (coeff p.1 P * coeff p.2 Q) := by
      rw [sum_mul_sum, ← sum_product']
      refine sum_congr rfl fun p _ => ?_
      rw [pow_add]
      ring
    have hlow : ∑ k ∈ range N, w x ^ k * coeff k (P * Q) =
        ∑ p ∈ (range N ×ˢ range N).filter (fun p => p.1 + p.2 < N),
          w x ^ (p.1 + p.2) * (coeff p.1 P * coeff p.2 Q) := by
      rw [← hbi, sum_biUnion hdisj]
      refine sum_congr rfl fun k _ => ?_
      rw [coeff_mul, mul_sum]
      refine sum_congr rfl fun p hp => ?_
      rw [mem_antidiagonal.mp hp]
    rw [hprod, hlow, ← sum_filter_add_sum_filter_not (range N ×ˢ range N) (fun p => p.1 + p.2 < N),
      add_sub_cancel_left]
  simp_rw [hident]
  refine IsBigO.fun_sum fun p hp => ?_
  have hge : N ≤ p.1 + p.2 := not_lt.mp (mem_filter.mp hp).2
  have h1 := ((isAsymptoticScale_pow hw).isBigO_of_le hge).const_mul_left
    (coeff p.1 P * coeff p.2 Q)
  exact h1.congr' (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl

private lemma hasAsymptoticExpansion_pow_trunc (hw : Tendsto w l (𝓝 0)) (Q : 𝕜⟦X⟧) (N : ℕ) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k))
      (fun x => ∑ k ∈ range N, w x ^ k * coeff k Q) := by
  rw [hasAsymptoticExpansion_iff]
  intro M
  by_cases hMN : M ≤ N
  · have hdiff : ∀ x : α,
        (∑ k ∈ range N, w x ^ k * coeff k Q) -
          ∑ n ∈ range M, w x ^ n * coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k) =
        ∑ k ∈ Ico M N, w x ^ k * coeff k Q := fun x => by
      have heq : ∑ n ∈ range M, w x ^ n * coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k) =
          ∑ n ∈ range M, w x ^ n * coeff n Q :=
        sum_congr rfl fun n hn => by simp [lt_of_lt_of_le (mem_range.mp hn) hMN]
      rw [heq, ← sum_range_add_sum_Ico _ hMN, add_sub_cancel_left]
    simp_rw [smul_eq_mul, hdiff]
    refine IsBigO.fun_sum fun k hk => ?_
    have h1 := ((isAsymptoticScale_pow hw).isBigO_of_le (mem_Ico.mp hk).1).const_mul_left
      (coeff k Q)
    exact h1.congr' (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
  · have hNM : N ≤ M := le_of_not_ge hMN
    have hdiff : ∀ x : α,
        (∑ k ∈ range N, w x ^ k * coeff k Q) -
          ∑ n ∈ range M, w x ^ n * coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k) = 0 := fun x => by
      have heq : ∑ n ∈ range M, w x ^ n * coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k) =
          ∑ k ∈ range N, w x ^ k * coeff k Q := by
        rw [← sum_range_add_sum_Ico _ hNM]
        have h1 : ∑ n ∈ range N, w x ^ n * coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k) =
            ∑ k ∈ range N, w x ^ k * coeff k Q :=
          sum_congr rfl fun n hn => by simp [mem_range.mp hn]
        have h2 : ∑ n ∈ Ico N M, w x ^ n * coeff n (∑ k ∈ range N, C (coeff k Q) * X ^ k) = 0 :=
          sum_eq_zero fun n hn => by simp [not_lt.mpr (mem_Ico.mp hn).1]
        rw [h1, h2, add_zero]
      rw [heq, sub_self]
    simp_rw [smul_eq_mul, hdiff]
    exact isBigO_zero _ _

end Helpers

/-! ### Ring operations on asymptotic power series -/

section LinearAlgebra

variable {α 𝕜 : Type*} {l : Filter α} {w : α → 𝕜}

/-- A constant function `fun _ => c` has the constant asymptotic power series `C c`. -/
theorem hasAsymptoticExpansion_pow_const [SeminormedRing 𝕜] [NormOneClass 𝕜] (c : 𝕜) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (C c)) (fun _ => c) := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  cases N with
  | zero =>
    refine IsBigO.of_bound ‖c‖ <| Eventually.of_forall fun x => ?_
    simp
  | succ N =>
    have hsum : ∀ x : α, ∑ n ∈ range (N + 1), w x ^ n * coeff n (C c) = c := fun x => by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [coeff_C, hb]
      · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
    simp only [smul_eq_mul, hsum, sub_self]
    exact isBigO_zero _ _

/-- Sums of asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_add [SeminormedRing 𝕜] {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hg : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) g) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P + Q)) (f + g) :=
  (hf.add hg).congr_coeff fun n => by simp [Pi.add_apply]

/-- Negation of an asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_neg [SeminormedRing 𝕜] {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (-P)) (-f) :=
  hf.neg.congr_coeff fun n => by simp [Pi.neg_apply]

/-- Differences of asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_sub [SeminormedRing 𝕜] {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hg : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) g) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P - Q)) (f - g) :=
  (hf.sub hg).congr_coeff fun n => by simp [Pi.sub_apply]

/-- Constant scalar multiples of asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_const_mul [SeminormedCommRing 𝕜] {P : 𝕜⟦X⟧} {f : α → 𝕜} (c : 𝕜)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (C c * P))
      (fun x => c * f x) :=
  (hf.const_smul c).congr_coeff fun n => by simp [coeff_C_mul]

end LinearAlgebra

section Algebra

variable {α β 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {m : Filter β} {w : α → 𝕜}

/-- Products of asymptotic power series in a small variable `w` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_mul (hw : Tendsto w l (𝓝 0)) {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hg : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) g) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P * Q)) (f * g) := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  have hg0 : g =O[l] fun _ => (1 : 𝕜) := by
    simpa only [range_zero, sum_empty, sub_zero, pow_zero] using hg.isBigO 0
  have hP0 : (fun x => ∑ i ∈ range N, w x ^ i * coeff i P) =O[l] fun _ => (1 : 𝕜) :=
    isBigO_partialSum_one hw P N
  have h1 : (fun x => (f x - ∑ i ∈ range N, w x ^ i * coeff i P) * g x) =O[l]
      fun x => w x ^ N := by
    simpa only [smul_eq_mul, mul_one] using (hf.isBigO N).mul hg0
  have h2 : (fun x => (∑ i ∈ range N, w x ^ i * coeff i P) *
      (g x - ∑ j ∈ range N, w x ^ j * coeff j Q)) =O[l] fun x => w x ^ N := by
    simpa only [smul_eq_mul, one_mul] using hP0.mul (hg.isBigO N)
  have h3 := isBigO_mul_partialSum_sub hw P Q N
  refine ((h1.add h2).add h3).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [Pi.mul_apply, smul_eq_mul]
  ring

/-- Natural powers of an asymptotic power series in a small variable `w` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_pow (hw : Tendsto w l (𝓝 0)) {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (k : ℕ) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P ^ k)) (f ^ k) := by
  induction k with
  | zero =>
    exact ((hasAsymptoticExpansion_pow_const (l := l) (w := w) (1 : 𝕜)).congr_coeff
      fun n => by rw [pow_zero, map_one]).congr_fun (Eventually.of_forall fun _ => by simp)
  | succ k ih =>
    simpa only [pow_succ] using hasAsymptoticExpansion_pow_mul hw ih hf

/-- Reciprocals of asymptotic power series with nonzero constant term (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_inv (hw : Tendsto w l (𝓝 0)) {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hP : constantCoeff P ≠ 0)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P⁻¹) f⁻¹ := by
  have hftend : Tendsto f l (𝓝 (constantCoeff P)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have h1 : (fun x => f x - constantCoeff P) =O[l] w := by
      simpa only [range_one, sum_singleton, pow_zero, pow_one, smul_eq_mul, one_mul,
        coeff_zero_eq_constantCoeff_apply] using hf.isBigO 1
    exact h1.trans_tendsto hw
  have hfinv_tend : Tendsto f⁻¹ l (𝓝 (constantCoeff P)⁻¹) := hftend.inv₀ hP
  have hfinv_O : f⁻¹ =O[l] fun _ => (1 : 𝕜) := hfinv_tend.isBigO_one 𝕜
  have hfne : ∀ᶠ x in l, f x ≠ 0 := hftend.eventually_ne hP
  rw [hasAsymptoticExpansion_iff]
  intro N
  cases N with
  | zero =>
    simpa only [range_zero, sum_empty, sub_zero, pow_zero] using hfinv_O
  | succ N =>
    set M := N + 1
    have hQ0 : (fun x => ∑ j ∈ range M, w x ^ j * coeff j P⁻¹) =O[l] fun _ => (1 : 𝕜) :=
      isBigO_partialSum_one hw P⁻¹ M
    have h1 : (fun x => (f x - ∑ i ∈ range M, w x ^ i * coeff i P) *
        (∑ j ∈ range M, w x ^ j * coeff j P⁻¹)) =O[l] fun x => w x ^ M := by
      simpa only [smul_eq_mul, mul_one] using (hf.isBigO M).mul hQ0
    have h2 := isBigO_mul_partialSum_sub hw P P⁻¹ M
    have hPQ1 : ∀ x : α, ∑ k ∈ range M, w x ^ k * coeff k (P * P⁻¹) = 1 := fun x => by
      rw [PowerSeries.mul_inv_cancel P hP, Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [coeff_one, hk]
      · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
    have hprod : (fun x => 1 - f x * ∑ j ∈ range M, w x ^ j * coeff j P⁻¹) =O[l]
        fun x => w x ^ M := by
      refine (h1.add h2).neg_left.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
      dsimp only
      rw [hPQ1 x]
      ring
    have hmul : (fun x => (f x)⁻¹ * (1 - f x * ∑ j ∈ range M, w x ^ j * coeff j P⁻¹)) =O[l]
        fun x => w x ^ M := by
      simpa only [Pi.inv_apply, one_mul] using hfinv_O.mul hprod
    refine hmul.congr' (hfne.mono fun x hx => ?_) EventuallyEq.rfl
    simp only [Pi.inv_apply, smul_eq_mul, mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hx,
      one_mul]

/-- Quotients of asymptotic power series when the denominator has nonzero constant term
(DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_div (hw : Tendsto w l (𝓝 0)) {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}
    (hQ : constantCoeff Q ≠ 0)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hg : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) g) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P * Q⁻¹)) (f / g) := by
  simpa only [div_eq_mul_inv] using
    hasAsymptoticExpansion_pow_mul hw hf (hasAsymptoticExpansion_pow_inv hw hQ hg)

/-! ### Composition and inversion of asymptotic power series -/

/-- Composition of asymptotic power series (DLMF §2.1(iii)). The inner map `y` carries `l` to `m`;
`H ~ P` in the small variable `σ` along `m`, and `σ ∘ y ~ Q` in `w` along `l` with
`constantCoeff Q = 0`. -/
theorem hasAsymptoticExpansion_pow_subst {σ H : β → 𝕜} {y : α → β} {P Q : 𝕜⟦X⟧}
    (hw : Tendsto w l (𝓝 0)) (hy : Tendsto y l m) (hQ : constantCoeff Q = 0)
    (hH : HasAsymptoticExpansion m (fun n x => σ x ^ n) (fun n => coeff n P) H)
    (hs : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) fun x => σ (y x)) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P.subst Q))
      fun x => H (y x) := by
  have hsO : (fun x => σ (y x)) =O[l] w := by
    simpa only [range_one, sum_singleton, pow_zero, pow_one, smul_eq_mul, one_mul,
      coeff_zero_eq_constantCoeff_apply, hQ, sub_zero] using hs.isBigO 1
  rw [hasAsymptoticExpansion_iff]
  intro N
  have h1 : (fun x => H (y x) - ∑ k ∈ range N, σ (y x) ^ k * coeff k P) =O[l]
      fun x => w x ^ N :=
    ((hH.isBigO N).comp_tendsto hy).trans (hsO.pow N)
  have h2 : (fun x => ∑ k ∈ range N, (σ (y x) ^ k * coeff k P -
      ∑ n ∈ range N, w x ^ n * (coeff k P * coeff n (Q ^ k)))) =O[l] fun x => w x ^ N := by
    refine IsBigO.fun_sum fun k _ => ?_
    have hk := (hasAsymptoticExpansion_pow_pow hw hs k).isBigO N
    refine (hk.const_mul_left (coeff k P)).congr' (Eventually.of_forall fun x => ?_)
      EventuallyEq.rfl
    simp only [Pi.pow_apply, smul_eq_mul, mul_sub, mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl fun n _ => ?_; ring
  refine (h1.add h2).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  rw [sum_sub_distrib]
  have hswap : ∑ k ∈ range N, ∑ n ∈ range N, w x ^ n * (coeff k P * coeff n (Q ^ k)) =
      ∑ n ∈ range N, w x ^ n * coeff n (P.subst Q) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun n hn => ?_
    rw [← mul_sum, PowerSeries.coeff_subst_eq_sum_range_of_lt P hQ (mem_range.mp hn)]
    simp_rw [smul_eq_mul]
  rw [hswap]
  simp only [smul_eq_mul]
  abel

private lemma isBigO_sum_pow_sub_pow_sub_linear {s q : α → 𝕜} {P : 𝕜⟦X⟧} {M : ℕ}
    (hw0 : Tendsto w l (𝓝 0)) (hP0 : constantCoeff P = 0) (hM : 1 ≤ M)
    (hsO : s =O[l] w) (hqO : q =O[l] w) (hrM : (fun x => s x - q x) =O[l] fun x => w x ^ M) :
    (fun x => (∑ k ∈ range (M + 1), s x ^ k * coeff k P -
        ∑ k ∈ range (M + 1), q x ^ k * coeff k P) - (s x - q x) * coeff 1 P) =O[l]
      fun x => w x ^ (M + 1) := by
  have hrew : ∀ x : α,
      (∑ k ∈ range (M + 1), s x ^ k * coeff k P -
        ∑ k ∈ range (M + 1), q x ^ k * coeff k P) - (s x - q x) * coeff 1 P =
      ∑ k ∈ Ico 2 (M + 1), (s x ^ k - q x ^ k) * coeff k P := fun x => by
    rw [← sum_sub_distrib]
    have h2le : 2 ≤ M + 1 := by omega
    have hsplit := sum_range_add_sum_Ico
      (f := fun k => s x ^ k * coeff k P - q x ^ k * coeff k P) h2le
    rw [← hsplit]
    have h01 : ∑ k ∈ range 2, (s x ^ k * coeff k P - q x ^ k * coeff k P) =
        (s x - q x) * coeff 1 P := by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, pow_one,
        coeff_zero_eq_constantCoeff_apply, hP0, mul_zero, sub_self]
      ring
    rw [h01, add_sub_cancel_left]
    refine sum_congr rfl fun k _ => by ring
  simp_rw [hrew]
  refine IsBigO.fun_sum fun k hk => ?_
  have hk2 : 2 ≤ k := (mem_Ico.mp hk).1
  have hfac : (fun x => ∑ j ∈ range k, s x ^ j * q x ^ (k - 1 - j)) =O[l] w := by
    refine IsBigO.fun_sum fun j hj => ?_
    have hjk : j < k := mem_range.mp hj
    have hadd : j + (k - 1 - j) = k - 1 := by omega
    have h1le : 1 ≤ k - 1 := by omega
    have hprod : (fun x => s x ^ j * q x ^ (k - 1 - j)) =O[l] fun x => w x ^ (k - 1) := by
      have h := (hsO.pow j).mul (hqO.pow (k - 1 - j))
      refine h.congr' EventuallyEq.rfl (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [← pow_add, hadd]
    exact hprod.trans (by
      simpa only [pow_one] using (isAsymptoticScale_pow hw0).isBigO_of_le h1le)
  have hdiff_k : (fun x => s x ^ k - q x ^ k) =O[l] fun x => w x ^ (M + 1) := by
    have h := hfac.mul hrM
    refine h.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact geom_sum₂_mul (s x) (q x) k
    · exact (pow_succ' (w x) M).symm
  have hc := hdiff_k.const_mul_left (coeff k P)
  exact hc.congr' (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl

private lemma isBigO_sum_trunc_substInv {P Q : 𝕜⟦X⟧} {M : ℕ}
    (hw0 : Tendsto w l (𝓝 0)) (hQ0 : constantCoeff Q = 0) (hPQ : P.subst Q = X) (hM : 1 ≤ M) :
    (fun x => (∑ k ∈ range (M + 1), (∑ n ∈ range (M + 1), w x ^ n * coeff n Q) ^ k * coeff k P) -
        w x) =O[l]
      fun x => w x ^ (M + 1) := by
  set T : 𝕜⟦X⟧ := ∑ n ∈ range (M + 1), C (coeff n Q) * X ^ n
  have hT0 : constantCoeff T = 0 := by
    simp [T, ← coeff_zero_eq_constantCoeff_apply, hQ0]
  have hdvd : (X : 𝕜⟦X⟧) ^ (M + 1) ∣ Q - T := X_pow_dvd_iff.mpr fun j hj => by
    simp [T, hj]
  have hdvd_subst : (X : 𝕜⟦X⟧) ^ (M + 1) ∣ P.subst Q - P.subst T :=
    PowerSeries.X_pow_dvd_subst_sub_subst hQ0 hdvd P
  have hqT : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n T)
      (fun x => ∑ n ∈ range (M + 1), w x ^ n * coeff n Q) :=
    hasAsymptoticExpansion_pow_trunc hw0 Q (M + 1)
  have hsum : (fun x => ∑ k ∈ range (M + 1),
      ((∑ n ∈ range (M + 1), w x ^ n * coeff n Q) ^ k * coeff k P -
        ∑ n ∈ range (M + 1), w x ^ n * (coeff k P * coeff n (T ^ k)))) =O[l]
      fun x => w x ^ (M + 1) := by
    refine IsBigO.fun_sum fun k _ => ?_
    have hk := (hasAsymptoticExpansion_pow_pow hw0 hqT k).isBigO (M + 1)
    refine (hk.const_mul_left (coeff k P)).congr'
      (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    simp only [Pi.pow_apply, smul_eq_mul, mul_sub, mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl fun n _ => ?_; ring
  refine hsum.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  rw [sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  have hswap : ∑ n ∈ range (M + 1), ∑ k ∈ range (M + 1),
      w x ^ n * (coeff k P * coeff n (T ^ k)) =
      ∑ n ∈ range (M + 1), w x ^ n * coeff n (X : 𝕜⟦X⟧) := by
    refine sum_congr rfl fun n hn => ?_
    have hcoeff_eq : coeff n (P.subst T) = coeff n (P.subst Q) := by
      have h0 := X_pow_dvd_iff.mp hdvd_subst n (mem_range.mp hn)
      rw [map_sub, sub_eq_zero] at h0
      exact h0.symm
    have hsubst := PowerSeries.coeff_subst_eq_sum_range_of_lt P hT0 (mem_range.mp hn)
    simp only [smul_eq_mul] at hsubst
    rw [← mul_sum, ← hsubst, hcoeff_eq, hPQ]
  have h1lt : 1 < M + 1 := by omega
  rw [hswap, Finset.sum_eq_single 1]
  · simp
  · intro n _ hn1; simp [coeff_X, hn1]
  · intro h1; exact absurd (mem_range.mpr h1lt) h1

/-- Inversion of asymptotic power series (DLMF §2.1(iii)). The condition `Tendsto y l m` selects
the branch of the inverse near `σ = 0`. -/
theorem hasAsymptoticExpansion_pow_substInv {σ H : β → 𝕜} {y : α → β} {P : 𝕜⟦X⟧}
    (hσ : Tendsto σ m (𝓝 0))
    (hH : HasAsymptoticExpansion m (fun n x => σ x ^ n) (fun n => coeff n P) H)
    (hP0 : constantCoeff P = 0) (hP1 : coeff 1 P ≠ 0) (hy : Tendsto y l m)
    (heq : ∀ᶠ x in l, H (y x) = w x) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (P.substInvOfIsUnit hP1.isUnit)) fun x => σ (y x) := by
  set Q : 𝕜⟦X⟧ := P.substInvOfIsUnit hP1.isUnit
  set s : α → 𝕜 := fun x => σ (y x)
  have hQ0 : constantCoeff Q = 0 := PowerSeries.constantCoeff_substInvOfIsUnit P hP1.isUnit
  have hPQ : P.subst Q = X := PowerSeries.subst_substInvOfIsUnit_right P hP0 hP1.isUnit
  have hs0 : Tendsto s l (𝓝 0) := hσ.comp hy
  -- Step 1: Linearization `w = s * P₁ + o(s)`, giving `s = O(w)`, `w = O(s)`, and `w → 0`.
  have hlin : (fun x => w x - s x * coeff 1 P) =o[l] s := by
    have h2 : (fun x => H (y x) - s x * coeff 1 P) =O[l] fun x => s x ^ 2 := by
      refine ((hH.isBigO 2).comp_tendsto hy).congr' (Eventually.of_forall fun x => ?_)
        EventuallyEq.rfl
      simp only [Function.comp_apply, sum_range_succ, range_zero, sum_empty, zero_add,
        pow_zero, pow_one, smul_eq_mul, one_mul, coeff_zero_eq_constantCoeff_apply, hP0, s]
    have h2' : (fun x => w x - s x * coeff 1 P) =O[l] fun x => s x ^ 2 :=
      h2.congr' (heq.mono fun x hx => by dsimp only; rw [hx]) EventuallyEq.rfl
    have hsq : (fun x => s x ^ 2) =o[l] s := by
      simpa only [Function.comp_def, pow_one] using
        (isLittleO_pow_pow one_lt_two (𝕜 := 𝕜)).comp_tendsto hs0
    exact h2'.trans_isLittleO hsq
  have hsO : s =O[l] w := by
    have hpos : 0 < ‖coeff 1 P‖ / 2 := half_pos (norm_pos_iff.mpr hP1)
    refine IsBigO.of_bound (2 / ‖coeff 1 P‖) ?_
    filter_upwards [hlin.bound hpos] with x hx
    have htri : ‖s x‖ * ‖coeff 1 P‖ - ‖w x‖ ≤ ‖w x - s x * coeff 1 P‖ := by
      rw [← norm_mul, norm_sub_rev]
      exact norm_sub_norm_le _ _
    have hc : 0 < ‖coeff 1 P‖ := norm_pos_iff.mpr hP1
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have hwO : w =O[l] s := by
    refine (hlin.isBigO.add ((isBigO_refl s l).const_mul_left (coeff 1 P))).congr'
      (Eventually.of_forall fun x => by dsimp only; ring) EventuallyEq.rfl
  have hw0 : Tendsto w l (𝓝 0) := hwO.trans_tendsto hs0
  -- Step 2: Induction on the truncation order `N`.
  rw [hasAsymptoticExpansion_iff]
  intro N
  induction N with
  | zero =>
    simpa only [range_zero, sum_empty, sub_zero, pow_zero] using hs0.isBigO_one 𝕜
  | succ N ih =>
    cases N with
    | zero =>
      simpa only [zero_add, range_one, sum_singleton, pow_zero, pow_one, smul_eq_mul, one_mul,
        coeff_zero_eq_constantCoeff_apply, hQ0, sub_zero] using hsO
    | succ N =>
      set M := N + 1
      set q : α → 𝕜 := fun x => ∑ n ∈ range (M + 1), w x ^ n * coeff n Q
      set r : α → 𝕜 := fun x => s x - q x
      have hrM : r =O[l] fun x => w x ^ M := by
        have hterm : (fun x => w x ^ M * coeff M Q) =O[l] fun x => w x ^ M :=
          ((isBigO_refl _ _).const_mul_left (coeff M Q)).congr'
            (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
        refine (ih.sub hterm).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
        dsimp only [r, q]
        simp only [smul_eq_mul, sum_range_succ]
        ring
      have hqO : q =O[l] w := by
        refine IsBigO.fun_sum fun n _ => ?_
        cases n with
        | zero =>
          simp only [pow_zero, coeff_zero_eq_constantCoeff_apply, hQ0, mul_zero]
          exact isBigO_zero _ _
        | succ n =>
          have h1 := ((isAsymptoticScale_pow hw0).isBigO_of_le
            (Nat.succ_le_succ (Nat.zero_le n))).const_mul_left (coeff (n + 1) Q)
          simpa only [pow_one] using
            h1.congr' (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
      have hA : (fun x => w x - ∑ k ∈ range (M + 1), s x ^ k * coeff k P) =O[l]
          fun x => w x ^ (M + 1) := by
        have h := ((hH.isBigO (M + 1)).comp_tendsto hy).trans (hsO.pow (M + 1))
        exact h.congr' (heq.mono fun x hx => by simp only [Function.comp_apply, hx, smul_eq_mul, s])
          EventuallyEq.rfl
      have hB := isBigO_sum_pow_sub_pow_sub_linear hw0 hP0 (Nat.succ_pos N) hsO hqO hrM
      have hC := isBigO_sum_trunc_substInv hw0 hQ0 hPQ (Nat.succ_pos N)
      have hcomb : (fun x => r x * coeff 1 P) =O[l] fun x => w x ^ (M + 1) := by
        refine ((hA.add hB).add hC).neg_left.congr' (Eventually.of_forall fun x => ?_)
          EventuallyEq.rfl
        dsimp only [r, q]
        ring
      have hrM1 : r =O[l] fun x => w x ^ (M + 1) := by
        refine (hcomb.const_mul_left (coeff 1 P)⁻¹).congr' (Eventually.of_forall fun x => ?_)
          EventuallyEq.rfl
        dsimp only
        rw [mul_comm (r x), ← mul_assoc, inv_mul_cancel₀ hP1, one_mul]
      simpa only [r, q, smul_eq_mul] using hrM1

end Algebra

/-! ### Formal complex powers and logarithms -/

section ComplexPowerLog

private lemma hasAsymptoticExpansion_pow_unit_sub_one {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ} {ℓ : ℂ}
    (hP : constantCoeff P = Complex.exp ℓ)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.exp (-ℓ)) * P - 1))
      (fun x => Complex.exp (-ℓ) * f x - 1) ∧
    Tendsto (fun x => Complex.exp (-ℓ) * f x - 1) l (𝓝 0) := by
  have hu_exp : HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.exp (-ℓ)) * P - 1))
      (fun x => Complex.exp (-ℓ) * f x - 1) := by
    have hsub := hasAsymptoticExpansion_pow_sub
      (hasAsymptoticExpansion_pow_const_mul (Complex.exp (-ℓ)) hf)
      (hasAsymptoticExpansion_pow_const (l := l) (w := w) (1 : ℂ))
    exact (hsub.congr_coeff fun n => by simp only [map_one]).congr_fun
      (Eventually.of_forall fun _ => rfl)
  refine ⟨hu_exp, ?_⟩
  have hU0 : constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 :=
    constantCoeff_exp_neg_mul_sub_one hP
  have h1 : (fun x => Complex.exp (-ℓ) * f x - 1) =O[l] w := by
    simpa only [range_one, sum_singleton, pow_zero, pow_one, smul_eq_mul, one_mul,
      coeff_zero_eq_constantCoeff_apply, hU0, sub_zero] using hu_exp.isBigO 1
  exact h1.trans_tendsto hw

/-- Principal logarithm of a complex asymptotic power series whose constant coefficient lies in
`Complex.slitPlane` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_log {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ}
    (hP : constantCoeff P ∈ Complex.slitPlane)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.log (constantCoeff P)) +
        (PowerSeries.log ℂ).subst (C (Complex.exp (-Complex.log (constantCoeff P))) * P - 1)))
      fun x => Complex.log (f x) := by
  set p₀ : ℂ := constantCoeff P
  set ℓ : ℂ := Complex.log p₀
  have hp₀_ne : p₀ ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hexpℓ : Complex.exp ℓ = p₀ := Complex.exp_log hp₀_ne
  obtain ⟨hu_exp, hu0⟩ := hasAsymptoticExpansion_pow_unit_sub_one hw hexpℓ.symm hf
  have hU0 : constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 :=
    constantCoeff_exp_neg_mul_sub_one hexpℓ.symm
  have hlog_at0 : HasAsymptoticExpansion (𝓝 (0 : ℂ)) (fun n z => z ^ n)
      (fun n => coeff n (PowerSeries.log ℂ)) (fun z => Complex.log (1 + z)) := by
    have hfp := hasFPowerSeriesAt_clog_one_add.hasAsymptoticExpansion
    refine (hfp.congr_scale fun n => Eventually.of_forall fun z => by
      dsimp only; rw [sub_zero]).congr_coeff fun n => ?_
    rw [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_log]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, map_div₀, map_pow, map_neg, map_one, map_natCast]
      rw [pow_succ, pow_succ]
      ring
  have hcomp := hasAsymptoticExpansion_pow_subst hw hu0 hU0 hlog_at0 hu_exp
  have hadd := hasAsymptoticExpansion_pow_add (hasAsymptoticExpansion_pow_const (l := l) (w := w) ℓ)
    hcomp
  refine hadd.congr_fun ?_
  filter_upwards [Complex.eventually_log_mul_one_add hP hu0] with x hx
  have hfx : f x = p₀ * (1 + (Complex.exp (-ℓ) * f x - 1)) := by
    rw [Complex.exp_neg, hexpℓ]
    field_simp [hp₀_ne]
    ring
  dsimp only [Pi.add_apply]
  conv_rhs => rw [hfx, hx]

/-- Principal complex power of a complex asymptotic power series whose constant coefficient lies in
`Complex.slitPlane` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_cpow {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ}
    (hP : constantCoeff P ∈ Complex.slitPlane)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (r : ℂ) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (formalCpow (Complex.log (constantCoeff P)) r P))
      fun x => f x ^ r := by
  set p₀ : ℂ := constantCoeff P
  set ℓ : ℂ := Complex.log p₀
  have hp₀_ne : p₀ ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hexpℓ : Complex.exp ℓ = p₀ := Complex.exp_log hp₀_ne
  obtain ⟨hu_exp, hu0⟩ := hasAsymptoticExpansion_pow_unit_sub_one hw hexpℓ.symm hf
  have hU0 : constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 :=
    constantCoeff_exp_neg_mul_sub_one hexpℓ.symm
  have hbin_at0 : HasAsymptoticExpansion (𝓝 (0 : ℂ)) (fun n z => z ^ n)
      (fun n => coeff n (PowerSeries.binomialSeries ℂ r)) (fun z => (1 + z) ^ r) := by
    have hfp := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := r)).hasAsymptoticExpansion
    refine (hfp.congr_scale fun n => Eventually.of_forall fun z => by
      dsimp only; rw [sub_zero]).congr_coeff fun n => ?_
    simp [_root_.binomialSeries, PowerSeries.binomialSeries_coeff]
  have hcomp := hasAsymptoticExpansion_pow_subst hw hu0 hU0 hbin_at0 hu_exp
  have hmul := hasAsymptoticExpansion_pow_const_mul (Complex.exp (r * ℓ)) hcomp
  refine (hmul.congr_coeff fun n => by rw [formalCpow_def]).congr_fun ?_
  have h1u : Tendsto (fun x => 1 + (Complex.exp (-ℓ) * f x - 1)) l (𝓝 (1 : ℂ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hu0
  filter_upwards [Complex.eventually_log_mul_one_add hP hu0, h1u.eventually_ne one_ne_zero]
    with x hx h1ne
  have hfx : f x = p₀ * (1 + (Complex.exp (-ℓ) * f x - 1)) := by
    rw [Complex.exp_neg, hexpℓ]
    field_simp [hp₀_ne]
    ring
  conv_rhs => rw [hfx, Complex.cpow_def_of_ne_zero (mul_ne_zero hp₀_ne h1ne), hx]
  rw [Complex.cpow_def_of_ne_zero h1ne, add_mul, Complex.exp_add, mul_comm ℓ r]

end ComplexPowerLog

end Asymptotics
