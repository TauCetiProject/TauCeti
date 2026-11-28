/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Analysis.Asymptotics.Expansion.Basic

import TauCeti.Analysis.Asymptotics.TruncatedPowerSeries
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Algebra of asymptotic power series

This file develops the algebraic operations on asymptotic power series in a small variable
`w : α → 𝕜` tending to `0` along a filter `l` (NIST DLMF §2.1(iii)): leading-term bounds,
truncation expansions, sums, differences, scalar multiples, products, powers, reciprocals,
quotients, composition, and reversion/inversion. For principal complex powers and logarithms of
complex asymptotic power series, see `TauCeti.Analysis.Asymptotics.Expansion.ComplexPowerLog`.

An asymptotic power series `P : 𝕜⟦X⟧` of a function `f : α → 𝕜` in a small variable `w → 0` is
expressed via `Asymptotics.HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f`.
Poincaré expansions at infinity are the specialization `w z = z⁻¹`.

## Main results

* `Asymptotics.HasAsymptoticExpansion.isBigO_sub_constantCoeff` and
  `Asymptotics.HasAsymptoticExpansion.tendsto_constantCoeff`: first-order leading-term bound and
  limit to `constantCoeff P`.
* `Asymptotics.hasAsymptoticExpansion_pow_eval` and
  `Asymptotics.HasAsymptoticExpansion.isBigO_sub_trunc_eval`: asymptotic expansion of polynomial
  evaluations and remainder estimate after truncation.
* `Asymptotics.hasAsymptoticExpansion_pow_add`, `Asymptotics.hasAsymptoticExpansion_pow_mul`,
  `Asymptotics.hasAsymptoticExpansion_pow_pow`, `Asymptotics.hasAsymptoticExpansion_pow_inv`:
  closure of asymptotic power series under ring operations and reciprocals (when
  `constantCoeff P ≠ 0`).
* `Asymptotics.hasAsymptoticExpansion_pow_subst`: composition `H ∘ y ~ P.subst Q` when `H ~ P`
  in `σ`, `σ ∘ y ~ Q` in `w`, and `constantCoeff Q = 0`.
* `Asymptotics.hasAsymptoticExpansion_pow_substInv`: inversion `σ ∘ y ~ P.substInvOfIsUnit _`
  when `σ → 0`, `H ~ P` in `σ` with `constantCoeff P = 0` and `coeff 1 P ≠ 0`, and eventually
  `H (y x) = w x`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1(iii),
  <https://dlmf.nist.gov/2.1#iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1, §8.
-/

public section

open Filter Topology Finset PowerSeries
open scoped Polynomial

namespace Asymptotics

/-! ### Leading-term bounds -/

section LeadingTerm

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

/-- The remainder after the constant term of an asymptotic power series is `O(w)`. -/
theorem HasAsymptoticExpansion.isBigO_sub_constantCoeff {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    (fun x => f x - constantCoeff P) =O[l] w := by
  simpa only [range_one, sum_singleton, pow_zero, pow_one, smul_eq_mul, one_mul,
    coeff_zero_eq_constantCoeff_apply] using hf.isBigO 1

/-- An asymptotic power series in `w → 0` converges to its constant coefficient along `l`. -/
theorem HasAsymptoticExpansion.tendsto_constantCoeff {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hw : Tendsto w l (𝓝 0)) :
    Tendsto f l (𝓝 (constantCoeff P)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun x => ‖f x - constantCoeff P‖) =O[l] fun x => ‖w x‖ :=
    isBigO_norm_left.mpr (isBigO_norm_right.mpr hf.isBigO_sub_constantCoeff)
  have h0 : Tendsto (fun x => ‖f x - constantCoeff P‖) l (𝓝 0) :=
    hnorm.trans_tendsto (by simpa using hw.norm)
  simpa using h0

end LeadingTerm

/-! ### Polynomial evaluations and truncated power series -/

section Truncation

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

/-- Rewrites `(PowerSeries.trunc N P).eval y` in the `y ^ k • coeff k P` order used by
`HasAsymptoticExpansion`. -/
private lemma eval_trunc_eq_sum_smul (N : ℕ) (P : 𝕜⟦X⟧) (y : 𝕜) :
    (PowerSeries.trunc N P).eval y = ∑ k ∈ range N, y ^ k • coeff k P := by
  simp [PowerSeries.eval_trunc, mul_comm]

/-- A polynomial whose coefficients below degree `N` vanish is `O(w ^ N)` when evaluated at
`w → 0`. -/
private lemma isBigO_eval_pow_of_coeff_eq_zero {N : ℕ} (hw : Tendsto w l (𝓝 0))
    (R : 𝕜[X]) (h : ∀ k < N, R.coeff k = 0) :
    (fun x => R.eval (w x)) =O[l] fun x => w x ^ N :=
  Polynomial.isBigO_eval_of_X_pow_dvd hw (Polynomial.X_pow_dvd_iff.mpr h)

/-- A polynomial `p : 𝕜[X]` evaluated at `w → 0` has the asymptotic power series `(p : 𝕜⟦X⟧)`
in `w`. -/
theorem hasAsymptoticExpansion_pow_eval (hw : Tendsto w l (𝓝 0)) (p : 𝕜[X]) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (p : 𝕜⟦X⟧))
      (fun x => p.eval (w x)) := by
  have hsum := HasAsymptoticExpansion.sum (range (p.natDegree + 1)) fun k _ =>
    (isAsymptoticScale_pow hw).hasAsymptoticExpansion_single k (p.coeff k)
  refine (hsum.congr_coeff fun n => ?_).congr' (Eventually.of_forall fun x => ?_)
  · simp only [Finset.sum_apply, Polynomial.coeff_coe, Pi.single_apply, Finset.sum_ite_eq,
      mem_range]
    split_ifs with hn
    · rfl
    · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (not_lt.mp hn)).symm
  · simp only [Finset.sum_apply, smul_eq_mul, Polynomial.eval_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The remainder of an asymptotic power series `P` of `f` after degree `< N` is
`f x - (PowerSeries.trunc N P).eval (w x) = O(w x ^ N)`. -/
theorem HasAsymptoticExpansion.isBigO_sub_trunc_eval {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (N : ℕ) :
    (fun x => f x - (PowerSeries.trunc N P).eval (w x)) =O[l] fun x => w x ^ N := by
  refine (hf.isBigO N).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  rw [eval_trunc_eq_sum_smul]

end Truncation

/-! ### Ring operations on asymptotic power series -/

section LinearAlgebra

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

/-- A constant function `fun _ => c` has the constant asymptotic power series `C c`. -/
theorem hasAsymptoticExpansion_pow_const (c : 𝕜) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (C c)) (fun _ => c) :=
  ((HasAsymptoticExpansion.single_zero (φ := fun n x => w x ^ n) c).congr_coeff fun n => by
    cases n <;> simp [coeff_C]).congr' (Eventually.of_forall fun _ => by simp)

/-- Sums of asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_add {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hg : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) g) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P + Q)) (f + g) :=
  (hf.add hg).congr_coeff fun n => by simp [Pi.add_apply]

/-- Negation of an asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_neg {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (-P)) (-f) :=
  hf.neg.congr_coeff fun n => by simp [Pi.neg_apply]

/-- Differences of asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_sub {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f)
    (hg : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n Q) g) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P - Q)) (f - g) :=
  (hf.sub hg).congr_coeff fun n => by simp [Pi.sub_apply]

/-- Constant scalar multiples of asymptotic power series (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_const_mul {P : 𝕜⟦X⟧} {f : α → 𝕜} (c : 𝕜)
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
  refine (PowerSeries.isBigO_mul_sub_eval_trunc_mul hw
    (hf.isBigO_sub_trunc_eval N) (hg.isBigO_sub_trunc_eval N)).congr'
    (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  dsimp only
  rw [eval_trunc_eq_sum_smul, Pi.mul_apply]

/-- Natural powers of an asymptotic power series in a small variable `w` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_pow (hw : Tendsto w l (𝓝 0)) {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (k : ℕ) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P ^ k)) (f ^ k) := by
  induction k with
  | zero =>
    exact ((hasAsymptoticExpansion_pow_const (l := l) (w := w) (1 : 𝕜)).congr_coeff
      fun n => by rw [pow_zero, map_one]).congr' (Eventually.of_forall fun _ => by simp)
  | succ k ih =>
    simpa only [pow_succ] using hasAsymptoticExpansion_pow_mul hw ih hf

/-- Reciprocals of asymptotic power series with nonzero constant term (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_inv (hw : Tendsto w l (𝓝 0)) {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hP : constantCoeff P ≠ 0)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P⁻¹) f⁻¹ := by
  have hftend : Tendsto f l (𝓝 (constantCoeff P)) := hf.tendsto_constantCoeff hw
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
    have hQ0 := PowerSeries.isBigO_trunc_eval_one hw P⁻¹ M
    have h1 : (fun x => (f x - (PowerSeries.trunc M P).eval (w x)) *
        (PowerSeries.trunc M P⁻¹).eval (w x)) =O[l] fun x => w x ^ M := by
      simpa only [mul_one] using (hf.isBigO_sub_trunc_eval M).mul hQ0
    have h2 := PowerSeries.isBigO_mul_trunc_eval_sub hw P P⁻¹ M
    have hPQ1 : ∀ x : α, (PowerSeries.trunc M (P * P⁻¹)).eval (w x) = 1 := fun x => by
      rw [PowerSeries.mul_inv_cancel P hP, PowerSeries.eval_trunc, Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [coeff_one, hk]
      · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
    have hprod : (fun x => 1 - f x * (PowerSeries.trunc M P⁻¹).eval (w x)) =O[l]
        fun x => w x ^ M := by
      refine (h1.add h2).neg_left.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
      dsimp only
      rw [hPQ1 x]
      ring
    have hmul : (fun x => (f x)⁻¹ * (1 - f x * (PowerSeries.trunc M P⁻¹).eval (w x))) =O[l]
        fun x => w x ^ M := by
      simpa only [Pi.inv_apply, one_mul] using hfinv_O.mul hprod
    refine hmul.congr' (hfne.mono fun x hx => ?_) EventuallyEq.rfl
    dsimp only
    rw [eval_trunc_eq_sum_smul]
    simp only [Pi.inv_apply, mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

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
    simpa only [hQ, sub_zero] using hs.isBigO_sub_constantCoeff
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

private lemma isBigO_sum_trunc_substInv {P Q : 𝕜⟦X⟧} {M : ℕ}
    (hw0 : Tendsto w l (𝓝 0)) (hQ0 : constantCoeff Q = 0) (hPQ : P.subst Q = X) :
    (fun x => (∑ k ∈ range (M + 1), (PowerSeries.trunc (M + 1) Q).eval (w x) ^ k * coeff k P) -
        w x) =O[l]
      fun x => w x ^ (M + 1) := by
  set R : 𝕜[X] :=
    (PowerSeries.trunc (M + 1) P).comp (PowerSeries.trunc (M + 1) Q) - Polynomial.X
  have hcoeff : ∀ k < M + 1, R.coeff k = 0 := fun k hk => by
    rw [← Polynomial.coeff_coe]
    simp only [R, Polynomial.coeff_coe, Polynomial.coeff_sub,
      PowerSeries.coeff_trunc_comp_trunc P hQ0 hk hk, hPQ, coeff_X, Polynomial.coeff_X]
    split_ifs <;> first | exact sub_self _ | omega
  refine (isBigO_eval_pow_of_coeff_eq_zero hw0 R hcoeff).congr'
    (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [R, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X,
    eval_trunc_eq_sum_smul, smul_eq_mul]

private lemma isBigO_substInv_linear {σ H : β → 𝕜} {y : α → β} {P : 𝕜⟦X⟧}
    (hσ : Tendsto σ m (𝓝 0))
    (hH : HasAsymptoticExpansion m (fun n x => σ x ^ n) (fun n => coeff n P) H)
    (hP0 : constantCoeff P = 0) (hP1 : coeff 1 P ≠ 0) (hy : Tendsto y l m)
    (heq : ∀ᶠ x in l, H (y x) = w x) :
    (fun x => σ (y x)) =O[l] w ∧ w =O[l] fun x => σ (y x) := by
  set s : α → 𝕜 := fun x => σ (y x)
  have hs0 : Tendsto s l (𝓝 0) := hσ.comp hy
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
  exact ⟨hsO, hwO⟩

/-- Bootstrap step for power-series inversion: given an `O(w ^ M)` remainder after `M` terms of
`Q = P.substInvOfIsUnit _` (with `M ≥ 1`), upgrade the remainder to `O(w ^ (M + 1))` after
`M + 1` terms by inverting the linear coefficient `coeff 1 P ≠ 0`. -/
private lemma isBigO_substInv_step {σ H : β → 𝕜} {y : α → β} {P Q : 𝕜⟦X⟧} {M : ℕ}
    (hw0 : Tendsto w l (𝓝 0))
    (hH : HasAsymptoticExpansion m (fun n x => σ x ^ n) (fun n => coeff n P) H)
    (hP1 : coeff 1 P ≠ 0) (hy : Tendsto y l m) (heq : ∀ᶠ x in l, H (y x) = w x)
    (hQ0 : constantCoeff Q = 0) (hPQ : P.subst Q = X)
    (hsO : (fun x => σ (y x)) =O[l] w) (hM : 1 ≤ M)
    (ih : (fun x => σ (y x) - (PowerSeries.trunc M Q).eval (w x)) =O[l] fun x => w x ^ M) :
    (fun x => σ (y x) - (PowerSeries.trunc (M + 1) Q).eval (w x)) =O[l]
      fun x => w x ^ (M + 1) := by
  set s : α → 𝕜 := fun x => σ (y x)
  set q : α → 𝕜 := fun x => (PowerSeries.trunc (M + 1) Q).eval (w x)
  set r : α → 𝕜 := fun x => s x - q x
  -- Adding the `M`-th term keeps the remainder `r = s - q` at `O(w ^ M)`, and `q = O(w)`
  -- since `constantCoeff Q = 0`.
  have hrM : r =O[l] fun x => w x ^ M := by
    have hterm : (fun x => w x ^ M * coeff M Q) =O[l] fun x => w x ^ M :=
      ((isBigO_refl _ _).const_mul_left (coeff M Q)).congr'
        (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
    refine (ih.sub hterm).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    simp only [r, q, eval_trunc_eq_sum_smul, smul_eq_mul, sum_range_succ]
    ring
  have hqO : q =O[l] w := by
    refine (isBigO_eval_pow_of_coeff_eq_zero (N := 1) hw0 (PowerSeries.trunc (M + 1) Q)
      fun k hk => ?_).congr' EventuallyEq.rfl
      (Eventually.of_forall fun _ => pow_one _)
    rw [Nat.lt_one_iff.mp hk, PowerSeries.coeff_trunc]
    simp [hQ0]
  -- Split `-r * coeff 1 P` into three `O(w ^ (M + 1))` pieces:
  -- `hA`: `w - P_{≤M}(s)` from `H(y) = w` and `H ~ P` (since `s = O(w)`),
  -- `hB`: `(P_{≤M}(s) - P_{≤M}(q)) - r * P_1` from the higher-degree difference estimate,
  -- `hC`: `P_{≤M}(q) - w` from the formal inverse relation `P.subst Q = X`.
  have hA : (fun x => w x - ∑ k ∈ range (M + 1), s x ^ k * coeff k P) =O[l]
      fun x => w x ^ (M + 1) := by
    have h := ((hH.isBigO (M + 1)).comp_tendsto hy).trans (hsO.pow (M + 1))
    exact h.congr' (heq.mono fun x hx => by simp only [Function.comp_apply, hx, smul_eq_mul, s])
      EventuallyEq.rfl
  have hB : (fun x => (∑ k ∈ range (M + 1), s x ^ k * coeff k P -
      ∑ k ∈ range (M + 1), q x ^ k * coeff k P) - (s x - q x) * coeff 1 P) =O[l]
      fun x => w x ^ (M + 1) := by
    refine (PowerSeries.isBigO_trunc_eval_sub_sub_linear hw0 P hM hsO hqO hrM).congr'
      (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    simp only [eval_trunc_eq_sum_smul, smul_eq_mul]
  have hC : (fun x => (∑ k ∈ range (M + 1), q x ^ k * coeff k P) - w x) =O[l]
      fun x => w x ^ (M + 1) :=
    isBigO_sum_trunc_substInv hw0 hQ0 hPQ
  have hcomb : (fun x => r x * coeff 1 P) =O[l] fun x => w x ^ (M + 1) := by
    refine ((hA.add hB).add hC).neg_left.congr' (Eventually.of_forall fun x => ?_)
      EventuallyEq.rfl
    dsimp only [r, q]
    ring
  refine (hcomb.const_mul_left (coeff 1 P)⁻¹).congr' (Eventually.of_forall fun x => ?_)
    EventuallyEq.rfl
  dsimp only
  rw [mul_comm (r x), ← mul_assoc, inv_mul_cancel₀ hP1, one_mul]

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
  obtain ⟨hsO, hwO⟩ := isBigO_substInv_linear hσ hH hP0 hP1 hy heq
  have hw0 : Tendsto w l (𝓝 0) := hwO.trans_tendsto hs0
  rw [hasAsymptoticExpansion_iff]
  intro N
  suffices htrunc : (fun x => s x - (PowerSeries.trunc N Q).eval (w x)) =O[l] fun x => w x ^ N by
    refine htrunc.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    dsimp only
    rw [eval_trunc_eq_sum_smul]
  induction N with
  | zero =>
    simpa only [eval_trunc_eq_sum_smul, range_zero, sum_empty, sub_zero, pow_zero] using
      hs0.isBigO_one 𝕜
  | succ N ih =>
    cases N with
    | zero =>
      simpa only [zero_add, eval_trunc_eq_sum_smul, range_one, sum_singleton, pow_zero, pow_one,
        smul_eq_mul, one_mul, coeff_zero_eq_constantCoeff_apply, hQ0, sub_zero] using hsO
    | succ N =>
      exact isBigO_substInv_step (y := y) hw0 hH hP1 hy heq hQ0 hPQ hsO (Nat.succ_pos N) ih

end Algebra

end Asymptotics
