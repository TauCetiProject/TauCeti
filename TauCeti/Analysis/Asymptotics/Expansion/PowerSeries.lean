/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Analysis.Asymptotics.Expansion.Basic

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

/-- A polynomial `p : 𝕜[X]` evaluated at `w → 0` has the asymptotic power series `(p : 𝕜⟦X⟧)`
in `w`. -/
theorem hasAsymptoticExpansion_pow_eval (hw : Tendsto w l (𝓝 0)) (p : 𝕜[X]) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (p : 𝕜⟦X⟧))
      (fun x => p.eval (w x)) := by
  rw [hasAsymptoticExpansion_iff]
  intro M
  by_cases hMp : M ≤ p.natDegree + 1
  · have hdiff : ∀ x : α,
        p.eval (w x) - ∑ n ∈ range M, w x ^ n * coeff n (p : 𝕜⟦X⟧) =
          ∑ k ∈ Ico M (p.natDegree + 1), w x ^ k * p.coeff k := fun x => by
      rw [Polynomial.eval_eq_sum_range, ← sum_range_add_sum_Ico _ hMp]
      have heq : ∑ n ∈ range M, w x ^ n * coeff n (p : 𝕜⟦X⟧) =
          ∑ n ∈ range M, p.coeff n * w x ^ n :=
        sum_congr rfl fun n _ => by rw [Polynomial.coeff_coe, mul_comm]
      rw [heq, add_sub_cancel_left]
      exact sum_congr rfl fun k _ => mul_comm _ _
    simp_rw [smul_eq_mul, hdiff]
    refine IsBigO.fun_sum fun k hk => ?_
    have h1 := ((isAsymptoticScale_pow hw).isBigO_of_le (mem_Ico.mp hk).1).const_mul_left
      (p.coeff k)
    exact h1.congr' (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
  · have hpM : p.natDegree < M := by omega
    have hdiff : ∀ x : α,
        p.eval (w x) - ∑ n ∈ range M, w x ^ n * coeff n (p : 𝕜⟦X⟧) = 0 := fun x => by
      rw [Polynomial.eval_eq_sum_range' hpM]
      have heq : ∑ n ∈ range M, w x ^ n * coeff n (p : 𝕜⟦X⟧) =
          ∑ n ∈ range M, p.coeff n * w x ^ n :=
        sum_congr rfl fun n _ => by rw [Polynomial.coeff_coe, mul_comm]
      rw [heq, sub_self]
    simp_rw [smul_eq_mul, hdiff]
    exact isBigO_zero _ _

/-- The remainder of an asymptotic power series `P` of `f` after degree `< N` is
`f x - (PowerSeries.trunc N P).eval (w x) = O(w x ^ N)`. -/
theorem HasAsymptoticExpansion.isBigO_sub_trunc_eval {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (N : ℕ) :
    (fun x => f x - (PowerSeries.trunc N P).eval (w x)) =O[l] fun x => w x ^ N := by
  refine (hf.isBigO N).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [PowerSeries.eval_trunc, smul_eq_mul]
  congr 1
  exact sum_congr rfl fun n _ => mul_comm _ _

/-- The `N`-th truncation `(PowerSeries.trunc N P).eval (w x)` is `O(1)` when `w → 0`. -/
theorem isBigO_trunc_eval_one (hw : Tendsto w l (𝓝 0)) (P : 𝕜⟦X⟧) (N : ℕ) :
    (fun x => (PowerSeries.trunc N P).eval (w x)) =O[l] fun _ => (1 : 𝕜) := by
  simpa only [range_zero, sum_empty, sub_zero, pow_zero] using
    (hasAsymptoticExpansion_pow_eval hw (PowerSeries.trunc N P)).isBigO 0

/-- Multiplying two `N`-th truncations agrees with the `N`-th truncation of the product up to
`O(w ^ N)` when `w → 0`. -/
theorem isBigO_mul_trunc_eval_sub (hw : Tendsto w l (𝓝 0)) (P Q : 𝕜⟦X⟧) (N : ℕ) :
    (fun x => (PowerSeries.trunc N P).eval (w x) * (PowerSeries.trunc N Q).eval (w x) -
      (PowerSeries.trunc N (P * Q)).eval (w x)) =O[l] fun x => w x ^ N := by
  set R : 𝕜[X] := PowerSeries.trunc N P * PowerSeries.trunc N Q - PowerSeries.trunc N (P * Q)
  have hcoeff : ∀ k < N, coeff k (R : 𝕜⟦X⟧) = 0 := fun k hk => by
    have hmul := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc P Q hk
    simp only [R, Polynomial.coeff_coe, Polynomial.coeff_sub,
      ← Polynomial.coeff_coe (PowerSeries.trunc N P * PowerSeries.trunc N Q),
      Polynomial.coe_mul, ← hmul, PowerSeries.coeff_trunc, hk, ↓reduceIte, sub_self]
  refine ((hasAsymptoticExpansion_pow_eval hw R).isBigO N).congr'
    (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  have hzero : ∑ k ∈ range N, w x ^ k • coeff k (R : 𝕜⟦X⟧) = 0 :=
    sum_eq_zero fun k hk => by rw [hcoeff k (mem_range.mp hk), smul_zero]
  simp only [R, hzero, sub_zero, Polynomial.eval_sub, Polynomial.eval_mul]

/-- Remainder estimate for evaluating a truncated power series at two `O(w)` functions differing
by `O(w ^ M)`. -/
private lemma isBigO_trunc_eval_sub_sub_linear {s q : α → 𝕜} {M : ℕ}
    (hw0 : Tendsto w l (𝓝 0)) (P : 𝕜⟦X⟧) (hM : 1 ≤ M)
    (hsO : s =O[l] w) (hqO : q =O[l] w) (hrM : (fun x => s x - q x) =O[l] fun x => w x ^ M) :
    (fun x => ((PowerSeries.trunc (M + 1) P).eval (s x) -
        (PowerSeries.trunc (M + 1) P).eval (q x)) - (s x - q x) * coeff 1 P) =O[l]
      fun x => w x ^ (M + 1) := by
  simp_rw [PowerSeries.eval_trunc]
  have hrew : ∀ x : α,
      (∑ k ∈ range (M + 1), coeff k P * s x ^ k -
        ∑ k ∈ range (M + 1), coeff k P * q x ^ k) - (s x - q x) * coeff 1 P =
      ∑ k ∈ Ico 2 (M + 1), (s x ^ k - q x ^ k) * coeff k P := fun x => by
    rw [← sum_sub_distrib]
    have h2le : 2 ≤ M + 1 := by omega
    have hsplit := sum_range_add_sum_Ico
      (f := fun k => coeff k P * s x ^ k - coeff k P * q x ^ k) h2le
    rw [← hsplit]
    have h01 : ∑ k ∈ range 2, (coeff k P * s x ^ k - coeff k P * q x ^ k) =
        (s x - q x) * coeff 1 P := by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, pow_one]
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

end Truncation

/-! ### Ring operations on asymptotic power series -/

section LinearAlgebra

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

/-- A constant function `fun _ => c` has the constant asymptotic power series `C c`. -/
theorem hasAsymptoticExpansion_pow_const (c : 𝕜) :
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
  have hg0 : g =O[l] fun _ => (1 : 𝕜) := by
    simpa only [range_zero, sum_empty, sub_zero, pow_zero] using hg.isBigO 0
  have hP0 := isBigO_trunc_eval_one hw P N
  have h1 : (fun x => (f x - (PowerSeries.trunc N P).eval (w x)) * g x) =O[l]
      fun x => w x ^ N := by
    simpa only [mul_one] using (hf.isBigO_sub_trunc_eval N).mul hg0
  have h2 : (fun x => (PowerSeries.trunc N P).eval (w x) *
      (g x - (PowerSeries.trunc N Q).eval (w x))) =O[l] fun x => w x ^ N := by
    simpa only [one_mul] using hP0.mul (hg.isBigO_sub_trunc_eval N)
  have h3 := isBigO_mul_trunc_eval_sub hw P Q N
  refine ((h1.add h2).add h3).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [Pi.mul_apply, smul_eq_mul, PowerSeries.eval_trunc]
  have hswap : ∑ i ∈ range N, w x ^ i * coeff i (P * Q) =
      ∑ i ∈ range N, coeff i (P * Q) * w x ^ i :=
    sum_congr rfl fun i _ => mul_comm _ _
  rw [hswap]
  ring

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
    have hQ0 := isBigO_trunc_eval_one hw P⁻¹ M
    have h1 : (fun x => (f x - (PowerSeries.trunc M P).eval (w x)) *
        (PowerSeries.trunc M P⁻¹).eval (w x)) =O[l] fun x => w x ^ M := by
      simpa only [mul_one] using (hf.isBigO_sub_trunc_eval M).mul hQ0
    have h2 := isBigO_mul_trunc_eval_sub hw P P⁻¹ M
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
    simp only [Pi.inv_apply, smul_eq_mul, PowerSeries.eval_trunc, mul_sub, mul_one, ← mul_assoc,
      inv_mul_cancel₀ hx, one_mul]
    congr 1
    exact sum_congr rfl fun n _ => mul_comm _ _

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
  have hcoeff : ∀ k < M + 1, coeff k (R : 𝕜⟦X⟧) = 0 := fun k hk => by
    simp only [R, Polynomial.coeff_coe, Polynomial.coeff_sub,
      PowerSeries.coeff_trunc_comp_trunc P hQ0 hk hk, hPQ, coeff_X, Polynomial.coeff_X]
    split_ifs <;> first | exact sub_self _ | omega
  refine ((hasAsymptoticExpansion_pow_eval hw0 R).isBigO (M + 1)).congr'
    (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  have hzero : ∑ k ∈ range (M + 1), w x ^ k • coeff k (R : 𝕜⟦X⟧) = 0 :=
    sum_eq_zero fun k hk => by rw [hcoeff k (mem_range.mp hk), smul_zero]
  simp only [R, hzero, sub_zero, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X,
    PowerSeries.eval_trunc]
  congr 1
  exact sum_congr rfl fun k _ => mul_comm _ _

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
      set q : α → 𝕜 := fun x => (PowerSeries.trunc (M + 1) Q).eval (w x)
      set r : α → 𝕜 := fun x => s x - q x
      have hrM : r =O[l] fun x => w x ^ M := by
        have hterm : (fun x => w x ^ M * coeff M Q) =O[l] fun x => w x ^ M :=
          ((isBigO_refl _ _).const_mul_left (coeff M Q)).congr'
            (Eventually.of_forall fun x => mul_comm _ _) EventuallyEq.rfl
        refine (ih.sub hterm).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
        dsimp only [r, q]
        rw [PowerSeries.eval_trunc]
        simp only [smul_eq_mul, sum_range_succ]
        have hswap : ∑ i ∈ range M, coeff i Q * w x ^ i =
            ∑ i ∈ range M, w x ^ i * coeff i Q :=
          sum_congr rfl fun i _ => mul_comm _ _
        rw [hswap]
        ring
      have hqO : q =O[l] w := by
        simp_rw [q, PowerSeries.eval_trunc]
        refine IsBigO.fun_sum fun n _ => ?_
        cases n with
        | zero =>
          simp only [pow_zero, coeff_zero_eq_constantCoeff_apply, hQ0, zero_mul]
          exact isBigO_zero _ _
        | succ n =>
          have h1 := ((isAsymptoticScale_pow hw0).isBigO_of_le
            (Nat.succ_le_succ (Nat.zero_le n))).const_mul_left (coeff (n + 1) Q)
          simpa only [pow_one] using h1
      have hA : (fun x => w x - ∑ k ∈ range (M + 1), s x ^ k * coeff k P) =O[l]
          fun x => w x ^ (M + 1) := by
        have h := ((hH.isBigO (M + 1)).comp_tendsto hy).trans (hsO.pow (M + 1))
        exact h.congr' (heq.mono fun x hx => by simp only [Function.comp_apply, hx, smul_eq_mul, s])
          EventuallyEq.rfl
      have hB : (fun x => (∑ k ∈ range (M + 1), s x ^ k * coeff k P -
          ∑ k ∈ range (M + 1), q x ^ k * coeff k P) - (s x - q x) * coeff 1 P) =O[l]
          fun x => w x ^ (M + 1) := by
        refine (isBigO_trunc_eval_sub_sub_linear hw0 P (Nat.succ_pos N) hsO hqO hrM).congr'
          (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
        simp only [PowerSeries.eval_trunc]
        congr 1
        congr 1 <;> exact sum_congr rfl fun k _ => mul_comm _ _
      have hC : (fun x => (∑ k ∈ range (M + 1), q x ^ k * coeff k P) - w x) =O[l]
          fun x => w x ^ (M + 1) :=
        isBigO_sum_trunc_substInv hw0 hQ0 hPQ
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
      refine hrM1.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
      simp only [r, q, PowerSeries.eval_trunc, smul_eq_mul]
      congr 1
      exact sum_congr rfl fun n _ => mul_comm _ _

end Algebra

end Asymptotics
