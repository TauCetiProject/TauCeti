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
* `Asymptotics.hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc`,
  `Asymptotics.hasAsymptoticExpansion_pow_eval`, and
  `Asymptotics.HasAsymptoticExpansion.isBigO_sub_eval_trunc`: equivalence between asymptotic
  power series and truncation-evaluation remainders, polynomial evaluations, and remainder bounds.
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

/-- An asymptotic power series `P` of `f` in `w` is equivalent to every truncation
`(PowerSeries.trunc N P).eval (w x)` approximating `f x` up to `O(w x ^ N)`. -/
theorem hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc {P : 𝕜⟦X⟧} {f : α → 𝕜} :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f ↔
      ∀ N, (fun x => f x - (PowerSeries.trunc N P).eval (w x)) =O[l] fun x => w x ^ N := by
  simp only [hasAsymptoticExpansion_iff, PowerSeries.eval_trunc, smul_eq_mul, mul_comm]

/-- A polynomial `p : 𝕜[X]` evaluated at `w → 0` has the asymptotic power series `(p : 𝕜⟦X⟧)`
in `w`. -/
theorem hasAsymptoticExpansion_pow_eval (hw : Tendsto w l (𝓝 0)) (p : 𝕜[X]) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (p : 𝕜⟦X⟧))
      (fun x => p.eval (w x)) :=
  hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc.mpr
    (fun N => Polynomial.isBigO_eval_sub_eval_trunc_coe hw N p)

/-- The remainder of an asymptotic power series `P` of `f` after degree `< N` is
`f x - (PowerSeries.trunc N P).eval (w x) = O(w x ^ N)`. -/
theorem HasAsymptoticExpansion.isBigO_sub_eval_trunc {P : 𝕜⟦X⟧} {f : α → 𝕜}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (N : ℕ) :
    (fun x => f x - (PowerSeries.trunc N P).eval (w x)) =O[l] fun x => w x ^ N :=
  hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc.mp hf N

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
    HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n (P * Q)) (f * g) :=
  hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc.mpr fun N =>
    PowerSeries.isBigO_mul_sub_eval_trunc_mul hw
      (hf.isBigO_sub_eval_trunc N) (hg.isBigO_sub_eval_trunc N)

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
  refine hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc.mpr fun N => ?_
  cases N with
  | zero =>
    simpa only [PowerSeries.eval_trunc, range_zero, sum_empty, sub_zero, pow_zero] using hfinv_O
  | succ N =>
    set M := N + 1
    have hprod : (fun x => 1 - f x * (PowerSeries.trunc M P⁻¹).eval (w x)) =O[l]
        fun x => w x ^ M := by
      have h := (PowerSeries.isBigO_mul_sub_eval_trunc_mul hw (hf.isBigO_sub_eval_trunc M)
        (Q := P⁻¹) (G := fun x => (PowerSeries.trunc M P⁻¹).eval (w x))
        (by simpa only [sub_self] using isBigO_zero (fun x => w x ^ M) l)).neg_left
      refine h.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
      dsimp only
      rw [PowerSeries.mul_inv_cancel P hP, PowerSeries.trunc_one, Polynomial.eval_one, neg_sub]
    have hmul : (fun x => (f x)⁻¹ * (1 - f x * (PowerSeries.trunc M P⁻¹).eval (w x))) =O[l]
        fun x => w x ^ M := by
      simpa only [Pi.inv_apply, one_mul] using hfinv_O.mul hprod
    refine hmul.congr' (hfne.mono fun x hx => ?_) EventuallyEq.rfl
    dsimp only
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
  have hm : (fun x => coeff 1 P * s x) =Θ[l] s := (isTheta_refl s l).const_mul_left hP1
  have hwΘ := hlin.add_isTheta hm
  exact ⟨hwΘ.2.congr_right fun x => by simp only [Pi.add_apply]; ring,
    hwΘ.1.congr_left fun x => by simp only [Pi.add_apply]; ring⟩

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
  have hQP : Q.subst P = X := PowerSeries.subst_substInvOfIsUnit_left P hP0 hP1.isUnit
  have hs0 : Tendsto s l (𝓝 0) := hσ.comp hy
  obtain ⟨hsO, hwO⟩ := isBigO_substInv_linear hσ hH hP0 hP1 hy heq
  have hw0 : Tendsto w l (𝓝 0) := hwO.trans_tendsto hs0
  refine hasAsymptoticExpansion_pow_iff_isBigO_sub_eval_trunc.mpr fun N => ?_
  cases N with
  | zero =>
    simpa only [PowerSeries.eval_trunc, range_zero, sum_empty, sub_zero, pow_zero] using
      hs0.isBigO_one 𝕜
  | succ N =>
    cases N with
    | zero =>
      simpa only [zero_add, PowerSeries.eval_trunc, range_one, sum_singleton, pow_zero, pow_one,
        mul_one, coeff_zero_eq_constantCoeff_apply, hQ0, sub_zero] using hsO
    | succ N =>
      set M := N + 2
      have hHy0 : Tendsto (fun x => H (y x)) l (𝓝 0) := hw0.congr' (heq.mono fun _ hx => hx.symm)
      have hcomp := hasAsymptoticExpansion_pow_subst hs0 tendsto_id hP0
        (hasAsymptoticExpansion_pow_eval hHy0 (PowerSeries.trunc M Q)) (hH.comp_tendsto hy)
      have hcoeff (n : ℕ) (hn : n < M) :
          coeff n ((PowerSeries.trunc M Q : 𝕜⟦X⟧).subst P) = coeff n X := by
        rw [PowerSeries.coeff_subst_eq_sum_range _ hP0, ← hQP,
          PowerSeries.coeff_subst_eq_sum_range _ hP0]
        refine sum_congr rfl fun k hk => ?_
        have hkM : k < M := Nat.lt_of_lt_of_le (mem_range.mp hk) hn
        rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hkM]
      have hsum (x : α) :
          ∑ n ∈ range M, s x ^ n • coeff n ((PowerSeries.trunc M Q : 𝕜⟦X⟧).subst P) = s x := by
        rw [sum_congr rfl fun n hn => by rw [hcoeff n (mem_range.mp hn)],
          sum_eq_single 1 (fun n _ hn => by simp [coeff_X, hn]) (by simp [M])]
        simp
      refine ((hcomp.isBigO M).trans (hsO.pow M)).neg_left.congr'
        (heq.mono fun x hx => ?_) EventuallyEq.rfl
      dsimp only [id_eq]
      rw [hsum x, hx, neg_sub]

end Algebra

end Asymptotics
