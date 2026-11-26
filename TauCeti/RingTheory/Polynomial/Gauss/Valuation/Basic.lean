/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Valuation.Basic
import TauCeti.RingTheory.Valuation.Sum

/-!
# Gauss valuation of polynomials

Given a valuation `v : Valuation R Γ₀` and a radius `r : Γ₀`, `Polynomial.gaussValuation p v r` is
the maximum of `v (p.coeff i) * r ^ i` over all `i : ℕ`. Unlike `Polynomial.gaussNorm`, which
targets real-valued absolute values `AbsoluteValue R ℝ`, `Polynomial.gaussValuation` applies to
arbitrary value monoids and groups `Γ₀`, and bundles into a valuation `Valuation.gauss v r` on
`R[X]`.

## Main definitions

* `Polynomial.gaussValuation`: the Gauss valuation `p.support.sup fun i ↦ v (p.coeff i) * r ^ i`.
* `Valuation.gauss`: the bundled `Valuation R[X] Γ₀` given by `Polynomial.gaussValuation`.

## Main results

* `Polynomial.gaussValuation_le_iff`, `Polynomial.monotone_gaussValuation`,
  `Polynomial.gaussValuation_eq_zero_iff`, `Polynomial.gaussValuation_add_le`,
  `Polynomial.gaussValuation_map`, `Polynomial.valuation_eval₂_le_gaussValuation`,
  `Polynomial.valuation_eval_le_gaussValuation`: coefficient characterization, radius monotonicity,
  support characterization, ultrametric addition bound, coefficient-map pullback, and evaluation
  bounds.
* `Polynomial.gaussValuation_mul`: multiplicativity `(p * q).gaussValuation v r =
  p.gaussValuation v r * q.gaussValuation v r`.
* `Valuation.gauss_comap_C`, `Valuation.gauss_zero`, `Valuation.le_gauss_of_comap_C_eq`:
  restriction to constants, radius-zero pullback, and pointwise maximality among extensions of `v`
  with `w X ≤ r`.
* `Polynomial.gaussValuation_eq_mul_prod_roots`,
  `Polynomial.valuation_eval_eq_gaussValuation_of_forall_roots_ne`: root-product formula for split
  polynomials and sphere-evaluation equality away from root valuations.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.
* L. Alpöge, `New.Selmer.gaussVal` and `New.Selmer.gaussVal_eq_mul_prod_roots` in
  `src/Lib/General/NumberTheory/GaussValuation.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

namespace Valuation

open Polynomial

/-- Weighted convolution bound for the coefficients of a product of polynomials: if
`v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i` and `v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j`, then
`v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k`. -/
theorem map_coeff_mul_mul_pow_le_of_le {R Γ₀ : Type*} [Ring R]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) {p q : R[X]} {r s₁ s₂ A₁ A₂ S : Γ₀}
    (hp : ∀ i, v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i)
    (hq : ∀ j, v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j) (k : ℕ) :
    v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k := by
  rw [coeff_mul, mul_assoc]
  refine v.map_sum_mul_le fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  calc v (p.coeff ij.1 * q.coeff ij.2) * (r ^ k * (s₁ * s₂))
      = v (p.coeff ij.1) * r ^ ij.1 * s₁ * (v (q.coeff ij.2) * r ^ ij.2 * s₂) := by
        simp only [← hij, pow_add, map_mul]
        ac_rfl
    _ ≤ A₁ * S ^ ij.1 * (A₂ * S ^ ij.2) := mul_le_mul' (hp _) (hq _)
    _ = (A₁ * A₂) * S ^ k := by
        rw [← hij, pow_add]
        ac_rfl

end Valuation

namespace Polynomial

section Ring

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- The Gauss valuation of a polynomial `p` at a valuation `v` and radius `r`:
the supremum of `v (p.coeff i) * r ^ i` over all `i ∈ p.support` (and `0` when `p = 0`). -/
def gaussValuation (p : R[X]) (v : Valuation R Γ₀) (r : Γ₀) : Γ₀ :=
  p.support.sup fun i ↦ v (p.coeff i) * r ^ i

/-- Definitional unfolding of `Polynomial.gaussValuation`. -/
theorem gaussValuation_def (p : R[X]) (v : Valuation R Γ₀) (r : Γ₀) :
    p.gaussValuation v r = p.support.sup fun i ↦ v (p.coeff i) * r ^ i := by
  rfl

variable (v : Valuation R Γ₀) (r : Γ₀)

/-- The Gauss valuation of `0` is `0`. -/
@[simp]
theorem gaussValuation_zero : (0 : R[X]).gaussValuation v r = 0 := by
  rw [gaussValuation_def, support_zero, Finset.sup_empty, bot_eq_zero]

/-- The Gauss valuation of `p` is at most `c` iff every weighted coefficient
`v (p.coeff i) * r ^ i` is at most `c`. -/
theorem gaussValuation_le_iff {p : R[X]} {c : Γ₀} :
    p.gaussValuation v r ≤ c ↔ ∀ i, v (p.coeff i) * r ^ i ≤ c := by
  rw [gaussValuation_def, Finset.sup_le_iff]
  refine ⟨fun h i ↦ ?_, fun h i _ ↦ h i⟩
  by_cases hi : i ∈ p.support
  · exact h i hi
  · rw [notMem_support_iff.mp hi, map_zero, zero_mul]
    exact zero_le

/-- Each weighted coefficient `v (p.coeff i) * r ^ i` is bounded above by the Gauss valuation. -/
theorem le_gaussValuation (p : R[X]) (i : ℕ) :
    v (p.coeff i) * r ^ i ≤ p.gaussValuation v r :=
  (gaussValuation_le_iff v r).mp le_rfl i

/-- The Gauss valuation is monotone in the radius `r`. -/
theorem monotone_gaussValuation (p : R[X]) : Monotone (p.gaussValuation v) :=
  fun _ _ hr ↦ (gaussValuation_le_iff v _).mpr fun i ↦
    (mul_le_mul_right (pow_le_pow_left' hr i) _).trans (le_gaussValuation v _ p i)

/-- At a nonzero radius `r`, `p.gaussValuation v r = 0` iff every coefficient of `p` has
valuation `0`. -/
theorem gaussValuation_eq_zero_iff {r : Γ₀} (hr : r ≠ 0) {p : R[X]} :
    p.gaussValuation v r = 0 ↔ ∀ i, v (p.coeff i) = 0 := by
  rw [← nonpos_iff_eq_zero, gaussValuation_le_iff]
  simp [nonpos_iff_eq_zero, pow_ne_zero, hr]

/-- For any nonzero polynomial `p`, some index in `p.support` attains `p.gaussValuation v r`. -/
theorem exists_eq_gaussValuation {p : R[X]} (hp : p ≠ 0) :
    ∃ i ∈ p.support, v (p.coeff i) * r ^ i = p.gaussValuation v r := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    fun i ↦ v (p.coeff i) * r ^ i
  exact ⟨i, hi, heq.symm⟩

/-- The Gauss valuation of a monomial `monomial n a` at radius `r` is `v a * r ^ n`. -/
@[simp]
theorem gaussValuation_monomial (n : ℕ) (a : R) :
    (monomial n a).gaussValuation v r = v a * r ^ n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [gaussValuation_def, support_monomial n ha, Finset.sup_singleton, coeff_monomial_same]

/-- The Gauss valuation of a constant polynomial `C a` is `v a`. -/
@[simp]
theorem gaussValuation_C (a : R) : (C a).gaussValuation v r = v a := by
  rw [← monomial_zero_left, gaussValuation_monomial, pow_zero, mul_one]

/-- The Gauss valuation of `1` is `1`. -/
@[simp]
theorem gaussValuation_one : (1 : R[X]).gaussValuation v r = 1 := by
  rw [← C_1, gaussValuation_C, map_one]

/-- The Gauss valuation of `X` at radius `r` is `r`. -/
@[simp]
theorem gaussValuation_X : (X : R[X]).gaussValuation v r = r := by
  rw [← monomial_one_one_eq_X, gaussValuation_monomial, map_one, one_mul, pow_one]

/-- The Gauss valuation of `X - C a` at radius `r` is `max r (v a)`. -/
@[simp]
theorem gaussValuation_X_sub_C (a : R) : (X - C a).gaussValuation v r = max r (v a) :=
  le_antisymm ((gaussValuation_le_iff v r).mpr fun i ↦ by
      rcases i with _ | _ | n <;> simp [coeff_X])
    (max_le (by have h := le_gaussValuation v r (X - C a) 1; simpa [coeff_sub, coeff_X] using h)
      (by have h := le_gaussValuation v r (X - C a) 0; simpa [coeff_sub, coeff_X] using h))

/-- The Gauss valuation at radius `0` is the valuation of the constant term. -/
@[simp]
theorem gaussValuation_at_zero (p : R[X]) : p.gaussValuation v 0 = v (p.coeff 0) :=
  le_antisymm ((gaussValuation_le_iff v 0).mpr fun i ↦ by cases i <;> simp)
    (by simpa using le_gaussValuation v 0 p 0)

/-- The Gauss valuation satisfies the ultrametric triangle inequality. -/
theorem gaussValuation_add_le (p q : R[X]) :
    (p + q).gaussValuation v r ≤ max (p.gaussValuation v r) (q.gaussValuation v r) := by
  refine (gaussValuation_le_iff v r).mpr fun i ↦ ?_
  rw [coeff_add]
  exact (mul_le_mul_left (v.map_add (p.coeff i) (q.coeff i)) _).trans
    ((max_mul ..).trans_le (max_le_max (le_gaussValuation v r p i) (le_gaussValuation v r q i)))

/-- Mapping coefficients along a ring homomorphism `f : R →+* S` pulls the Gauss valuation back
to the comapped valuation `v.comap f`. -/
@[simp]
theorem gaussValuation_map {S : Type*} [Ring S] (f : R →+* S) (v : Valuation S Γ₀) (r : Γ₀)
    (p : R[X]) :
    (p.map f).gaussValuation v r = p.gaussValuation (v.comap f) r :=
  eq_of_forall_ge_iff fun c ↦ by
    simp only [gaussValuation_le_iff, coeff_map, Valuation.comap_apply]

/-- Evaluating `p` across a ring homomorphism `f : R →+* S` at `x : S` with `v x ≤ r` gives
valuation at most `p.gaussValuation (v.comap f) r`. -/
theorem valuation_eval₂_le_gaussValuation {S : Type*} [Ring S] (f : R →+* S) (v : Valuation S Γ₀)
    (r : Γ₀) (p : R[X]) {x : S} (hx : v x ≤ r) :
    v (p.eval₂ f x) ≤ p.gaussValuation (v.comap f) r := by
  rw [eval₂_eq_sum]
  refine v.map_sum_le fun i _ ↦ ?_
  rw [map_mul, map_pow]
  exact (mul_le_mul_right (pow_le_pow_left' hx i) _).trans (le_gaussValuation (v.comap f) r p i)

/-- Evaluating `p` at `x` with `v x ≤ r` gives valuation at most `p.gaussValuation v r`. -/
theorem valuation_eval_le_gaussValuation (p : R[X]) {x : R} (hx : v x ≤ r) :
    v (p.eval x) ≤ p.gaussValuation v r := by
  simpa [eval₂_id] using valuation_eval₂_le_gaussValuation (RingHom.id R) v r p hx

/-- Rescaling the variable by `C a * X` multiplies the radius of the Gauss valuation by `v a`. -/
theorem gaussValuation_comp_C_mul_X (p : R[X]) (a : R) :
    (p.comp (C a * X)).gaussValuation v r = p.gaussValuation v (v a * r) :=
  eq_of_forall_ge_iff fun c ↦ by
    simp only [gaussValuation_le_iff, comp_C_mul_X_coeff, map_mul, map_pow, mul_pow, mul_assoc]

/-- The least index attaining the Gauss valuation of a polynomial has strictly smaller
weighted coefficients at all lower indices. -/
private lemma exists_min_eq_gaussValuation (p : R[X]) :
    ∃ i₀, v (p.coeff i₀) * r ^ i₀ = p.gaussValuation v r ∧
      ∀ i < i₀, v (p.coeff i) * r ^ i < p.gaussValuation v r := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, by simp, fun _ h ↦ (Nat.not_lt_zero _ h).elim⟩
  have hex : ∃ i, v (p.coeff i) * r ^ i = p.gaussValuation v r :=
    let ⟨i, _, hi⟩ := exists_eq_gaussValuation v r hp; ⟨i, hi⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi ↦
    lt_of_le_of_ne (le_gaussValuation v r p i) (Nat.find_min hex hi)⟩

/-- **Gauss's lemma for valuations**: the Gauss valuation of a product of polynomials is the
product of their Gauss valuations. -/
@[simp]
theorem gaussValuation_mul (p q : R[X]) :
    (p * q).gaussValuation v r = p.gaussValuation v r * q.gaussValuation v r := by
  refine le_antisymm ((gaussValuation_le_iff v r).mpr fun k ↦ ?_) ?_
  · simpa using v.map_coeff_mul_mul_pow_le_of_le (r := r) (s₁ := 1) (s₂ := 1) (S := 1)
      (fun i ↦ by simpa using le_gaussValuation v r p i)
      (fun j ↦ by simpa using le_gaussValuation v r q j) k
  rcases eq_or_ne (p.gaussValuation v r) 0 with hp | hp; · simp [hp]
  rcases eq_or_ne (q.gaussValuation v r) 0 with hq | hq; · simp [hq]
  obtain ⟨i₀, hi₀, hlt_p⟩ := exists_min_eq_gaussValuation v r p
  obtain ⟨j₀, hj₀, hlt_q⟩ := exists_min_eq_gaussValuation v r q
  have hterm (x : ℕ × ℕ) : v (p.coeff x.1 * q.coeff x.2) * r ^ (x.1 + x.2) =
      (v (p.coeff x.1) * r ^ x.1) * (v (q.coeff x.2) * r ^ x.2) := by
    rw [map_mul, pow_add, mul_mul_mul_comm]
  have hlead : v (p.coeff i₀ * q.coeff j₀) * r ^ (i₀ + j₀) =
      p.gaussValuation v r * q.gaussValuation v r := by
    rw [hterm (i₀, j₀), hi₀, hj₀]
  have hcoeff : v ((p * q).coeff (i₀ + j₀)) = v (p.coeff i₀ * q.coeff j₀) := by
    rw [coeff_mul]
    refine v.map_sum_eq_of_lt (j := (i₀, j₀)) (Finset.mem_antidiagonal.mpr rfl) fun x hx ↦ ?_
    rw [Finset.mem_sdiff, Finset.mem_antidiagonal, Finset.mem_singleton] at hx
    refine lt_of_mul_lt_mul_right' (a := r ^ (i₀ + j₀)) ?_
    rw [hlead, ← hx.1, hterm x]
    rcases lt_or_ge x.1 i₀ with h1 | h1
    · exact (mul_le_mul_right (le_gaussValuation v r q x.2) _).trans_lt
        (mul_lt_mul_of_pos_right (hlt_p x.1 h1) (pos_iff_ne_zero.mpr hq))
    · have h2 : x.2 < j₀ := by
        have hne : x ≠ (i₀, j₀) := hx.2
        have hne' : x.1 ≠ i₀ ∨ x.2 ≠ j₀ := by contrapose! hne; exact Prod.ext hne.1 hne.2
        omega
      exact (mul_le_mul_left (le_gaussValuation v r p x.1) _).trans_lt
        (mul_lt_mul_of_pos_left (hlt_q x.2 h2) (pos_iff_ne_zero.mpr hp))
  calc p.gaussValuation v r * q.gaussValuation v r
      = v ((p * q).coeff (i₀ + j₀)) * r ^ (i₀ + j₀) := by rw [hcoeff, hlead]
    _ ≤ (p * q).gaussValuation v r := le_gaussValuation v r (p * q) (i₀ + j₀)

end Ring

end Polynomial

namespace Valuation

open Polynomial

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- The Gauss valuation on `R[X]` at radius `r`, bundled as a `Valuation R[X] Γ₀`. -/
def gauss (v : Valuation R Γ₀) (r : Γ₀) : Valuation R[X] Γ₀ where
  toFun p := p.gaussValuation v r
  map_zero' := gaussValuation_zero v r
  map_one' := gaussValuation_one v r
  map_mul' := gaussValuation_mul v r
  map_add_le_max' := gaussValuation_add_le v r

/-- Applying `v.gauss r` to a polynomial `p` yields `p.gaussValuation v r`. -/
@[simp]
theorem gauss_apply (v : Valuation R Γ₀) (r : Γ₀) (p : R[X]) :
    v.gauss r p = p.gaussValuation v r := by
  rfl

/-- Restricting `v.gauss r` to constant polynomials recovers `v`. -/
@[simp]
theorem gauss_comap_C (v : Valuation R Γ₀) (r : Γ₀) :
    (v.gauss r).comap Polynomial.C = v := by
  ext a
  simp

/-- At radius `0`, `v.gauss 0` is the pullback of `v` along `Polynomial.constantCoeff`. -/
@[simp]
theorem gauss_zero (v : Valuation R Γ₀) :
    v.gauss 0 = v.comap Polynomial.constantCoeff := by
  ext p
  simp

/-- Maximality of the Gauss valuation: any valuation `w` on `R[X]` extending `v` with `w X ≤ r`
is bounded pointwise by `v.gauss r`. -/
theorem le_gauss_of_comap_C_eq {v : Valuation R Γ₀} {r : Γ₀} {w : Valuation R[X] Γ₀}
    (hwC : w.comap Polynomial.C = v) (hwX : w Polynomial.X ≤ r) (p : R[X]) :
    w p ≤ v.gauss r p := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [gauss_apply]
  refine w.map_sum_le fun i _ ↦ ?_
  rw [map_mul, map_pow, ← Valuation.comap_apply Polynomial.C w, hwC]
  exact (mul_le_mul_right (pow_le_pow_left' hwX i) _).trans (le_gaussValuation v r p i)

end Valuation

namespace Polynomial

section RingNeg

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) (r : Γ₀)

/-- Negation preserves the Gauss valuation. -/
@[simp]
theorem gaussValuation_neg (p : R[X]) : (-p).gaussValuation v r = p.gaussValuation v r :=
  (v.gauss r).map_neg p

end RingNeg

section CommRing

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- For a split polynomial `p`, the Gauss valuation at radius `r` is the valuation of the leading
coefficient times the product of `max r (v α)` over all roots `α` of `p`. -/
theorem gaussValuation_eq_mul_prod_roots [IsDomain R] (v : Valuation R Γ₀) (p : R[X])
    (hp : p.Splits) (r : Γ₀) :
    p.gaussValuation v r = v p.leadingCoeff * (p.roots.map fun α ↦ max r (v α)).prod := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [gaussValuation_mul, gaussValuation_C, ← Valuation.gauss_apply, map_multiset_prod,
    Multiset.map_map]
  simp

/-- If a split polynomial `p` has no root of valuation `v x`, then `v (p.eval x)` equals the Gauss
valuation `p.gaussValuation v (v x)`. -/
theorem valuation_eval_eq_gaussValuation_of_forall_roots_ne [IsDomain R] (v : Valuation R Γ₀)
    (p : R[X]) (hp : p.Splits) {x : R} (hroots : ∀ α ∈ p.roots, v α ≠ v x) :
    v (p.eval x) = p.gaussValuation v (v x) := by
  have hmap : (p.roots.map fun α ↦ v (x - α)) = p.roots.map fun α ↦ max (v x) (v α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      rcases lt_or_gt_of_ne (hroots α hα) with hlt | hgt
      · rw [v.map_sub_eq_of_lt_left hlt, max_eq_left hlt.le]
      · rw [v.map_sub_eq_of_lt_right hgt, max_eq_right hgt.le]
  rw [hp.eval_eq_prod_roots x, map_mul, map_multiset_prod, Multiset.map_map,
    gaussValuation_eq_mul_prod_roots v p hp (v x), Function.comp_def, hmap]

end CommRing

end Polynomial
