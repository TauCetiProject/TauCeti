/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GoodPrimes
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.PadicValRat

/-!
# Good reduction and Legendre parameters

At an odd prime of good reduction of an elliptic curve in scaled Legendre form, both the
parameter and its complement are p-adic units. Indeed, when either factor fails to be a
unit, the Legendre `j`-invariant has a pole. Conversely, unit parameters give an integral
unscaled Legendre equation with unit discriminant and hence good reduction.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, Lemma 6.2(i) and the proof of Lemma 6.4.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and VII.5.
-/

public section

namespace TauCeti

open WeierstrassCurve

variable (p : Nat.Primes) {l : ℚ}

/-- Write `s = vₚ(l (1 - l))`. If `s ≠ 0` at an odd prime, the valuation of the Legendre
`j`-invariant is `s` when `s < 0` and `-2 * s` when `s > 0`. -/
theorem padicValRat_legendre_j_of_nonunit (hp : (p : ℕ) ≠ 2)
    (hs : padicValRat p (l * (1 - l)) ≠ 0) :
    let hE : (legendre l).IsElliptic := (isElliptic_legendre_iff_ne_zero l (by norm_num)).2
      ⟨fun h ↦ hs (by simp [h]), fun h ↦ hs (by simp [h])⟩
    padicValRat p (legendre l).j =
      min (padicValRat p (l * (1 - l))) (-2 * padicValRat p (l * (1 - l))) := by
  intro hE
  set t := l * (1 - l)
  have ht : t ≠ 0 := fun h ↦ hs (by simp only [h, padicValRat.zero])
  have ht' : 1 - t ≠ 0 := fun h ↦ hs (by simp only [← sub_eq_zero.mp h, padicValRat.one])
  have h256 : padicValRat p 256 = 0 := by
    have hdvd : ¬ (p : ℕ) ∣ 256 := fun h ↦
      hp (Nat.prime_eq_prime_of_dvd_pow p.prop Nat.prime_two (m := 8) (by
        norm_num
        exact h))
    calc
      padicValRat p 256 = padicValRat p ((256 : ℕ) : ℚ) := by norm_num
      _ = 0 := by
        rw [padicValRat.of_nat]
        simp [multiplicity_eq_zero_of_not_dvd hdvd]
  have hj : (legendre l).j = 256 * (1 - t) ^ 3 / t ^ 2 := by
    rw [legendre_j]
    congr 1 <;> dsimp [t] <;> ring
  -- The two terms of the numerator have distinct valuations before cubing.
  have hsub : padicValRat p (1 - t) = min 0 (padicValRat p t) := by
    rw [sub_eq_add_neg] at ht' ⊢
    rw [padicValRat.add_eq_min ht' one_ne_zero (neg_ne_zero.mpr ht), padicValRat.one,
      padicValRat.neg]
    simpa only [padicValRat.one, padicValRat.neg] using hs.symm
  have hnum : padicValRat p (256 * (1 - t) ^ 3) = 3 * min 0 (padicValRat p t) := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero _ ht'), h256, zero_add,
      padicValRat.pow, hsub]
    norm_num
  have hden : padicValRat p (t ^ 2) = 2 * padicValRat p t := by
    rw [padicValRat.pow]
    norm_num
  rw [hj, padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ ht')) (pow_ne_zero _ ht),
    hnum, hden]
  omega

/-- If the Legendre `j`-invariant is integral at an odd prime, both parameter factors have
valuation zero. -/
theorem legendre_units_of_padicValRat_j_nonneg [(legendre l).IsElliptic]
    (hp : (p : ℕ) ≠ 2) (hj : 0 ≤ padicValRat p (legendre l).j) :
    padicValRat p l = 0 ∧ padicValRat p (1 - l) = 0 := by
  have ht : padicValRat p (l * (1 - l)) = 0 := by
    by_contra h
    rw [padicValRat_legendre_j_of_nonunit p hp h] at hj
    omega
  exact padicValRat.eq_zero_and_eq_zero_of_add_eq_one_of_mul_eq_zero (by ring) ht

/-- With both parameter factors units at an odd prime, the Legendre equation lifts to an
elliptic Weierstrass equation over the p-adic integers. -/
theorem exists_isElliptic_legendre_padicInt (hp : (p : ℕ) ≠ 2) (h₀ : l ≠ 0) (h₁ : l ≠ 1)
    (hl : padicValRat p l = 0) (hsub : padicValRat p (1 - l) = 0) :
    ∃ lp : ℤ_[p], (lp : ℚ_[p]) = (l : ℚ_[p]) ∧ (legendre lp).IsElliptic := by
  have hn := Padic.norm_ratCast_eq_one_of_padicValRat_eq_zero h₀ hl
  let lp : ℤ_[p] := Padic.lift (l : ℚ_[p]) hn.le
  have hcoe : (lp : ℚ_[p]) = (l : ℚ_[p]) := PadicInt.coe_lift hn.le
  have hsubcoe : ((1 - lp : ℤ_[p]) : ℚ_[p]) = ((1 - l : ℚ) : ℚ_[p]) := by
    simp [hcoe]
  have isUnit_of_ratCast {z : ℤ_[p]} {q : ℚ} (h : (z : ℚ_[p]) = (q : ℚ_[p]))
      (hq : q ≠ 0) (hv : padicValRat p q = 0) : IsUnit z := by
    rw [PadicInt.isUnit_iff, ← PadicInt.norm_coe, h]
    exact Padic.norm_ratCast_eq_one_of_padicValRat_eq_zero hq hv
  have hu := isUnit_of_ratCast hcoe h₀ hl
  have husub := isUnit_of_ratCast hsubcoe (sub_ne_zero.mpr h₁.symm) hsub
  exact ⟨lp, hcoe, (isElliptic_legendre_iff lp).mpr
    ((PadicInt.isUnit_two hp).mul hu |>.mul (by simpa only [neg_sub] using husub.neg))⟩

end TauCeti

namespace WeierstrassCurve

open TauCeti

/-- At an odd prime of good reduction, any scaled Legendre equation in the variable-change
orbit of a rational curve has parameter and complement of valuation zero. -/
theorem legendre_units_of_good_reduction (E : WeierstrassCurve ℚ) {p : Nat.Primes}
    (hp : (p : ℕ) ≠ 2) {d l : ℚ} {C : VariableChange ℚ}
    (hC : C • E = scaledLegendre d l) (hgood : E.HasGoodReductionAt p) :
    padicValRat p l = 0 ∧ padicValRat p (1 - l) = 0 := by
  have := hgood.isElliptic
  have : (scaledLegendre d l).IsElliptic := hC ▸ inferInstanceAs (C • E).IsElliptic
  have := isElliptic_legendre_of_scaledLegendre d l ‹(scaledLegendre d l).IsElliptic›
  have hjC : (scaledLegendre d l).j = E.j := by
    simpa only [hC] using E.variableChange_j C
  apply legendre_units_of_padicValRat_j_nonneg p hp
  rw [← scaledLegendre_j_eq_legendre_j d l, hjC]
  exact hgood.padicValRat_j_nonneg

end WeierstrassCurve

namespace TauCeti

open WeierstrassCurve

/-- For a parameter `l` different from `0` and `1`, the unscaled Legendre curve has good
reduction at an odd prime exactly when `l` and `1 - l` both have valuation zero. -/
theorem hasGoodReductionAt_legendre_iff {p : Nat.Primes} {l : ℚ}
    (hp : (p : ℕ) ≠ 2) (h₀ : l ≠ 0) (h₁ : l ≠ 1) :
    (legendre l).HasGoodReductionAt p ↔ padicValRat p l = 0 ∧ padicValRat p (1 - l) = 0 := by
  refine ⟨(legendre l).legendre_units_of_good_reduction hp (C := 1) (d := 1) (by
    rw [one_smul, scaledLegendre_one]), fun ⟨hl, hsub⟩ ↦ ?_⟩
  obtain ⟨lp, hcoe, hE⟩ := exists_isElliptic_legendre_padicInt p hp h₀ h₁ hl hsub
  have hbase : (legendre lp).baseChange ℚ_[p] = (legendre l).baseChange ℚ_[p] := by
    simp only [baseChange, map_legendre, PadicInt.algebraMap_apply, hcoe, eq_ratCast]
  have hg : ((legendre lp).baseChange ℚ_[p]).HasGoodReduction ℤ_[p] :=
    (hasGoodReduction_baseChange_iff_isUnit_algebraMap_Δ ℤ_[p] (legendre lp)).mpr (by
      simpa using hE.isUnit)
  rw [hasGoodReductionAt_iff, ← hbase]
  exact hg.hasGoodReduction_minimal ℤ_[p]

end TauCeti
