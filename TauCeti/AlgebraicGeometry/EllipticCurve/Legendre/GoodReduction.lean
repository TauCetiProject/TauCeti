/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GoodPrimes
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
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
theorem padicValRat_legendre_j_of_nonunit [(legendre l).IsElliptic] (hp : (p : ℕ) ≠ 2)
    (hs : padicValRat p (l * (1 - l)) ≠ 0) :
    padicValRat p (legendre l).j =
      min (padicValRat p (l * (1 - l))) (-2 * padicValRat p (l * (1 - l))) := by
  set t := l * (1 - l)
  have ht : t ≠ 0 := fun h ↦ hs (by simp only [h, padicValRat.zero])
  have ht' : 1 - t ≠ 0 := by
    dsimp [t]
    nlinarith [sq_nonneg (l - 1 / 2)]
  have h256 : padicValRat p 256 = 0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcast : (256 : ℚ) = ((2 ^ 8 : ℕ) : ℚ) := by norm_num
    rw [hcast, padicValRat.of_nat, multiplicity_prime_prime_pow 8 hp, Nat.cast_zero]
  have hj : (legendre l).j = 256 * (1 - t) ^ 3 / t ^ 2 := by
    rw [legendre_j]
    congr 1 <;> dsimp [t] <;> ring
  -- The two terms of the numerator have distinct valuations before cubing.
  have hnum : padicValRat p (1 - t) = min 0 (padicValRat p t) := by
    rw [sub_eq_add_neg] at ht' ⊢
    rw [padicValRat.add_eq_min ht' one_ne_zero (neg_ne_zero.mpr ht), padicValRat.one,
      padicValRat.neg]
    simpa only [padicValRat.one, padicValRat.neg] using hs.symm
  rw [hj, padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ ht')) (pow_ne_zero _ ht),
    padicValRat.mul (by norm_num) (pow_ne_zero _ ht'), h256, zero_add, padicValRat.pow,
    padicValRat.pow, hnum]
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
  obtain ⟨h₀, h₁⟩ := (isElliptic_legendre_iff_ne_zero l two_ne_zero).mp ‹_›
  have h₁' : 1 - l ≠ 0 := sub_ne_zero.mpr h₁.symm
  rw [padicValRat.mul h₀ h₁'] at ht
  have hadd : l + (1 - l) = 1 := by ring
  rcases lt_trichotomy (padicValRat p l) 0 with hneg | hzero | hpos
  · have := padicValRat.eq_of_add_eq_one_of_neg hadd hneg
    omega
  · omega
  · have := padicValRat.eq_zero_of_add_eq_one_of_pos hadd hpos
    omega

/-- With both parameter factors units at an odd prime, the Legendre equation lifts to an
elliptic Weierstrass equation over the p-adic integers. -/
theorem exists_isElliptic_legendre_padicInt (hp : (p : ℕ) ≠ 2) (h₀ : l ≠ 0) (h₁ : l ≠ 1)
    (hl : padicValRat p l = 0) (hsub : padicValRat p (1 - l) = 0) :
    ∃ lp : ℤ_[p], (lp : ℚ_[p]) = (l : ℚ_[p]) ∧ (legendre lp).IsElliptic := by
  have hn := Padic.norm_ratCast_eq_one_of_padicValRat_eq_zero h₀ hl
  let lp : ℤ_[p] := ⟨(l : ℚ_[p]), hn.le⟩
  have hcoe : (lp : ℚ_[p]) = (l : ℚ_[p]) := rfl
  have hu : IsUnit lp := PadicInt.isUnit_iff.mpr hn
  have husub : IsUnit (1 - lp) := by
    apply PadicInt.isUnit_iff.mpr
    simpa only [← PadicInt.norm_coe, PadicInt.coe_sub, PadicInt.coe_one, hcoe, Rat.cast_sub,
      Rat.cast_one] using Padic.norm_ratCast_eq_one_of_padicValRat_eq_zero
        (sub_ne_zero.mpr h₁.symm) hsub
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
  rw [hasGoodReductionAt_iff] at hgood
  have hpot : (E.baseChange ℚ_[p]).HasPotentialGoodReduction ℤ_[p] :=
    .intro ℤ_[p] ℚ_[p] ℤ_[p] (by ext; simp) (by rwa [baseChange, Algebra.algebraMap_self, map_id])
  have hlocal := hpot.isElliptic ℤ_[p]
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr fun hΔ ↦
    hlocal.isUnit.ne_zero (by rw [baseChange, map_Δ, hΔ, map_zero])⟩
  have : (scaledLegendre d l).IsElliptic := hC ▸ inferInstanceAs (C • E).IsElliptic
  have := isElliptic_legendre_of_scaledLegendre d l ‹(scaledLegendre d l).IsElliptic›
  have hjC : (scaledLegendre d l).j = E.j := by
    simpa only [hC] using E.variableChange_j C
  obtain ⟨z, hz⟩ := hpot.isInteger_j ℤ_[p]
  simp only [baseChange, map_j, eq_ratCast, PadicInt.algebraMap_apply] at hz
  rw [← hjC, scaledLegendre_j_eq_legendre_j] at hz
  apply legendre_units_of_padicValRat_j_nonneg p hp
  rw [← Padic.valuation_ratCast, ← hz]
  exact PadicInt.valuation_coe_nonneg

end WeierstrassCurve

namespace TauCeti

open WeierstrassCurve

/-- At an odd prime the unscaled Legendre curve has good reduction exactly when the parameter
and its complement both have valuation zero. -/
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
