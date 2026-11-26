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

/-!
# Good reduction and Legendre parameters

At an odd prime of good reduction of an elliptic curve in scaled Legendre form, both the
parameter and its complement are p-adic units. Indeed, when either factor fails to be a
unit, the Legendre `j`-invariant has a pole. Conversely, unit parameters give an integral
unscaled Legendre equation with unit discriminant. Its reduction remains in Legendre form by
`map_legendre`.

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
`j`-invariant is `s` when `s < 0` and `-2 * s` when `s > 0`. In the first case the valuations
of `l` and `1 - l` are equal and negative. In the second case one is positive and the other
is zero. -/
theorem padicValRat_legendre_j_of_nonunit [(legendre l).IsElliptic] (hp : (p : ℕ) ≠ 2)
    (hs : padicValRat p (l * (1 - l)) ≠ 0) :
    padicValRat p (legendre l).j =
      min (padicValRat p (l * (1 - l))) (-2 * padicValRat p (l * (1 - l))) := by
  set t := l * (1 - l)
  have ht : t ≠ 0 := fun h ↦ hs (by simp only [h, padicValRat.zero])
  have ht' : 1 - t ≠ 0 := by
    dsimp [t]
    nlinarith [sq_nonneg (l - 1 / 2)]
  have htwo : padicValRat p 2 = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    exact_mod_cast multiplicity_eq_zero_of_not_dvd
      (fun h ↦ hp ((Nat.dvd_prime_two_le Nat.prime_two p.prop.two_le).mp h))
  have h256 : padicValRat p 256 = 0 := by
    rw [show (256 : ℚ) = 2 ^ 8 by norm_num, padicValRat.pow, htwo, mul_zero]
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
theorem padicValRat_legendre_eq_zero_of_j_nonneg [(legendre l).IsElliptic]
    (hp : (p : ℕ) ≠ 2) (hj : 0 ≤ padicValRat p (legendre l).j) :
    padicValRat p l = 0 ∧ padicValRat p (1 - l) = 0 := by
  have ht : padicValRat p (l * (1 - l)) = 0 := by
    by_contra h
    rw [padicValRat_legendre_j_of_nonunit p hp h] at hj
    omega
  obtain ⟨h₀, h₁⟩ := (isElliptic_legendre_iff_ne_zero l two_ne_zero).mp ‹_›
  have h₁' : 1 - l ≠ 0 := sub_ne_zero.mpr h₁.symm
  rw [padicValRat.mul h₀ h₁'] at ht
  by_cases he : padicValRat p l = padicValRat p (1 - l)
  · omega
  · have hadd : l + (1 - l) = 1 := by ring
    have hmin := padicValRat.add_eq_min (p := (p : ℕ)) (by rw [hadd]; exact one_ne_zero) h₀ h₁' he
    rw [hadd, padicValRat.one] at hmin
    omega

/-- With both parameter factors units at an odd prime, the Legendre equation lifts to an
elliptic Weierstrass equation over the p-adic integers. -/
theorem exists_isElliptic_legendre_padicInt (hp : (p : ℕ) ≠ 2) (h₀ : l ≠ 0) (h₁ : l ≠ 1)
    (hl : padicValRat p l = 0) (hsub : padicValRat p (1 - l) = 0) :
    ∃ lp : ℤ_[p], (lp : ℚ_[p]) = (l : ℚ_[p]) ∧ (legendre lp).IsElliptic := by
  have norm_eq_one (q : ℚ) (hq : q ≠ 0) (hv : padicValRat p q = 0) :
      ‖(q : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq), Padic.valuation_ratCast, hv]
    simp
  have hn := norm_eq_one l h₀ hl
  let lp : ℤ_[p] := ⟨(l : ℚ_[p]), hn.le⟩
  have hcoe : (lp : ℚ_[p]) = (l : ℚ_[p]) := rfl
  have hu : IsUnit lp := PadicInt.isUnit_iff.mpr hn
  have husub : IsUnit (1 - lp) := by
    apply PadicInt.isUnit_iff.mpr
    simpa only [← PadicInt.norm_coe, PadicInt.coe_sub, PadicInt.coe_one, hcoe, Rat.cast_sub,
      Rat.cast_one] using norm_eq_one (1 - l) (sub_ne_zero.mpr h₁.symm) hsub
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
  obtain ⟨D, hD⟩ := (E.baseChange ℚ_[p]).exists_smul_eq_minimal ℤ_[p]
  have hmin := hgood.isElliptic ℤ_[p]
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr fun hΔ ↦
    hmin.isUnit.ne_zero (by
      rw [← hD, variableChange_Δ, baseChange, map_Δ, hΔ, map_zero, mul_zero])⟩
  have : (scaledLegendre d l).IsElliptic := hC ▸ inferInstanceAs (C • E).IsElliptic
  have := isElliptic_legendre_of_scaledLegendre d l ‹(scaledLegendre d l).IsElliptic›
  have hjC : (scaledLegendre d l).j = E.j := by
    simpa only [hC] using E.variableChange_j C
  have hjD : ((E.baseChange ℚ_[p]).minimal ℤ_[p]).j = (E.j : ℚ_[p]) := by
    calc
      _ = (E.baseChange ℚ_[p]).j := by
        simpa only [hD] using (E.baseChange ℚ_[p]).variableChange_j D
      _ = _ := by simp only [baseChange, map_j, eq_ratCast]
  obtain ⟨z, hz⟩ := hgood.isInteger_j ℤ_[p]
  rw [hjD, ← hjC, scaledLegendre_j_eq_legendre_j, PadicInt.algebraMap_apply] at hz
  apply padicValRat_legendre_eq_zero_of_j_nonneg p hp
  rw [← Padic.valuation_ratCast, ← hz]
  exact PadicInt.valuation_coe_nonneg

end WeierstrassCurve

namespace TauCeti

open WeierstrassCurve

/-- At an odd prime the unscaled Legendre curve has good reduction exactly when the parameter
and its complement both have valuation zero. The integral Legendre equation itself is minimal
in this case. -/
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
