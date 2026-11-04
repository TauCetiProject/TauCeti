/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.PowerSeries.Weierstrass.DivMod
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Examples of Weierstrass theory over Banach rings

These examples test units, Weierstrass division and Weierstrass preparation of restricted power
series in one variable over ultrametric Banach rings whose norm need not be multiplicative, and
at radii that are not norms of scalars.

The coefficient ring with nilpotents is the ring of dual numbers `K[ε]`, `ε ^ 2 = 0`, with the
maximum norm `‖a + b ε‖ = max ‖a‖ ‖b‖` (`TauCeti.Examples.MaxDualNumber`). Mathlib's
`DualNumber K` carries the `ℓ¹` norm `‖a‖ + ‖b‖` instead, which is not ultrametric, so the
maximum norm lives on a type synonym. Over a complete ultrametric normed ring `K` with `‖1‖ = 1`
it is a complete ultrametric normed ring with `‖1‖ = 1` and `‖ε‖ = 1`, and its norm is not
multiplicative since `ε * ε = 0`.

* `1 + ε X` is a unit of the restricted series at every radius, with inverse `1 - ε X`. At radius
  one its coefficient `ε` has the same norm as its constant coefficient, so it is a unit that is
  not distinguished of degree zero: `TauCeti.PowerSeries.isDistinguished_zero_of_isUnit`, and with
  it the unit criterion for multiplicative coefficient norms, fails without that hypothesis.
* `X ^ 2 - a` is multiplicatively distinguished of degree two at every radius `c` with
  `‖a‖ ≤ c ^ 2`, also when the constant coefficient ties with the leading one. Division of `X ^ 4`
  by it has quotient `X ^ 2 + a` and remainder `a ^ 2`, and `X ^ 2 - a` is its own Weierstrass
  polynomial. Over the dual numbers, at radius one, the remainder of `X ^ 4` on division by
  `X ^ 2 - ε` is zero, with quotient `X ^ 2 + ε`.
* If instead `a` is a multiplicative unit with `c ^ 2 < ‖a‖`, then `X ^ 2 - a` is distinguished
  of degree zero at `c`, every Weierstrass remainder vanishes, and `X ^ 2 - a` is a unit.
* `X - 1` is distinguished of degree one at radius one and is its own Weierstrass polynomial,
  although its lower coefficient is not smaller than its leading one.
* Over `ℚ_p`, the polynomial `X ^ 2 - p⁻¹` is a unit at radius one. At radius `√p`, which is not
  the norm of an element of `ℚ_p`, it is distinguished of degree two and not a unit, and division
  of `X ^ 4` by it has quotient `X ^ 2 + p⁻¹` and remainder `p⁻²`.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Lemma 1.21 and Remark 1.22 for units, and Definition 1.24,
  Proposition 1.27 and Corollary 1.28 for distinguished series, division and preparation.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2.
-/

public section

open Polynomial TauCeti.PowerSeries

namespace TauCeti.Examples

/-- The dual numbers `K[ε]` with the maximum norm `‖a + b ε‖ = max ‖a‖ ‖b‖` of the two
coefficients, in place of the `ℓ¹` norm Mathlib puts on `DualNumber K`. -/
@[expose] def MaxDualNumber (K : Type*) : Type _ := DualNumber K

namespace MaxDualNumber

variable {K : Type*} [NormedCommRing K] [IsUltrametricDist K]

/-- The maximum norm of the coefficients of dual numbers is submultiplicative, because the norm of
`K` is ultrametric: `‖a * d + b * c‖ ≤ max ‖a * d‖ ‖b * c‖`. -/
private theorem max_norm_mul_le (a b : DualNumber K) :
    max ‖(a * b).fst‖ ‖(a * b).snd‖ ≤ max ‖a.fst‖ ‖a.snd‖ * max ‖b.fst‖ ‖b.snd‖ := by
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul,
    mul_max_of_nonneg _ _ ((norm_nonneg _).trans (le_max_left _ _)),
    max_mul_of_nonneg _ _ (norm_nonneg _), max_mul_of_nonneg _ _ (norm_nonneg _)]
  exact max_le (le_max_of_le_left (le_max_of_le_left (norm_mul_le _ _)))
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (le_max_of_le_right (le_max_of_le_left (norm_mul_le _ _)))
      (le_max_of_le_left (le_max_of_le_right (norm_mul_le _ _)))))

/-- The ring structure of the dual numbers with the maximum norm of the coefficient pair, which
is the norm of `K × K`. -/
noncomputable instance : NormedCommRing (MaxDualNumber K) where
  __ : NormedAddCommGroup (K × K) := inferInstance
  __ : CommRing (DualNumber K) := inferInstance
  -- The norm of `x` is by definition the maximum norm of its coefficients.
  norm_mul_le a b := by exact max_norm_mul_le a b

/-- The identification of `MaxDualNumber K` with Mathlib's dual numbers, as rings. -/
def ofDualNumber : DualNumber K ≃+* MaxDualNumber K := RingEquiv.refl _

/-- The norm of a dual number is the maximum of the norms of its two coefficients. -/
theorem norm_ofDualNumber (x : DualNumber K) :
    ‖ofDualNumber x‖ = max ‖x.fst‖ ‖x.snd‖ := (rfl)

/-- The square-zero generator `ε` of `MaxDualNumber K`. -/
def eps : MaxDualNumber K := ofDualNumber DualNumber.eps

/-- The generator `ε` squares to zero, so `MaxDualNumber K` has nilpotents. -/
theorem eps_mul_eps : (eps * eps : MaxDualNumber K) = 0 := by
  rw [eps, ← map_mul, DualNumber.eps_mul_eps, map_zero]

instance : IsUltrametricDist (MaxDualNumber K) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ ?_
  obtain ⟨a, rfl⟩ := ofDualNumber.surjective x
  obtain ⟨b, rfl⟩ := ofDualNumber.surjective y
  rw [← map_add, norm_ofDualNumber, norm_ofDualNumber, norm_ofDualNumber, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.snd_add, max_max_max_comm]
  exact max_le_max (IsUltrametricDist.norm_add_le_max _ _) (IsUltrametricDist.norm_add_le_max _ _)

instance [CompleteSpace K] : CompleteSpace (MaxDualNumber K) :=
  inferInstanceAs (CompleteSpace (K × K))

variable [NormOneClass K]

instance : NormOneClass (MaxDualNumber K) :=
  ⟨by rw [← map_one ofDualNumber, norm_ofDualNumber]; simp⟩

/-- The generator `ε` has norm one, the norm of its only nonzero coefficient. -/
@[simp]
theorem norm_eps : ‖(eps : MaxDualNumber K)‖ = 1 := by
  rw [eps, norm_ofDualNumber, DualNumber.fst_eps, DualNumber.snd_eps]
  simp

/-- The maximum norm on the dual numbers is not multiplicative: `‖ε * ε‖ = 0` while `‖ε‖ = 1`. -/
theorem not_normMulClass : ¬NormMulClass (MaxDualNumber K) := fun _ ↦ by
  simpa [eps_mul_eps] using norm_mul (eps : MaxDualNumber K) eps

end MaxDualNumber

open MaxDualNumber

section Units

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ}

/-- If `ε * ε = 0`, then `1 + ε X` and `1 - ε X` are inverse to each other among the series
restricted at any radius, with no condition on the norm of `ε`. -/
private theorem one_add_mul_one_sub_eq_one {ε : R} (hε : ε * ε = 0) :
    polynomialToRestricted c (1 + C ε * X) * polynomialToRestricted c (1 - C ε * X) = 1 := by
  have h : C ε * C ε = (0 : R[X]) := by rw [← C_mul, hε, C_0]
  rw [← map_mul, ← map_one (polynomialToRestricted c)]
  congr 1
  linear_combination (-X ^ 2 : R[X]) * h

variable {K : Type*} [NormedCommRing K] [IsUltrametricDist K] [NormOneClass K]

-- Over the dual numbers with the maximum norm, `1 + ε X` is a unit at radius one, but it is not
-- distinguished of degree zero: its coefficient `ε` has norm one, like its constant coefficient.
example : IsUnit (polynomialToRestricted 1 (1 + C eps * X : (MaxDualNumber K)[X])) ∧
    ¬IsDistinguished 1 0 ((1 + C eps * X : (MaxDualNumber K)[X]) : PowerSeries (MaxDualNumber K)) :=
  ⟨IsUnit.of_mul_eq_one _ (one_add_mul_one_sub_eq_one eps_mul_eps), fun hd ↦ by
    have h := hd.norm_coeff_mul_pow_lt 1 one_pos
    rw [← hd.norm_coeff_mul_pow_eq] at h
    simp at h⟩

end Units

section Weierstrass

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] {c : ℝ}

omit [IsUltrametricDist R] in
private theorem isMonicOfDegree_X_sq_sub_C (a : R) : (X ^ 2 - C a : R[X]).IsMonicOfDegree 2 :=
  have := NormOneClass.nontrivial (G := R)
  (isMonicOfDegree_X_pow (R := R) 2).sub (by rw [natDegree_C]; norm_num)

/-- `X ^ 2 - a` is multiplicatively distinguished of degree two at every radius `c > 0` with
`‖a‖ ≤ c ^ 2`, including when the constant coefficient attains the Gauss norm. -/
private theorem isMulDistinguished_X_sq_sub_C (hc : 0 < c) {a : R} (ha : ‖a‖ ≤ c ^ 2) :
    IsMulDistinguished c 2 (polynomialToRestricted c (X ^ 2 - C a) : PowerSeries R) := by
  rw [coe_polynomialToRestricted]
  refine ⟨isDistinguished_of_isMonicOfDegree hc (isMonicOfDegree_X_sq_sub_C a) fun k hk ↦ ?_, ?_⟩
  · interval_cases k
    · simpa [coeff_X_pow, coeff_C] using ha
    · simp only [coeff_sub, coeff_X_pow, coeff_C]
      simp [sq_nonneg]
  · rw [(isMonicOfDegree_X_sq_sub_C a).coeff_coe_self]
    exact isNormMulUnit_one

/-- If `a` is a multiplicative unit and `c ^ 2 < ‖a‖`, then `X ^ 2 - a` is multiplicatively
distinguished of degree zero at `c`: its constant coefficient strictly dominates. -/
private theorem isMulDistinguished_zero_X_sq_sub_C {a : R} (ha : IsNormMulUnit a)
    (hca : c ^ 2 < ‖a‖) :
    IsMulDistinguished c 0 (polynomialToRestricted c (X ^ 2 - C a) : PowerSeries R) := by
  rw [coe_polynomialToRestricted]
  have hcoeff (m : ℕ) : ‖PowerSeries.coeff m ((X ^ 2 - C a : R[X]) : PowerSeries R)‖ * c ^ m =
      if m = 2 then c ^ 2 else if m = 0 then ‖a‖ else 0 := by
    rw [Polynomial.coeff_coe, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs <;> simp_all
  have hn : ((X ^ 2 - C a : R[X]) : PowerSeries R).gaussNorm norm c = ‖a‖ := by
    rw [gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_, hcoeff]
    · simp
    · rw [hcoeff, hcoeff]
      split_ifs <;> simp_all [hca.le, (sq_nonneg c).trans hca.le]
  refine ⟨⟨by rw [hn, hcoeff]; simp, fun m hm ↦ ?_⟩, ?_⟩
  · rw [hn, hcoeff]
    split_ifs <;> simp_all [(sq_nonneg c).trans_lt hca]
  · rw [Polynomial.coeff_coe, coeff_sub, coeff_X_pow, coeff_C]
    simp only [OfNat.zero_ne_ofNat, ↓reduceIte, zero_sub]
    exact (isNormMulUnit_iff _).mpr
      ⟨ha.isUnit.neg, fun x ↦ by rw [neg_mul, norm_neg, norm_neg, ha.norm_mul]⟩

/-- Weierstrass division of `X ^ 4` by `X ^ 2 - a`, at a radius `c > 0` with `‖a‖ ≤ c ^ 2`, has
quotient `X ^ 2 + a` and remainder `a ^ 2`. -/
private theorem weierstrassDiv_X_pow_four [CompleteSpace R] (hc : 0 < c) {a : R}
    (ha : ‖a‖ ≤ c ^ 2) :
    (isMulDistinguished_X_sq_sub_C hc ha).weierstrassDiv hc (polynomialToRestricted c (X ^ 4)) =
        polynomialToRestricted c (X ^ 2 + C a) ∧
      (isMulDistinguished_X_sq_sub_C hc ha).weierstrassMod hc (polynomialToRestricted c (X ^ 4)) =
        C (a ^ 2) := by
  refine ((isMulDistinguished_X_sq_sub_C hc ha).weierstrassDiv_eq_and_weierstrassMod_eq_iff hc
    (degree_C_le.trans_lt (by norm_num))).mpr ?_
  rw [← map_mul, ← map_add, C_pow]
  congr 1
  ring

-- `X ^ 2 - a` is its own Weierstrass polynomial: in a factorisation `e * ω` of it, with `e` a
-- unit of the restricted series and `ω` monic of degree two, `e = 1` and `ω = X ^ 2 - a`.
example (hc : 0 < c) {a : R} (ha : ‖a‖ ≤ c ^ 2) {e : PowerSeries.IsRestricted.subring (R := R) c}
    {ω : R[X]} (he : IsUnit e) (hω : ω.IsMonicOfDegree 2)
    (h : (e : PowerSeries R) * ω = (X ^ 2 - C a : R[X])) : e = 1 ∧ ω = X ^ 2 - C a :=
  (isMulDistinguished_X_sq_sub_C hc ha).eq_and_eq_of_mul_eq_of_mul_eq hc he isUnit_one hω
    (isMonicOfDegree_X_sq_sub_C a) (by simpa using h) (by simp)

-- Where the constant term of `X ^ 2 - a` strictly dominates, division by it is in degree zero:
-- every remainder vanishes, so `X ^ 2 - a` is a unit of the restricted series.
example [CompleteSpace R] (hc : 0 < c) {a : R} (ha : IsNormMulUnit a) (hca : c ^ 2 < ‖a‖) :
    IsUnit (polynomialToRestricted c (X ^ 2 - C a)) := by
  have hg := isMulDistinguished_zero_X_sq_sub_C ha hca
  obtain ⟨q, hq⟩ := (hg.weierstrassMod_eq_zero_iff_dvd hc).mp (hg.weierstrassMod_eq_zero hc 1)
  exact IsUnit.of_mul_eq_one q hq.symm

-- `X - 1` is its own Weierstrass polynomial at radius one, although its constant coefficient has
-- the same norm as its leading coefficient.
example {e : PowerSeries.IsRestricted.subring (R := R) 1} {ω : R[X]} (he : IsUnit e)
    (hω : ω.IsMonicOfDegree 1) (h : (e : PowerSeries R) * ω = (X - 1 : R[X])) :
    e = 1 ∧ ω = X - 1 := by
  have := NormOneClass.nontrivial (G := R)
  have hg := isMulDistinguished_X_sub_C (R := R) one_pos (b := 1) (by simp)
  rw [map_one] at hg
  exact hg.eq_and_eq_of_mul_eq_of_mul_eq one_pos he isUnit_one hω
    (by simpa using isMonicOfDegree_X_sub_one (1 : R)) (by simpa using h) (by simp)

variable {K : Type*} [NormedCommRing K] [IsUltrametricDist K] [NormOneClass K] [CompleteSpace K]

-- Over the dual numbers with the maximum norm, at radius one, `X ^ 2 - ε` is distinguished of
-- degree two although `‖ε‖ = 1`. Division of `X ^ 4` by it has quotient `X ^ 2 + ε` and
-- remainder zero, since `ε ^ 2 = 0`.
example :
    (isMulDistinguished_X_sq_sub_C one_pos (a := (eps : MaxDualNumber K))
        (by simp)).weierstrassDiv one_pos (polynomialToRestricted 1 (X ^ 4)) =
        polynomialToRestricted 1 (X ^ 2 + C eps) ∧
      (isMulDistinguished_X_sq_sub_C one_pos (a := (eps : MaxDualNumber K))
        (by simp)).weierstrassMod one_pos (polynomialToRestricted 1 (X ^ 4)) = 0 := by
  obtain ⟨hq, hr⟩ := weierstrassDiv_X_pow_four one_pos (a := (eps : MaxDualNumber K)) (by simp)
  exact ⟨hq, by rw [hr, sq, eps_mul_eps, C_0]⟩

end Weierstrass

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

private theorem sqrt_p_pos : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.out.pos)

private theorem norm_inv_p : ‖(p : ℚ_[p])⁻¹‖ = √(p : ℝ) ^ 2 := by
  rw [norm_inv, Padic.norm_p, inv_inv, Real.sq_sqrt (Nat.cast_nonneg _)]

-- At radius one, the constant coefficient of `X ^ 2 - p⁻¹` dominates, so it is a unit of `ℚ_p⟨X⟩`.
example : IsUnit (polynomialToRestricted 1 (X ^ 2 - C (p : ℚ_[p])⁻¹)) := by
  have hg := isMulDistinguished_zero_X_sq_sub_C (c := 1) (a := (p : ℚ_[p])⁻¹)
    ((isNormMulUnit_iff_isUnit _).mpr (isUnit_iff_ne_zero.mpr (by simp [hp.out.ne_zero])))
    (by rw [norm_inv_p, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; exact_mod_cast hp.out.one_lt)
  obtain ⟨q, hq⟩ := (hg.weierstrassMod_eq_zero_iff_dvd one_pos).mp
    (hg.weierstrassMod_eq_zero one_pos 1)
  exact IsUnit.of_mul_eq_one q hq.symm

-- At the radius `√p`, which is not the norm of an element of `ℚ_p` (see
-- `TauCeti/Examples/RingTheory/PowerSeries/Restricted.lean`), `X ^ 2 - p⁻¹` is distinguished of
-- degree two, so it is not a unit: the remainder of `1` on division by it is `1`.
example : ¬IsUnit (polynomialToRestricted (√(p : ℝ)) (X ^ 2 - C (p : ℚ_[p])⁻¹)) := fun hu ↦ by
  have hg := isMulDistinguished_X_sq_sub_C (sqrt_p_pos p) (norm_inv_p p).le
  have h := (hg.weierstrassMod_eq_zero_iff_dvd (sqrt_p_pos p)).mpr (hu.dvd (a := 1))
  rw [← map_one (polynomialToRestricted _), hg.weierstrassMod_polynomialToRestricted_of_degree_lt
    (sqrt_p_pos p) (by rw [degree_one]; norm_num)] at h
  exact one_ne_zero h

-- At the radius `√p`, division of `X ^ 4` by `X ^ 2 - p⁻¹` has quotient `X ^ 2 + p⁻¹` and
-- remainder `p⁻²`.
example :
    (isMulDistinguished_X_sq_sub_C (sqrt_p_pos p) (norm_inv_p p).le).weierstrassDiv (sqrt_p_pos p)
        (polynomialToRestricted _ (X ^ 4)) = polynomialToRestricted _ (X ^ 2 + C (p : ℚ_[p])⁻¹) ∧
      (isMulDistinguished_X_sq_sub_C (sqrt_p_pos p) (norm_inv_p p).le).weierstrassMod
        (sqrt_p_pos p) (polynomialToRestricted _ (X ^ 4)) = C ((p : ℚ_[p]) ^ 2)⁻¹ := by
  rw [← inv_pow]
  exact weierstrassDiv_X_pow_four (sqrt_p_pos p) (norm_inv_p p).le

end Padic

end TauCeti.Examples
