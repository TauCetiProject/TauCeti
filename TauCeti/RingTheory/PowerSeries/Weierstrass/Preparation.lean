/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division

/-!
# Weierstrass preparation for restricted power series

The power series restricted at a radius `c` form a subring `PowerSeries.IsRestricted.subring c`
of `K⟦X⟧`; over a complete nonarchimedean field and at a positive radius it is the Tate algebra of
the closed disc of radius `c`. This file describes its units and factors a distinguished series
through a monic polynomial.

A restricted series is a unit of that subring exactly when it is distinguished of degree `0`, that
is, when its constant coefficient dominates every other weighted coefficient. Weierstrass
preparation then says that a restricted series `f` distinguished of degree `s` factors as

```text
f = e * ω,    e a unit of the ring of restricted series,    ω monic of degree s,
```

and that the pair `(e, ω)` is unique. Both statements come from Weierstrass division. Dividing `1`
by a series distinguished of degree `0` leaves a remainder that vanishes in every degree, so the
quotient is an inverse. Dividing `X ^ s` by `f` leaves a remainder `r` of degree less than `s`
whose weighted coefficients are bounded by `c ^ s`, so `ω = X ^ s - r` is distinguished of degree
`s`; the quotient is then distinguished of degree `0`, hence a unit, and `f` is its inverse
times `ω`.

The factorization presents the quotient of the ring of restricted series by `f` as the quotient of
`K[X]` by a polynomial of degree `s`, which is the route to noetherianity of the Tate algebra.

## Main results

* `TauCeti.PowerSeries.isDistinguished_zero_of_isUnit` and
  `TauCeti.PowerSeries.isUnit_iff_isDistinguished_zero`: a restricted series is a unit of the ring
  of restricted series exactly when it is distinguished of degree `0`.
* `TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul`: multiplying by such a unit leaves the
  distinguished degree unchanged.
* `TauCeti.PowerSeries.IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq`,
  `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_eq_mul` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq`: Weierstrass
  preparation, in its existence, uniqueness and unique-existence forms.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1, whose statement this is;
  the statement there is for the unit radius, and the argument is the one used here.

Mathlib's `PowerSeries.exists_isWeierstrassFactorization` is a different factorization theorem, for
the divisors of `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation`: there the series lives over
an `I`-adically complete coefficient ring, the distinguished polynomial is one whose lower
coefficients lie in `I`, and the unit is a unit of the whole of `A⟦X⟧`. Here the coefficient field
is complete for an ultrametric norm, the polynomial is monic with its lower coefficients bounded by
the Gauss norm, and the unit is a unit of the subring of restricted series. Neither statement
implies the other.
-/

public section

namespace TauCeti.PowerSeries

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [NormMulClass R] [Nontrivial R]
  {c : ℝ} {s : ℕ}

/-- A unit of the ring of restricted power series at a positive radius is distinguished of
degree `0`: its constant coefficient dominates every other weighted coefficient. -/
theorem isDistinguished_zero_of_isUnit (hc : 0 < c)
    {x : PowerSeries.IsRestricted.subring (R := R) c} (hx : IsUnit x) :
    IsDistinguished c 0 (x : PowerSeries R) := by
  obtain ⟨y, hxy⟩ := hx.exists_right_inv
  have hxy' : (x : PowerSeries R) * (y : PowerSeries R) = 1 := by
    simpa using congrArg (Subring.subtype _) hxy
  have hx0 : (x : PowerSeries R) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxy'
    exact zero_ne_one hxy'
  have hy0 : (y : PowerSeries R) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxy'
    exact zero_ne_one hxy'
  obtain ⟨i, hi⟩ := exists_isDistinguished hc (mem_isRestricted_subring_iff.mp x.2) hx0
  obtain ⟨j, hj⟩ := exists_isDistinguished hc (mem_isRestricted_subring_iff.mp y.2) hy0
  -- The dominant coefficient of the product `x * y = 1` sits in degree `i + j`.
  have hdom := hi.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hj hc
  rw [hxy'] at hdom
  have hij : i + j = 0 := by
    by_contra hne
    rw [PowerSeries.coeff_one, ite_eq_right hne, norm_zero, zero_mul] at hdom
    exact (mul_pos hi.gaussNorm_pos hj.gaussNorm_pos).ne hdom
  have hi0 : i = 0 := by omega
  rwa [hi0] at hi

/-- Multiplying by a unit of the ring of restricted power series leaves the distinguished degree
unchanged. -/
theorem IsDistinguished.of_isUnit_mul {u : PowerSeries.IsRestricted.subring (R := R) c}
    {g : PowerSeries R} (h : IsDistinguished c s ((u : PowerSeries R) * g)) (hc : 0 < c)
    (hu : IsUnit u) : IsDistinguished c s g := by
  obtain ⟨w, rfl⟩ := hu
  obtain ⟨v, hv, hvu⟩ : ∃ v : PowerSeries.IsRestricted.subring (R := R) c, IsUnit v ∧
      (v : PowerSeries R) * ((w : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R)
        = 1 :=
    ⟨(w⁻¹ : (PowerSeries.IsRestricted.subring (R := R) c)ˣ),
      Units.isUnit (w⁻¹ : (PowerSeries.IsRestricted.subring (R := R) c)ˣ),
      by rw [← Subring.coe_mul, w.inv_mul, Subring.coe_one]⟩
  have hvg : (v : PowerSeries R)
      * (((w : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R) * g) = g := by
    rw [← mul_assoc, hvu, one_mul]
  have hd := (isDistinguished_zero_of_isUnit hc hv).mul h hc
  rwa [zero_add, hvg] at hd

end NormedRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {c : ℝ} {s : ℕ} {f : PowerSeries K}

/-- **The units of the ring of restricted power series.** Over a complete nonarchimedean field, a
restricted power series is a unit of the ring of series restricted at a positive radius `c`
exactly when it is distinguished of degree `0` at `c`. -/
theorem isUnit_iff_isDistinguished_zero [CompleteSpace K] (hc : 0 < c)
    (x : PowerSeries.IsRestricted.subring (R := K) c) :
    IsUnit x ↔ IsDistinguished c 0 (x : PowerSeries K) := by
  refine ⟨isDistinguished_zero_of_isUnit hc, fun hx ↦ ?_⟩
  -- Dividing `1` by `x` leaves a remainder vanishing in every degree.
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    hx.exists_mul_add_eq hc (mem_isRestricted_subring_iff.mp x.2) (PowerSeries.isRestricted_one c)
  have hr0 : r = 0 := PowerSeries.ext fun m ↦ by rw [hr m (Nat.zero_le m), map_zero]
  rw [hr0, add_zero] at hqr
  refine IsUnit.of_mul_eq_one ⟨q, mem_isRestricted_subring_iff.mpr hq⟩ (Subtype.ext ?_)
  rw [Subring.coe_mul, Subring.coe_one, mul_comm]
  exact hqr

/-- **Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1). Over a complete
nonarchimedean field, a restricted series `f` distinguished of degree `s` at a positive radius `c`
is a unit of the ring of restricted series times a monic polynomial of degree `s`:

```text
f = e * ω,    e a unit,    ω monic of degree s.
```

The polynomial `ω` is then itself distinguished of degree `s`, by
`TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul`, so no bound on its lower coefficients needs
stating separately. The factorization is unique by
`TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_eq_mul`. -/
theorem IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq [CompleteSpace K]
    (hf : IsDistinguished c s f) (hc : 0 < c) (hfr : f.IsRestricted c) :
    ∃ (e : PowerSeries.IsRestricted.subring (R := K) c) (ω : Polynomial K),
      IsUnit e ∧ ω.IsMonicOfDegree s ∧ (e : PowerSeries K) * (ω : PowerSeries K) = f := by
  -- Divide `X ^ s` by `f`.
  have hXr : (PowerSeries.X ^ s : PowerSeries K).IsRestricted c :=
    isRestricted_of_forall_coeff_eq_zero (n := s + 1) fun m hm ↦ by
      rw [PowerSeries.coeff_X_pow, ite_eq_right (by omega : ¬(m = s))]
  obtain ⟨q, r, hq, hr, hqr⟩ := hf.exists_mul_add_eq hc hfr hXr
  have hrr : r.IsRestricted c := isRestricted_of_forall_coeff_eq_zero hr
  -- The Gauss norm of `X ^ s` is `c ^ s`, so the remainder is bounded by `c ^ s`.
  have hXle : ∀ m, ‖(PowerSeries.X ^ s : PowerSeries K).coeff m‖ * c ^ m
      ≤ ‖(PowerSeries.X ^ s : PowerSeries K).coeff s‖ * c ^ s := by
    intro m
    rcases eq_or_ne m s with rfl | hm
    · exact le_rfl
    · rw [PowerSeries.coeff_X_pow, ite_eq_right hm, norm_zero, zero_mul,
        PowerSeries.coeff_X_pow_self, norm_one, one_mul]
      exact pow_nonneg hc.le s
  have hXnorm : (PowerSeries.X ^ s : PowerSeries K).gaussNorm norm c = c ^ s := by
    rw [gaussNorm_eq_of_forall_le hXle, PowerSeries.coeff_X_pow_self, norm_one, one_mul]
  have hrle : r.gaussNorm norm c ≤ c ^ s := by
    have hmax := hf.gaussNorm_mul_add_eq_max hc hq hr
    rw [hqr, hXnorm] at hmax
    rw [hmax]
    exact le_max_right _ _
  -- The remainder is a polynomial of degree less than `s`; subtract it from `X ^ s`.
  have hpc : ((r.trunc s : Polynomial K) : PowerSeries K) = r :=
    PowerSeries.ext fun m ↦ by
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hm
      · rfl
      · exact (hr m (by omega)).symm
  set ω : Polynomial K := Polynomial.X ^ s - r.trunc s with hω
  have hωc : (ω : PowerSeries K) = PowerSeries.X ^ s - r := by
    rw [hω, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, hpc]
  have hωq : (ω : PowerSeries K) = q * f := by rw [hωc, ← hqr]; ring
  have hωs : ω.coeff s = 1 := by
    rw [hω, Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_left rfl,
      PowerSeries.coeff_trunc, ite_eq_right (lt_irrefl s), sub_zero]
  have hωgt : ∀ m, s < m → ω.coeff m = 0 := fun m hm ↦ by
    rw [hω, Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right (by omega : ¬(m = s)),
      PowerSeries.coeff_trunc, ite_eq_right (by omega : ¬(m < s)), sub_zero]
  have hωdeg : ω.natDegree ≤ s := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hωgt
  -- `ω` is distinguished of degree `s`: its leading coefficient `1` dominates.
  have hcs : ‖(ω : PowerSeries K).coeff s‖ * c ^ s = c ^ s := by
    rw [Polynomial.coeff_coe, hωs, norm_one, one_mul]
  have hbound : ∀ m, ‖(ω : PowerSeries K).coeff m‖ * c ^ m ≤ c ^ s := fun m ↦ by
    rcases eq_or_ne m s with rfl | hm
    · exact hcs.le
    · have hcoeff : (ω : PowerSeries K).coeff m = -r.coeff m := by
        rw [hωc, map_sub, PowerSeries.coeff_X_pow, ite_eq_right hm, zero_sub]
      rw [hcoeff, norm_neg]
      exact (PowerSeries.le_gaussNorm norm c r (hasGaussNorm_of_isRestricted hrr) m).trans hrle
  have hωnorm : (ω : PowerSeries K).gaussNorm norm c = c ^ s := by
    rw [gaussNorm_eq_of_forall_le (s := s) fun m ↦ (hbound m).trans hcs.ge, hcs]
  have hωd : IsDistinguished c s (ω : PowerSeries K) :=
    ⟨by rw [hcs, hωnorm], fun m hm ↦ by
      rw [Polynomial.coeff_coe, hωgt m hm, norm_zero, zero_mul, hωnorm]
      exact pow_pos hc s⟩
  -- Comparing distinguished degrees in `ω = q * f` makes `q` distinguished of degree `0`.
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hωq
    exact hωd.ne_zero hωq
  obtain ⟨n, hn⟩ := exists_isDistinguished hc hq hq0
  have hn0 : n = 0 := by
    have hmul := hn.mul hf hc
    rw [← hωq] at hmul
    have := hωd.unique hmul
    omega
  rw [hn0] at hn
  obtain ⟨e, he⟩ :=
    ((isUnit_iff_isDistinguished_zero hc ⟨q, mem_isRestricted_subring_iff.mpr hq⟩).mpr
      hn).exists_right_inv
  have hcoe : q * (e : PowerSeries K) = 1 := by
    simpa using congrArg (Subring.subtype _) he
  refine ⟨e, ω, IsUnit.of_mul_eq_one_right _ he,
    (Polynomial.isMonicOfDegree_iff ω s).mpr ⟨hωdeg, hωs⟩, ?_⟩
  calc (e : PowerSeries K) * (ω : PowerSeries K) = q * (e : PowerSeries K) * f := by
        rw [hωq]; ring
    _ = f := by rw [hcoe, one_mul]

/-- **Uniqueness in Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1). A
restricted series distinguished of degree `s` at a positive radius has at most one factorization
as a unit of the ring of restricted series times a monic polynomial of degree `s`. -/
theorem IsDistinguished.eq_and_eq_of_mul_eq_mul (hf : IsDistinguished c s f) (hc : 0 < c)
    {e e' : PowerSeries.IsRestricted.subring (R := K) c} {ω ω' : Polynomial K} (he : IsUnit e)
    (he' : IsUnit e') (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : (e : PowerSeries K) * (ω : PowerSeries K) = f)
    (h' : (e' : PowerSeries K) * (ω' : PowerSeries K) = f) :
    e = e' ∧ ω = ω' := by
  -- The cofactor of a unit in a distinguished series is distinguished of the same degree.
  have hωd : IsDistinguished c s (ω : PowerSeries K) :=
    IsDistinguished.of_isUnit_mul (by rw [h]; exact hf) hc he
  -- Dividing `ω'` by `ω`, once as it stands and once with quotient `1`, identifies the two.
  obtain ⟨v, hv⟩ := he'.exists_right_inv
  have hv' : (e' : PowerSeries K) * (v : PowerSeries K) = 1 := by
    simpa using congrArg (Subring.subtype _) hv
  have hquot : ((v * e : PowerSeries.IsRestricted.subring (R := K) c) : PowerSeries K)
      * (ω : PowerSeries K) = (ω' : PowerSeries K) := by
    rw [Subring.coe_mul, mul_assoc, h, ← h', ← mul_assoc, mul_comm (v : PowerSeries K), hv',
      one_mul]
  obtain ⟨hdeg, hone⟩ := (Polynomial.isMonicOfDegree_iff ω s).mp hω
  obtain ⟨hdeg', hone'⟩ := (Polynomial.isMonicOfDegree_iff ω' s).mp hω'
  have hdiff : ∀ m, s ≤ m → ((ω' : PowerSeries K) - (ω : PowerSeries K)).coeff m = 0 := by
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe]
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [hone, hone', sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg'.trans_lt hlt),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt), sub_self]
  obtain ⟨hq1, hr1⟩ := hωd.eq_and_eq_of_mul_add_eq_mul_add hc
    (q := ((v * e : PowerSeries.IsRestricted.subring (R := K) c) : PowerSeries K)) (r := 0)
    (q' := 1) (r' := (ω' : PowerSeries K) - (ω : PowerSeries K))
    (mem_isRestricted_subring_iff.mp (v * e).2) (PowerSeries.isRestricted_one c)
    (fun m _ ↦ by simp) hdiff (by rw [hquot]; ring)
  refine ⟨?_, (Polynomial.coe_inj.mp (sub_eq_zero.mp hr1.symm)).symm⟩
  -- The quotient `v * e` is `1`, so `e` and `e'` are the same inverse of `v`.
  have hve : v * e = 1 := Subtype.ext (by rw [Subring.coe_one]; exact hq1)
  calc e = e' * v * e := by rw [hv, one_mul]
    _ = e' := by rw [mul_assoc, hve, mul_one]

/-- **Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1), in its unique-existence
form: over a complete nonarchimedean field, a restricted series distinguished of degree `s` at a
positive radius is in exactly one way a unit of the ring of restricted series times a monic
polynomial of degree `s`. -/
theorem IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq [CompleteSpace K]
    (hf : IsDistinguished c s f) (hc : 0 < c) (hfr : f.IsRestricted c) :
    ∃! p : PowerSeries.IsRestricted.subring (R := K) c × Polynomial K,
      IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧ (p.1 : PowerSeries K) * (p.2 : PowerSeries K) = f := by
  obtain ⟨e, ω, he, hm, heq⟩ := hf.exists_isUnit_isMonicOfDegree_mul_eq hc hfr
  refine ⟨(e, ω), ⟨he, hm, heq⟩, fun p ⟨h1, h2, h3⟩ ↦ ?_⟩
  obtain ⟨u1, u2⟩ := hf.eq_and_eq_of_mul_eq_mul hc h1 he h2 hm h3 heq
  exact Prod.ext u1 u2

end Field

end TauCeti.PowerSeries
