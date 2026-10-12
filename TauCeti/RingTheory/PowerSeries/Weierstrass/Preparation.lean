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
of `R⟦X⟧`; over a complete nonarchimedean field and at a positive radius it is the Tate algebra of
the closed disc of radius `c`. This file describes its units and factors a distinguished series
through a monic polynomial. The coefficients may lie in any complete ultrametric normed
commutative ring with multiplicative norm, such as a Tate algebra in fewer variables; the series
to be factored is then asked to have a unit coefficient in its distinguished degree, which is
automatic over a field.

Over such a ring, a restricted series is a unit of that subring exactly when it is distinguished
of degree `0`, that is, when its constant coefficient strictly dominates every positive-degree
weighted coefficient and attains the Gauss norm, and its constant coefficient is a unit. Over a
field the second condition follows from the first. Weierstrass preparation then says that a
restricted series `f` distinguished of degree `s`, with a unit coefficient in degree `s`, factors as

```text
f = e * ω,    e a unit of the ring of restricted series,    ω monic of degree s,
```

and that the pair `(e, ω)` is unique; the polynomial `ω` is again distinguished of degree `s`.
Both statements are consequences of Weierstrass division.

Since `e` is a unit, `f` and `ω` generate the same ideal, so the factorization presents the
quotient of the ring of restricted series by `f` as the quotient of `R[X]` by a monic polynomial of
degree `s`. This is the route to noetherianity of the Tate algebra.

## Main results

* `TauCeti.PowerSeries.isDistinguished_zero_of_isUnit`,
  `TauCeti.PowerSeries.isUnit_iff_isDistinguished_zero_and_isUnit_coeff_zero` and, over a field,
  `TauCeti.PowerSeries.isUnit_iff_isDistinguished_zero`: the units of the ring of restricted
  series.
* `TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul`: multiplying by such a unit leaves the
  distinguished degree unchanged.
* `TauCeti.PowerSeries.IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq`,
  `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_eq_mul` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq`: Weierstrass
  preparation, in its existence, uniqueness and unique-existence forms.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1, whose statement this is;
  the statement there is for the unit radius. The factor `ω` is constructed as there; that the
  quotient is a unit is deduced here from a second Weierstrass division.

Mathlib's `PowerSeries.exists_isWeierstrassFactorization` is a different factorization theorem, for
the divisors of `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation`: there the series lives over
an `I`-adically complete coefficient ring, the distinguished polynomial is one whose lower
coefficients lie in `I`, and the unit is a unit of the whole of `A⟦X⟧`. Here the coefficient ring
is complete for a multiplicative ultrametric norm, the polynomial is monic with its lower
coefficients bounded by the Gauss norm, and the unit is a unit of the subring of restricted series.
Neither statement implies the other.
-/

public section

namespace TauCeti.PowerSeries

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ} {s : ℕ}

/-- A unit of the ring of restricted power series at a positive radius is distinguished of
degree `0`: its constant coefficient strictly dominates every positive-degree weighted coefficient
and attains the Gauss norm. -/
theorem isDistinguished_zero_of_isUnit [Nontrivial R] (hc : 0 < c)
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
  obtain ⟨i, hi⟩ := exists_isDistinguished hc x.2 hx0
  obtain ⟨j, hj⟩ := exists_isDistinguished hc y.2 hy0
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
  let _ : Nontrivial R := nontrivial_of_ne _ _ h.coeff_ne_zero
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

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ} {s : ℕ}
  {f : PowerSeries R}

/-- **The units of the ring of restricted power series.** Over a complete ultrametric normed
commutative ring with multiplicative norm, a restricted power series is a unit of the ring of
series restricted at a positive radius `c` exactly when it is distinguished of degree `0` at `c`
and its constant coefficient is a unit. -/
theorem isUnit_iff_isDistinguished_zero_and_isUnit_coeff_zero [CompleteSpace R] [Nontrivial R]
    (hc : 0 < c) (x : PowerSeries.IsRestricted.subring (R := R) c) :
    IsUnit x ↔ IsDistinguished c 0 (x : PowerSeries R) ∧ IsUnit ((x : PowerSeries R).coeff 0) := by
  refine ⟨fun hx ↦ ⟨isDistinguished_zero_of_isUnit hc hx, ?_⟩, fun ⟨hx, hu⟩ ↦ ?_⟩
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hx.map (PowerSeries.IsRestricted.subring (R := R) c).subtype).map _
  -- Dividing `1` by `x` leaves a remainder vanishing in every degree.
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    hx.exists_mul_add_eq hu hc x.2 (PowerSeries.isRestricted_one c)
  have hr0 : r = 0 := PowerSeries.ext fun m ↦ by rw [hr m (Nat.zero_le m), map_zero]
  rw [hr0, add_zero] at hqr
  refine IsUnit.of_mul_eq_one ⟨q, hq⟩ (Subtype.ext ?_)
  rw [Subring.coe_mul, Subring.coe_one, mul_comm]
  exact hqr

/-- **Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1). Over a complete
ultrametric normed commutative ring with multiplicative norm, a restricted series `f`
distinguished of degree `s` at a positive radius `c`, whose coefficient in degree `s` is a unit,
is a unit of the ring of restricted series times a monic polynomial of degree `s`:

```text
f = e * ω,    e a unit,    ω monic of degree s.
```

Over a field the unit condition is automatic, by
`TauCeti.PowerSeries.IsDistinguished.coeff_ne_zero`. The polynomial `ω` is then itself
distinguished of degree `s`, by `TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul`, so no bound
on its lower coefficients needs stating separately. The factorization is unique by
`TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_eq_mul`. -/
theorem IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq [CompleteSpace R]
    (hf : IsDistinguished c s f) (hu : IsUnit (f.coeff s)) (hc : 0 < c)
    (hfr : f.IsRestricted c) :
    ∃ (e : PowerSeries.IsRestricted.subring (R := R) c) (ω : Polynomial R),
      IsUnit e ∧ ω.IsMonicOfDegree s ∧ (e : PowerSeries R) * (ω : PowerSeries R) = f := by
  have : Nontrivial R := nontrivial_of_ne _ _ hf.coeff_ne_zero
  have : NormOneClass R := NormMulClass.toNormOneClass
  -- Divide `X ^ s` by `f`.
  have hXr : (PowerSeries.X ^ s : PowerSeries R).IsRestricted c :=
    isRestricted_of_forall_coeff_eq_zero (n := s + 1) fun m hm ↦ by
      rw [PowerSeries.coeff_X_pow, ite_eq_right (by omega : ¬(m = s))]
  obtain ⟨q, r, hq, hr, hqr⟩ := hf.exists_mul_add_eq hu hc hfr hXr
  have hrr : r.IsRestricted c := isRestricted_of_forall_coeff_eq_zero hr
  -- The Gauss norm of `X ^ s` is `c ^ s`, so the remainder is bounded by `c ^ s`.
  have hXle : ∀ m, ‖(PowerSeries.X ^ s : PowerSeries R).coeff m‖ * c ^ m
      ≤ ‖(PowerSeries.X ^ s : PowerSeries R).coeff s‖ * c ^ s := by
    intro m
    rcases eq_or_ne m s with rfl | hm
    · exact le_rfl
    · rw [PowerSeries.coeff_X_pow, ite_eq_right hm, norm_zero, zero_mul,
        PowerSeries.coeff_X_pow_self, norm_one, one_mul]
      exact pow_nonneg hc.le s
  have hXnorm : (PowerSeries.X ^ s : PowerSeries R).gaussNorm norm c = c ^ s := by
    rw [gaussNorm_eq_of_forall_le hXle, PowerSeries.coeff_X_pow_self, norm_one, one_mul]
  have hrle : r.gaussNorm norm c ≤ c ^ s := by
    have hmax := hf.gaussNorm_mul_add_eq_max hc hq hr
    rw [hqr, hXnorm] at hmax
    rw [hmax]
    exact le_max_right _ _
  -- The remainder is a polynomial of degree less than `s`; subtract it from `X ^ s`.
  have hpc : ((r.trunc s : Polynomial R) : PowerSeries R) = r :=
    PowerSeries.ext fun m ↦ by
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hm
      · rfl
      · exact (hr m (by omega)).symm
  set ω : Polynomial R := Polynomial.X ^ s - r.trunc s with hω
  have hωc : (ω : PowerSeries R) = PowerSeries.X ^ s - r := by
    rw [hω, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, hpc]
  have hωq : (ω : PowerSeries R) = q * f := by rw [hωc, ← hqr]; ring
  have hωm : ω.IsMonicOfDegree s := by
    rcases s with _ | s
    · simp [hω]
    · simpa [Nat.succ_eq_add_one] using
        (Polynomial.isMonicOfDegree_X_pow R (s + 1)).sub
          (PowerSeries.natDegree_trunc_lt r s)
  -- `ω` is distinguished of degree `s`: its leading coefficient `1` dominates.
  have hωs : (ω : PowerSeries R).coeff s = 1 := by
    rw [Polynomial.coeff_coe, hωm.coeff_eq (Polynomial.isMonicOfDegree_X_pow R s) le_rfl,
      Polynomial.coeff_X_pow, ite_eq_left rfl]
  have hcs : ‖(ω : PowerSeries R).coeff s‖ * c ^ s = c ^ s := by
    rw [hωs, norm_one, one_mul]
  have hbound : ∀ m, ‖(ω : PowerSeries R).coeff m‖ * c ^ m ≤ c ^ s := fun m ↦ by
    rcases eq_or_ne m s with rfl | hm
    · exact hcs.le
    · have hcoeff : (ω : PowerSeries R).coeff m = -r.coeff m := by
        rw [hωc, map_sub, PowerSeries.coeff_X_pow, ite_eq_right hm, zero_sub]
      rw [hcoeff, norm_neg]
      exact (PowerSeries.le_gaussNorm norm c r (hasGaussNorm_of_isRestricted hrr) m).trans hrle
  have hωnorm : (ω : PowerSeries R).gaussNorm norm c = c ^ s := by
    rw [gaussNorm_eq_of_forall_le (s := s) fun m ↦ (hbound m).trans hcs.ge, hcs]
  have hωd : IsDistinguished c s (ω : PowerSeries R) :=
    ⟨by rw [hcs, hωnorm], fun m hm ↦ by
      rw [Polynomial.coeff_coe,
        hωm.coeff_eq (Polynomial.isMonicOfDegree_X_pow R s) hm.le,
        Polynomial.coeff_X_pow, ite_eq_right hm.ne', norm_zero, zero_mul, hωnorm]
      exact pow_pos hc s⟩
  -- Divide `f` by the monic `ω`: `f = e * ω + r'`. Then `f = (e * q) * f + r'`, and uniqueness of
  -- division by `f` makes `q` an inverse of `e` and the remainder `r'` zero.
  have hωr : (ω : PowerSeries R).IsRestricted c :=
    isRestricted_of_forall_coeff_eq_zero (n := ω.natDegree + 1) fun m hm ↦ by
      rw [Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨e, r', he, hr', her'⟩ := hωd.exists_mul_add_eq (by rw [hωs]; exact isUnit_one) hc hωr hfr
  have hself : e * q * f + r' = 1 * f + 0 := by
    rw [mul_assoc, ← hωq, her', one_mul, add_zero]
  obtain ⟨heq, hr0⟩ := hf.eq_and_eq_of_mul_add_eq_mul_add hc
    (PowerSeries.isRestricted.mul c he hq) (PowerSeries.isRestricted_one c) hr'
    (fun m _ ↦ by simp) hself
  rw [hr0, add_zero] at her'
  exact ⟨⟨e, he⟩, ω, IsUnit.of_mul_eq_one ⟨q, hq⟩ (Subtype.ext heq), hωm, her'⟩

/-- **Uniqueness in Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1). A
restricted series distinguished of degree `s` at a positive radius has at most one factorization
as a unit of the ring of restricted series times a monic polynomial of degree `s`. -/
theorem IsDistinguished.eq_and_eq_of_mul_eq_mul (hf : IsDistinguished c s f) (hc : 0 < c)
    {e e' : PowerSeries.IsRestricted.subring (R := R) c} {ω ω' : Polynomial R} (he : IsUnit e)
    (he' : IsUnit e') (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = f)
    (h' : (e' : PowerSeries R) * (ω' : PowerSeries R) = f) :
    e = e' ∧ ω = ω' := by
  -- The cofactor of a unit in a distinguished series is distinguished of the same degree.
  have hωd : IsDistinguished c s (ω : PowerSeries R) :=
    IsDistinguished.of_isUnit_mul (by rw [h]; exact hf) hc he
  -- Dividing `ω'` by `ω`, once as it stands and once with quotient `1`, identifies the two.
  obtain ⟨v, hv⟩ := he'.exists_right_inv
  have hv' : (e' : PowerSeries R) * (v : PowerSeries R) = 1 := by
    simpa using congrArg (Subring.subtype _) hv
  have hquot : ((v * e : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R)
      * (ω : PowerSeries R) = (ω' : PowerSeries R) := by
    rw [Subring.coe_mul, mul_assoc, h, ← h', ← mul_assoc, mul_comm (v : PowerSeries R), hv',
      one_mul]
  have hdiff : ∀ m, s ≤ m → ((ω' : PowerSeries R) - (ω : PowerSeries R)).coeff m = 0 := by
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, hω'.coeff_eq hω hm, sub_self]
  obtain ⟨hq1, hr1⟩ := hωd.eq_and_eq_of_mul_add_eq_mul_add hc
    (q := ((v * e : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R)) (r := 0)
    (q' := 1) (r' := (ω' : PowerSeries R) - (ω : PowerSeries R))
    (v * e).2 (PowerSeries.isRestricted_one c)
    (fun m _ ↦ by simp) hdiff (by rw [hquot]; ring)
  refine ⟨?_, (Polynomial.coe_inj.mp (sub_eq_zero.mp hr1.symm)).symm⟩
  -- The quotient `v * e` is `1`, so `e` and `e'` are the same inverse of `v`.
  have hve : v * e = 1 := Subtype.ext (by rw [Subring.coe_one]; exact hq1)
  calc e = e' * v * e := by rw [hv, one_mul]
    _ = e' := by rw [mul_assoc, hve, mul_one]

/-- **Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1), in its unique-existence
form: over a complete ultrametric normed commutative ring with multiplicative norm, a restricted
series distinguished of degree `s` at a positive radius, whose coefficient in degree `s` is a unit,
is in exactly one way a unit of the ring of restricted series times a monic polynomial of degree
`s`. -/
theorem IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq [CompleteSpace R]
    (hf : IsDistinguished c s f) (hu : IsUnit (f.coeff s)) (hc : 0 < c)
    (hfr : f.IsRestricted c) :
    ∃! p : PowerSeries.IsRestricted.subring (R := R) c × Polynomial R,
      IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧ (p.1 : PowerSeries R) * (p.2 : PowerSeries R) = f := by
  obtain ⟨e, ω, he, hm, heq⟩ := hf.exists_isUnit_isMonicOfDegree_mul_eq hu hc hfr
  refine ⟨(e, ω), ⟨he, hm, heq⟩, fun p ⟨h1, h2, h3⟩ ↦ ?_⟩
  obtain ⟨u1, u2⟩ := hf.eq_and_eq_of_mul_eq_mul hc h1 he h2 hm h3 heq
  exact Prod.ext u1 u2

end NormedCommRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {c : ℝ}

/-- **The units of the ring of restricted power series over a field.** Over a complete
nonarchimedean field, a restricted power series is a unit of the ring of series restricted at a
positive radius `c` exactly when it is distinguished of degree `0` at `c`. -/
@[simp] theorem isUnit_iff_isDistinguished_zero (hc : 0 < c)
    (x : PowerSeries.IsRestricted.subring (R := K) c) :
    IsUnit x ↔ IsDistinguished c 0 (x : PowerSeries K) := by
  rw [isUnit_iff_isDistinguished_zero_and_isUnit_coeff_zero hc,
    and_iff_left_of_imp fun h ↦ h.coeff_ne_zero.isUnit]

end Field

end TauCeti.PowerSeries
