/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division

/-!
# Weierstrass preparation for restricted power series

The power series restricted at a radius `c` form a subring `PowerSeries.IsRestricted.subring c`
of `R⟦X⟧`; over a complete nonarchimedean field and at a positive radius it is the Tate algebra of
the closed disc of radius `c`. This file factors a distinguished series through a monic polynomial
and describes the units of that subring.

Over a complete ultrametric normed commutative ring `R`, whose norm need not be multiplicative and
which may have nilpotents, Weierstrass preparation says that a restricted series `g` which is
multiplicatively distinguished of degree `s` at `c` (`TauCeti.PowerSeries.IsMulDistinguished`)
factors as

```text
g = e * ω,    e a multiplicative unit of the ring of restricted series,
              ω monic of degree s,    ‖ω‖ = c ^ s,
```

for the Gauss norm at `c`, and that the pair `(e, ω)` is unique. The normalisation `‖ω‖ = c ^ s`
says that `ω` is itself multiplicatively distinguished of degree `s`
(`TauCeti.PowerSeries.isMulDistinguished_iff_gaussNorm_eq`), and it is what makes the factorization
unique without a multiplicative norm. The proof takes for `ω` the polynomial `X ^ s` minus the
remainder of `X ^ s` on division by `g`, and a second division shows that the quotient is the
inverse of `e`. Existence and uniqueness are thus both consequences of Weierstrass division by a
multiplicatively distinguished series.

When the norm of `R` is multiplicative, such as over a Tate algebra in fewer variables, a
distinguished series is multiplicatively distinguished as soon as its coefficient in its
distinguished degree is a unit, which is automatic over a field, and the normalisation of `ω` is
automatic. The theorems for that case are recovered as corollaries. Over such a ring, a restricted
series is a unit of the ring of restricted series exactly when it is distinguished of degree `0`,
that is, when its constant coefficient strictly dominates every positive-degree weighted
coefficient and attains the Gauss norm, and its constant coefficient is a unit. Over a field the
second condition follows from the first.

Since `e` is a unit, `g` and `ω` generate the same ideal, so the factorization presents the
quotient of the ring of restricted series by `g` as the quotient of `R[X]` by a monic polynomial of
degree `s`. This is the route to noetherianity of the Tate algebra.

## Main results

* `TauCeti.PowerSeries.IsMulDistinguished.exists_isNormMulUnit_isMonicOfDegree_mul_eq`,
  `TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_eq_mul` and
  `TauCeti.PowerSeries.IsMulDistinguished.existsUnique_isNormMulUnit_isMonicOfDegree_mul_eq`:
  Weierstrass preparation over a Banach ring, in its existence, uniqueness and unique-existence
  forms.
* `TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_eq_of_mul_eq`: a multiplicatively
  distinguished series has at most one factorization as a unit of the ring of restricted series
  times a monic polynomial of its distinguished degree, with no normalisation of the polynomial.
* `TauCeti.PowerSeries.IsMulDistinguished.isNormMulUnit_of_mul_eq`: a unit factor of a
  multiplicatively distinguished series by another one is a multiplicative unit.
* `TauCeti.PowerSeries.IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq`,
  `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_eq_mul` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq`: Weierstrass
  preparation for a multiplicative coefficient norm.
* `TauCeti.PowerSeries.isDistinguished_zero_of_isUnit`,
  `TauCeti.PowerSeries.isUnit_iff_isDistinguished_zero_and_isUnit_coeff_zero` and, over a field,
  `TauCeti.PowerSeries.isUnit_iff_isDistinguished_zero`: the units of the ring of restricted
  series, for a multiplicative coefficient norm.
* `TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul`: multiplying by such a unit leaves the
  distinguished degree unchanged.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Corollary 1.28, for preparation over a Banach ring.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1, whose statement the
  multiplicative-norm case is; the statement there is for the unit radius. The factor `ω` is
  constructed as there; that the quotient is a unit is deduced here from a second Weierstrass
  division.

Mathlib's `PowerSeries.exists_isWeierstrassFactorization` is a different factorization theorem, for
the divisors of `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation`: there the series lives over
an `I`-adically complete coefficient ring, the distinguished polynomial is one whose lower
coefficients lie in `I`, and the unit is a unit of the whole of `A⟦X⟧`. Here the coefficient ring
is complete for an ultrametric norm, the polynomial is monic with its lower coefficients bounded by
the Gauss norm, and the unit is a unit of the subring of restricted series. Neither statement
implies the other.
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
  have hxy' : (x : PowerSeries R) * (y : PowerSeries R) = 1 := coe_mul_coe_eq_one hxy
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
  have hdom := hi.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hj hc (norm_mul _ _)
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
  have hd := (isDistinguished_zero_of_isUnit hc hv).mul h hc (norm_mul _ _)
  rwa [zero_add, hvg] at hd

end NormedRing

section MulDistinguished

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {s t : ℕ}
  {g ω : PowerSeries R}

/-- **The unit factor of a Weierstrass factorization is a multiplicative unit.** Over an ultrametric
normed commutative ring, if a multiplicatively distinguished series `g` is a unit `e` of the ring
of restricted series times a multiplicatively distinguished series `ω`, then `e` is a
multiplicative unit of that ring for its Gauss norm: left multiplication by `e` scales every norm
exactly. -/
theorem IsMulDistinguished.isNormMulUnit_of_mul_eq [Fact (0 < c)] (hg : IsMulDistinguished c s g)
    (hω : IsMulDistinguished c t ω) {e : PowerSeries.IsRestricted.subring (R := R) c}
    (he : IsUnit e) (h : (e : PowerSeries R) * ω = g) : IsNormMulUnit e := by
  have hc : 0 < c := Fact.out
  have : NormOneClass R := hg.normOneClass
  -- `‖ω‖ * ‖e * x‖ = ‖g‖ * ‖x‖` for every restricted `x`.
  have key : ∀ x : PowerSeries.IsRestricted.subring (R := R) c,
      ω.gaussNorm norm c * ‖e * x‖ = g.gaussNorm norm c * ‖x‖ := fun x ↦ by
    rw [norm_eq_gaussNorm, norm_eq_gaussNorm, ← hω.gaussNorm_mul hc (e * x).2,
      ← hg.gaussNorm_mul hc x.2, ← h, Subring.coe_mul, mul_left_comm, mul_assoc]
  have hω0 : ω.gaussNorm norm c ≠ 0 := hω.gaussNorm_pos.ne'
  have he1 := key 1
  rw [mul_one, norm_one, mul_one] at he1
  refine (isNormMulUnit_iff e).mpr ⟨he, fun x ↦ mul_left_cancel₀ hω0 ?_⟩
  rw [key, ← mul_assoc, he1]

/-- The polynomial factor of Weierstrass preparation: `X ^ s` minus the remainder of `X ^ s` on
division by `g` is a monic polynomial of degree `s`, multiplicatively distinguished of degree `s`,
and a restricted multiple of `g`. -/
private theorem IsMulDistinguished.exists_isMonicOfDegree_eq_mul [CompleteSpace R]
    (hg : IsMulDistinguished c s g) (hc : 0 < c) (hgr : g.IsRestricted c) :
    ∃ (q : PowerSeries R) (ω : Polynomial R), q.IsRestricted c ∧ ω.IsMonicOfDegree s ∧
      IsMulDistinguished c s (ω : PowerSeries R) ∧ (ω : PowerSeries R) = g * q := by
  have : Nontrivial R := hg.nontrivial
  have : NormOneClass R := hg.normOneClass
  -- Divide `X ^ s` by `g`.
  have hXr : (PowerSeries.X ^ s : PowerSeries R).IsRestricted c := by
    rw [← Polynomial.coe_X, ← Polynomial.coe_pow]
    exact isRestricted_polynomial _
  obtain ⟨q, r, hq, hr, hqr⟩ := hg.exists_mul_add_eq hc hgr hXr
  -- The Gauss norm of `X ^ s` is `c ^ s`, so the remainder is bounded by `c ^ s`.
  have hXnorm : (PowerSeries.X ^ s : PowerSeries R).gaussNorm norm c = c ^ s := by
    rw [PowerSeries.X_pow_eq, ← (isMulDistinguished_monomial hc isNormMulUnit_one s
      (R := R)).norm_coeff_mul_pow_eq, PowerSeries.coeff_monomial_same, norm_one, one_mul]
  have hrle : r.gaussNorm norm c ≤ c ^ s := by
    have hmax := hg.gaussNorm_mul_add_eq_max hc hq hr
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
  have hωq : (ω : PowerSeries R) = g * q := by rw [hωc, ← hqr]; ring
  have hωm : ω.IsMonicOfDegree s := by
    rcases s with _ | s
    · simp [hω]
    · simpa [Nat.succ_eq_add_one] using
        (Polynomial.isMonicOfDegree_X_pow R (s + 1)).sub
          (PowerSeries.natDegree_trunc_lt r s)
  -- `ω` is multiplicatively distinguished of degree `s`: its lower weighted coefficients are those
  -- of `-r`, bounded by `c ^ s`.
  have hωd : IsMulDistinguished c s (ω : PowerSeries R) :=
    ⟨isDistinguished_of_isMonicOfDegree hc hωm fun k hk ↦ by
      rw [← Polynomial.coeff_coe, hωc, map_sub, PowerSeries.coeff_X_pow, ite_eq_right hk.ne,
        zero_sub, norm_neg]
      exact (PowerSeries.le_gaussNorm norm c r
        (hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr)) k).trans hrle,
      by
        rw [Polynomial.coeff_coe, hωm.coeff_eq (Polynomial.isMonicOfDegree_X_pow R s) le_rfl,
          Polynomial.coeff_X_pow_self]
        exact isNormMulUnit_one⟩
  exact ⟨q, ω, hq, hωm, hωd, hωq⟩

/-- **Weierstrass preparation over a Banach ring** (Martin, Corollary 1.28). Over a complete
ultrametric normed commutative ring, a restricted series `g` multiplicatively distinguished of
degree `s` at a positive radius `c` is a multiplicative unit of the ring of restricted series
times a monic polynomial of degree `s` with Gauss norm `c ^ s`:

```text
g = e * ω,    e a multiplicative unit,    ω monic of degree s,    ‖ω‖ = c ^ s.
```

The norm of the coefficient ring need not be multiplicative, and the ring may have nilpotents. By
`TauCeti.PowerSeries.isMulDistinguished_iff_gaussNorm_eq`, the normalisation `‖ω‖ = c ^ s` says
that `ω` is itself multiplicatively distinguished of degree `s`. The factorization is unique by
`TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_eq_mul`. -/
theorem IsMulDistinguished.exists_isNormMulUnit_isMonicOfDegree_mul_eq [CompleteSpace R]
    [Fact (0 < c)] (hg : IsMulDistinguished c s g) (hgr : g.IsRestricted c) :
    ∃ (e : PowerSeries.IsRestricted.subring (R := R) c) (ω : Polynomial R),
      IsNormMulUnit e ∧ ω.IsMonicOfDegree s ∧ (ω : PowerSeries R).gaussNorm norm c = c ^ s ∧
      (e : PowerSeries R) * (ω : PowerSeries R) = g := by
  have hc : 0 < c := Fact.out
  have : NormOneClass R := hg.normOneClass
  obtain ⟨q, ω, hq, hωm, hωd, hωq⟩ := hg.exists_isMonicOfDegree_eq_mul hc hgr
  -- Divide `g` by `ω`: `g = ω * e + r'`. Then `g = g * (q * e) + r'`, and uniqueness of division
  -- by `g` makes `e` an inverse of `q` and the remainder `r'` zero.
  obtain ⟨e, r', he, hr', her'⟩ := hωd.exists_mul_add_eq hc (isRestricted_polynomial ω) hgr
  have hself : g * (q * e) + r' = g * 1 + 0 := by
    rw [← mul_assoc, ← hωq, her', mul_one, add_zero]
  obtain ⟨heq, hr0⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add hc (hq.mul he)
    (PowerSeries.isRestricted_one c) hr' (fun m _ ↦ by simp) hself
  rw [hr0, add_zero, mul_comm] at her'
  have heu : IsUnit (⟨e, he⟩ : PowerSeries.IsRestricted.subring (R := R) c) :=
    IsUnit.of_mul_eq_one ⟨q, hq⟩ (Subtype.ext (by rw [mul_comm] at heq; exact heq))
  exact ⟨⟨e, he⟩, ω, hg.isNormMulUnit_of_mul_eq hωd heu her',
    hωm, (isMulDistinguished_iff_gaussNorm_eq hc hωm).mp hωd, her'⟩

/-- **Uniqueness in Weierstrass preparation over a Banach ring** (Martin, Corollary 1.28). Over an
ultrametric normed commutative ring, let `ω` be a monic polynomial of degree `s` which is
multiplicatively distinguished of degree `s` at a positive radius `c`, that is, has Gauss norm
`c ^ s`. If `e * ω = e' * ω'` with `e`, `e'` restricted at `c`, `e'` a unit of the ring of
restricted series and `ω'` another monic polynomial of degree `s`, then `e = e'` and `ω = ω'`.
Only `e'` needs to be a unit, and no hypothesis on the product is needed beyond the equation. -/
theorem IsMulDistinguished.eq_and_eq_of_mul_eq_mul {ω ω' : Polynomial R}
    (hω : IsMulDistinguished c s (ω : PowerSeries R)) (hc : 0 < c) (hωm : ω.IsMonicOfDegree s)
    (hωm' : ω'.IsMonicOfDegree s) {e e' : PowerSeries.IsRestricted.subring (R := R) c}
    (he' : IsUnit e')
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = (e' : PowerSeries R) * (ω' : PowerSeries R)) :
    e = e' ∧ ω = ω' := by
  obtain ⟨v, hv⟩ := he'.exists_right_inv
  have hv' : (e' : PowerSeries R) * (v : PowerSeries R) = 1 := coe_mul_coe_eq_one hv
  have hquot : (ω : PowerSeries R)
      * ((v * e : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R)
      = (ω' : PowerSeries R) := by
    rw [Subring.coe_mul, mul_left_comm, mul_comm (ω : PowerSeries R), h, ← mul_assoc,
      mul_comm (v : PowerSeries R), hv', one_mul]
  have hdiff : ∀ m, s ≤ m → ((ω' : PowerSeries R) - (ω : PowerSeries R)).coeff m = 0 := by
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, hωm'.coeff_eq hωm hm, sub_self]
  obtain ⟨hq1, hr1⟩ := hω.eq_and_eq_of_mul_add_eq_mul_add hc
    (q := ((v * e : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R)) (r := 0)
    (q' := 1) (r' := (ω' : PowerSeries R) - (ω : PowerSeries R))
    (v * e).2 (PowerSeries.isRestricted_one c)
    (fun m _ ↦ by simp) hdiff (by rw [hquot]; ring)
  refine ⟨?_, (Polynomial.coe_inj.mp (sub_eq_zero.mp hr1.symm)).symm⟩
  -- The quotient `v * e` is `1`, so `e` and `e'` are the same inverse of `v`.
  have hve : v * e = 1 := Subtype.ext (by rw [Subring.coe_one]; exact hq1)
  calc e = e' * v * e := by rw [hv, one_mul]
    _ = e' := by rw [mul_assoc, hve, mul_one]

/-- **Uniqueness of the factorizations of a multiplicatively distinguished series.** Over an
ultrametric normed commutative ring, let `g` be multiplicatively distinguished of degree `s` at a
positive radius `c`. If `g = e * ω = e' * ω'` with `e`, `e'` units of the ring of restricted
series and `ω`, `ω'` monic polynomials of degree `s`, then `e = e'` and `ω = ω'`. Unlike
`TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_eq_mul`, no normalisation of the
polynomial factors is assumed: for the inverse `v` of `e`, `X ^ s = g * v + (X ^ s - ω)` is a
Weierstrass division by `g`, so `ω` is `X ^ s` minus the remainder of `X ^ s` on division by
`g`. -/
theorem IsMulDistinguished.eq_and_eq_of_mul_eq_of_mul_eq (hg : IsMulDistinguished c s g)
    (hc : 0 < c) {e e' : PowerSeries.IsRestricted.subring (R := R) c} {ω ω' : Polynomial R}
    (he : IsUnit e) (he' : IsUnit e') (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g)
    (h' : (e' : PowerSeries R) * (ω' : PowerSeries R) = g) : e = e' ∧ ω = ω' := by
  have : Nontrivial R := hg.nontrivial
  have key : ∀ (e : PowerSeries.IsRestricted.subring (R := R) c) (ω : Polynomial R), IsUnit e →
      ω.IsMonicOfDegree s → (e : PowerSeries R) * (ω : PowerSeries R) = g →
      ∃ v : PowerSeries.IsRestricted.subring (R := R) c, e * v = 1 ∧
        (∀ m, s ≤ m → (((Polynomial.X ^ s - ω : Polynomial R) : PowerSeries R)).coeff m = 0) ∧
        g * (v : PowerSeries R) + ((Polynomial.X ^ s - ω : Polynomial R) : PowerSeries R) =
          ((Polynomial.X ^ s : Polynomial R) : PowerSeries R) := by
    intro e ω he hω h
    obtain ⟨v, hv⟩ := he.exists_right_inv
    have hv' : (e : PowerSeries R) * (v : PowerSeries R) = 1 := coe_mul_coe_eq_one hv
    refine ⟨v, hv, fun m hm ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_coe, Polynomial.coeff_sub,
        (Polynomial.isMonicOfDegree_X_pow R s).coeff_eq hω hm, sub_self]
    · rw [← h, Polynomial.coe_sub]
      linear_combination (ω : PowerSeries R) * hv'
  obtain ⟨v, hv, hr, hdiv⟩ := key e ω he hω h
  obtain ⟨v', hv', hr', hdiv'⟩ := key e' ω' he' hω' h'
  obtain ⟨hvv, hrr⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add hc v.2 v'.2 hr hr' (hdiv.trans hdiv'.symm)
  obtain rfl : v = v' := Subtype.ext hvv
  refine ⟨?_, sub_right_injective (Polynomial.coe_inj.mp hrr)⟩
  calc e = e * (e' * v) := by rw [hv', mul_one]
    _ = e' * (e * v) := by ring
    _ = e' := by rw [hv, mul_one]

/-- **Weierstrass preparation over a Banach ring** (Martin, Corollary 1.28), in its
unique-existence form: over a complete ultrametric normed commutative ring, a restricted series
multiplicatively distinguished of degree `s` at a positive radius `c` is in exactly one way a
multiplicative unit of the ring of restricted series times a monic polynomial of degree `s` with
Gauss norm `c ^ s`. -/
theorem IsMulDistinguished.existsUnique_isNormMulUnit_isMonicOfDegree_mul_eq [CompleteSpace R]
    [Fact (0 < c)] (hg : IsMulDistinguished c s g) (hgr : g.IsRestricted c) :
    ∃! p : PowerSeries.IsRestricted.subring (R := R) c × Polynomial R,
      IsNormMulUnit p.1 ∧ p.2.IsMonicOfDegree s ∧ (p.2 : PowerSeries R).gaussNorm norm c = c ^ s ∧
      (p.1 : PowerSeries R) * (p.2 : PowerSeries R) = g := by
  have hc : 0 < c := Fact.out
  have : NormOneClass R := hg.normOneClass
  obtain ⟨e, ω, he, hm, hn, heq⟩ := hg.exists_isNormMulUnit_isMonicOfDegree_mul_eq hgr
  refine ⟨(e, ω), ⟨he, hm, hn, heq⟩, fun p ⟨h1, h2, _, h4⟩ ↦ ?_⟩
  obtain ⟨u1, u2⟩ := ((isMulDistinguished_iff_gaussNorm_eq hc hm).mpr hn).eq_and_eq_of_mul_eq_mul
    hc hm h2 h1.isUnit (heq.trans h4.symm)
  exact Prod.ext u1.symm u2.symm

end MulDistinguished

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
    (isMulDistinguished_iff_isUnit.mpr ⟨hx, hu⟩).exists_mul_add_eq hc x.2
      (PowerSeries.isRestricted_one c)
  rw [mul_comm] at hqr
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
on its lower coefficients needs stating separately. With a multiplicative norm, `f` is
multiplicatively distinguished, so this is
`TauCeti.PowerSeries.IsMulDistinguished.exists_isNormMulUnit_isMonicOfDegree_mul_eq`. The
factorization is unique by `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_eq_mul`. -/
theorem IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq [CompleteSpace R]
    (hf : IsDistinguished c s f) (hu : IsUnit (f.coeff s)) (hc : 0 < c)
    (hfr : f.IsRestricted c) :
    ∃ (e : PowerSeries.IsRestricted.subring (R := R) c) (ω : Polynomial R),
      IsUnit e ∧ ω.IsMonicOfDegree s ∧ (e : PowerSeries R) * (ω : PowerSeries R) = f := by
  have : Fact (0 < c) := ⟨hc⟩
  obtain ⟨e, ω, he, hm, -, heq⟩ := (isMulDistinguished_iff_isUnit.mpr
    ⟨hf, hu⟩).exists_isNormMulUnit_isMonicOfDegree_mul_eq hfr
  exact ⟨e, ω, he.isUnit, hm, heq⟩

/-- **Uniqueness in Weierstrass preparation** (Bosch–Güntzer–Remmert §5.2.2, Theorem 1). A
restricted series distinguished of degree `s` at a positive radius has at most one factorization
as a unit of the ring of restricted series times a monic polynomial of degree `s`. With a
multiplicative norm no normalisation of the polynomial factor is needed: it is distinguished of
degree `s` by `TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul`, so this is
`TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_eq_mul`. -/
theorem IsDistinguished.eq_and_eq_of_mul_eq_mul (hf : IsDistinguished c s f) (hc : 0 < c)
    {e e' : PowerSeries.IsRestricted.subring (R := R) c} {ω ω' : Polynomial R} (he : IsUnit e)
    (he' : IsUnit e') (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = f)
    (h' : (e' : PowerSeries R) * (ω' : PowerSeries R) = f) :
    e = e' ∧ ω = ω' := by
  have hωd : IsDistinguished c s (ω : PowerSeries R) :=
    IsDistinguished.of_isUnit_mul (by rw [h]; exact hf) hc he
  have hωd' : IsMulDistinguished c s (ω : PowerSeries R) :=
    isMulDistinguished_iff_isUnit.mpr ⟨hωd, hω.coeff_coe_self ▸ isUnit_one⟩
  exact hωd'.eq_and_eq_of_mul_eq_mul hc hω hω' he' (h.trans h'.symm)

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
