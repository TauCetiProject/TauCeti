/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.DivMod
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
import TauCeti.RingTheory.PowerSeries.GaussNorm.Estimates
import TauCeti.RingTheory.PowerSeries.Weierstrass.Polynomial

/-!
# The Weierstrass factors through division

Let `R` be an ultrametric normed commutative ring, `c > 0` a radius and `g` a power series
multiplicatively distinguished of degree `s` at `c` (`TauCeti.PowerSeries.IsMulDistinguished`).
Weierstrass preparation writes `g = e * ω` with `e` a unit of the ring of series restricted at
`c` and `ω` a monic polynomial of degree `s`. This file expresses both factors through
Weierstrass division by `g`, and compares division by `g` with division by `ω`.

Write `b` for the Weierstrass remainder of `X ^ s` on division by `g`. For every such
factorization `g = e * ω`:

```text
ω = X ^ s - b,    e * (X ^ s / g) = 1,
f mod ω = f mod g,    f / ω = e * (f / g)    for every restricted f.
```

So the polynomial factor is determined by a single division, without solving for `e`, and the
two divisions have the same remainders: `g` and `ω` generate the same ideal, and the remainder
is the canonical representative of a class modulo that ideal. Nothing is assumed of `ω` beyond
being monic of degree `s`; it is then automatically multiplicatively distinguished of degree `s`,
with Gauss norm `c ^ s`, by the norm identity of Weierstrass division applied to
`X ^ s = g * e⁻¹ + (X ^ s - ω)`.

When `g` is itself a polynomial `p`, Weierstrass division of `p` by `ω` is polynomial division
by the monic polynomial `ω`. The equation `p = ω * e + 0` is then a division with remainder, so
`ω` divides `p` in `R[X]` and the unit factor `e` is the polynomial `p /ₘ ω`.

The norm of `R` need not be multiplicative, and `R` may have nilpotents. Completeness of `R` is
used only to name the Weierstrass quotient and remainder; the comparison of `ω` with `g` and the
polynomial case hold without it.

## Main results

* `TauCeti.PowerSeries.IsMulDistinguished.isMulDistinguished_of_mul_eq`: a monic polynomial of
  degree `s` which is a unit multiple of `g` is multiplicatively distinguished of degree `s`.
* `TauCeti.PowerSeries.IsMulDistinguished.eq_X_pow_sub_weierstrassMod_of_mul_eq`: the
  polynomial factor is `X ^ s` minus the Weierstrass remainder of `X ^ s`.
* `TauCeti.PowerSeries.IsMulDistinguished.mul_weierstrassDiv_X_pow_eq_one_of_mul_eq`: the
  Weierstrass quotient of `X ^ s` is the inverse of the unit factor.
* `TauCeti.PowerSeries.IsMulDistinguished.weierstrassMod_eq_of_mul_eq` and
  `TauCeti.PowerSeries.IsMulDistinguished.weierstrassDiv_eq_mul_of_mul_eq`: division by `ω` has
  the same remainders as division by `g`, and quotients multiplied by `e`.
* `TauCeti.PowerSeries.IsMulDistinguished.dvd_of_mul_eq` and
  `TauCeti.PowerSeries.IsMulDistinguished.coe_divByMonic_eq_of_mul_eq`: for a polynomial `p`,
  the polynomial factor divides `p` and the unit factor is `p /ₘ ω`.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27 and Corollary 1.28.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, and §5.2.2.
-/

public section

namespace TauCeti.PowerSeries.IsMulDistinguished

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {s : ℕ}
  {e : PowerSeries.IsRestricted.subring (R := R) c} {ω : Polynomial R}

section Series

variable {g : PowerSeries R}

omit [IsUltrametricDist R] in
/-- The polynomial `X ^ s - ω`, for `ω` monic of degree `s`, has degree less than `s`. -/
private theorem degree_X_pow_sub_lt [Nontrivial R] (hω : ω.IsMonicOfDegree s) :
    (Polynomial.X ^ s - ω : Polynomial R).degree < s :=
  (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun m hm ↦ by
    rw [Polynomial.coeff_sub, (Polynomial.isMonicOfDegree_X_pow R s).coeff_eq hω hm, sub_self]

/-- If `e * ω = g` and `e * v = 1`, then `X ^ s = g * v + (X ^ s - ω)`. -/
private theorem mul_add_X_pow_sub_eq {v : PowerSeries.IsRestricted.subring (R := R) c}
    (hv : e * v = 1) (h : (e : PowerSeries R) * (ω : PowerSeries R) = g) :
    g * (v : PowerSeries R) + ((Polynomial.X ^ s - ω : Polynomial R) : PowerSeries R) =
      ((Polynomial.X ^ s : Polynomial R) : PowerSeries R) := by
  have hv' : (e : PowerSeries R) * (v : PowerSeries R) = 1 := by exact_mod_cast hv
  rw [← h, Polynomial.coe_sub]
  linear_combination (ω : PowerSeries R) * hv'

/-- **The polynomial factor of a Weierstrass factorization is a Weierstrass polynomial.** Over an
ultrametric normed commutative ring, if a series `g` multiplicatively distinguished of degree `s`
at a radius `c > 0` is `e * ω`, with `e` a unit of the ring of series restricted at `c` and `ω`
a monic polynomial of degree `s`, then `ω` is multiplicatively distinguished of degree `s`, that
is, has Gauss norm `c ^ s` (`TauCeti.PowerSeries.isMulDistinguished_iff_gaussNorm_eq`). The
coefficient ring need not be complete. -/
theorem isMulDistinguished_of_mul_eq (hg : IsMulDistinguished c s g) (hc : 0 < c)
    (he : IsUnit e) (hω : ω.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g) :
    IsMulDistinguished c s (ω : PowerSeries R) := by
  have : Nontrivial R := hg.nontrivial
  have : NormOneClass R := hg.normOneClass
  obtain ⟨v, hv⟩ := he.exists_right_inv
  have hXs : ((Polynomial.X ^ s : Polynomial R) : PowerSeries R).gaussNorm norm c = c ^ s := by
    simpa using gaussNorm_X_sub_C_pow hc.le (a := (0 : R)) (by simpa using hc.le) s
  -- `X ^ s = g * v + (X ^ s - ω)`, so the norm identity bounds `‖X ^ s - ω‖` by `‖X ^ s‖ = c ^ s`.
  have hmax := hg.gaussNorm_mul_add_eq_max hc v.property fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp (degree_X_pow_sub_lt hω) m hm
  rw [mul_add_X_pow_sub_eq hv h, hXs] at hmax
  have hle : ((Polynomial.X ^ s - ω : Polynomial R) : PowerSeries R).gaussNorm norm c ≤ c ^ s := by
    rw [hmax]
    exact le_max_right _ _
  -- Hence `ω = X ^ s - (X ^ s - ω)` has Gauss norm at most `c ^ s`, the least possible value.
  rw [isMulDistinguished_iff_gaussNorm_eq hc hω]
  refine le_antisymm ?_ (pow_le_gaussNorm_of_isMonicOfDegree hω)
  -- The two Gauss-norm hypotheses are stated with their types to keep elaboration fast.
  have hsub : (((Polynomial.X ^ s : Polynomial R) : PowerSeries R) -
      ((Polynomial.X ^ s - ω : Polynomial R) : PowerSeries R)).gaussNorm norm c ≤ c ^ s :=
    have h1 : ((Polynomial.X ^ s : Polynomial R) : PowerSeries R).HasGaussNorm norm c :=
      hasGaussNorm_of_isRestricted (isRestricted_polynomial _)
    have h2 : ((Polynomial.X ^ s - ω : Polynomial R) : PowerSeries R).HasGaussNorm norm c :=
      hasGaussNorm_of_isRestricted (isRestricted_polynomial _)
    gaussNorm_sub_le_of_le hc.le h1 h2 hXs.le hle
  rwa [← Polynomial.coe_sub, sub_sub_cancel] at hsub

/-- Weierstrass division of a polynomial `p = e * ω` by its polynomial factor `ω`: the
polynomial division `p = ω * (p /ₘ ω) + p %ₘ ω` and `p = ω * e + 0` are both Weierstrass
divisions by `ω`, so they agree. -/
private theorem coe_divByMonic_eq_and_modByMonic_eq_zero {p : Polynomial R}
    (hg : IsMulDistinguished c s (p : PowerSeries R)) (hc : 0 < c) (he : IsUnit e)
    (hω : ω.IsMonicOfDegree s) (h : (e : PowerSeries R) * (ω : PowerSeries R) = p) :
    ((p /ₘ ω : Polynomial R) : PowerSeries R) = e ∧ p %ₘ ω = 0 := by
  have : Nontrivial R := hg.nontrivial
  have hdeg : (p %ₘ ω).degree < s := by
    simpa [Polynomial.degree_eq_natDegree hω.ne_zero, hω.natDegree_eq] using
      Polynomial.degree_modByMonic_lt p hω.monic
  have hr : ∀ m, s ≤ m → ((p %ₘ ω : Polynomial R) : PowerSeries R).coeff m = 0 := fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp hdeg m hm
  have hdiv : (ω : PowerSeries R) * ((p /ₘ ω : Polynomial R) : PowerSeries R) +
      ((p %ₘ ω : Polynomial R) : PowerSeries R) = (ω : PowerSeries R) * e + 0 := by
    rw [← Polynomial.coe_mul, ← Polynomial.coe_add, add_comm, Polynomial.modByMonic_add_div,
      add_zero, mul_comm, h]
  obtain ⟨hq, hr0⟩ :=
    (hg.isMulDistinguished_of_mul_eq hc he hω h).eq_and_eq_of_mul_add_eq_mul_add hc
      (isRestricted_polynomial (p /ₘ ω)) e.property
      hr (fun _ _ ↦ by simp) hdiv
  exact ⟨hq, Polynomial.coe_eq_zero_iff.mp hr0⟩

/-- **The unit factor of a prepared polynomial is a polynomial.** Over an ultrametric normed
commutative ring, let a polynomial `p` be multiplicatively distinguished of degree `s` at a
radius `c > 0`, and let `p = e * ω` with `e` a unit of the ring of series restricted at `c` and
`ω` a monic polynomial of degree `s`. Then `e` is the polynomial `p /ₘ ω`. -/
theorem coe_divByMonic_eq_of_mul_eq {p : Polynomial R}
    (hg : IsMulDistinguished c s (p : PowerSeries R)) (hc : 0 < c) (he : IsUnit e)
    (hω : ω.IsMonicOfDegree s) (h : (e : PowerSeries R) * (ω : PowerSeries R) = p) :
    ((p /ₘ ω : Polynomial R) : PowerSeries R) = e :=
  (coe_divByMonic_eq_and_modByMonic_eq_zero hg hc he hω h).1

/-- **The polynomial factor of a prepared polynomial divides it.** Over an ultrametric normed
commutative ring, let a polynomial `p` be multiplicatively distinguished of degree `s` at a
radius `c > 0`, and let `p = e * ω` with `e` a unit of the ring of series restricted at `c` and
`ω` a monic polynomial of degree `s`. Then `ω` divides `p` in `R[X]`. -/
theorem dvd_of_mul_eq {p : Polynomial R} (hg : IsMulDistinguished c s (p : PowerSeries R))
    (hc : 0 < c) (he : IsUnit e) (hω : ω.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = p) : ω ∣ p :=
  (Polynomial.modByMonic_eq_zero_iff_dvd hω.monic).mp
    (coe_divByMonic_eq_and_modByMonic_eq_zero hg hc he hω h).2

end Series

section Subring

variable [CompleteSpace R] {g : PowerSeries.IsRestricted.subring (R := R) c}
  (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)

include hg hc

/-- The pair `(e⁻¹, X ^ s - ω)` is the Weierstrass division of `X ^ s` by `g = e * ω`. -/
private theorem weierstrassDiv_X_pow_eq_and_weierstrassMod_X_pow_eq
    {v : PowerSeries.IsRestricted.subring (R := R) c} (hv : e * v = 1)
    (hω : ω.IsMonicOfDegree s) (h : (e : PowerSeries R) * (ω : PowerSeries R) = g) :
    hg.weierstrassDiv hc (polynomialToRestricted c (Polynomial.X ^ s)) = v ∧
      hg.weierstrassMod hc (polynomialToRestricted c (Polynomial.X ^ s)) =
        Polynomial.X ^ s - ω := by
  have : Nontrivial R := hg.nontrivial
  refine (hg.weierstrassDiv_eq_and_weierstrassMod_eq_iff hc (degree_X_pow_sub_lt hω)).mpr
    (Subtype.ext ?_)
  simpa using mul_add_X_pow_sub_eq hv h

/-- **The Weierstrass polynomial is `X ^ s` minus a remainder.** Over a complete ultrametric
normed commutative ring, let `g` be restricted and multiplicatively distinguished of degree `s`
at a radius `c > 0`, and let `g = e * ω` with `e` a unit of the ring of series restricted at `c`
and `ω` a monic polynomial of degree `s`. Then `ω = X ^ s - b`, where `b` is the Weierstrass
remainder of `X ^ s` on division by `g`. -/
theorem eq_X_pow_sub_weierstrassMod_of_mul_eq (he : IsUnit e) (hω : ω.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g) :
    ω = Polynomial.X ^ s - hg.weierstrassMod hc (polynomialToRestricted c (Polynomial.X ^ s)) := by
  obtain ⟨v, hv⟩ := he.exists_right_inv
  rw [(weierstrassDiv_X_pow_eq_and_weierstrassMod_X_pow_eq hg hc hv hω h).2, sub_sub_cancel]

/-- **The Weierstrass quotient of `X ^ s` inverts the unit factor.** Over a complete ultrametric
normed commutative ring, let `g` be restricted and multiplicatively distinguished of degree `s`
at a radius `c > 0`, and let `g = e * ω` with `e` a unit of the ring of series restricted at `c`
and `ω` a monic polynomial of degree `s`. Then `e` times the Weierstrass quotient of `X ^ s` by
`g` is `1`. -/
theorem mul_weierstrassDiv_X_pow_eq_one_of_mul_eq (he : IsUnit e) (hω : ω.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g) :
    e * hg.weierstrassDiv hc (polynomialToRestricted c (Polynomial.X ^ s)) = 1 := by
  obtain ⟨v, hv⟩ := he.exists_right_inv
  rw [(weierstrassDiv_X_pow_eq_and_weierstrassMod_X_pow_eq hg hc hv hω h).1, hv]

/-- Division by `ω` of a decomposition `f = g * q + r` by `g = e * ω`: it is
`f = ω * (e * q) + r`. -/
private theorem weierstrassDiv_eq_and_weierstrassMod_eq_of_mul_eq
    (hω' : IsMulDistinguished c s (polynomialToRestricted c ω : PowerSeries R))
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g)
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    hω'.weierstrassDiv hc f = e * hg.weierstrassDiv hc f ∧
      hω'.weierstrassMod hc f = hg.weierstrassMod hc f := by
  refine (hω'.weierstrassDiv_eq_and_weierstrassMod_eq_iff hc
    (hg.degree_weierstrassMod_lt hc f)).mpr ?_
  have hg' : polynomialToRestricted c ω * e = g := Subtype.ext (by simpa [mul_comm] using h)
  rw [← mul_assoc, hg']
  exact hg.mul_weierstrassDiv_add_weierstrassMod hc f

/-- **Division by the Weierstrass polynomial has the same remainders.** Over a complete
ultrametric normed commutative ring, let `g` be restricted and multiplicatively distinguished of
degree `s` at a radius `c > 0`, and let `g = e * ω` with `e` restricted at `c` and `ω` a polynomial
multiplicatively distinguished of degree `s`. Then every restricted `f` has the same Weierstrass
remainder on division by `ω` as on division by `g`. -/
theorem weierstrassMod_eq_of_mul_eq
    (hω' : IsMulDistinguished c s (polynomialToRestricted c ω : PowerSeries R))
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g)
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    hω'.weierstrassMod hc f = hg.weierstrassMod hc f :=
  (weierstrassDiv_eq_and_weierstrassMod_eq_of_mul_eq hg hc hω' h f).2

/-- **The quotients of division by `g` and by its Weierstrass polynomial.** Over a complete
ultrametric normed commutative ring, let `g` be restricted and multiplicatively distinguished of
degree `s` at a radius `c > 0`, and let `g = e * ω` with `e` restricted at `c` and `ω` a polynomial
multiplicatively distinguished of degree `s`. Then the Weierstrass quotient of every restricted
`f` by `ω` is `e` times its Weierstrass quotient by `g`. -/
theorem weierstrassDiv_eq_mul_of_mul_eq
    (hω' : IsMulDistinguished c s (polynomialToRestricted c ω : PowerSeries R))
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g)
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    hω'.weierstrassDiv hc f = e * hg.weierstrassDiv hc f :=
  (weierstrassDiv_eq_and_weierstrassMod_eq_of_mul_eq hg hc hω' h f).1

end Subring

end TauCeti.PowerSeries.IsMulDistinguished
