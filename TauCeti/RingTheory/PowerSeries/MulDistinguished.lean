/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Monoid.MulUnit
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Multiplicatively distinguished power series

A power series `g` is *multiplicatively distinguished of degree `s`* at the radius `c` when it is
distinguished of degree `s` in the sense of `TauCeti.PowerSeries.IsDistinguished` and its
coefficient in degree `s` is a multiplicative unit (`TauCeti.IsNormMulUnit`): an invertible
element by which left multiplication scales every norm exactly.

This is the divisor hypothesis of Weierstrass division and preparation over an ultrametric
Banach ring whose norm need not be multiplicative, such as a coefficient ring with nilpotents.
Its basic consequence is the multiplication estimate: multiplying a restricted series `q` by such
a `g` on the left loses no norm, `‖g * q‖ = ‖g‖ * ‖q‖`, and if `q` is distinguished of degree
`k` then `g * q` is distinguished of degree `s + k`. No multiplicativity of the norm of `R` is
assumed. When the norm of `R` is multiplicative, the extra condition says only that the
distinguished coefficient is a unit.

## Main definitions

* `TauCeti.PowerSeries.IsMulDistinguished`: `g` is distinguished of degree `s` at `c`, and its
  coefficient in degree `s` is a multiplicative unit.

## Main results

* `TauCeti.PowerSeries.isMulDistinguished_iff_isUnit`: over a ring with multiplicative norm, a
  series is multiplicatively distinguished exactly when it is distinguished with invertible
  distinguished coefficient.
* `TauCeti.PowerSeries.IsMulDistinguished.isDistinguished_mul`: left multiplication by a
  multiplicatively distinguished series of degree `s` raises distinguished degrees by `s`.
* `TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_mul`: left multiplication by a
  multiplicatively distinguished series multiplies the Gauss norm of a restricted series by the
  Gauss norm of the divisor.
* `TauCeti.PowerSeries.isMulDistinguished_monomial` and
  `TauCeti.PowerSeries.isMulDistinguished_X_sub_C`: monomials with multiplicative-unit
  coefficient, and `X - b` for `b` in the closed disc of radius `c`.
* `TauCeti.PowerSeries.isMulDistinguished_iff_gaussNorm_eq`: a monic polynomial of degree `s` is
  multiplicatively distinguished of degree `s` at `c` exactly when its Gauss norm is `c ^ s`.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Definition 1.24, Lemma 1.26 and Corollary 1.28.
-/

public section

namespace TauCeti.PowerSeries

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {s k : ℕ} {g q : PowerSeries R}

variable (c s g) in
/-- `g` is **multiplicatively distinguished of degree `s`** at the radius `c` when it is
distinguished of degree `s` at `c` and its coefficient in degree `s` is a multiplicative unit.

The first condition says that the Gauss norm of `g` at `c` is attained in degree `s` and that
every later weighted coefficient norm is strictly smaller; earlier coefficients may tie. The
second makes left multiplication by `g` lose no norm, without any multiplicativity assumption on
the norm of the coefficient ring. -/
structure IsMulDistinguished : Prop extends IsDistinguished c s g where
  /-- The coefficient in the distinguished degree is a multiplicative unit. -/
  isNormMulUnit_coeff : IsNormMulUnit (g.coeff s)

/-- A series is multiplicatively distinguished exactly when it is distinguished and its
coefficient in the distinguished degree is a multiplicative unit. -/
theorem isMulDistinguished_iff :
    IsMulDistinguished c s g ↔ IsDistinguished c s g ∧ IsNormMulUnit (g.coeff s) :=
  ⟨fun h ↦ ⟨h.toIsDistinguished, h.isNormMulUnit_coeff⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Over a ring with multiplicative norm, a series is multiplicatively distinguished exactly when
it is distinguished and its coefficient in the distinguished degree is a unit. -/
theorem isMulDistinguished_iff_isUnit [NormMulClass R] :
    IsMulDistinguished c s g ↔ IsDistinguished c s g ∧ IsUnit (g.coeff s) := by
  rw [isMulDistinguished_iff, isNormMulUnit_iff_isUnit]

/-- The coefficient ring of a multiplicatively distinguished series is nontrivial. -/
theorem IsMulDistinguished.nontrivial (hg : IsMulDistinguished c s g) : Nontrivial R :=
  nontrivial_of_ne _ _ hg.coeff_ne_zero

/-- The truncation of a multiplicatively distinguished series just past its distinguished degree
is again multiplicatively distinguished of that degree. -/
theorem IsMulDistinguished.trunc (hg : IsMulDistinguished c s g) :
    IsMulDistinguished c s ((g.trunc (s + 1) : Polynomial R) : PowerSeries R) := by
  refine ⟨hg.toIsDistinguished.trunc, ?_⟩
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left (Nat.lt_succ_self s)]
  exact hg.isNormMulUnit_coeff

/-- A linear polynomial `X - b` whose root lies in the closed disc of radius `c > 0` is
multiplicatively distinguished of degree `1` at `c`, over a norm-one ring. The constant term may
have the same weighted norm as the leading one. -/
theorem isMulDistinguished_X_sub_C [NormOneClass R] (hc : 0 < c) {b : R} (hb : ‖b‖ ≤ c) :
    IsMulDistinguished c 1 (PowerSeries.X - PowerSeries.C b) :=
  ⟨isDistinguished_X_sub_C hc hb, by simp⟩

variable [IsUltrametricDist R]

/-- **Distinguished degrees under multiplication by a multiplicatively distinguished series.**
If `g` is multiplicatively distinguished of degree `s` and `q` is distinguished of degree `k` at
a positive radius, then `g * q` is distinguished of degree `s + k`. -/
theorem IsMulDistinguished.isDistinguished_mul (hg : IsMulDistinguished c s g)
    (hq : IsDistinguished c k q) (hc : 0 < c) : IsDistinguished c (s + k) (g * q) :=
  hg.toIsDistinguished.mul hq hc (hg.isNormMulUnit_coeff.norm_mul _)

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {s : ℕ} {g q : PowerSeries R}

/-- The norm of the coefficient ring of a multiplicatively distinguished series takes the value
`1` at `1`, since the distinguished coefficient is a nonzero multiplicative unit. -/
theorem IsMulDistinguished.normOneClass (hg : IsMulDistinguished c s g) : NormOneClass R :=
  ⟨NormedRing.norm_one_of_norm_mul (norm_ne_zero_iff.mpr hg.coeff_ne_zero)
    hg.isNormMulUnit_coeff.norm_mul⟩

/-- A monomial whose coefficient is a multiplicative unit is multiplicatively distinguished of
its degree at a positive radius, over a nontrivial ring. -/
theorem isMulDistinguished_monomial [Nontrivial R] (hc : 0 < c) {a : R} (ha : IsNormMulUnit a)
    (n : ℕ) : IsMulDistinguished c n (PowerSeries.monomial n a) :=
  ⟨isDistinguished_monomial hc ha.isUnit.ne_zero n, by
    rwa [PowerSeries.coeff_monomial_same]⟩

/-- **Weierstrass polynomials at a radius.** Over a norm-one ring, a monic polynomial of degree `s`
is multiplicatively distinguished of degree `s` at a positive radius `c` exactly when its Gauss
norm at `c` is `c ^ s`, the weighted norm of its leading term. This is the normalisation of the
polynomial factor in Weierstrass preparation. Lower coefficients may tie with the leading one, as
for `X - 1` at the radius `1`. -/
theorem isMulDistinguished_iff_gaussNorm_eq [NormOneClass R] (hc : 0 < c) {p : Polynomial R}
    (hp : p.IsMonicOfDegree s) :
    IsMulDistinguished c s (p : PowerSeries R) ↔ (p : PowerSeries R).gaussNorm norm c = c ^ s := by
  have hs := hp.coeff_coe_self
  refine ⟨fun h ↦ by rw [← h.norm_coeff_mul_pow_eq, hs, norm_one, one_mul], fun h ↦
    ⟨isDistinguished_of_isMonicOfDegree hc hp fun k _ ↦ ?_, by rw [hs]; exact isNormMulUnit_one⟩⟩
  rw [← h, ← Polynomial.coeff_coe]
  exact PowerSeries.le_gaussNorm norm c _
    (hasGaussNorm_of_isRestricted (isRestricted_polynomial p)) k

variable [IsUltrametricDist R]

/-- **The multiplication estimate.** Left multiplication by a multiplicatively distinguished
series multiplies the Gauss norm of a restricted series by the Gauss norm of the divisor, at
a positive radius:

```text
‖g * q‖ = ‖g‖ * ‖q‖.
```

No multiplicativity of the norm of the coefficient ring is assumed. -/
theorem IsMulDistinguished.gaussNorm_mul (hg : IsMulDistinguished c s g) (hc : 0 < c)
    (hq : q.IsRestricted c) :
    (g * q).gaussNorm norm c = g.gaussNorm norm c * q.gaussNorm norm c := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  obtain ⟨k, hk⟩ := exists_isDistinguished hc hq hq0
  exact hg.toIsDistinguished.gaussNorm_mul hk hc (hg.isNormMulUnit_coeff.norm_mul _)

end NormedRing

end TauCeti.PowerSeries
