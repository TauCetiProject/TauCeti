/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.MulDistinguished
import Mathlib.Algebra.Polynomial.Monic

/-!
# Weierstrass polynomials

A *Weierstrass polynomial* of degree `s` at a radius `c > 0` is a monic polynomial `p` of degree
`s` which, read as a restricted power series, is distinguished of degree `s` at `c`
(`TauCeti.PowerSeries.IsDistinguished`). These are the polynomials produced by Weierstrass
preparation, and the divisors for which Weierstrass division of restricted series reduces to
polynomial division with remainder.

This file characterises Weierstrass polynomials by their coefficients and by their Gauss norm:
`p` is one exactly when every weighted coefficient `‖pₖ‖ cᵏ` is at most `cˢ`, the weight of the
leading term, or equivalently when the Gauss norm of `p` at `c` is `cˢ`. At the unit radius these
say that every coefficient of `p` has norm at most one, and that `p` has Gauss norm one.

Over a ring with an ultrametric norm, Weierstrass polynomials are closed under products
(`TauCeti.PowerSeries.IsDistinguished.mul`). If the norm is also multiplicative, as for a Tate
algebra over a complete nonarchimedean field, they are closed under taking monic factors: a monic
polynomial of degree `s` has Gauss norm at least `cˢ`, so a product of two monic polynomials has
Gauss norm `cˢ` exactly when both factors do. Multiplicativity of the norm cannot be dropped here.
Over the dual numbers `K[ε]` of a nonarchimedean field `K`, with the norm
`‖x + yε‖ = max ‖x‖ (C ‖y‖)` for some `C > 1`, the product `(X - ε) * (X + ε) = X ^ 2` is a
Weierstrass polynomial at the unit radius, but `X - ε` is not.

## Main results

* `TauCeti.PowerSeries.isDistinguished_iff_of_isMonicOfDegree`: a monic polynomial of degree `s`
  is distinguished of degree `s` at `c > 0` iff `‖pₖ‖ cᵏ ≤ cˢ` for every `k < s`.
* `TauCeti.PowerSeries.pow_le_gaussNorm_of_isMonicOfDegree`: a monic polynomial of degree `s` has
  Gauss norm at least `cˢ`.
* `TauCeti.PowerSeries.isDistinguished_iff_gaussNorm_eq_of_isMonicOfDegree`: it is distinguished
  of degree `s` iff its Gauss norm is `cˢ`.
* `TauCeti.PowerSeries.isDistinguished_one_iff_of_isMonicOfDegree`: at the unit radius, it is
  distinguished iff all its coefficients have norm at most one.
* `TauCeti.PowerSeries.isDistinguished_mul_iff_of_isMonicOfDegree`: for a multiplicative
  ultrametric norm, a product of monic polynomials is a Weierstrass polynomial iff both factors
  are.
* `TauCeti.PowerSeries.IsDistinguished.of_dvd`: for a multiplicative ultrametric norm, every monic
  factor of a Weierstrass polynomial is a Weierstrass polynomial.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1 (Weierstrass polynomials) and
  §5.2.6.
-/

public section

namespace TauCeti.PowerSeries

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [NormOneClass R] {c : ℝ} {s : ℕ} {p : Polynomial R}

/-- A monic polynomial of degree `s` is distinguished of degree `s` at a radius `c > 0` iff each of
its lower weighted coefficients `‖pₖ‖ cᵏ` is at most `cˢ`, the weight of its leading term. -/
theorem isDistinguished_iff_of_isMonicOfDegree (hc : 0 < c) (hp : p.IsMonicOfDegree s) :
    IsDistinguished c s (p : PowerSeries R) ↔ ∀ k < s, ‖p.coeff k‖ * c ^ k ≤ c ^ s := by
  refine ⟨fun h k _ ↦ ?_, isDistinguished_of_isMonicOfDegree hc hp⟩
  have hnorm := h.norm_coeff_mul_pow_eq
  rw [hp.coeff_coe_self, norm_one, one_mul] at hnorm
  simpa [hnorm] using PowerSeries.le_gaussNorm norm c _ h.hasGaussNorm k

/-- At the unit radius, a monic polynomial of degree `s` is distinguished of degree `s` iff all of
its coefficients have norm at most one. -/
theorem isDistinguished_one_iff_of_isMonicOfDegree (hp : p.IsMonicOfDegree s) :
    IsDistinguished 1 s (p : PowerSeries R) ↔ ∀ k, ‖p.coeff k‖ ≤ 1 := by
  rw [isDistinguished_iff_of_isMonicOfDegree one_pos hp]
  refine ⟨fun h k ↦ ?_, fun h k _ ↦ by simpa using h k⟩
  rcases lt_or_ge k s with hk | hk
  · simpa using h k hk
  · have : Nontrivial R := NormOneClass.nontrivial
    rw [hp.coeff_eq (Polynomial.isMonicOfDegree_X_pow (R := R) s) hk, Polynomial.coeff_X_pow]
    split_ifs <;> simp

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [NormOneClass R] {c : ℝ} {s : ℕ} {p : Polynomial R}

/-- A monic polynomial of degree `s` has Gauss norm at least `cˢ` at every radius `c`: its leading
term already has weighted norm `cˢ`. -/
theorem pow_le_gaussNorm_of_isMonicOfDegree (hp : p.IsMonicOfDegree s) :
    c ^ s ≤ (p : PowerSeries R).gaussNorm norm c := by
  simpa [hp.coeff_coe_self] using PowerSeries.le_gaussNorm norm c _
    (hasGaussNorm_of_isRestricted (isRestricted_polynomial p)) s

/-- A monic polynomial of degree `s` is distinguished of degree `s` at a radius `c > 0` iff its
Gauss norm at `c` is `cˢ`. -/
theorem isDistinguished_iff_gaussNorm_eq_of_isMonicOfDegree (hc : 0 < c)
    (hp : p.IsMonicOfDegree s) :
    IsDistinguished c s (p : PowerSeries R) ↔ (p : PowerSeries R).gaussNorm norm c = c ^ s :=
  -- For a monic polynomial the distinguished coefficient is `1`, a multiplicative unit.
  ⟨fun h ↦ (isMulDistinguished_iff_gaussNorm_eq hc hp).mp
      ⟨h, by rw [hp.coeff_coe_self]; exact isNormMulUnit_one⟩,
    fun h ↦ ((isMulDistinguished_iff_gaussNorm_eq hc hp).mpr h).toIsDistinguished⟩

end NormedRing

section NormMulClass

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ} {i j s : ℕ}
  {p q w : Polynomial R}

/-- For a multiplicative ultrametric norm, a product of monic polynomials of degrees `i` and `j` is
distinguished of degree `i + j` at a radius `c > 0` iff each factor is distinguished of its
degree. -/
theorem isDistinguished_mul_iff_of_isMonicOfDegree (hc : 0 < c) (hp : p.IsMonicOfDegree i)
    (hq : q.IsMonicOfDegree j) :
    IsDistinguished c (i + j) ((p : PowerSeries R) * (q : PowerSeries R)) ↔
      IsDistinguished c i (p : PowerSeries R) ∧ IsDistinguished c j (q : PowerSeries R) := by
  refine ⟨fun h ↦ ?_, fun ⟨hpd, hqd⟩ ↦ ?_⟩
  · have : Nontrivial R := nontrivial_of_ne _ _ h.coeff_ne_zero
    have : NormOneClass R := NormMulClass.toNormOneClass
    -- Both factors have Gauss norm at least the weight of their leading term, and the product of
    -- the two Gauss norms is the Gauss norm of the product, which is the product of those weights.
    have hpq : (p : PowerSeries R).gaussNorm norm c * (q : PowerSeries R).gaussNorm norm c =
        c ^ i * c ^ j := by
      rw [← gaussNorm_mul_of_isRestricted hc (isRestricted_polynomial p)
        (isRestricted_polynomial q), ← pow_add, ← Polynomial.coe_mul]
      exact (isDistinguished_iff_gaussNorm_eq_of_isMonicOfDegree hc (hp.mul hq)).mp
        (by rwa [Polynomial.coe_mul])
    have hpi := pow_le_gaussNorm_of_isMonicOfDegree (c := c) hp
    have hqj := pow_le_gaussNorm_of_isMonicOfDegree (c := c) hq
    have hci := pow_pos hc i
    have hcj := pow_pos hc j
    rw [isDistinguished_iff_gaussNorm_eq_of_isMonicOfDegree hc hp,
      isDistinguished_iff_gaussNorm_eq_of_isMonicOfDegree hc hq]
    constructor <;> nlinarith
  · exact hpd.mul hqd hc (norm_mul _ _)

/-- For a multiplicative ultrametric norm, a monic factor `p` of a monic polynomial `w` of degree
`s` which is distinguished of degree `s` at a radius `c > 0` is distinguished of its own degree at
`c`: monic factors of Weierstrass polynomials are Weierstrass polynomials. -/
theorem IsDistinguished.of_dvd (hw : IsDistinguished c s (w : PowerSeries R)) (hc : 0 < c)
    (hwm : w.IsMonicOfDegree s) (hp : p.Monic) (hpw : p ∣ w) :
    IsDistinguished c p.natDegree (p : PowerSeries R) := by
  obtain ⟨q, rfl⟩ := hpw
  have hq : q.Monic := Polynomial.Monic.of_mul_monic_left hp hwm.monic
  have hs : s = p.natDegree + q.natDegree :=
    hwm.natDegree_eq.symm.trans (Polynomial.Monic.natDegree_mul hp hq)
  subst hs
  rw [Polynomial.coe_mul] at hw
  exact ((isDistinguished_mul_iff_of_isMonicOfDegree hc ⟨rfl, hp⟩ ⟨rfl, hq⟩).mp hw).1

end NormMulClass

end TauCeti.PowerSeries
