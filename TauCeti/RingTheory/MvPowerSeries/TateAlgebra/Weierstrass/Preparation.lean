/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Weierstrass preparation in several variables over Banach rings

Let `R` be a complete ultrametric normed commutative ring and let `c : Option σ → ℝ` be positive
polyradii. Separating the variable `X none` identifies restricted series in `Option σ` at `c`
with univariate series restricted at the radius `c none` over the ring `R{X/(c ∘ some)}` of
restricted series in the remaining variables (`MvPowerSeries.restrictedOptionEquiv`), and this
identification preserves the Gauss norms. A polynomial `ω` in the separated variable with
coefficients in `R{X/(c ∘ some)}` is a restricted series in `Option σ` through this
identification.

Suppose that the iterated series of `g` in the separated variable is multiplicatively
distinguished of degree `s` at the radius `c none` (`TauCeti.PowerSeries.IsMulDistinguished`):
its coefficient in degree `s`, a restricted series in the remaining variables, is a
multiplicative unit of `R{X/(c ∘ some)}`, its weighted norm attains the Gauss norm, and every
later weighted coefficient norm is strictly smaller. Then `g` factors as

```text
g = e * ω,    e a multiplicative unit of R{X/c},
              ω monic of degree s in X none,    ‖ω‖ = c none ^ s,
```

and the factorization is unique among units `e` and monic polynomials `ω` of degree `s`. The norm
of `R` need not be multiplicative, and `R` may have nilpotents. This is one-variable preparation
over the coefficient ring `R{X/(c ∘ some)}`, transported along the isometric identification.
Since `e` is a unit, `g` and `ω` generate the same ideal, so quotients of restricted series by
such `g` are quotients by a monic polynomial in `X none`.

## Main results

* `TauCeti.MvPowerSeries.exists_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished`:
  Weierstrass preparation in several variables over a Banach ring, with the normalisation
  `‖ω‖ = c none ^ s` of the polynomial factor.
* `TauCeti.MvPowerSeries.eq_and_eq_of_mul_eq_of_mul_eq_of_isMulDistinguished`: the unit and the
  monic polynomial factor are unique, with no normalisation of the polynomial.
* `TauCeti.MvPowerSeries.existsUnique_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished`:
  the unique-existence form.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Corollary 1.28 and the remark following it, for preparation by a
  multiplicatively distinguished series over a Banach ring and its several-variable form.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1, for the unit-radius
  case over a complete nonarchimedean field.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : Option σ → ℝ}
  [∀ i, Fact (0 < c i)] {s : ℕ}

local notation "Inner" => IsRestricted.subring (R := R) (fun i : σ ↦ c (some i))
local notation "Flat" => IsRestricted.subring (R := R) c

/-- The iterated series of `e * ω`, for a polynomial `ω` in the separated variable, is the
product of the iterated series of `e` with `ω`. -/
private theorem coe_restrictedOptionEquiv_mul_polynomial (e : Flat) (ω : Polynomial Inner) :
    (restrictedOptionEquiv
        (e * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω)) :
      PowerSeries Inner) =
      (restrictedOptionEquiv e : PowerSeries Inner) * (ω : PowerSeries Inner) := by
  rw [map_mul, AlgEquiv.apply_symm_apply, Subring.coe_mul,
    PowerSeries.coe_polynomialToRestricted]

/-- **Weierstrass preparation in several variables over a Banach ring** (Martin, Corollary 1.28,
iterated). Over a complete ultrametric normed commutative ring, let the iterated series of a
restricted series `g` in the separated variable `X none` be multiplicatively distinguished of
degree `s` at the radius `c none`. Then `g` is a multiplicative unit `e` of the ring of
restricted series at `c` times a polynomial `ω` in `X none` with coefficients restricted in the
remaining variables, monic of degree `s`, whose Gauss norm at `c` is `c none ^ s`. The norm of
the coefficient ring need not be multiplicative. The factorization is unique by
`TauCeti.MvPowerSeries.eq_and_eq_of_mul_eq_of_mul_eq_of_isMulDistinguished`. -/
theorem exists_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished [CompleteSpace R]
    {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner)) :
    ∃ (e : Flat) (ω : Polynomial Inner), IsNormMulUnit e ∧ ω.IsMonicOfDegree s ∧
      ‖(restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω) : Flat)‖ =
        c none ^ s ∧
      e * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω) = g := by
  obtain ⟨e, ω, he, hω, hn, heω⟩ :=
    hg.exists_isNormMulUnit_isMonicOfDegree_mul_eq (restrictedOptionEquiv g).2
  refine ⟨restrictedOptionEquiv.symm e, ω, ?_, hω, ?_, ?_⟩
  · -- The identification is norm-preserving, so it reflects multiplicative units.
    refine (MulEquiv.isNormMulUnit_iff (restrictedOptionEquiv (c := c)).toMulEquiv
      norm_restrictedOptionEquiv _).mp ?_
    simpa using he
  · rw [← norm_restrictedOptionEquiv, AlgEquiv.apply_symm_apply, PowerSeries.norm_eq_gaussNorm,
      PowerSeries.coe_polynomialToRestricted]
    exact hn
  · refine restrictedOptionEquiv.injective (Subtype.ext ?_)
    rw [coe_restrictedOptionEquiv_mul_polynomial, AlgEquiv.apply_symm_apply]
    exact heω

/-- **Uniqueness in Weierstrass preparation in several variables over a Banach ring.** Over an
ultrametric normed commutative ring, let the iterated series of `g` in the separated variable
`X none` be multiplicatively distinguished of degree `s` at the radius `c none`. If `g` is
`e * ω = e' * ω'` with `e`, `e'` units of the ring of restricted series at `c` and `ω`, `ω'`
polynomials in `X none`, with coefficients restricted in the remaining variables, monic of degree
`s`, then `e = e'` and `ω = ω'`. No normalisation of the polynomial factors is assumed. -/
theorem eq_and_eq_of_mul_eq_of_mul_eq_of_isMulDistinguished {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner))
    {e e' : Flat} {ω ω' : Polynomial Inner} (he : IsUnit e) (he' : IsUnit e')
    (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : e * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω) = g)
    (h' : e' * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω') = g) :
    e = e' ∧ ω = ω' := by
  have key {e : Flat} {ω : Polynomial Inner}
      (h : e * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω) = g) :
      (restrictedOptionEquiv e : PowerSeries Inner) * (ω : PowerSeries Inner) =
        (restrictedOptionEquiv g : PowerSeries Inner) := by
    rw [← coe_restrictedOptionEquiv_mul_polynomial, h]
  obtain ⟨he_eq, hω_eq⟩ := hg.eq_and_eq_of_mul_eq_of_mul_eq Fact.out
    (he.map restrictedOptionEquiv) (he'.map restrictedOptionEquiv) hω hω' (key h) (key h')
  exact ⟨restrictedOptionEquiv.injective he_eq, hω_eq⟩

/-- **Weierstrass preparation in several variables over a Banach ring**, in its unique-existence
form: over a complete ultrametric normed commutative ring, if the iterated series of `g` in the
separated variable `X none` is multiplicatively distinguished of degree `s` at the radius
`c none`, then `g` is in exactly one way a multiplicative unit of the ring of restricted series at
`c` times a polynomial in `X none`, with coefficients restricted in the remaining variables, monic
of degree `s` and of Gauss norm `c none ^ s`. -/
theorem existsUnique_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished
    [CompleteSpace R] {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner)) :
    ∃! p : Flat × Polynomial Inner, IsNormMulUnit p.1 ∧ p.2.IsMonicOfDegree s ∧
      ‖(restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) p.2) : Flat)‖ =
        c none ^ s ∧
      p.1 * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) p.2) = g := by
  obtain ⟨e, ω, he, hω, hn, heω⟩ :=
    exists_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished hg
  refine ⟨(e, ω), ⟨he, hω, hn, heω⟩, fun p ⟨hp1, hp2, _, hp4⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq_of_mul_eq_of_isMulDistinguished hg hp1.isUnit he.isUnit
    hp2 hω hp4 heω
  exact Prod.ext h1 h2

end TauCeti.MvPowerSeries
