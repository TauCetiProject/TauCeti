/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Degree.IsMonicOfDegree
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Division
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Preparation

/-!
# Coefficient maps and Weierstrass theory in several variables

Let `φ : R →+* S` be a bounded homomorphism of ultrametric normed commutative rings,
`‖φ a‖ ≤ C ‖a‖`, and let `c : Option σ → ℝ` be positive polyradii. Then `φ` acts coefficientwise
on restricted series at `c` (`TauCeti.MvPowerSeries.restrictedMap`), and this action commutes with
separating the variable `X none`: on iterated series it is the coefficientwise action of the
induced map `R{X/(c ∘ some)} →+* S{X/(c ∘ some)}` of coefficient rings
(`MvPowerSeries.coe_restrictedOptionEquiv_restrictedMap`).

This file shows that the coefficient map commutes with Weierstrass division and preparation in
the separated variable. Suppose the iterated series of the image `restrictedMap φ hφ g` of a
divisor `g` is multiplicatively distinguished of degree `s` at the radius `c none`. Then:

* if `f = g * q + r` with `r` of degree less than `s` in `X none`, the image of `(q, r)` is the
  Weierstrass division of the image of `f` by the image of `g`;
* if `g = e * ω` with `e` a unit and `ω` a monic polynomial of degree `s` in `X none`, the image
  of `(e, ω)` is the Weierstrass preparation of the image of `g`. Over a complete target, the
  image of `e` is therefore a multiplicative unit and the image of `ω` has Gauss norm
  `c none ^ s`, although a bounded homomorphism need not preserve multiplicative units in general.

These comparisons use only uniqueness of division and preparation over `S`. They need neither a
distinguishedness hypothesis over `R`, nor injectivity of `φ`, nor completeness of `R`. A
bounded homomorphism need not preserve distinguishedness or the distinguished degree. When `φ`
preserves norms, for instance for an isometric extension of complete ultrametric fields, it does:
`TauCeti.MvPowerSeries.isMulDistinguished_restrictedOptionEquiv_restrictedMap`.

## Main results

* `TauCeti.MvPowerSeries.eq_and_eq_restrictedMap_of_mul_add_eq_of_isMulDistinguished`: bounded
  coefficient maps commute with Weierstrass division in several variables.
* `TauCeti.MvPowerSeries.eq_and_eq_restrictedMap_of_mul_eq_of_isMulDistinguished` and
  `TauCeti.MvPowerSeries.isNormMulUnit_restrictedMap_and_norm_eq_of_mul_eq_of_isMulDistinguished`:
  bounded coefficient maps commute with Weierstrass preparation in several variables, including
  its normalisations.
* `TauCeti.MvPowerSeries.isMulDistinguished_restrictedOptionEquiv_restrictedMap`: norm-preserving
  coefficient maps preserve multiplicative distinguishedness in the separated variable.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27, Corollary 1.28 and the remark following it, for
  the several-variable division and preparation theorems whose uniqueness gives these
  compatibilities.
* `TauCeti/RingTheory/PowerSeries/Weierstrass/Map.lean`, the one-variable formalization that
  this file follows. Its division comparisons are `IsMulDistinguished.map_weierstrassDiv` and
  `IsMulDistinguished.map_weierstrassMod`, its preparation comparison is
  `IsMulDistinguished.eq_and_eq_map_of_mul_eq_map_mul`, and its preparation normalizations are
  `IsMulDistinguished.isNormMulUnit_restrictedMap_and_gaussNorm_map_eq_of_mul_eq`, all in the
  namespace `TauCeti.PowerSeries`.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedCommRing S]
  [IsUltrametricDist S] {c : Option σ → ℝ} [∀ i, Fact (0 < c i)] {s : ℕ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)

local notation "Inner" => IsRestricted.subring (R := R) (fun i : σ ↦ c (some i))
local notation "Flat" => IsRestricted.subring (R := R) c
local notation "Inner'" => IsRestricted.subring (R := S) (fun i : σ ↦ c (some i))
local notation "Flat'" => IsRestricted.subring (R := S) c

section Division

/-- **Bounded coefficient maps commute with Weierstrass division in several variables.** Let the
iterated series of the image of `g` in the separated variable `X none` be multiplicatively
distinguished of degree `s`. If `f = g * q + r` with `r` of degree less than `s` in `X none`, and
the image of `f` is `restrictedMap φ hφ g * q' + r'` with `r'` of degree less than `s` in
`X none`, then `q'` and `r'` are the images of `q` and `r`. -/
theorem eq_and_eq_restrictedMap_of_mul_add_eq_of_isMulDistinguished {g f q r : Flat}
    (hg' : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv (restrictedMap φ hφ g) : PowerSeries Inner'))
    (hr : ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r : MvPowerSeries (Option σ) R) = 0)
    (hf : g * q + r = f) {q' r' : Flat'}
    (hr' : ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r' : MvPowerSeries (Option σ) S) = 0)
    (h : restrictedMap φ hφ g * q' + r' = restrictedMap φ hφ f) :
    q' = restrictedMap φ hφ q ∧ r' = restrictedMap φ hφ r :=
  eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished hg' hr'
    (fun t ht ↦ by rw [coeff_restrictedMap, hr t ht, map_zero])
    (by rw [h, ← hf, map_add, map_mul])

end Division

section Preparation

/-- **Bounded coefficient maps commute with Weierstrass preparation in several variables.** Let
the iterated series of the image of `g` in the separated variable `X none` be multiplicatively
distinguished of degree `s`. If `g = e * ω` with `e` a unit and `ω` a polynomial in `X none`
monic of degree `s`, and the image of `g` is `e' * ω'` with `e'` a unit and `ω'` monic of degree
`s`, then `e'` and `ω'` are the images of `e` and `ω`. No normalisation of the polynomial factors
is assumed. -/
theorem eq_and_eq_restrictedMap_of_mul_eq_of_isMulDistinguished {g e : Flat}
    {ω : Polynomial Inner}
    (hg' : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv (restrictedMap φ hφ g) : PowerSeries Inner'))
    (he : IsUnit e) (hω : ω.IsMonicOfDegree s)
    (h : e * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω) = g)
    {e' : Flat'} {ω' : Polynomial Inner'} (he' : IsUnit e') (hω' : ω'.IsMonicOfDegree s)
    (h' : e' * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω') =
      restrictedMap φ hφ g) :
    e' = restrictedMap φ hφ e ∧ ω' = ω.map (restrictedMap φ hφ) := by
  have : Nontrivial Inner' := hg'.nontrivial
  exact eq_and_eq_of_mul_eq_of_mul_eq_of_isMulDistinguished hg' he' (he.map _) hω' (hω.map _) h'
    (by rw [← restrictedMap_restrictedOptionEquiv_symm_polynomialToRestricted, ← map_mul, h])

/-- **The image of a prepared factorization is prepared.** Over a complete target, let the
iterated series of the image of `g` in the separated variable `X none` be multiplicatively
distinguished of degree `s`. If `g = e * ω` with `e` a unit and `ω` a polynomial in `X none`
monic of degree `s`, then the image of `e` is a multiplicative unit and the image of `ω` has
Gauss norm `c none ^ s`: these images are the normalised factors of Weierstrass preparation of
the image of `g`. -/
theorem isNormMulUnit_restrictedMap_and_norm_eq_of_mul_eq_of_isMulDistinguished
    [CompleteSpace S] {g e : Flat} {ω : Polynomial Inner}
    (hg' : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv (restrictedMap φ hφ g) : PowerSeries Inner'))
    (he : IsUnit e) (hω : ω.IsMonicOfDegree s)
    (h : e * restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none) ω) = g) :
    IsNormMulUnit (restrictedMap φ hφ e) ∧
      ‖(restrictedOptionEquiv.symm (PowerSeries.polynomialToRestricted (c none)
          (ω.map (restrictedMap φ hφ))) : Flat')‖ = c none ^ s := by
  obtain ⟨e', ω', he', hω', hn, h'⟩ :=
    exists_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished hg'
  obtain ⟨rfl, rfl⟩ := eq_and_eq_restrictedMap_of_mul_eq_of_isMulDistinguished φ hφ hg' he hω h
    he'.isUnit hω' h'
  exact ⟨he', hn⟩

end Preparation

/-- **Norm-preserving coefficient maps preserve distinguishedness in several variables.** If
`‖φ a‖ = ‖a‖` for every `a` and the iterated series of `g` in the separated variable `X none` is
multiplicatively distinguished of degree `s`, so is the iterated series of its image. This
supplies the hypothesis of the comparisons above, for instance for an isometric extension of
complete ultrametric fields. -/
theorem isMulDistinguished_restrictedOptionEquiv_restrictedMap (hφ' : ∀ a, ‖φ a‖ = ‖a‖)
    {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner)) :
    PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv (restrictedMap φ hφ g) : PowerSeries Inner') := by
  rw [MvPowerSeries.coe_restrictedOptionEquiv_restrictedMap]
  exact hg.map _ (norm_restrictedMap φ hφ hφ')

end TauCeti.MvPowerSeries
