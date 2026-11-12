/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscreteValuationRing
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.RingTheory.PowerSeries.Active

/-!
# Formal and normed Weierstrass preparation near the unit radius

Let `O` be a local ring with maximal ideal `𝔪`, and let `φ : O →+* R` be a ring homomorphism
into a normed ring which maps `O` into the closed unit ball and `𝔪` into the open unit ball. The
model case is the valuation ring `O = 𝒪[K]` of a nonarchimedean field `K`, with `φ` the inclusion
`O → K`, where the two hypotheses are `Valued.integer.norm_le_one` and
`Valued.integer.mem_maximalIdeal_iff`. Then `φ` maps units of `O` to elements of norm one, so
for `x : O`

```text
‖φ x‖ = 1 ↔ x is a unit,    ‖φ x‖ < 1 ↔ x ∈ 𝔪.
```

A power series `g ∈ O⟦X⟧` has two notions of Weierstrass degree. The *formal* degree is the
order of its reduction modulo `𝔪`: the least index of a unit coefficient. It is the degree of the
distinguished polynomial in Mathlib's ideal-adic preparation theorem
(`PowerSeries.IsWeierstrassFactorization`). The *normed* degree at a radius `r > 0` is the
distinguished degree `TauCeti.PowerSeries.IsDistinguished` of the image series `g.map φ`, the last
index attaining its Gauss norm at `r`, which is the degree of the normed preparation polynomial
at `r`. This file compares the two.

Every series with coefficients in the closed unit ball is restricted at every radius `r` with
`|r| < 1`, but need not be restricted at `r = 1`. If the least unit coefficient of `g` has index
`s`, then for all `r < 1` sufficiently close to one the weighted coefficient `‖φ aₛ‖ rˢ = rˢ` is
the unique dominant one: the finitely many earlier coefficients have norm less than one, and the
later ones are weighted by strictly smaller powers of `r`. Thus the formal degree is the normed
distinguished degree, and also the lowest dominant degree, at those radii. Consequently a formal
Weierstrass factorization `g = P * h` maps to the normed preparation of `g.map φ` at every such
radius: the image of the formal unit `h` is a unit of the ring of series restricted at `r`, and by
uniqueness of normed preparation the image of `P` is the monic preparation polynomial.

At the radius one itself the two notions differ in general. When `g` has a unit coefficient, the
lowest dominant degree of `g.map φ` at radius one is still the formal degree, but its
distinguished degree is the *last* index of a unit coefficient, if there is one. The two agree
exactly when `g` has a single unit coefficient. For example, over `ℤ_p` the series `p + X + X²`
has formal degree one and distinguished degree two at radius one, while `∑ Xⁿ` is a formal unit
which is not restricted at radius one.

No completeness, discreteness or ultrametric hypothesis is needed for the comparison of degrees;
the comparison of factorizations uses the uniqueness theorem of normed preparation, over an
ultrametric ring with multiplicative norm, but no completeness. Over a discrete valuation ring,
a series with μ-invariant zero has a unit coefficient, and the least index of one is its
λ-invariant.

The supporting lemmas need no preparation theory and live in lower modules: the comparison of
norms on `O` (`TauCeti.norm_map_eq_one_of_isUnit`, `TauCeti.norm_map_eq_one_iff_isUnit`,
`TauCeti.norm_map_lt_one_iff_mem_maximalIdeal`) in `TauCeti.Analysis.Normed.Ring.UnitBall`;
restrictedness and units inside the unit disc (`PowerSeries.isRestricted_map_of_abs_lt_one`,
`TauCeti.PowerSeries.isUnit_mk_map`), which need no local ring, in
`TauCeti.RingTheory.PowerSeries.TateAlgebra`; and the persistence of a lowest dominant degree as
the unique dominant degree just inside its radius
(`TauCeti.PowerSeries.IsLowestDominant.eventually_isDistinguished_and_isLowestDominant`), which
needs no local ring either, in `TauCeti.RingTheory.PowerSeries.Active`.

## Main results

* `TauCeti.PowerSeries.order_map_residue_eq_iff`: the formal degree is the least index of a unit
  coefficient.
* `TauCeti.PowerSeries.eventually_isDistinguished_and_isLowestDominant_map`: near the unit radius,
  the formal degree is the unique dominant index.
* `PowerSeries.IsWeierstrassFactorization.eventually_isDistinguished_and_isLowestDominant_map` and
  `PowerSeries.IsWeierstrassFactorization.eventually_eq_map_of_mul_eq`: near the unit radius,
  the image of a formal Weierstrass factorization `g = P * h` is distinguished of degree `deg P`,
  and every normed preparation of `g.map φ` is the image of the formal one.
* `PowerSeries.IsWeierstrassFactorization.eq_map_of_mul_eq`: the same identification at any
  radius `0 < r < 1` where `g.map φ` is distinguished of degree `deg P`.
* `TauCeti.PowerSeries.isDistinguished_one_map_iff` and
  `TauCeti.PowerSeries.isLowestDominant_one_map_iff`: at the radius one, the distinguished degree
  is the last index of a unit coefficient and the lowest dominant degree is the formal degree.
* `TauCeti.PowerSeries.eventually_isDistinguished_and_isLowestDominant_map_lambdaInvariant`: over a
  discrete valuation ring, the λ-invariant of a series with μ-invariant zero is its distinguished
  degree near the unit radius.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.
-/

public section

open Filter Topology IsLocalRing

namespace TauCeti

namespace PowerSeries

section LocalRing

variable {O R : Type*} [CommRing O] [IsLocalRing O] [SeminormedRing R] [NormOneClass R]
  {φ : O →+* R} {g : _root_.PowerSeries O} {s : ℕ}

/-- The reduction of `g` modulo the maximal ideal has order `s` exactly when the coefficient in
degree `s` is a unit and every earlier coefficient lies in the maximal ideal. -/
theorem order_map_residue_eq_iff :
    (g.map (residue O)).order = s ↔ IsUnit (g.coeff s) ∧ ∀ m < s, g.coeff m ∈ maximalIdeal O := by
  rw [_root_.PowerSeries.order_eq_nat]
  simp only [_root_.PowerSeries.coeff_map, residue_ne_zero_iff_isUnit, residue_eq_zero_iff]

/-- If `φ` maps into the closed unit ball and `g` has a unit coefficient, the Gauss norm of
`g.map φ` at the radius one is one. -/
theorem gaussNorm_one_map_eq_one (hφ : ∀ x, ‖φ x‖ ≤ 1) (hg : g.map (residue O) ≠ 0) :
    (g.map φ).gaussNorm norm 1 = 1 := by
  obtain ⟨n, hn⟩ := _root_.PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mpr hg
  rw [_root_.PowerSeries.coeff_map, residue_ne_zero_iff_isUnit] at hn
  rw [gaussNorm_eq_of_forall_le (s := n) fun m ↦ ?_]
  · simp [norm_map_eq_one_of_isUnit hφ hn]
  · simpa [norm_map_eq_one_of_isUnit hφ hn] using hφ (g.coeff m)

/-- **The distinguished degree at the radius one.** If `φ` maps `O` into the closed unit ball and
the maximal ideal into the open unit ball, and `g` has a unit coefficient, then `g.map φ` is
distinguished of degree `s` at the radius one exactly when `s` is the last index of a unit
coefficient of `g`. -/
theorem isDistinguished_one_map_iff (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1)
    (hg : g.map (residue O) ≠ 0) :
    IsDistinguished 1 s (g.map φ) ↔
      IsUnit (g.coeff s) ∧ ∀ m, s < m → g.coeff m ∈ maximalIdeal O := by
  have h1 := gaussNorm_one_map_eq_one hφ hg
  refine ⟨fun ⟨heq, hlt⟩ ↦ ⟨?_, fun m hm' ↦ ?_⟩, fun ⟨hu, hlt⟩ ↦ ⟨?_, fun m hm' ↦ ?_⟩⟩
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm] using heq
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm] using hu
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'

/-- **The lowest dominant degree at the radius one is the formal degree.** If `φ` maps `O` into
the closed unit ball and the maximal ideal into the open unit ball, and `g` has a unit
coefficient, then `s` is the lowest dominant degree of `g.map φ` at the radius one exactly when
the reduction of `g` modulo the maximal ideal has order `s`. -/
theorem isLowestDominant_one_map_iff (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) (hg : g.map (residue O) ≠ 0) :
    IsLowestDominant 1 s (g.map φ) ↔ (g.map (residue O)).order = s := by
  have h1 := gaussNorm_one_map_eq_one hφ hg
  rw [order_map_residue_eq_iff]
  refine ⟨fun ⟨_, heq, hlt⟩ ↦ ⟨?_, fun m hm' ↦ ?_⟩, fun ⟨hu, hlt⟩ ↦ ⟨?_, ?_, fun m hm' ↦ ?_⟩⟩
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm] using heq
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'
  · rw [h1]
    exact one_pos
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm] using hu
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'

/-- **The formal degree is the normed degree near the unit radius.** If `φ` maps `O` into the
closed unit ball and the maximal ideal into the open unit ball, and the reduction of `g` modulo
the maximal ideal has order `s`, then for all radii `r < 1` close enough to one, `s` is both the
distinguished and the lowest dominant degree of `g.map φ` at `r`. -/
theorem eventually_isDistinguished_and_isLowestDominant_map (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) (hs : (g.map (residue O)).order = s) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r s (g.map φ) ∧ IsLowestDominant r s (g.map φ) := by
  have hg : g.map (residue O) ≠ 0 := by
    rintro h
    simp [h] at hs
  exact ((isLowestDominant_one_map_iff hφ hm hg).mpr hs)
    |>.eventually_isDistinguished_and_isLowestDominant one_pos

end LocalRing

section DiscreteValuationRing

open IsDiscreteValuationRing

variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [SeminormedRing R]
  [NormOneClass R] {φ : O →+* R} {g : _root_.PowerSeries O}

/-- **The λ-invariant is the normed degree near the unit radius.** Over a discrete valuation ring,
if `φ` maps `O` into the closed unit ball and the maximal ideal into the open unit ball, and `g`
has μ-invariant zero, then for all radii `r < 1` close enough to one, the λ-invariant of `g` is
both the distinguished and the lowest dominant degree of `g.map φ` at `r`. -/
theorem eventually_isDistinguished_and_isLowestDominant_map_lambdaInvariant
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) (hg : g.muInvariant = 0) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r g.lambdaInvariant (g.map φ) ∧
      IsLowestDominant r g.lambdaInvariant (g.map φ) :=
  eventually_isDistinguished_and_isLowestDominant_map hφ hm
    (_root_.PowerSeries.order_map_residue_eq_lambdaInvariant hg)

end DiscreteValuationRing

end PowerSeries

end TauCeti

namespace PowerSeries.IsWeierstrassFactorization

open TauCeti.PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] {g : PowerSeries O} {P : Polynomial O}
  {h : PowerSeries O}

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [NormOneClass R] {φ : O →+* R}

/-- If `φ` maps `O` into the closed unit ball and the maximal ideal into the open unit ball, and
`g = P * h` is a formal Weierstrass factorization over `O`, then for all radii `r < 1` close enough
to one, the degree of `P` is both the distinguished and the lowest dominant degree of `g.map φ`
at `r`. -/
theorem eventually_isDistinguished_and_isLowestDominant_map (H : g.IsWeierstrassFactorization P h)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r P.natDegree (g.map φ) ∧
      IsLowestDominant r P.natDegree (g.map φ) := by
  refine TauCeti.PowerSeries.eventually_isDistinguished_and_isLowestDominant_map hφ hm ?_
  rw [H.natDegree_eq_toNat_order_map, ENat.natCast_toNat]
  exact _root_.PowerSeries.order_finite_iff_ne_zero.mpr H.map_ne_zero |>.ne

end SeminormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  {φ : O →+* R} {r : ℝ}

/-- **Formal preparation is normed preparation at a distinguished radius.** Let `φ` map `O` into
the closed unit ball, let `g = P * h` be a formal Weierstrass factorization over `O`, with `P`
distinguished at the maximal ideal and `h` a unit, and let `0 < r < 1` be a radius at which
`g.map φ` is distinguished of degree `deg P`. Then any factorization of `g.map φ` as a unit `e` of
the ring of series restricted at `r` times a monic polynomial `ω` of degree `deg P` is the image of
the formal one: `e = h.map φ` and `ω = P.map φ`. -/
theorem eq_map_of_mul_eq (H : g.IsWeierstrassFactorization P h) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hd : IsDistinguished r P.natDegree (g.map φ))
    (e : PowerSeries.IsRestricted.subring (R := R) r) (ω : Polynomial R) (he : IsUnit e)
    (hω : ω.IsMonicOfDegree P.natDegree)
    (heq : (e : PowerSeries R) * (ω : PowerSeries R) = g.map φ) :
    (e : PowerSeries R) = h.map φ ∧ ω = P.map φ := by
  have hr : |r| < 1 := by rwa [abs_of_pos hr0]
  have : Nontrivial R := NormOneClass.nontrivial
  have hP : (P.map φ).IsMonicOfDegree P.natDegree :=
    ⟨H.isDistinguishedAt.monic.natDegree_map φ, H.isDistinguishedAt.monic.map φ⟩
  have hformal : ((⟨h.map φ, h.isRestricted_map_of_abs_lt_one hφ hr⟩ :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) *
        ((P.map φ : Polynomial R) : PowerSeries R) = g.map φ := by
    rw [H.eq_mul, map_mul, Polynomial.polynomial_map_coe, mul_comm]
  obtain ⟨h1, h2⟩ := hd.eq_and_eq_of_mul_eq_mul hr0 he (isUnit_mk_map hφ H.isUnit hr) hω hP heq
    hformal
  exact ⟨congrArg Subtype.val h1, h2⟩

/-- **Formal preparation is normed preparation near the unit radius.** Let `φ` map `O` into the
closed unit ball and the maximal ideal into the open unit ball, and let `g = P * h` be a formal
Weierstrass factorization over `O`, with `P` distinguished at the maximal ideal and `h` a unit.
For all radii `r < 1` close enough to one, any factorization of `g.map φ` as a unit `e` of the
ring of series restricted at `r` times a monic polynomial `ω` of degree `deg P` is the image of
the formal one: `e = h.map φ` and `ω = P.map φ`. -/
theorem eventually_eq_map_of_mul_eq (H : g.IsWeierstrassFactorization P h)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ (e : PowerSeries.IsRestricted.subring (R := R) r) (ω : Polynomial R),
      IsUnit e → ω.IsMonicOfDegree P.natDegree → (e : PowerSeries R) * (ω : PowerSeries R) =
        g.map φ → (e : PowerSeries R) = h.map φ ∧ ω = P.map φ := by
  filter_upwards [H.eventually_isDistinguished_and_isLowestDominant_map hφ hm,
    Ioo_mem_nhdsLT zero_lt_one] with r ⟨hd, _⟩ ⟨hr0, hr1⟩
  exact H.eq_map_of_mul_eq hφ hr0 hr1 hd

end NormedCommRing

end PowerSeries.IsWeierstrassFactorization
