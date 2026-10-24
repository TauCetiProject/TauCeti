/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Map
public import TauCeti.RingTheory.PowerSeries.Weierstrass.DivMod
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Coefficient maps and Weierstrass theory

A bounded homomorphism of ultrametric normed commutative rings acts coefficientwise on
restricted series. When a divisor and its image are multiplicatively distinguished of the same
degree at the same positive radius, this map commutes with Weierstrass quotient and remainder.
No assumption that the coefficient map preserves norms or is injective is needed.

Preparation is also compatible with coefficient maps. The image of a monic polynomial factor
and a restricted unit factor is the prepared factorization of the image series, provided that
the latter is multiplicatively distinguished of the same degree. In particular the mapped
polynomial has the required Gauss norm and the mapped unit is multiplicative, even though a
bounded homomorphism need not preserve multiplicative units in general.

The comparison of given prepared factorizations uses only uniqueness and needs no completeness.
Completeness of the target suffices to show that a mapped factorization has the preparation
normalizations. These results apply in particular to isometric extensions of complete
ultrametric fields: `IsMulDistinguished.map` supplies the image distinguishedness.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27 and Corollary 1.28, for the division and
  preparation theorems whose uniqueness gives these compatibilities.
-/

public section

namespace TauCeti.PowerSeries

open TauCeti.MvPowerSeries

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {c : ℝ} {s : ℕ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)

section Division

variable [CompleteSpace R] [CompleteSpace S]
  {g : PowerSeries.IsRestricted.subring (R := R) c}
  (hg : IsMulDistinguished c s (g : PowerSeries R))
  (hg' : IsMulDistinguished c s (restrictedMap φ hφ g : PowerSeries S)) (hc : 0 < c)

private theorem map_division (f : PowerSeries.IsRestricted.subring (R := R) c) :
    hg'.weierstrassDiv hc (restrictedMap φ hφ f) =
        restrictedMap φ hφ (hg.weierstrassDiv hc f) ∧
      hg'.weierstrassMod hc (restrictedMap φ hφ f) = (hg.weierstrassMod hc f).map φ := by
  apply (hg'.weierstrassDiv_eq_and_weierstrassMod_eq_iff hc
    ((Polynomial.degree_map_le).trans_lt (hg.degree_weierstrassMod_lt hc f))).mpr
  -- Give the multivariate map its native univariate source and target, so the ring laws match.
  let Φ : PowerSeries.IsRestricted.subring (R := R) c →+*
      PowerSeries.IsRestricted.subring (R := S) c := restrictedMap φ hφ
  have hpoly (p : Polynomial R) : Φ (polynomialToRestricted c p) =
      polynomialToRestricted c (p.map φ) := by
    apply Subtype.ext
    calc
      (Φ (polynomialToRestricted c p) : PowerSeries S) =
          PowerSeries.map φ (polynomialToRestricted c p : PowerSeries R) :=
        coe_restrictedMap φ hφ _
      _ = PowerSeries.map φ (p : PowerSeries R) := by rw [coe_polynomialToRestricted]
      _ = (p.map φ : PowerSeries S) := Polynomial.polynomial_map_coe.symm
      _ = (polynomialToRestricted c (p.map φ) : PowerSeries S) :=
        (coe_polynomialToRestricted (c := c) _).symm
  have h := congrArg Φ (hg.mul_weierstrassDiv_add_weierstrassMod hc f)
  simp only [map_add, map_mul, hpoly] at h
  exact h

/-- Bounded coefficient maps commute with the Weierstrass quotient, provided the divisor
and its image are multiplicatively distinguished of the same degree at the given radius. -/
@[simp]
theorem IsMulDistinguished.map_weierstrassDiv
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    restrictedMap φ hφ (hg.weierstrassDiv hc f) =
      hg'.weierstrassDiv hc (restrictedMap φ hφ f) :=
  (map_division φ hφ hg hg' hc f).1.symm

/-- Bounded coefficient maps commute with the polynomial Weierstrass remainder, provided
the divisor and its image are multiplicatively distinguished of the same degree. The coefficient
bound is supplied explicitly, since it cannot be inferred from the polynomial on the left. -/
theorem IsMulDistinguished.map_weierstrassMod
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (hg.weierstrassMod hc f).map φ =
      hg'.weierstrassMod hc (restrictedMap φ hφ f) :=
  (map_division φ hφ hg hg' hc f).2.symm

end Division

section Preparation

variable {e : PowerSeries.IsRestricted.subring (R := R) c}
  {e' : PowerSeries.IsRestricted.subring (R := S) c} {ω : Polynomial R} {ω' : Polynomial S}

/-- A prepared factorization over the target agrees with a mapped monic factorization
whose restricted factor is a unit. Only the target polynomial needs to be distinguished;
the coefficient map may be noninjective and need not preserve norms. -/
theorem IsMulDistinguished.eq_map_of_mul_eq
    (hω' : IsMulDistinguished c s (ω' : PowerSeries S)) (hc : 0 < c)
    (hωm' : ω'.IsMonicOfDegree s) (hωm : ω.IsMonicOfDegree s) (he : IsUnit e)
    (h : (e' : PowerSeries S) * (ω' : PowerSeries S) =
      PowerSeries.map φ ((e : PowerSeries R) * (ω : PowerSeries R))) :
    e' = restrictedMap φ hφ e ∧ ω' = ω.map φ := by
  have : Nontrivial S := hω'.nontrivial
  have hm : (ω.map φ).IsMonicOfDegree s :=
    ⟨(hωm.monic.natDegree_map φ).trans hωm.natDegree_eq, hωm.monic.map φ⟩
  apply hω'.eq_and_eq_of_mul_eq_mul hc hωm' hm (he.map (restrictedMap φ hφ))
  -- Specialize the coefficient-map formula to the native univariate carrier.
  have hmap : (restrictedMap φ hφ e : PowerSeries S) = PowerSeries.map φ (e : PowerSeries R) :=
    coe_restrictedMap φ hφ e
  exact h.trans ((map_mul (PowerSeries.map φ) _ _).trans
    (congrArg₂ (· * ·) hmap.symm Polynomial.polynomial_map_coe.symm))

/-- If the image series is multiplicatively distinguished of degree `s`, mapping any
factorization into a restricted unit and a monic degree-`s` polynomial gives a prepared
factorization: the mapped unit is multiplicative and the mapped polynomial has Gauss norm
`c ^ s`. Completeness is required only of the target coefficient ring. -/
theorem IsMulDistinguished.map_preparation [CompleteSpace S] [Fact (0 < c)]
    {g : PowerSeries R} (hg' : IsMulDistinguished c s (PowerSeries.map φ g))
    (he : IsUnit e) (hωm : ω.IsMonicOfDegree s)
    (h : (e : PowerSeries R) * (ω : PowerSeries R) = g) :
    IsNormMulUnit (restrictedMap φ hφ e) ∧
      (ω.map φ : PowerSeries S).gaussNorm norm c = c ^ s := by
  have : NormOneClass S := hg'.normOneClass
  have hgr : g.IsRestricted c := h ▸ e.2.mul (isRestricted_polynomial ω)
  obtain ⟨u, p, hu, hp, hn, hmul⟩ :=
    hg'.exists_isNormMulUnit_isMonicOfDegree_mul_eq (hgr.map φ hφ)
  have hp' := (isMulDistinguished_iff_gaussNorm_eq (Fact.out : 0 < c) hp).mpr hn
  obtain ⟨rfl, rfl⟩ := hp'.eq_map_of_mul_eq φ hφ Fact.out hp hωm he (by rw [h, hmul])
  exact ⟨hu, hn⟩

end Preparation

end TauCeti.PowerSeries
