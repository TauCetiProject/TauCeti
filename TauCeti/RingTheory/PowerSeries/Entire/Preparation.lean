/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Division
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Normalization
import Mathlib.Tactic.LinearCombination

/-!
# Normalised Weierstrass preparation of entire power series

Let `R` be a complete ultrametric normed commutative ring, whose norm need not be multiplicative
and which may have nilpotents, and let `F` be an entire power series over `R` with `F(0) = 1`.
If `F` is multiplicatively distinguished of degree `d` at a radius `c > 0`, Weierstrass
preparation at `c` writes `F = e * ω` with `ω` monic of degree `d` and `e` a unit of the ring of
series restricted at `c`. Since `F(0) = 1`, the constant coefficient of `ω` is a unit, and
rescaling both factors gives the *normalised* factorization

```text
F = P * G,    P(0) = G(0) = 1,    deg P = d,    the leading coefficient of P a unit,
              G entire and a unit of the ring of series restricted at c.
```

The inverse of `G` is in general only restricted at `c`, but `G` itself is entire: dividing `F`
by `ω` as an entire series gives an entire quotient, which by uniqueness of Weierstrass division
at `c` is `e`. The same argument shows that `P` and `G` are coprime in the ring of entire series.
The factorization is unique, the monic normalisation of `P` is the Weierstrass polynomial of `F`
at `c`, and a normalised preparation at `c` is one at every smaller radius.

Fredholm determinants of compact operators are entire series with constant coefficient `1`; this
factorization splits off from them a polynomial factor of degree `d`, coprime to the remaining
entire factor.

## Main definitions

* `TauCeti.PowerSeries.IsEntirePreparation`: `F = P * G` is a normalised entire preparation of
  `F` at the radius `c` in degree `d`.

## Main results

* `TauCeti.PowerSeries.IsMulDistinguished.exists_isEntirePreparation`,
  `TauCeti.PowerSeries.IsEntirePreparation.unique` and
  `TauCeti.PowerSeries.IsMulDistinguished.existsUnique_isEntirePreparation`: an entire series
  with constant coefficient `1`, multiplicatively distinguished of degree `d` at `c > 0`, has
  exactly one normalised entire preparation at `c` in degree `d`.
* `TauCeti.PowerSeries.IsEntirePreparation.eq_smul_and_smul_eq`: the normalised preparation is
  the rescaling of any factorization of `F` as a unit of the ring of restricted series times a
  monic polynomial of degree `d`, in particular of Weierstrass preparation.
* `TauCeti.PowerSeries.IsEntirePreparation.isCoprime`: the two factors are coprime in the ring
  of entire series.
* `TauCeti.PowerSeries.IsEntirePreparation.mono`: a normalised preparation at `c` is one at every
  smaller radius.

## References

* R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  Appendix A3.
* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Corollary 1.28, for preparation over a Banach ring.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c c' : ℝ} {d : ℕ}
  {F : R⟦X⟧} {P P' : Polynomial R} {G G' : R⟦X⟧}

variable (c d F P G) in
/-- `F = P * G` is a **normalised entire preparation** of `F` at the radius `c` in degree `d`:
`P` is a polynomial of degree `d` with invertible leading coefficient and constant coefficient
`1`, and `G` is an entire series with constant coefficient `1` which is a unit of the ring of
series restricted at `c`. An entire series with constant coefficient `1` which is
multiplicatively distinguished of degree `d` at `c > 0` has exactly one such factorization, over
a complete ultrametric ring
(`TauCeti.PowerSeries.IsMulDistinguished.existsUnique_isEntirePreparation`). Its shape is
modelled on Mathlib's `PowerSeries.IsWeierstrassFactorizationAt`. -/
structure IsEntirePreparation : Prop where
  /-- The polynomial factor has constant coefficient `1`. -/
  coeff_zero_eq_one : P.coeff 0 = 1
  /-- The polynomial factor has degree `d`. -/
  natDegree_eq : P.natDegree = d
  /-- The leading coefficient of the polynomial factor is a unit. -/
  isUnit_leadingCoeff : IsUnit P.leadingCoeff
  /-- The series factor is entire. -/
  isEntire : G.IsEntire
  /-- The series factor has constant coefficient `1`. -/
  constantCoeff_eq_one : constantCoeff G = 1
  /-- The series factor is a unit of the ring of series restricted at `c`. -/
  isUnit : IsUnit (⟨G, isEntire.isRestricted c⟩ : IsRestricted.subring (R := R) c)
  /-- `F` is the product of the two factors. -/
  eq_mul : F = P * G

/-- **The normalised preparation rescales every unit-times-monic factorization.** Let `F` be
multiplicatively distinguished of degree `d` at a positive radius `c`, and let `F = e * ω` with
`e` a unit of the ring of series restricted at `c` and `ω` a monic polynomial of degree `d`. Then
a normalised entire preparation `F = P * G` at `c` in degree `d` is `P = a • ω` and `a • G = e`,
for the leading coefficient `a` of `P`. Applied to Weierstrass preparation
(`TauCeti.PowerSeries.IsMulDistinguished.exists_isNormMulUnit_isMonicOfDegree_mul_eq`), this
says that the monic normalisation of `P` is the Weierstrass polynomial of `F` at `c`. -/
theorem IsEntirePreparation.eq_smul_and_smul_eq (h : IsEntirePreparation c d F P G)
    (hF : IsMulDistinguished c d F) (hc : 0 < c) {e : IsRestricted.subring (R := R) c}
    {ω : Polynomial R} (he : IsUnit e) (hω : ω.IsMonicOfDegree d)
    (heω : (e : R⟦X⟧) * (ω : R⟦X⟧) = F) :
    P = P.leadingCoeff • ω ∧ P.leadingCoeff • G = e := by
  exact hF.eq_smul_and_smul_eq hc h.isUnit_leadingCoeff h.natDegree_eq h.isUnit
    h.eq_mul he hω heω

/-- **Uniqueness of the normalised entire preparation.** Over an ultrametric normed commutative
ring, a series multiplicatively distinguished of degree `d` at a positive radius `c` has at most
one normalised entire preparation at `c` in degree `d`. -/
theorem IsEntirePreparation.unique (h : IsEntirePreparation c d F P G)
    (h' : IsEntirePreparation c d F P' G') (hF : IsMulDistinguished c d F) (hc : 0 < c) :
    P = P' ∧ G = G' := by
  obtain ⟨hP, hG⟩ := hF.eq_and_eq_of_normalized_mul_eq hc h.isUnit_leadingCoeff
    h'.isUnit_leadingCoeff h.natDegree_eq h'.natDegree_eq h.coeff_zero_eq_one
    h'.coeff_zero_eq_one h.isUnit h'.isUnit h.eq_mul h'.eq_mul
  exact ⟨hP, congrArg Subtype.val hG⟩

/-- A normalised entire preparation at the radius `c` is one at every radius `c'` with
`|c'| ≤ |c|`. Together with `TauCeti.PowerSeries.IsEntirePreparation.unique`, the normalised
preparations of `F` at two nested radii, at which `F` is multiplicatively distinguished of the
same degree, agree. -/
theorem IsEntirePreparation.mono (h : IsEntirePreparation c d F P G) (hc' : |c'| ≤ |c|) :
    IsEntirePreparation c' d F P G :=
  { h with isUnit := h.isUnit.map (Subring.inclusion (isRestrictedSubring_le_of_abs_le hc')) }

/-- **Normalised preparation of entire series.** Over a complete ultrametric normed commutative
ring, an entire series `F` with `F(0) = 1` which is multiplicatively distinguished of degree `d`
at a positive radius `c` is `P * G`, with `P` a polynomial of degree `d` whose leading
coefficient is a unit, `G` entire and a unit of the ring of series restricted at `c`, and
`P(0) = G(0) = 1`. -/
theorem IsMulDistinguished.exists_isEntirePreparation [CompleteSpace R]
    (hF : IsMulDistinguished c d F) (hc : 0 < c) (hFe : F.IsEntire) (hF0 : constantCoeff F = 1) :
    ∃ (P : Polynomial R) (G : R⟦X⟧), IsEntirePreparation c d F P G := by
  obtain ⟨e, ω, he, hω, hωd, heω⟩ :=
    hF.exists_isUnit_isMonicOfDegree_isMulDistinguished_mul_eq hc (hFe.isRestricted c)
  have heE : (e : R⟦X⟧).IsEntire :=
    hωd.isEntire_of_isEntire_coe_mul hc hω e.2 (by rw [mul_comm, heω]; exact hFe)
  obtain ⟨a, U, hP0, hd, ha, hU0, hU, hPU, hUe⟩ :=
    exists_normalized_factors_of_mul_eq he hω heω hF0
  have hUE : (U : R⟦X⟧).IsEntire := hUe ▸ heE.smul _
  exact ⟨a • ω, U,
    { coeff_zero_eq_one := hP0
      natDegree_eq := hd
      isUnit_leadingCoeff := ha
      isEntire := hUE
      constantCoeff_eq_one := hU0
      isUnit := hU
      eq_mul := hPU }⟩

/-- **Normalised preparation of entire series**, in its unique-existence form: over a complete
ultrametric normed commutative ring, an entire series with constant coefficient `1` which is
multiplicatively distinguished of degree `d` at a positive radius `c` has exactly one normalised
entire preparation at `c` in degree `d`. -/
theorem IsMulDistinguished.existsUnique_isEntirePreparation [CompleteSpace R]
    (hF : IsMulDistinguished c d F) (hc : 0 < c) (hFe : F.IsEntire) (hF0 : constantCoeff F = 1) :
    ∃! PG : Polynomial R × R⟦X⟧, IsEntirePreparation c d F PG.1 PG.2 := by
  obtain ⟨P, G, h⟩ := hF.exists_isEntirePreparation hc hFe hF0
  refine ⟨(P, G), h, fun PG h' ↦ ?_⟩
  obtain ⟨hP, hG⟩ := h'.unique h hF hc
  exact Prod.ext hP hG

/-- **The factors of a normalised entire preparation are coprime.** Over a complete ultrametric
normed commutative ring, if `F = P * G` is a normalised entire preparation at `c > 0` and `F` is
multiplicatively distinguished of degree `d` at `c`, then `P` and `G` are coprime in the ring of
entire series. -/
theorem IsEntirePreparation.isCoprime [CompleteSpace R] (h : IsEntirePreparation c d F P G)
    (hF : IsMulDistinguished c d F) (hc : 0 < c) :
    IsCoprime (⟨P, IsEntire.mem_subring.mpr (isEntire_coe P)⟩ : IsEntire.subring R)
      ⟨G, IsEntire.mem_subring.mpr h.isEntire⟩ := by
  have hFe : F.IsEntire := h.eq_mul ▸ (isEntire_coe P).mul h.isEntire
  obtain ⟨e, ω, he, hω, hωd, heω⟩ :=
    hF.exists_isUnit_isMonicOfDegree_isMulDistinguished_mul_eq hc (hFe.isRestricted c)
  obtain ⟨hP, -⟩ := h.eq_smul_and_smul_eq hF hc he hω heω
  -- Divide the inverse `H` of `G` at `c` by `ω`: `H = ω * q + b`. Then `1 = ω * (G * q) + G * b`,
  -- so `ω * (G * q)` is entire, and hence so is `G * q`.
  obtain ⟨H, hGH⟩ := h.isUnit.exists_right_inv
  have hGH' : G * (H : R⟦X⟧) = 1 := congrArg Subtype.val hGH
  obtain ⟨q, b, hq, hb, hqb⟩ := hωd.exists_mul_add_eq hc (isRestricted_polynomial ω) H.2
  have hbE : b.IsEntire := isEntire_iff.mpr fun _ ↦ isRestricted_of_forall_coeff_eq_zero hb
  have hωGq : (ω : R⟦X⟧) * (G * q) = 1 - G * b := by linear_combination hGH' + G * hqb
  have hGq : (G * q).IsEntire := hωd.isEntire_of_isEntire_coe_mul hc hω
    ((h.isEntire.isRestricted c).mul hq) (by rw [hωGq]; exact isEntire_one.sub (h.isEntire.mul hbE))
  set u := h.isUnit_leadingCoeff.unit
  refine ⟨⟨((u⁻¹ : Rˣ) : R) • (G * q), IsEntire.mem_subring.mpr (hGq.smul _)⟩,
    ⟨b, IsEntire.mem_subring.mpr hbE⟩, Subtype.ext ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_one]
  rw [hP, Polynomial.coe_smul, smul_mul_smul_comm, h.isUnit_leadingCoeff.val_inv_mul, one_smul]
  linear_combination hωGq

end TauCeti.PowerSeries
