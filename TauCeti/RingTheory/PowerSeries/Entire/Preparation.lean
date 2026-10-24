/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Division
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
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

* `TauCeti.PowerSeries.IsMulDistinguished.isEntire_of_isEntire_coe_mul`: a series restricted at
  `c` whose product with a Weierstrass polynomial at `c` is entire is itself entire.
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

/-- **Restricted quotients of entire series by Weierstrass polynomials are entire.** Over a
complete ultrametric normed commutative ring, let `ω` be a monic polynomial of degree `d` which
is multiplicatively distinguished of degree `d` at a positive radius `c`. If `q` is restricted at
`c` and `ω * q` is entire, then `q` is entire: it is the quotient of the entire division of
`ω * q` by `ω`. The hypothesis on `ω` cannot be dropped: `(X - 1) * ∑ Xⁿ = -1` is entire. -/
theorem IsMulDistinguished.isEntire_of_isEntire_coe_mul [CompleteSpace R] {ω : Polynomial R}
    {q : R⟦X⟧} (hω : IsMulDistinguished c d (ω : R⟦X⟧)) (hc : 0 < c)
    (hωm : ω.IsMonicOfDegree d) (hq : q.IsRestricted c) (h : ((ω : R⟦X⟧) * q).IsEntire) :
    q.IsEntire := by
  have hdiv := h.modByMonic_add_divByMonic hωm.monic
  have hr : ∀ m, d ≤ m →
      ((((ω : R⟦X⟧) * q).modByMonic ω : Polynomial R) : R⟦X⟧).coeff m = 0 := fun m hm ↦ by
    rw [Polynomial.coeff_coe, coeff_modByMonic, ite_eq_right (by rw [hωm.natDegree_eq]; omega)]
  obtain ⟨hq', -⟩ := hω.eq_and_eq_of_mul_add_eq_mul_add hc ((h.divByMonic ω).isRestricted c) hq
    hr (fun _ _ ↦ map_zero _) (by rw [add_comm, hdiv, add_zero])
  exact hq' ▸ h.divByMonic ω

variable (c d F P G) in
/-- `F = P * G` is a **normalised entire preparation** of `F` at the radius `c` in degree `d`:
`P` is a polynomial of degree `d` with invertible leading coefficient and constant coefficient
`1`, and `G` is an entire series with constant coefficient `1` which is a unit of the ring of
series restricted at `c`. An entire series with constant coefficient `1` which is
multiplicatively distinguished of degree `d` at `c > 0` has exactly one such factorization, over
a complete ultrametric ring
(`TauCeti.PowerSeries.IsMulDistinguished.existsUnique_isEntirePreparation`). -/
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

/-- Dividing the polynomial factor of a normalised entire preparation by its leading coefficient
`u`, and multiplying the series factor by `u`, writes `F` as a unit of the ring of restricted
series times a monic polynomial of degree `d`. -/
private theorem IsEntirePreparation.exists_isUnit_isMonicOfDegree_mul_eq
    (h : IsEntirePreparation c d F P G) :
    ∃ e : IsRestricted.subring (R := R) c, IsUnit e ∧
      (h.isUnit_leadingCoeff.unit⁻¹ • P).IsMonicOfDegree d ∧ (e : R⟦X⟧) = P.leadingCoeff • G ∧
      (e : R⟦X⟧) * ((h.isUnit_leadingCoeff.unit⁻¹ • P : Polynomial R) : R⟦X⟧) = F := by
  set u := h.isUnit_leadingCoeff.unit
  have hu : (u : R) = P.leadingCoeff := h.isUnit_leadingCoeff.unit_spec
  refine ⟨algebraMap R _ u * ⟨G, h.isEntire.isRestricted c⟩,
    (u.isUnit.map (algebraMap R _)).mul h.isUnit,
    ⟨by rw [Polynomial.natDegree_smul_of_smul_regular P (IsSMulRegular.all _), h.natDegree_eq],
      Polynomial.monic_of_isUnit_leadingCoeff_inv_smul h.isUnit_leadingCoeff⟩, ?_, ?_⟩
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, hu, smul_eq_C_mul]
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, ← smul_eq_C_mul, Units.smul_def,
      Polynomial.coe_smul, smul_mul_smul_comm, u.mul_inv, one_smul, mul_comm]
    exact h.eq_mul.symm

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
  obtain ⟨e', he', hω', he'G, he'F⟩ := h.exists_isUnit_isMonicOfDegree_mul_eq
  obtain ⟨rfl, rfl⟩ := hF.eq_and_eq_of_mul_eq_of_mul_eq hc he' he hω' hω he'F heω
  refine ⟨?_, he'G.symm⟩
  rw [Units.smul_def, smul_smul, h.isUnit_leadingCoeff.mul_val_inv, one_smul]

/-- **Uniqueness of the normalised entire preparation.** Over an ultrametric normed commutative
ring, a series multiplicatively distinguished of degree `d` at a positive radius `c` has at most
one normalised entire preparation at `c` in degree `d`. -/
theorem IsEntirePreparation.unique (h : IsEntirePreparation c d F P G)
    (h' : IsEntirePreparation c d F P' G') (hF : IsMulDistinguished c d F) (hc : 0 < c) :
    P = P' ∧ G = G' := by
  obtain ⟨e', he', hω', he'G, he'F⟩ := h'.exists_isUnit_isMonicOfDegree_mul_eq
  obtain ⟨hP, hG⟩ := h.eq_smul_and_smul_eq hF hc he' hω' he'F
  set ω := h'.isUnit_leadingCoeff.unit⁻¹ • P' with hω
  -- Both `P` and `P'` are multiples of `ω` with constant coefficient `1`, so their leading
  -- coefficients are both the inverse of the constant coefficient of `ω`.
  have h1 : P.leadingCoeff * ω.coeff 0 = 1 := by
    rw [← smul_eq_mul, ← Polynomial.coeff_smul, ← hP, h.coeff_zero_eq_one]
  have h2 : P'.leadingCoeff * ω.coeff 0 = 1 := by
    rw [hω, Units.smul_def, Polynomial.coeff_smul, smul_eq_mul, ← mul_assoc,
      h'.isUnit_leadingCoeff.mul_val_inv, one_mul, h'.coeff_zero_eq_one]
  have ha : P.leadingCoeff = P'.leadingCoeff :=
    calc P.leadingCoeff = P.leadingCoeff * (P'.leadingCoeff * ω.coeff 0) := by rw [h2, mul_one]
      _ = P'.leadingCoeff * (P.leadingCoeff * ω.coeff 0) := by ring
      _ = P'.leadingCoeff := by rw [h1, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hP, ha, hω, Units.smul_def, smul_smul, h'.isUnit_leadingCoeff.mul_val_inv, one_smul]
  · rw [he'G, ← ha] at hG
    exact (h.isUnit_leadingCoeff.smul_left_cancel).mp hG

/-- A normalised entire preparation at the radius `c` is one at every radius `c'` with
`|c'| ≤ |c|`. Together with `TauCeti.PowerSeries.IsEntirePreparation.unique`, the normalised
preparations of `F` at two nested radii, at which `F` is multiplicatively distinguished of the
same degree, agree. -/
theorem IsEntirePreparation.mono (h : IsEntirePreparation c d F P G) (hc' : |c'| ≤ |c|) :
    IsEntirePreparation c' d F P G :=
  { h with isUnit := h.isUnit.map (Subring.inclusion (isRestrictedSubring_le_of_abs_le hc')) }

/-- Weierstrass preparation `F = e * ω` of a series restricted at `c > 0`, with the monic
polynomial `ω` itself multiplicatively distinguished. -/
private theorem IsMulDistinguished.exists_isUnit_isMonicOfDegree_isMulDistinguished_mul_eq
    [CompleteSpace R] (hF : IsMulDistinguished c d F) (hc : 0 < c) (hFr : F.IsRestricted c) :
    ∃ (e : IsRestricted.subring (R := R) c) (ω : Polynomial R), IsUnit e ∧
      ω.IsMonicOfDegree d ∧ IsMulDistinguished c d (ω : R⟦X⟧) ∧ (e : R⟦X⟧) * ω = F := by
  have : Fact (0 < c) := ⟨hc⟩
  have : NormOneClass R := hF.normOneClass
  obtain ⟨e, ω, he, hω, hn, heω⟩ := hF.exists_isNormMulUnit_isMonicOfDegree_mul_eq hFr
  exact ⟨e, ω, he.isUnit, hω, (isMulDistinguished_iff_gaussNorm_eq hc hω).mpr hn, heω⟩

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
  -- `F(0) = e(0) * ω(0) = 1`, so `e(0)` is a unit with inverse `ω(0)`.
  have h0 : constantCoeff (e : R⟦X⟧) * ω.coeff 0 = 1 := by
    rw [← hF0, ← heω, map_mul, ← Polynomial.coeff_coe, coeff_zero_eq_constantCoeff_apply]
  let v : Rˣ := ⟨constantCoeff (e : R⟦X⟧), ω.coeff 0, h0, by rw [mul_comm]; exact h0⟩
  refine ⟨v • ω, ((v⁻¹ : Rˣ) : R) • (e : R⟦X⟧),
    { coeff_zero_eq_one := by rw [Units.smul_def, Polynomial.coeff_smul, smul_eq_mul]; exact h0
      natDegree_eq := by
        rw [Polynomial.natDegree_smul_of_smul_regular ω (IsSMulRegular.all _), hω.natDegree_eq]
      isUnit_leadingCoeff := by
        rw [Polynomial.leadingCoeff_smul_of_smul_regular ω (IsSMulRegular.all _),
          hω.leadingCoeff_eq, Units.smul_def, smul_eq_mul, mul_one]
        exact v.isUnit
      isEntire := heE.smul _
      constantCoeff_eq_one := by
        rw [smul_eq_C_mul, map_mul, constantCoeff_C, mul_comm]
        exact v.mul_inv
      isUnit := ?_
      eq_mul := ?_ }⟩
  · convert ((v⁻¹).isUnit.map (algebraMap R (IsRestricted.subring (R := R) c))).mul he using 1
    refine Subtype.ext ?_
    rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring]
    exact smul_eq_C_mul _ _
  · rw [Units.smul_def, Polynomial.coe_smul, smul_mul_smul_comm, v.mul_inv, one_smul, mul_comm,
      heω]

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
  have hGH' : G * (H : R⟦X⟧) = 1 := coe_mul_coe_eq_one hGH
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
