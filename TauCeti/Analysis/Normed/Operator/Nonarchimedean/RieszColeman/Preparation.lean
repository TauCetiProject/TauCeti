/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.PrModule
public import TauCeti.RingTheory.PowerSeries.Entire.Preparation
import TauCeti.Algebra.Polynomial.Reverse

/-!
# Finite spectral summands from Weierstrass preparation

If the last Gauss-dominant coefficient of the Fredholm series `det (1 - Tu)` at a positive
radius is a norm-multiplicative unit, normalised preparation splits off a polynomial `Q`.
The cofactor is a unit on that closed disc and is coprime to `Q` in the entire-series ring.
Thus `ker Q*(u)` is the finite projective summand cut out by the associated Riesz–Coleman
projection. Its rank at every prime is the distinguished degree. When both radii admit
preparation, enlarging the radius enlarges the spectral summand.

This construction is over complete ultrametric Tate rings, including rings with nilpotents.
It requires no valuation on the coefficient ring and makes no numerical slope assertion about
its fibres.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  Appendix A3–A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  Algebra Number Theory **13** (2019), §2.2.
-/

public section

open TauCeti.PowerSeries (IsEntirePreparation IsMulDistinguished)
open scoped PowerSeries

namespace ContinuousLinearMap

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u : M →L[R] M} {r s : ℝ} {d e : ℕ} {P Q : Polynomial R} {G H : R⟦X⟧}
  {E F : M →L[R] M}

/-- A multiplicatively distinguished Fredholm series at a positive radius determines a unique
normalised entire preparation together with its Riesz–Coleman projection. -/
theorem IsPrCompact.existsUnique_isRieszColemanProjection_of_isMulDistinguished
    (hu : u.IsPrCompact) (hd : IsMulDistinguished r d u.charPowerSeries) (hr : 0 < r) :
    ∃! data : Polynomial R × R⟦X⟧ × (M →L[R] M),
      IsEntirePreparation r d u.charPowerSeries data.1 data.2.1 ∧
        IsRieszColemanProjection u data.1 data.2.2 := by
  obtain ⟨P, G, h⟩ := hd.exists_isEntirePreparation hr hu.isEntire_charPowerSeries
    (constantCoeff_charPowerSeries u)
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection h.coeff_zero_eq_one h.isUnit_leadingCoeff
    h.isEntire h.eq_mul (h.isCoprime hd hr)
  refine ⟨(P, G, E), ⟨h, hE⟩, ?_⟩
  rintro ⟨Q, H, F⟩ ⟨h', hF⟩
  obtain ⟨rfl, rfl⟩ := h'.unique h hd hr
  exact Prod.ext rfl (Prod.ext rfl (hF.unique hE))

/-- The finite summand associated to a normalised entire preparation of a Fredholm series
has rank equal to the distinguished degree at every prime of the coefficient ring. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isEntirePreparation
    (hE : IsRieszColemanProjection u P E) (hu : u.IsPrCompact)
    (h : IsEntirePreparation r d u.charPowerSeries P G)
    (hd : IsMulDistinguished r d u.charPowerSeries) (hr : 0 < r) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = d :=
  (hE.rankAtStalk_range_of_isPrCompact hu h.coeff_zero_eq_one h.isUnit_leadingCoeff
    h.isEntire h.eq_mul (h.isCoprime hd hr) p).trans h.natDegree_eq

/-- At two nested radii with normalised entire preparations of the Fredholm series, the
smaller-radius spectral summand is contained in the larger-radius spectral summand. The
Fredholm series need only be known to be multiplicatively distinguished at the smaller radius
when both preparations and projections are given. -/
theorem IsRieszColemanProjection.range_le_of_isEntirePreparation
    (hE : IsRieszColemanProjection u P E) (hF : IsRieszColemanProjection u Q F)
    (h : IsEntirePreparation r d u.charPowerSeries P G)
    (h' : IsEntirePreparation s e u.charPowerSeries Q H)
    (hd : IsMulDistinguished r d u.charPowerSeries) (hr : 0 < r) (hrs : r ≤ s) :
    E.range ≤ F.range :=
  hE.range_le_of_reverse_dvd hF (Polynomial.reverse_dvd_reverse_of_isLeftRegular_leadingCoeff
    h.isUnit_leadingCoeff.isRegular.left (h.dvd_of_le h' hd hr hrs))

end ContinuousLinearMap
