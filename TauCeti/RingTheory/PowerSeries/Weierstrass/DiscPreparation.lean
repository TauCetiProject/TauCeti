/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Normalization

/-!
# Constant-one preparation on a closed disc

For a restricted series `f` with constant coefficient one over a complete ultrametric
field, Weierstrass preparation can be normalised as `f = P * U`, where both factors
have constant coefficient one. The polynomial has degree equal to the last active
coefficient index, and `U` is a unit of the algebra of series restricted to the disc.
These conditions determine both factors uniquely. In particular, the unit condition
is a condition in the restricted algebra, not merely in the formal power-series ring.

The normalised unit satisfies `‖U - 1‖ < 1` in the Gauss norm. Consequently the
polynomial approximation satisfies the scale-correct bound `‖f - P‖ < ‖f‖`.
No assumption of entire convergence is made.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué
  complet*, Publications Mathématiques de l'IHÉS 14 (1962), §3.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {r : ℝ} {d : ℕ}
  {f : K⟦X⟧} {P P' : Polynomial K}
  {U U' : IsRestricted.subring (R := K) r}

/-- A constant-one disc preparation at the last active index `d` is a polynomial of
degree `d` with constant coefficient one times a restricted unit with constant
coefficient one. Recording the active-index condition excludes extraneous polynomial
factors which are themselves units on the disc. -/
structure IsDiscPreparation (r : ℝ) (d : ℕ) (f : K⟦X⟧) (P : Polynomial K)
    (U : IsRestricted.subring (R := K) r) : Prop where
  /-- The degree is the last active coefficient index of the original series. -/
  isDistinguished : IsDistinguished r d f
  /-- The polynomial has constant coefficient one. -/
  coeff_zero_eq_one : P.coeff 0 = 1
  /-- The polynomial has the specified degree. -/
  natDegree_eq : P.natDegree = d
  /-- The restricted cofactor has constant coefficient one. -/
  constantCoeff_unit_eq_one : constantCoeff (U : K⟦X⟧) = 1
  /-- The cofactor is a unit on the whole closed disc. -/
  isUnit : IsUnit U
  /-- The factorisation of the original series. -/
  eq_mul : f = (P : K⟦X⟧) * (U : K⟦X⟧)

/-- A disc preparation has a nonzero polynomial factor. -/
theorem IsDiscPreparation.polynomial_ne_zero (h : IsDiscPreparation r d f P U) : P ≠ 0 := by
  intro hP
  simpa [hP] using h.coeff_zero_eq_one

/-- The leading coefficient of a disc preparation's polynomial factor is a unit. -/
theorem IsDiscPreparation.isUnit_leadingCoeff (h : IsDiscPreparation r d f P U) :
    IsUnit P.leadingCoeff :=
  (Polynomial.leadingCoeff_ne_zero.mpr h.polynomial_ne_zero).isUnit

/-- A disc preparation is multiplicatively distinguished at its polynomial degree. -/
theorem IsDiscPreparation.isMulDistinguished (h : IsDiscPreparation r d f P U) :
    IsMulDistinguished r d f :=
  isMulDistinguished_iff_isUnit.mpr
    ⟨h.isDistinguished, h.isDistinguished.coeff_ne_zero.isUnit⟩

/-- Both normalised factors, and hence their product, have constant coefficient one. -/
theorem IsDiscPreparation.constantCoeff_eq_one (h : IsDiscPreparation r d f P U) :
    constantCoeff f = 1 := by
  rw [h.eq_mul, map_mul, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    h.coeff_zero_eq_one, h.constantCoeff_unit_eq_one, one_mul]

/-- The normalised restricted unit has Gauss norm one. -/
theorem IsDiscPreparation.gaussNorm_unit_eq_one (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : (U : K⟦X⟧).gaussNorm norm r = 1 := by
  have hU := isDistinguished_zero_of_isUnit hr h.isUnit
  rw [← hU.norm_coeff_mul_pow_eq, pow_zero, mul_one,
    coeff_zero_eq_constantCoeff_apply, h.constantCoeff_unit_eq_one, norm_one]

/-- The unit of a constant-one disc preparation is strictly within one of the identity
in the Gauss norm. -/
theorem IsDiscPreparation.gaussNorm_sub_one_lt (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : ((U : K⟦X⟧) - 1).gaussNorm norm r < 1 := by
  have hU := isDistinguished_zero_of_isUnit hr h.isUnit
  simpa [trunc_one_left, coeff_zero_eq_constantCoeff_apply, h.constantCoeff_unit_eq_one,
    h.gaussNorm_unit_eq_one hr] using hU.gaussNorm_sub_trunc_lt hr U.2

/-- The error in replacing a series by its constant-one disc polynomial is strictly
smaller than the Gauss norm of the series, not necessarily smaller than one. -/
theorem IsDiscPreparation.gaussNorm_sub_polynomial_lt (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : (f - (P : K⟦X⟧)).gaussNorm norm r < f.gaussNorm norm r := by
  have hP := isRestricted_polynomial P (c := r)
  have hpos : 0 < (P : K⟦X⟧).gaussNorm norm r :=
    gaussNorm_pos hr (hasGaussNorm_of_isRestricted hP)
      (Polynomial.coe_eq_zero_iff.not.mpr h.polynomial_ne_zero)
  have herr : f - (P : K⟦X⟧) = (P : K⟦X⟧) * ((U : K⟦X⟧) - 1) := by
    rw [h.eq_mul, mul_sub, mul_one]
  rw [herr, gaussNorm_mul_of_isRestricted hr hP (U.2.sub (isRestricted_one r)),
    h.eq_mul, gaussNorm_mul_of_isRestricted hr hP U.2, h.gaussNorm_unit_eq_one hr, mul_one]
  exact (mul_lt_mul_of_pos_left (h.gaussNorm_sub_one_lt hr) hpos).trans_eq (mul_one _)

/-- The constant-one preparation rescales every unit-times-monic preparation at the
last active coefficient. In particular, its monic normalisation is the usual
Weierstrass polynomial. -/
theorem IsDiscPreparation.eq_smul_and_smul_eq (h : IsDiscPreparation r d f P U)
    (hr : 0 < r)
    {e : IsRestricted.subring (R := K) r} {ω : Polynomial K}
    (he : IsUnit e) (hω : ω.IsMonicOfDegree d)
    (heω : (e : K⟦X⟧) * (ω : K⟦X⟧) = f) :
    P = P.leadingCoeff • ω ∧ P.leadingCoeff • (U : K⟦X⟧) = (e : K⟦X⟧) := by
  exact h.isMulDistinguished.eq_smul_and_smul_eq hr h.isUnit_leadingCoeff h.natDegree_eq
    h.isUnit h.eq_mul he hω heω

/-- Constant-one disc preparations at the last active coefficient are unique. The
restricted-unit hypotheses are essential; degree and constant coefficient alone do
not specify the disc polynomial. -/
theorem IsDiscPreparation.unique (h : IsDiscPreparation r d f P U)
    (h' : IsDiscPreparation r d f P' U') (hr : 0 < r) :
    P = P' ∧ U = U' := by
  exact h.isMulDistinguished.eq_and_eq_of_normalized_mul_eq hr
    h.isUnit_leadingCoeff h'.isUnit_leadingCoeff
    h.natDegree_eq h'.natDegree_eq h.coeff_zero_eq_one h'.coeff_zero_eq_one
    h.isUnit h'.isUnit h.eq_mul h'.eq_mul

/-- A restricted series with constant coefficient one has a constant-one disc
preparation at its last active coefficient. -/
theorem IsDistinguished.exists_isDiscPreparation [CompleteSpace K]
    (hf : IsDistinguished r d f) (hr : 0 < r) (hfr : f.IsRestricted r)
    (hf0 : constantCoeff f = 1) :
    ∃ (P : Polynomial K) (U : IsRestricted.subring (R := K) r),
      IsDiscPreparation r d f P U := by
  obtain ⟨e, ω, he, hω, heω⟩ :=
    hf.exists_isUnit_isMonicOfDegree_mul_eq hf.coeff_ne_zero.isUnit hr hfr
  -- The constant-one rescaling `exists_normalized_factors_of_mul_eq` is shared with
  -- `IsMulDistinguished.exists_isEntirePreparation`, without requiring entire convergence.
  obtain ⟨a, U, hP0, hd, -, hU0, hU, hPU, -⟩ :=
    exists_normalized_factors_of_mul_eq he hω heω hf0
  exact ⟨a • ω, U, ⟨hf, hP0, hd, hU0, hU, hPU⟩⟩

/-- Unique constant-one preparation on a closed disc, with the polynomial degree
given by the greatest active coefficient index. -/
theorem IsDistinguished.existsUnique_isDiscPreparation [CompleteSpace K]
    (hf : IsDistinguished r d f) (hr : 0 < r) (hfr : f.IsRestricted r)
    (hf0 : constantCoeff f = 1) :
    ∃! PU : Polynomial K × IsRestricted.subring (R := K) r,
      IsDiscPreparation r d f PU.1 PU.2 := by
  obtain ⟨P, U, h⟩ := hf.exists_isDiscPreparation hr hfr hf0
  refine ⟨(P, U), h, fun PU h' => ?_⟩
  obtain ⟨hP, hU⟩ := h'.unique h hr
  exact Prod.ext hP hU

end TauCeti.PowerSeries
